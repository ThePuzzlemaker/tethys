//! This module defines the AST "facade" that typechecking operates on. Instead
//!  of fully representing source code, like the AST does, this facade may be
//!  smaller (or larger) than the original source code, as typechecking and
//!  inference continues. This means that not all nodes in this facade may
//!  represent actual source code!  Many of them are generated, or normalized,
//!  during typechecking--specifically, mostly types.
//!
//! Another important thing to note is that many of the structures representing
//!  types and whatnot are interned. This way, they can be cheaply generated and
//!  manipulated without fear of insane memory usage--this is especially useful
//!  as many types generated will be the same! In many cases, they will just be
//!  hole types or functions that may be common, e.g. `Int -> Int -> Int`, which
//!  is common *at least* with a few integer operations. This interning is
//!  helpful so that each of these nodes don't take up however many bytes times
//!  however many times it shows up.
//!
//! Note that many of these structures won't contain span or
//!  [`crate::ast::AstId`] information. This means that when handling these
//!  types, you must be careful to correlate IDs when possible to make
//!  diagnostic information better.

pub mod traversal;

use std::{
    cell::RefCell,
    hash::{self, Hash},
    rc::Rc,
};

use calypso_base::symbol::{Ident, Symbol};
use id_arena::Id;

use crate::{
    ast::{self, AstId, PrimTy, Res},
    ctxt::GlobalCtxt,
    intern::Interned,
    parse::Span,
};

index_vec::define_index_type! {
    pub struct DeBruijnIdx = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
    DEBUG_FORMAT = "DebruijnIdx({})";
    DISPLAY_FORMAT = "{}";
    IMPL_RAW_CONVERSIONS = true;
}

index_vec::define_index_type! {
    pub struct DeBruijnLvl = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
    DEBUG_FORMAT = "DebruijnLvl({})";
    DISPLAY_FORMAT = "{}";
    IMPL_RAW_CONVERSIONS = true;
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Ty(pub(crate) Interned<TyS>);

impl Ty {
    #[inline]
    pub fn kind(self, gcx: &GlobalCtxt) -> TyKind {
        // &gcx.arenas.0 .0.kind
        gcx.arenas.tyck.tys(self.0 .0).kind
    }
}

/// The internal struct that represents a type.
///
/// # Important Notes
///
/// - You should not use this type in general.
/// - Values of this type are always interned and unique, stored as an
///   [`Interned<TyS>`].
/// - Instead, use the interned [`Ty`], which also provides all the methods you
///   will need to use it.
#[derive(Clone, Debug, Hash)]
pub(crate) struct TyS {
    /// Do not use this field directly, instead use [`Ty::kind`].
    pub(crate) kind: TyKind,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum TyKind {
    Unit,
    /// A bound variable under a `forall`-binder.
    ///
    /// The [`AstId`] here refers to the `forall`-binder where this variable is
    /// declared.
    Bound(AstId),
    /// A rigid type variable generated when traversing universally quantified
    ///  types.
    Rigid(DeBruijnLvl),
    Hole(HoleRef),
    Free(Symbol),
    Arrow(Ty, Ty),
    Forall(AstId, Ty),
    Err,
}

#[derive(Clone, Debug)]
pub struct HoleRef(pub Rc<RefCell<Hole>>);

impl PartialEq for HoleRef {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for HoleRef {}

impl Hash for HoleRef {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.0).hash(state);
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum Hole {
    Empty(DeBruijnLvl),
    Filled(Ty),
}

impl Ty {
    pub fn is_hole(&self, gcx: &GlobalCtxt) -> bool {
        matches!(self.kind(gcx), TyKind::Hole(_))
    }

    pub fn hole(&self, gcx: &GlobalCtxt) -> Option<HoleRef> {
        if let TyKind::Hole(hole) = self.kind(gcx) {
            Some(hole)
        } else {
            None
        }
    }

    pub fn deref(&self, gcx: &GlobalCtxt) -> Ty {
        if let TyKind::Hole(hole) = self.kind(gcx) {
            fn helper(ty: Ty, h: HoleRef, gcx: &GlobalCtxt) -> Ty {
                match &*h.0.borrow() {
                    Hole::Filled(ty) if ty.is_hole(gcx) => {
                        let hole = ty.hole(gcx).unwrap();
                        // path compression
                        let a = helper(*ty, hole.clone(), gcx);
                        *hole.0.borrow_mut() = Hole::Filled(a);
                        a
                    }
                    Hole::Filled(ty) => *ty,
                    _ => ty,
                }
            }
            helper(*self, hole, gcx)
        } else {
            *self
        }
    }
}

// #[derive(Clone, Debug, Hash, PartialEq, Eq)]
// pub struct SubstableForall {
//     // TODO: maybe use `im`, now that it won't cause lifetime issues? that way
//     // it won't be so expensive to `Clone` this--in practice it shouldn't be
//     // *too* expensive, but still, cloning a heap allocation somewhat
//     // gratuitously seems sad to me
//     pub(crate) env: Vec<(Symbol, Ty)>,
//     pub(crate) ty: Id<ast::Ty>,
// }

// impl SubstableForall {
//     pub fn instantiate(mut self, gcx: &GlobalCtxt, symbol: Symbol, ty: Ty) -> Ty {
//         self.env.push((symbol, ty));
//         ast_ty_to_facade(gcx, self.ty)
//     }
// }

// pub(crate) fn ast_ty_to_facade(
//     gcx: &GlobalCtxt,
//     env: &mut Vec<(Symbol, Ty)>,
//     ty: Id<ast::Ty>,
// ) -> Ty {
//     println!(
//         "ast_ty_to_facade env:{:#?} gcx:{:#?} ty:{:#?}",
//         env, gcx, ty
//     );
//     match gcx.arenas.ast.ty(ty).kind {
//         ast::TyKind::Unit => gcx.arenas.tyck.common_tys().unit,
//         ast::TyKind::Name(name) => {
//             let elem = env.iter().find(|&&(sym, _)| sym == name.symbol);
//             elem.map(|(_, ty)| ty)
//                 .copied()
//                 .unwrap_or_else(|| gcx.arenas.tyck.intern_ty(TyKind::Free(name.symbol)))
//         }
//         ast::TyKind::Arrow(a, b) => gcx.arenas.tyck.intern_ty(TyKind::Arrow(
//             ast_ty_to_facade(gcx, env, a),
//             ast_ty_to_facade(gcx, env, b),
//         )),
//         ast::TyKind::Forall(name, ty) => gcx.arenas.tyck.intern_ty(TyKind::Forall(
//             name.symbol,
//             SubstableForall {
//                 env: env.clone(),
//                 ty,
//             },
//         )),
//         ast::TyKind::Err => gcx.arenas.tyck.common_tys().err,
//     }
// }

// TODO: maybe find a way to memoize this?
pub(crate) fn ast_ty_to_facade(gcx: &GlobalCtxt, ty: Id<ast::Ty>) -> Ty {
    // println!("ast_ty_to_facade gcx:{:#?} ty:{:#?}", gcx, ty);
    let res_data = gcx.arenas.ast.res_data.borrow();
    let ty = gcx.arenas.ast.ty(ty);
    let ty_id = ty.id;
    match ty.kind {
        ast::TyKind::Unit => gcx.arenas.tyck.common_tys().unit,
        ast::TyKind::Name(_name) => {
            match res_data.get_by_id(ty_id) {
                Some(Res::TyVar(tyvar_id)) => gcx.arenas.tyck.intern_ty(TyKind::Bound(*tyvar_id)),
                Some(Res::PrimTy(PrimTy::Integer)) => gcx.arenas.tyck.common_tys().integer,
                // N.B. no type-level def'ns yet
                // Some(Res::Defn(defn_kind, ty_id)) =>
                Some(Res::Err) => unreachable!("ast_ty_to_facade: resolution error in name"),
                None => unreachable!("ast_ty_to_facade: unresolved name"),
                _ => unreachable!("ast_ty_to_facade: name resolved to a non-type"),
            }
        }
        ast::TyKind::Arrow(a, b) => gcx.arenas.tyck.intern_ty(TyKind::Arrow(
            ast_ty_to_facade(gcx, a),
            ast_ty_to_facade(gcx, b),
        )),
        ast::TyKind::Forall(_name, ty) => {
            gcx.arenas
                .tyck
                // N.B. forall-bound vars are indexed by their defining
                // `forall`-binder, so subst'ing can be done by traversing this
                // ty while checking vars against this `AstId`
                .intern_ty(TyKind::Forall(ty_id, ast_ty_to_facade(gcx, ty)))
        }
        ast::TyKind::Err => gcx.arenas.tyck.common_tys().err,
    }
}

pub(crate) fn outer_forall_binders(gcx: &GlobalCtxt, ty: Id<ast::Ty>) -> usize {
    fn helper(gcx: &GlobalCtxt, ty: Id<ast::Ty>, acc: usize) -> usize {
        match gcx.arenas.ast.ty(ty).kind {
            ast::TyKind::Forall(_, ty) => helper(gcx, ty, acc + 1),
            _ => acc,
        }
    }
    helper(gcx, ty, 0)
}

pub(crate) fn instantiate(gcx: &GlobalCtxt, ty: Ty, binder: AstId, with: Ty) -> Ty {
    match ty.kind(gcx) {
        TyKind::Unit
        | TyKind::Err
        | TyKind::Free(_)
	// TODO: do we need to inst. holes?
        | TyKind::Hole(_)
        | TyKind::Rigid(_) => ty,
        TyKind::Bound(id) if id == binder => with,
        TyKind::Bound(_) => ty,
        TyKind::Arrow(a, b) => gcx.arenas.tyck.intern_ty(TyKind::Arrow(
            instantiate(gcx, a, binder, with),
            instantiate(gcx, b, binder, with),
        )),
        TyKind::Forall(id1, ty1) => gcx
            .arenas
            .tyck
            .intern_ty(TyKind::Forall(id1, instantiate(gcx, ty1, binder, with))),
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    pub fn new(gcx: &GlobalCtxt, kind: ExprKind, span: Span) -> Id<Expr> {
        gcx.arenas.tyck.expr.borrow_mut().alloc(Expr { kind, span })
    }
}

#[derive(Copy, Clone, Debug)]
pub enum ExprKind {
    Unit,
    Name(Ident),
    Apply(Id<Expr>, Id<Expr>),
    Lambda(Ident, Id<Expr>),
    Let(Ident, Option<Ty>, Id<Expr>, Id<Expr>),
    Def(Ident, Ty, Id<Expr>),
    Number(i64),
    /// A placeholder for an expression that was not syntactically well-formed.
    Err,
}

pub(crate) fn instantiate_in_term(
    gcx: &GlobalCtxt,
    expr: Id<Expr>,
    binder: AstId,
    with: Ty,
) -> Id<Expr> {
    let span = gcx.arenas.tyck.expr(expr).span;
    match gcx.arenas.tyck.expr(expr).kind {
        ExprKind::Unit | ExprKind::Name(_) | ExprKind::Err | ExprKind::Number(_) => expr,
        ExprKind::Apply(func, arg) => Expr::new(
            gcx,
            ExprKind::Apply(
                instantiate_in_term(gcx, func, binder, with),
                instantiate_in_term(gcx, arg, binder, with),
            ),
            span,
        ),
        ExprKind::Lambda(name, expr) => Expr::new(
            gcx,
            ExprKind::Lambda(name, instantiate_in_term(gcx, expr, binder, with)),
            span,
        ),
        ExprKind::Let(name, ty, val, expr_in) => Expr::new(
            gcx,
            ExprKind::Let(
                name,
                ty.map(move |ty| instantiate(gcx, ty, binder, with)),
                instantiate_in_term(gcx, val, binder, with),
                instantiate_in_term(gcx, expr_in, binder, with),
            ),
            span,
        ),
        ExprKind::Def(name, ty, val) => Expr::new(
            gcx,
            ExprKind::Def(
                name,
                instantiate(gcx, ty, binder, with),
                instantiate_in_term(gcx, val, binder, with),
            ),
            span,
        ),
    }
}

pub(crate) fn ast_expr_to_facade(gcx: &GlobalCtxt, expr: Id<ast::Expr>) -> Id<Expr> {
    let span = gcx.arenas.ast.expr(expr).span;
    Expr::new(
        gcx,
        match gcx.arenas.ast.expr(expr).kind {
            ast::ExprKind::Unit => ExprKind::Unit,
            ast::ExprKind::Name(name) => ExprKind::Name(name),
            ast::ExprKind::Apply(func, arg) => {
                ExprKind::Apply(ast_expr_to_facade(gcx, func), ast_expr_to_facade(gcx, arg))
            }
            ast::ExprKind::Lambda(name, expr) => {
                ExprKind::Lambda(name, ast_expr_to_facade(gcx, expr))
            }
            ast::ExprKind::Let(name, ty, val, expr_in) => ExprKind::Let(
                name,
                ty.map(|ty| ast_ty_to_facade(gcx, ty)),
                ast_expr_to_facade(gcx, val),
                ast_expr_to_facade(gcx, expr_in),
            ),
            ast::ExprKind::Number(num) => ExprKind::Number(num),
            ast::ExprKind::Err => ExprKind::Err,
        },
        span,
    )
}

pub(crate) fn ast_item_to_facade(gcx: &GlobalCtxt, item: Id<ast::Item>) -> Id<Expr> {
    let span = gcx.arenas.ast.item(item).span;
    let ident = gcx.arenas.ast.item(item).ident;
    Expr::new(
        gcx,
        match gcx.arenas.ast.item(item).kind {
            ast::ItemKind::Value(ty, val) => ExprKind::Def(
                ident,
                ast_ty_to_facade(gcx, ty),
                ast_expr_to_facade(gcx, val),
            ),
        },
        span,
    )
}
