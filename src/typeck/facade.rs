//! This module defines the AST "facade" that typechecking operates on. Instead
//!  of fully representing source code, like the AST does, this facade may be
//!  smaller (or larger) than the original source code, as typechecking and
//!  inference continues. This means that not all nodes in this facade may
//!  represent actual source code! Many of them are generated, or normalized,
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

use calypso_base::symbol::Symbol;
use id_arena::Id;

use crate::{ast, ctxt::GlobalCtxt, intern::Interned};

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
    Bound(DeBruijnIdx, Symbol),
    /// A rigid type variable generated when traversing universally quantified
    ///  types.
    Rigid(DeBruijnLvl),
    Hole(HoleRef),
    Free(Symbol),
    Arrow(Ty, Ty),
    Forall(Symbol, SubstableForall),
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

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct SubstableForall {
    // TODO: maybe use `im`, now that it won't cause lifetime issues? that way
    // it won't be so expensive to `Clone` this--in practice it shouldn't be
    // *too* expensive, but still, cloning a heap allocation somewhat
    // gratuitously seems sad to me
    pub(crate) env: Vec<(Symbol, Ty)>,
    pub(crate) ty: Id<ast::Ty>,
}

impl SubstableForall {
    pub fn instantiate(mut self, gcx: &GlobalCtxt, symbol: Symbol, ty: Ty) -> Ty {
        self.env.push((symbol, ty));
        ast_ty_to_facade(gcx, &mut self.env, self.ty)
    }
}

pub(crate) fn ast_ty_to_facade(
    gcx: &GlobalCtxt,
    env: &mut Vec<(Symbol, Ty)>,
    ty: Id<ast::Ty>,
) -> Ty {
    match gcx.arenas.ast.ty(ty).kind {
        ast::TyKind::Unit => gcx.arenas.tyck.common_tys().unit,
        ast::TyKind::Name(name) => {
            let elem = env.iter().find(|&&(sym, _)| sym == name.symbol);
            elem.map(|(_, ty)| ty)
                .copied()
                .unwrap_or_else(|| gcx.arenas.tyck.intern_ty(TyKind::Free(name.symbol)))
        }
        ast::TyKind::Arrow(a, b) => gcx.arenas.tyck.intern_ty(TyKind::Arrow(
            ast_ty_to_facade(gcx, env, a),
            ast_ty_to_facade(gcx, env, b),
        )),
        ast::TyKind::Forall(name, ty) => gcx.arenas.tyck.intern_ty(TyKind::Forall(
            name.symbol,
            SubstableForall {
                env: env.clone(),
                ty,
            },
        )),
        ast::TyKind::Err => gcx.arenas.tyck.common_tys().err,
    }
}
