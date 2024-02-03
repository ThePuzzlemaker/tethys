use cranelift_entity::{entity_impl, PrimaryMap};
use id_arena::Id;
use im::vector;
use spinneret::encoder::ValType;

use crate::{
    ast::{AstId, BinOpKind, PrimTy, Recursive},
    ctxt::GlobalCtxt,
    typeck::{
        ast::{self as core, CoreAstId, DeBruijnIdx, DeBruijnLvl},
        norm::{self},
    },
};

use super::llvm::{Context, Type};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Expr(u32);
entity_impl!(Expr);

#[derive(Clone, Debug)]
pub struct ExprData {
    pub ty: Ty,
    pub kind: ExprKind,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Unit,
    LiftedVar(CoreAstId),
    LiftedFree(CoreAstId),
    LiftedLamRef(CoreAstId),
    Lam(im::Vector<CoreAstId>, Expr),
    App(Expr, im::Vector<Expr>),
    Free(AstId),
    // TODO: do I need these?
    // TyApp(Expr, im::Vector<Ty>),
    // TyAbs(im::Vector<CoreAstId>, Expr),
    EnumConstructor(AstId, usize),
    EnumRecursor(AstId),
    Number(i64),
    BinaryOp {
        left: Expr,
        kind: BinOpKind,
        right: Expr,
    },
    Boolean(bool),
    If(Expr, Expr, Expr),
    Let(CoreAstId, Recursive, Expr, Expr),
    Tuple(im::Vector<Expr>),
    TupleProj(Expr, u64),
}

impl Expr {
    pub fn new(cgir: &mut CgIrArenas, ty: Ty, kind: ExprKind) -> Self {
        cgir.exprs.push(ExprData { ty, kind })
    }

    pub fn from_core(gcx: &GlobalCtxt, cgir: &mut CgIrArenas, expr: Id<core::Expr>) -> Self {
        let ty = gcx.arenas.core.ty_of_expr(gcx.arenas.core.expr(expr).id);
        let ty = norm::quote_ty(gcx, DeBruijnLvl::from(0usize), ty);
        let ty = Ty::from_core(gcx, cgir, ty);
        match gcx.arenas.core.expr(expr).kind {
            core::ExprKind::Unit => Expr::new(cgir, ty, ExprKind::Unit),
            core::ExprKind::Var(_) => unreachable!(),
            core::ExprKind::LiftedVar(ix) => Expr::new(cgir, ty, ExprKind::LiftedVar(ix)),
            core::ExprKind::LiftedFree(lvl) => Expr::new(cgir, ty, ExprKind::LiftedFree(lvl)),
            core::ExprKind::Lam(_, _, _) => unimplemented!(),
            core::ExprKind::LiftedLam(ids, e) => {
                let e = Expr::from_core(gcx, cgir, e);
                Expr::new(cgir, ty, ExprKind::Lam(ids, e))
            }
            core::ExprKind::LiftedLamRef(id) => Expr::new(cgir, ty, ExprKind::LiftedLamRef(id)),
            core::ExprKind::LiftedApp(e, es) => {
                let e = Expr::from_core(gcx, cgir, e);
                let es = es
                    .into_iter()
                    .map(|x| Expr::from_core(gcx, cgir, x))
                    .collect();
                Expr::new(cgir, ty, ExprKind::App(e, es))
            }
            core::ExprKind::App(mut head, v) => {
                let mut vec = vector![Expr::from_core(gcx, cgir, v)];
                while let core::ExprKind::App(x, v) = gcx.arenas.core.expr(head).kind {
                    vec.push_front(Expr::from_core(gcx, cgir, v));
                    head = x;
                }
                let head = Expr::from_core(gcx, cgir, head);
                Expr::new(cgir, ty, ExprKind::App(head, vec))
            }
            core::ExprKind::TyApp(e, _) => Expr::from_core(gcx, cgir, e),
            core::ExprKind::Let(x, _, rec, _, e1, e2) => {
                let e1 = Expr::from_core(gcx, cgir, e1);
                let e2 = Expr::from_core(gcx, cgir, e2);
                Expr::new(cgir, ty, ExprKind::Let(x, rec, e1, e2))
            }
            core::ExprKind::TyAbs(_, _, e) => Expr::from_core(gcx, cgir, e),
            core::ExprKind::Free(id) => Expr::new(cgir, ty, ExprKind::Free(id)),
            core::ExprKind::EnumConstructor(id, ix) => {
                Expr::new(cgir, ty, ExprKind::EnumConstructor(id, ix))
            }
            core::ExprKind::EnumRecursor(id) => Expr::new(cgir, ty, ExprKind::EnumRecursor(id)),
            core::ExprKind::Number(n) => Expr::new(cgir, ty, ExprKind::Number(n)),
            core::ExprKind::BinaryOp { left, kind, right } => {
                let left = Expr::from_core(gcx, cgir, left);
                let right = Expr::from_core(gcx, cgir, right);
                Expr::new(cgir, ty, ExprKind::BinaryOp { left, kind, right })
            }
            core::ExprKind::Boolean(b) => Expr::new(cgir, ty, ExprKind::Boolean(b)),
            core::ExprKind::Err(_) => unimplemented!(),
            core::ExprKind::If(cond, then, then_else) => {
                let cond = Expr::from_core(gcx, cgir, cond);
                let then = Expr::from_core(gcx, cgir, then);
                let then_else = Expr::from_core(gcx, cgir, then_else);
                Expr::new(cgir, ty, ExprKind::If(cond, then, then_else))
            }
            core::ExprKind::Tuple(es) => {
                let es = es
                    .into_iter()
                    .map(|x| Expr::from_core(gcx, cgir, x))
                    .collect();
                Expr::new(cgir, ty, ExprKind::Tuple(es))
            }
            core::ExprKind::TupleProj(e, ix) => {
                let e = Expr::from_core(gcx, cgir, e);
                Expr::new(cgir, ty, ExprKind::TupleProj(e, ix))
            }
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ty(u32);
entity_impl!(Ty);

#[derive(Clone, Debug)]
pub struct TyData {
    pub kind: TyKind,
}

#[derive(Clone, Debug)]
pub enum TyKind {
    Unit,
    Primitive(PrimTy),
    Var(CoreAstId, DeBruijnIdx),
    Arrow(im::Vector<Ty>, Ty),
    Forall(CoreAstId, Ty),
    Free(AstId),
    Enum(AstId, im::Vector<Ty>),
    Tuple(im::Vector<Ty>),
}

#[derive(Debug, Default)]
pub struct CgIrArenas {
    pub exprs: PrimaryMap<Expr, ExprData>,
    pub tys: PrimaryMap<Ty, TyData>,
    pub unit: Option<Type>,
}

impl Ty {
    #[inline]
    pub fn from_core(gcx: &GlobalCtxt, cgir: &mut CgIrArenas, ty: Id<core::Ty>) -> Self {
        ty_from_core_inner(gcx, cgir, ty)
    }

    pub fn new(cgir: &mut CgIrArenas, kind: TyKind) -> Self {
        cgir.tys.push(TyData { kind })
    }

    /// N.B. this function only checks for outer monotypes.
    /// Higher-rank function inputs may still be present. Use this in
    /// combination with [`Self::is_higher_rank`] to check for full
    /// monotypes.
    pub fn is_monotype(self, cgir: &CgIrArenas) -> bool {
        !matches!(&cgir.tys[self].kind, TyKind::Forall(..))
    }

    pub fn is_higher_rank(self, cgir: &CgIrArenas) -> bool {
        fn inner(cgir: &CgIrArenas, this: Ty, outer: bool) -> bool {
            match &cgir.tys[this].kind {
                TyKind::Unit | TyKind::Primitive(..) | TyKind::Var(..) | TyKind::Free(..) => false,
                TyKind::Arrow(a, b) => {
                    a.iter().any(|x| inner(cgir, *x, false)) || inner(cgir, *b, false)
                }
                TyKind::Forall(_, b) if outer => inner(cgir, *b, true),
                TyKind::Forall(..) => true,
                TyKind::Enum(_, spine) | TyKind::Tuple(spine) => {
                    spine.iter().any(|x| inner(cgir, *x, false))
                }
            }
        }
        inner(cgir, self, true)
    }

    /// Returns the scalar type this type corresponds to, if
    /// any. Returns `None` for any value which is boxed (always uses
    /// `i32`).
    pub fn scalar_type(self, cgir: &CgIrArenas) -> Option<ValType> {
        match &cgir.tys[self].kind {
            TyKind::Unit => None,
            TyKind::Primitive(PrimTy::Boolean) => Some(ValType::I32),
            TyKind::Primitive(PrimTy::Integer) => Some(ValType::I64),
            TyKind::Tuple(spine) if spine.len() == 1 => spine.front().unwrap().scalar_type(cgir),
            _ => None,
        }
    }

    pub fn unboxed_type(self, cgir: &mut CgIrArenas, ctx: &Context) -> Option<Type> {
        match cgir.tys[self].kind.clone() {
            TyKind::Unit => None,
            TyKind::Primitive(PrimTy::Boolean) => Some(Type::i1(ctx)),
            TyKind::Primitive(PrimTy::Integer) => Some(Type::i64(ctx)),
            _ => todo!(),
        }
    }

    pub fn is_arrow(self, cgir: &CgIrArenas) -> bool {
        match &cgir.tys[self].kind {
            TyKind::Arrow(..) => true,
            TyKind::Forall(_, b) => b.is_arrow(cgir),
            _ => false,
        }
    }

    #[allow(clippy::match_like_matches_macro)]
    pub fn is_zero_sized(self, cgir: &CgIrArenas) -> bool {
        match &cgir.tys[self].kind {
            TyKind::Unit => true,
            _ => false,
        }
    }
}

fn ty_from_core_inner(gcx: &GlobalCtxt, cgir: &mut CgIrArenas, ty: Id<core::Ty>) -> Ty {
    match gcx.arenas.core.ty(ty).kind.clone() {
        core::TyKind::Unit => Ty::new(cgir, TyKind::Unit),
        core::TyKind::Primitive(prim) => Ty::new(cgir, TyKind::Primitive(prim)),
        core::TyKind::Var(c, x) => Ty::new(cgir, TyKind::Var(c, x)),
        core::TyKind::Arrow(a, mut b) => {
            let mut tys = im::vector![ty_from_core_inner(gcx, cgir, a)];
            while let core::TyKind::Arrow(a1, b1) = gcx.arenas.core.ty(b).kind {
                tys.push_back(ty_from_core_inner(gcx, cgir, a1));
                b = b1;
            }
            let b = ty_from_core_inner(gcx, cgir, b);
            Ty::new(cgir, TyKind::Arrow(tys, b))
        }
        core::TyKind::Forall(x, _, b) => {
            let b = ty_from_core_inner(gcx, cgir, b);
            Ty::new(cgir, TyKind::Forall(x, b))
        }
        core::TyKind::Meta(_, _) => unreachable!(),
        core::TyKind::InsertedMeta(_) => unreachable!(),
        core::TyKind::Free(x) => Ty::new(cgir, TyKind::Free(x)),
        core::TyKind::Enum(x, tys) => {
            let tys = tys
                .into_iter()
                .map(|x| ty_from_core_inner(gcx, cgir, x))
                .collect();

            Ty::new(cgir, TyKind::Enum(x, tys))
        }
        core::TyKind::Tuple(tys) => {
            let tys = tys
                .into_iter()
                .map(|x| ty_from_core_inner(gcx, cgir, x))
                .collect();
            Ty::new(cgir, TyKind::Tuple(tys))
        }
        core::TyKind::TupleFlex(_) => unreachable!(),
    }
}
