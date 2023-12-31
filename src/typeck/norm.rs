use std::cell::RefCell;

use id_arena::{Arena, Id};

use crate::{ast::AstId, ctxt::GlobalCtxt, parse::Span};

use super::ast::{DeBruijnIdx, DeBruijnLvl, MetaEntry, MetaVar, Ty, TyKind};

pub type Env = im::Vector<Id<VTy>>;
pub type VSpine = im::Vector<Id<VTy>>;
#[derive(Clone, Debug)]
pub struct Closure(pub Env, pub Id<Ty>);

#[derive(Clone, Debug)]
pub struct VTy {
    pub kind: VTyKind,
    pub span: Span,
}

impl VTy {
    pub fn new(gcx: &GlobalCtxt, kind: VTyKind, span: Span) -> Id<VTy> {
        gcx.arenas.tyck.vty.borrow_mut().alloc(VTy { kind, span })
    }

    pub fn rigid(gcx: &GlobalCtxt, astid: AstId, lvl: DeBruijnLvl) -> Id<VTy> {
        VTy::new(
            gcx,
            VTyKind::Rigid(astid, lvl),
            Span((u32::MAX..u32::MAX).into()),
        )
    }
}

#[derive(Clone, Debug)]
pub enum VTyKind {
    Flex(MetaVar, VSpine),
    // TODO: make applyTyClosure somehow take the var span from TVar
    Rigid(AstId, DeBruijnLvl),
    Unit,
    Arrow(Id<VTy>, Id<VTy>),
    Forall(AstId, Closure),
    Free(AstId),
    Enum(AstId),
}

pub fn apply_ty_closure(gcx: &GlobalCtxt, Closure(mut env, t): Closure, u: Id<VTy>) -> Id<VTy> {
    env.push_back(u);
    eval_ty(gcx, env, t)
}

pub fn apply_meta(gcx: &GlobalCtxt, a: Id<Ty>, sp: VSpine) -> Id<VTy> {
    eval_ty(gcx, sp, a)
}

pub fn eval_meta(gcx: &GlobalCtxt, p: Span, m: MetaVar, sp: VSpine) -> Id<VTy> {
    let m1 = m.clone();
    match &*m.0.borrow() {
        (MetaEntry::Solved(v), _) => apply_meta(gcx, *v, sp),
        (MetaEntry::Unsolved, _) => VTy::new(gcx, VTyKind::Flex(m1, sp), p),
    }
}

pub fn eval_ty(gcx: &GlobalCtxt, env: Env, ty: Id<Ty>) -> Id<VTy> {
    let ty = gcx.arenas.core.ty(ty);
    match ty.kind {
        TyKind::Var(_, i) => env[i.index()],
        TyKind::Unit => VTy::new(gcx, VTyKind::Unit, ty.span),
        TyKind::Arrow(a, b) => VTy::new(
            gcx,
            VTyKind::Arrow(eval_ty(gcx, env.clone(), a), eval_ty(gcx, env, b)),
            ty.span,
        ),
        TyKind::Free(id) => VTy::new(gcx, VTyKind::Free(id), ty.span),
        TyKind::Meta(m, sp) => eval_meta(gcx, ty.span, m, eval_spine(gcx, env, sp)),
        TyKind::InsertedMeta(m) => eval_meta(gcx, ty.span, m, env),
        TyKind::Forall(x, t) => VTy::new(gcx, VTyKind::Forall(x, Closure(env, t)), ty.span),
        TyKind::Enum(id) => VTy::new(gcx, VTyKind::Enum(id), ty.span),
    }
}

pub fn eval_spine(gcx: &GlobalCtxt, env: Env, spine: im::Vector<Id<Ty>>) -> VSpine {
    spine
        .into_iter()
        .map(move |t| eval_ty(gcx, env.clone(), t))
        .collect()
}

pub fn force(gcx: &GlobalCtxt, ty: Id<VTy>) -> Id<VTy> {
    let vty = gcx.arenas.tyck.vty(ty);
    match vty.kind {
        VTyKind::Flex(m, sp) => match m.clone().0.borrow().0 {
            MetaEntry::Solved(t) => force(gcx, apply_meta(gcx, t, sp)),
            MetaEntry::Unsolved => VTy::new(gcx, VTyKind::Flex(m, sp), vty.span),
        },
        _ => ty,
    }
}

pub fn lvl2ix(l: DeBruijnLvl, x: DeBruijnLvl) -> DeBruijnIdx {
    DeBruijnIdx::from(l.index() - x.index() - 1)
}

pub fn quote_ty(gcx: &GlobalCtxt, l: DeBruijnLvl, t: Id<VTy>) -> Id<Ty> {
    let t = force(gcx, t);
    let t = gcx.arenas.tyck.vty(t);
    match t.kind {
        VTyKind::Rigid(id, l1) => Ty::new(gcx, TyKind::Var(id, lvl2ix(l, l1)), t.span),
        VTyKind::Flex(m, sp) => Ty::new(gcx, TyKind::Meta(m, quote_ty_spine(gcx, l, sp)), t.span),
        VTyKind::Unit => Ty::new(gcx, TyKind::Unit, t.span),
        VTyKind::Arrow(a, b) => Ty::new(
            gcx,
            TyKind::Arrow(quote_ty(gcx, l, a), quote_ty(gcx, l, b)),
            t.span,
        ),
        VTyKind::Forall(x, b) => Ty::new(
            gcx,
            TyKind::Forall(
                x,
                quote_ty(
                    gcx,
                    l + 1,
                    apply_ty_closure(
                        gcx,
                        b,
                        VTy::new(gcx, VTyKind::Rigid(x, l), Span((u32::MAX..u32::MAX).into())),
                    ),
                ),
            ),
            t.span,
        ),
        VTyKind::Free(id) => Ty::new(gcx, TyKind::Free(id), t.span),
        VTyKind::Enum(id) => Ty::new(gcx, TyKind::Enum(id), t.span),
    }
}

pub fn quote_ty_spine(gcx: &GlobalCtxt, l: DeBruijnLvl, spine: VSpine) -> im::Vector<Id<Ty>> {
    spine
        .into_iter()
        .map(move |a| quote_ty(gcx, l, a))
        .collect()
}

pub fn nf_ty_force(gcx: &GlobalCtxt, l: DeBruijnLvl, e: Env, t: Id<Ty>) -> Id<Ty> {
    let vt = eval_ty(gcx, e, t);
    let vt = force(gcx, vt);
    quote_ty(gcx, l, vt)
}

#[derive(Debug, Default)]
pub struct TyckArenas {
    pub vty: RefCell<Arena<VTy>>,
}

impl TyckArenas {
    pub fn clear(&self) {}

    pub fn vty(&self, id: Id<VTy>) -> VTy {
        self.vty.borrow()[id].clone()
    }
}
