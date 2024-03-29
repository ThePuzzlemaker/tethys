use std::{
    cell::{Cell, RefCell},
    collections::{hash_map::Entry, HashMap},
    hash::Hash,
    rc::Rc,
};

use ariadne::{Color, Label, Report, ReportKind};
use calypso_base::symbol::{Ident, Symbol};
use id_arena::{Arena, Id};

use crate::{
    ast::{AstId, BinOpKind, PrimTy, Recursive},
    ctxt::GlobalCtxt,
    parse::Span,
};

use super::{
    norm::{nf_ty_force, VTy},
    TypeckCtxt,
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

pub const DUMMY_CORE_AST_ID: CoreAstId = CoreAstId { _raw: 0 };

index_vec::define_index_type! {
    pub struct CoreAstId = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
    DEBUG_FORMAT = "CoreAstId({})";
    DISPLAY_FORMAT = "{}";
    IMPL_RAW_CONVERSIONS = true;
}

#[derive(Clone, Debug)]
pub struct Ty {
    pub id: CoreAstId,
    pub kind: TyKind,
    pub span: Span,
}

impl Ty {
    pub fn new(gcx: &GlobalCtxt, id: CoreAstId, kind: TyKind, span: Span) -> Id<Ty> {
        let x = gcx.arenas.core.ty.borrow_mut().alloc(Ty { id, kind, span });
        assert_eq!(
            gcx.arenas
                .core
                .core_id_to_node
                .borrow_mut()
                .insert(id, Node::Ty(x)),
            None
        );
        x
    }

    pub fn is_arrow(gcx: &GlobalCtxt, mut this: Id<Ty>) -> bool {
        while let TyKind::Forall(_, _, b) = gcx.arenas.core.ty(this).kind {
            this = b;
        }
        matches!(gcx.arenas.core.ty(this).kind, TyKind::Arrow(..))
    }

    /// N.B. this function only checks for outer monotypes.
    /// Higher-rank function inputs may still be present. Use this in
    /// combination with [`Self::is_higher_rank`] to check for full
    /// monotypes.
    pub fn is_monotype(gcx: &GlobalCtxt, this: Id<Ty>) -> bool {
        !matches!(gcx.arenas.core.ty(this).kind, TyKind::Forall(..))
    }

    pub fn contains_holes(
        gcx: &GlobalCtxt,
        this: Id<Ty>,
        l: DeBruijnLvl,
        mut e: im::Vector<Id<VTy>>,
    ) -> bool {
        match gcx
            .arenas
            .core
            .ty(nf_ty_force(gcx, l, e.clone(), this))
            .kind
        {
            TyKind::Unit | TyKind::Primitive(_) | TyKind::Free(_) | TyKind::Var(..) => false,
            TyKind::Arrow(a, b) => {
                Self::contains_holes(gcx, a, l, e.clone()) || Self::contains_holes(gcx, b, l, e)
            }
            TyKind::Forall(x, _, b) => {
                e.push_back(VTy::rigid(gcx, gcx.arenas.core.next_id(), x, l));
                Self::contains_holes(gcx, b, l + 1, e)
            }
            TyKind::Meta(_, _) | TyKind::InsertedMeta(_) => true,
            TyKind::Enum(_, spine) | TyKind::Tuple(spine) => spine
                .iter()
                .any(|x| Self::contains_holes(gcx, *x, l, e.clone())),
            // Flex-tuples act as holes
            TyKind::TupleFlex(_) => true,
        }
    }

    pub fn is_higher_rank(
        gcx: &GlobalCtxt,
        this: Id<Ty>,
        l: DeBruijnLvl,
        e: im::Vector<Id<VTy>>,
    ) -> bool {
        fn inner(
            gcx: &GlobalCtxt,
            this: Id<Ty>,
            l: DeBruijnLvl,
            mut e: im::Vector<Id<VTy>>,
            outer: bool,
        ) -> bool {
            match gcx
                .arenas
                .core
                .ty(nf_ty_force(gcx, l, e.clone(), this))
                .kind
            {
                TyKind::Unit | TyKind::Primitive(_) | TyKind::Var(..) | TyKind::Free(_) => false,
                TyKind::Arrow(a, b) => {
                    inner(gcx, a, l, e.clone(), false) || inner(gcx, b, l, e, false)
                }
                TyKind::Forall(x, _, b) if outer => {
                    e.push_back(VTy::rigid(gcx, gcx.arenas.core.next_id(), x, l));
                    inner(gcx, b, l, e, true)
                }
                TyKind::Forall(_, _, _) => true,
                TyKind::Meta(_, _) | TyKind::InsertedMeta(_) => false,
                TyKind::Enum(_, spine) | TyKind::Tuple(spine) | TyKind::TupleFlex(spine) => {
                    spine.iter().any(|x| inner(gcx, *x, l, e.clone(), false))
                }
            }
        }
        inner(gcx, this, l, e, true)
    }
}

#[derive(Clone, Debug)]
pub enum TyKind {
    Unit,
    Primitive(PrimTy),
    Var(CoreAstId, DeBruijnIdx),
    Arrow(Id<Ty>, Id<Ty>),
    Forall(CoreAstId, Ident, Id<Ty>),
    Meta(MetaVar, im::Vector<Id<Ty>>),
    InsertedMeta(MetaVar),
    Free(AstId),
    Enum(AstId, im::Vector<Id<Ty>>),
    Tuple(im::Vector<Id<Ty>>),
    TupleFlex(im::Vector<Id<Ty>>),
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub id: CoreAstId,
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    pub fn new(
        gcx: &GlobalCtxt,
        id: CoreAstId,
        kind: ExprKind,
        span: Span,
        ty: Option<Id<VTy>>,
    ) -> Id<Expr> {
        let x = gcx
            .arenas
            .core
            .expr
            .borrow_mut()
            .alloc(Expr { id, kind, span });
        if let Some(ty) = ty {
            gcx.arenas.core.ty_map.borrow_mut().insert(id, ty);
        }
        assert_eq!(
            gcx.arenas
                .core
                .core_id_to_node
                .borrow_mut()
                .insert(id, Node::Expr(x)),
            None
        );
        x
    }
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Unit,
    Var(CoreAstId),
    LiftedVar(CoreAstId),
    /// N.B. this level is only valid within the most recent
    /// [`ExprKind::LiftedLam`] binder
    LiftedFree(CoreAstId),
    LiftedLamRef(CoreAstId),
    Lam(CoreAstId, Ident, Id<Expr>),
    LiftedLam(im::Vector<CoreAstId>, Id<Expr>),
    LiftedApp(Id<Expr>, im::Vector<Id<Expr>>),
    App(Id<Expr>, Id<Expr>),
    TyApp(Id<Expr>, Id<Ty>),
    Let(CoreAstId, Ident, Recursive, Id<Ty>, Id<Expr>, Id<Expr>),
    TyAbs(CoreAstId, Ident, Id<Expr>),
    Free(AstId),
    EnumConstructor(AstId, usize),
    EnumRecursor(AstId),
    Number(i64),
    BinaryOp {
        left: Id<Expr>,
        kind: BinOpKind,
        right: Id<Expr>,
    },
    Boolean(bool),
    Err(ExprDeferredError),
    If(Id<Expr>, Id<Expr>, Id<Expr>),
    Tuple(im::Vector<Id<Expr>>),
    TupleProj(Id<Expr>, u64),
}

#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum ExprDeferredError {
    Discarded(Id<Ty>, TypeckCtxt),
}

impl ExprDeferredError {
    #[allow(irrefutable_let_patterns)]
    pub fn build(self, gcx: &GlobalCtxt, span: Span) -> Report<'static, Span> {
        if let ExprDeferredError::Discarded(t, tcx) = self {
            let mut w = Vec::new();
            let t = nf_ty_force(gcx, tcx.lvl, tcx.env.clone(), t);
            let doc = super::pretty::pp_ty(0, gcx, tcx.lvl, tcx.env, t);
            doc.render(80, &mut w).unwrap();
            let t = String::from_utf8(w).unwrap();

            let report = Report::build(ReportKind::Error, (), span.lo() as usize)
                .with_message("invalid identifier `_`")
                .with_label(
                    Label::new(span)
                        .with_message("invalid identifier here")
                        .with_color(Color::Blue),
                )
                .with_help(format!("this value was expected to be of type {t}"))
                .with_note(
                    "`_` is only valid on the left-hand side of a variable definition, e.g. `λ_.x`",
                );

            report.finish()
        } else {
            todo!()
        }
    }
}

impl Expr {
    pub fn report_deferred(e: Id<Expr>, gcx: &GlobalCtxt) {
        match gcx.arenas.core.expr(e).kind {
            ExprKind::Lam(_, _, x) => Self::report_deferred(x, gcx),
            ExprKind::App(f, x) => {
                Self::report_deferred(f, gcx);
                Self::report_deferred(x, gcx);
            }
            ExprKind::TyApp(f, _) => Self::report_deferred(f, gcx),
            ExprKind::Let(_, _, _, _, e1, e2) => {
                Self::report_deferred(e1, gcx);
                Self::report_deferred(e2, gcx);
            }
            ExprKind::TyAbs(_, _, x) => Self::report_deferred(x, gcx),
            ExprKind::Err(err) => {
                gcx.drcx
                    .borrow_mut()
                    .report_syncd(err.build(gcx, gcx.arenas.core.expr(e).span));
            }
            _ => {}
        }
    }
}

#[derive(Clone, Debug)]
pub struct MetaVar(pub Rc<RefCell<(MetaEntry, MetaInfo)>>);

#[derive(Debug)]
pub enum MetaEntry {
    Solved(Id<Ty>),
    Unsolved,
}

#[derive(Debug)]
pub struct MetaInfo {
    pub level: DeBruijnLvl,
    pub name: Symbol,
    pub span: Span,
}

#[derive(Debug)]
pub struct CoreAstArenas {
    pub expr: RefCell<Arena<Expr>>,
    pub ty: RefCell<Arena<Ty>>,
    next_ast_id: Cell<u32>,
    core_id_to_node: RefCell<HashMap<CoreAstId, Node>>,
    surf_to_core: RefCell<HashMap<AstId, CoreAstId>>,
    ty_map: RefCell<HashMap<CoreAstId, Id<VTy>>>,
}

impl Default for CoreAstArenas {
    fn default() -> Self {
        Self {
            expr: Default::default(),
            ty: Default::default(),
            next_ast_id: Cell::new(1),
            core_id_to_node: Default::default(),
            surf_to_core: Default::default(),
            ty_map: Default::default(),
        }
    }
}

impl CoreAstArenas {
    pub fn ty_of_expr(&self, id: CoreAstId) -> Id<VTy> {
        *self.ty_map.borrow().get(&id).unwrap()
    }

    pub fn clear(&self) {
        self.next_ast_id.set(1);
        self.core_id_to_node.borrow_mut().clear();
        self.surf_to_core.borrow_mut().clear();
    }

    pub fn expr(&self, id: Id<Expr>) -> Expr {
        self.expr.borrow()[id].clone()
    }

    pub fn ty(&self, id: Id<Ty>) -> Ty {
        self.ty.borrow()[id].clone()
    }

    pub fn next_id(&self) -> CoreAstId {
        let id = self.next_ast_id.get();
        assert!(id < u32::MAX);
        self.next_ast_id.replace(id + 1);
        CoreAstId::from_raw(id)
    }

    pub fn lower_id(&self, id: AstId) -> CoreAstId {
        match self.surf_to_core.borrow_mut().entry(id) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                let id = self.next_id();
                entry.insert(id);
                id
            }
        }
    }

    pub fn raise_id(&self, id: CoreAstId) -> Option<AstId> {
        self.surf_to_core
            .borrow()
            .iter()
            .find_map(|(&surf, &core)| (core == id).then_some(surf))
    }

    pub fn get_node_by_id(&self, id: CoreAstId) -> Option<Node> {
        self.core_id_to_node.borrow().get(&id).copied()
    }
}

// TODO: Add VTy to Node?
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Node {
    Expr(Id<Expr>),
    Ty(Id<Ty>),
}

impl Node {
    pub fn span(self, gcx: &GlobalCtxt) -> Span {
        match self {
            Self::Expr(expr) => gcx.arenas.core.expr(expr).span,
            Self::Ty(ty) => gcx.arenas.core.ty(ty).span,
        }
    }

    pub fn ident(self, gcx: &GlobalCtxt) -> Option<Ident> {
        match self {
            Self::Expr(expr) => match gcx.arenas.core.expr(expr).kind {
                ExprKind::Unit
                | ExprKind::Var(_)
                | ExprKind::App(_, _)
                | ExprKind::TyApp(_, _)
                | ExprKind::Free(_)
                | ExprKind::EnumConstructor(_, _)
                | ExprKind::EnumRecursor(_)
                | ExprKind::Err(_)
                | ExprKind::Number(_)
                | ExprKind::BinaryOp { .. }
                | ExprKind::Boolean(_)
                | ExprKind::If(..)
                | ExprKind::Tuple(..)
                | ExprKind::TupleProj(..) => None,
                ExprKind::LiftedLam(..)
                | ExprKind::LiftedVar(..)
                | ExprKind::LiftedFree(..)
                | ExprKind::LiftedApp(..)
                | ExprKind::LiftedLamRef(..) => {
                    unimplemented!()
                }
                ExprKind::Lam(_, id, _)
                | ExprKind::Let(_, id, _, _, _, _)
                | ExprKind::TyAbs(_, id, _) => Some(id),
            },
            Self::Ty(ty) => match gcx.arenas.core.ty(ty).kind {
                TyKind::Unit
                | TyKind::Var(_, _)
                | TyKind::Arrow(_, _)
                | TyKind::Meta(_, _)
                | TyKind::InsertedMeta(_)
                | TyKind::Free(_)
                | TyKind::Enum(_, _)
                | TyKind::Primitive(_)
                | TyKind::Tuple(_)
                | TyKind::TupleFlex(_) => None,
                TyKind::Forall(_, id, _) => Some(id),
            },
        }
    }

    pub fn id(self, gcx: &GlobalCtxt) -> CoreAstId {
        match self {
            Self::Expr(id) => gcx.arenas.core.expr(id).id,
            Self::Ty(id) => gcx.arenas.core.ty(id).id,
        }
    }
}
