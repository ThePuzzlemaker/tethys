//! This module implements Tethys's AST.

use std::borrow::Cow;

use calypso_base::symbol::Ident;
use id_arena::Id;

use crate::{ctxt::TyCtxt, parse::Span};

pub const DUMMY_AST_ID: AstId = AstId { _raw: 0 };

index_vec::define_index_type! {
    pub struct AstId = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
    DEBUG_FORMAT = "AstId({})";
    DISPLAY_FORMAT = "{}";
    IMPL_RAW_CONVERSIONS = true;
}

#[derive(Copy, Clone, Debug)]
pub struct Item {
    pub id: AstId,
    pub ident: Ident,
    pub kind: ItemKind,
    pub span: Span,
}

impl Item {
    pub fn new(tcx: &TyCtxt, ident: Ident, kind: ItemKind, span: Span) -> Id<Item> {
        let id = tcx.arenas.ast.next_ast_id();
        let item = tcx.arenas.ast.item.borrow_mut().alloc(Item {
            id,
            kind,
            ident,
            span,
        });
        tcx.arenas.ast.insert_node(id, Node::Item(item));
        item
    }
}

#[derive(Copy, Clone, Debug)]
pub enum ItemKind {
    /// A value definition, as defined by `def`.
    Value(Id<Ty>, Id<Expr>),
}

#[derive(Copy, Clone, Debug)]
pub struct Expr {
    pub id: AstId,
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    pub fn new(tcx: &TyCtxt, kind: ExprKind, span: Span) -> Id<Expr> {
        let id = tcx.arenas.ast.next_ast_id();
        let expr = tcx
            .arenas
            .ast
            .expr
            .borrow_mut()
            .alloc(Expr { id, kind, span });
        tcx.arenas.ast.insert_node(id, Node::Expr(expr));
        expr
    }
}

#[derive(Copy, Clone, Debug)]
pub enum ExprKind {
    Unit,
    Name(Ident),
    Apply(Id<Expr>, Id<Expr>),
    Lambda(Ident, Id<Expr>),
    Let(Ident, Option<Id<Ty>>, Id<Expr>, Id<Expr>),
    /// A placeholder for an expression that was not syntactically well-formed.
    Err,
}

#[derive(Copy, Clone, Debug)]
pub struct Ty {
    pub id: AstId,
    pub kind: TyKind,
    pub span: Span,
}

impl Ty {
    pub fn new(tcx: &TyCtxt, kind: TyKind, span: Span) -> Id<Ty> {
        let id = tcx.arenas.ast.next_ast_id();
        let ty = tcx.arenas.ast.ty.borrow_mut().alloc(Ty { id, kind, span });
        tcx.arenas.ast.insert_node(id, Node::Ty(ty));
        ty
    }
}

#[derive(Copy, Clone, Debug)]
pub enum TyKind {
    /// N.B. This will eventually be generalized to tuples
    Unit,
    Name(Ident),
    Arrow(Id<Ty>, Id<Ty>),
    Forall(Ident, Id<Ty>),
    /// A placeholder for a type that was not syntactically well-formed
    Err,
}

impl TyKind {
    pub fn description(&'_ self) -> Cow<'_, str> {
        match self {
            TyKind::Unit => "unit".into(),
            TyKind::Name(..) => "type".into(),
            TyKind::Arrow(..) => "arrow".into(),
            TyKind::Forall(..) => "forall".into(),
            TyKind::Err => "invalid type".into(),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Res {
    /// A primitive type, e.g. `Int`.
    ///
    /// **Belongs to the type namespace.**
    PrimTy(PrimTy),
    /// Corresponds to something defined in user code, with a unique
    /// [`AstId`].
    ///
    /// **Does not belong to a specific namespace.**
    Defn(DefnKind, AstId),
    /// A local definition, in a `let`- or lambda-expression.
    ///
    /// The [`AstId`] here refers to the `let`- or lambda-expression where the
    /// value is declared.
    ///
    /// **Belongs to the value namespace.**
    Local(AstId),
    /// A type variable.
    ///
    /// Similarly to [`Res::Local`], the [`AstId`] here refers to the
    /// `forall`-type where the type variable is declared.
    ///
    /// **Belongs to the type namespace.**
    TyVar(AstId),
    /// A dummy [`Res`] variant representing a resolution error, so compilation
    /// can continue to gather further errors before crashing.
    ///
    /// **Does not belong to a specific namespace.**
    Err,
}

impl Res {
    pub fn id(self) -> Option<AstId> {
        match self {
            Res::PrimTy(_) | Res::Err => None,
            Res::Defn(_, id) | Res::Local(id) | Res::TyVar(id) => Some(id),
        }
    }
}

/// No primitive types except unit at the moment, and that's represented
/// elsewhere
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum PrimTy {}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum DefnKind {
    Value,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Node {
    Item(Id<Item>),
    Expr(Id<Expr>),
    Ty(Id<Ty>),
}
impl Node {
    pub fn span(self, tcx: &TyCtxt) -> Span {
        match self {
            Self::Item(id) => tcx.arenas.ast.item(id).span,
            Self::Expr(id) => tcx.arenas.ast.expr(id).span,
            Self::Ty(id) => tcx.arenas.ast.ty(id).span,
        }
    }

    pub fn ident(self, tcx: &TyCtxt) -> Option<Ident> {
        match self {
            Self::Item(id) => Some(tcx.arenas.ast.item(id).ident),
            Self::Expr(id) => match tcx.arenas.ast.expr(id).kind {
                ExprKind::Unit | ExprKind::Apply(_, _) | ExprKind::Err => None,
                ExprKind::Name(ident)
                | ExprKind::Lambda(ident, _)
                | ExprKind::Let(ident, _, _, _) => Some(ident),
            },
            Self::Ty(id) => match tcx.arenas.ast.ty(id).kind {
                TyKind::Unit | TyKind::Arrow(_, _) | TyKind::Err => None,
                TyKind::Name(ident) | TyKind::Forall(ident, _) => Some(ident),
            },
        }
    }

    pub fn id(self, tcx: &TyCtxt) -> AstId {
        match self {
            Self::Item(id) => tcx.arenas.ast.item(id).id,
            Self::Expr(id) => tcx.arenas.ast.expr(id).id,
            Self::Ty(id) => tcx.arenas.ast.ty(id).id,
        }
    }
}
