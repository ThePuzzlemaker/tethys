//! This module implements Tethys's AST.

use std::{borrow::Cow, ptr};

use calypso_base::symbol::Ident;

use crate::{ctxt::TyCtxt, parse::Span};

pub const DUMMY_AST_ID: AstId = AstId { _raw: 0 };

index_vec::define_index_type! {
    pub struct AstId = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
    DEBUG_FORMAT = "AstId({})";
    DISPLAY_FORMAT = "{}";
    IMPL_RAW_CONVERSIONS = true;
}

#[derive(Debug)]
pub struct Item<'ast> {
    pub id: AstId,
    pub ident: Ident,
    pub kind: ItemKind<'ast>,
    pub span: Span,
}

impl<'ast> Item<'ast> {
    pub fn new(
        tcx: &'ast TyCtxt<'ast>,
        ident: Ident,
        kind: ItemKind<'ast>,
        span: Span,
    ) -> &'ast Item<'ast> {
        let item = tcx.arenas.ast.item.alloc(Item {
            id: tcx.arenas.ast.next_ast_id(),
            kind,
            ident,
            span,
        });
        tcx.arenas.ast.insert_node(item.id, Node::Item(item));
        item
    }
}

#[derive(Debug)]
pub enum ItemKind<'ast> {
    /// A value definition, as defined by `def`.
    Value(&'ast Ty<'ast>, &'ast Expr<'ast>),
}

#[derive(Debug)]
pub struct Expr<'ast> {
    pub id: AstId,
    pub kind: ExprKind<'ast>,
    pub span: Span,
}

impl<'ast> Expr<'ast> {
    pub fn new(tcx: &'ast TyCtxt<'ast>, kind: ExprKind<'ast>, span: Span) -> &'ast Expr<'ast> {
        let expr = tcx.arenas.ast.expr.alloc(Expr {
            id: tcx.arenas.ast.next_ast_id(),
            kind,
            span,
        });
        tcx.arenas.ast.insert_node(expr.id, Node::Expr(expr));
        expr
    }
}

#[derive(Debug)]
pub enum ExprKind<'ast> {
    Unit,
    Name(Ident),
    Apply(&'ast Expr<'ast>, &'ast Expr<'ast>),
    Lambda(Ident, &'ast Expr<'ast>),
    Let(
        Ident,
        Option<&'ast Ty<'ast>>,
        &'ast Expr<'ast>,
        &'ast Expr<'ast>,
    ),
    /// A placeholder for an expression that was not syntactically well-formed.
    Err,
}

#[derive(Debug)]
pub struct Ty<'ast> {
    pub id: AstId,
    pub kind: TyKind<'ast>,
    pub span: Span,
}

impl<'ast> Ty<'ast> {
    pub fn new(tcx: &'ast TyCtxt<'ast>, kind: TyKind<'ast>, span: Span) -> &'ast Ty<'ast> {
        let ty = tcx.arenas.ast.ty.alloc(Ty {
            id: tcx.arenas.ast.next_ast_id(),
            kind,
            span,
        });
        tcx.arenas.ast.insert_node(ty.id, Node::Ty(ty));
        ty
    }
}

#[derive(Debug)]
pub enum TyKind<'ast> {
    /// N.B. This will eventually be generalized to tuples
    Unit,
    Name(Ident),
    Arrow(&'ast Ty<'ast>, &'ast Ty<'ast>),
    Forall(Ident, &'ast Ty<'ast>),
    /// A placeholder for a type that was not syntactically well-formed
    Err,
}

impl<'a> TyKind<'a> {
    pub fn description(&'a self) -> Cow<'a, str> {
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

#[derive(Copy, Clone, Debug)]
pub enum Node<'ast> {
    Item(&'ast Item<'ast>),
    Expr(&'ast Expr<'ast>),
    Ty(&'ast Ty<'ast>),
}

impl<'ast> PartialEq<Node<'ast>> for Node<'ast> {
    fn eq(&self, other: &Node<'ast>) -> bool {
        match (self, other) {
            (Self::Item(l0), Self::Item(r0)) => ptr::eq(*l0, *r0),
            (Self::Expr(l0), Self::Expr(r0)) => ptr::eq(*l0, *r0),
            (Self::Ty(l0), Self::Ty(r0)) => ptr::eq(*l0, *r0),
            _ => false,
        }
    }
}

impl<'ast> Eq for Node<'ast> {}

impl<'ast> Node<'ast> {
    pub fn span(self) -> Span {
        *match self {
            Self::Item(Item { span, .. })
            | Self::Expr(Expr { span, .. })
            | Self::Ty(Ty { span, .. }) => span,
        }
    }

    pub fn ident(self) -> Option<Ident> {
        match self {
            Self::Item(Item { ident, .. }) => Some(*ident),
            Self::Expr(Expr { kind, .. }) => match kind {
                ExprKind::Unit | ExprKind::Apply(_, _) | ExprKind::Err => None,
                ExprKind::Name(ident)
                | ExprKind::Lambda(ident, _)
                | ExprKind::Let(ident, _, _, _) => Some(*ident),
            },
            Self::Ty(Ty { kind, .. }) => match kind {
                TyKind::Unit | TyKind::Arrow(_, _) | TyKind::Err => None,
                TyKind::Name(ident) | TyKind::Forall(ident, _) => Some(*ident),
            },
        }
    }

    pub fn id(self) -> AstId {
        match self {
            Self::Item(Item { id, .. }) | Self::Expr(Expr { id, .. }) | Self::Ty(Ty { id, .. }) => {
                *id
            }
        }
    }
}
