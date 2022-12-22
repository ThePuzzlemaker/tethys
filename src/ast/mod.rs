//! This module implements Tethys's AST.

use std::{borrow::Cow, collections::HashMap};

use calypso_base::symbol::Ident;
use id_arena::Id;

use crate::{ctxt::GlobalCtxt, parse::Span};

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
    pub fn new(gcx: &GlobalCtxt, ident: Ident, kind: ItemKind, span: Span) -> Id<Item> {
        let id = gcx.arenas.ast.next_ast_id();
        let item = gcx.arenas.ast.item.borrow_mut().alloc(Item {
            id,
            kind,
            ident,
            span,
        });
        gcx.arenas.ast.insert_node(id, Node::Item(item));
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
    pub fn new(gcx: &GlobalCtxt, kind: ExprKind, span: Span) -> Id<Expr> {
        let id = gcx.arenas.ast.next_ast_id();
        let expr = gcx
            .arenas
            .ast
            .expr
            .borrow_mut()
            .alloc(Expr { id, kind, span });
        gcx.arenas.ast.insert_node(id, Node::Expr(expr));
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
    Number(i64),
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
    pub fn new(gcx: &GlobalCtxt, kind: TyKind, span: Span) -> Id<Ty> {
        let id = gcx.arenas.ast.next_ast_id();
        let ty = gcx.arenas.ast.ty.borrow_mut().alloc(Ty { id, kind, span });
        gcx.arenas.ast.insert_node(id, Node::Ty(ty));
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
    /// A primitive type, e.g. `Integer`.
    ///
    /// **Belongs to the type namespace.**
    PrimTy(PrimTy),
    /// A primitive function, e.g. `add`
    PrimFunc(PrimFunc),
    /// Corresponds to something defined in user code, with a unique [`AstId`].
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
            Res::PrimTy(_) | Res::Err | Res::PrimFunc(_) => None,
            Res::Defn(_, id) | Res::Local(id) | Res::TyVar(id) => Some(id),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum PrimTy {
    Integer,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum PrimFunc {
    Add,
}

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
    pub fn span(self, gcx: &GlobalCtxt) -> Span {
        match self {
            Self::Item(id) => gcx.arenas.ast.item(id).span,
            Self::Expr(id) => gcx.arenas.ast.expr(id).span,
            Self::Ty(id) => gcx.arenas.ast.ty(id).span,
        }
    }

    pub fn ident(self, gcx: &GlobalCtxt) -> Option<Ident> {
        match self {
            Self::Item(id) => Some(gcx.arenas.ast.item(id).ident),
            Self::Expr(id) => match gcx.arenas.ast.expr(id).kind {
                ExprKind::Unit | ExprKind::Apply(_, _) | ExprKind::Err | ExprKind::Number(_) => {
                    None
                }
                ExprKind::Name(ident)
                | ExprKind::Lambda(ident, _)
                | ExprKind::Let(ident, _, _, _) => Some(ident),
            },
            Self::Ty(id) => match gcx.arenas.ast.ty(id).kind {
                TyKind::Unit | TyKind::Arrow(_, _) | TyKind::Err => None,
                TyKind::Name(ident) | TyKind::Forall(ident, _) => Some(ident),
            },
        }
    }

    pub fn id(self, gcx: &GlobalCtxt) -> AstId {
        match self {
            Self::Item(id) => gcx.arenas.ast.item(id).id,
            Self::Expr(id) => gcx.arenas.ast.expr(id).id,
            Self::Ty(id) => gcx.arenas.ast.ty(id).id,
        }
    }
}

#[derive(Debug, Default)]
pub struct Parentage {
    pub map: HashMap<AstId, AstId>,
}

impl Parentage {
    pub fn calculate(&mut self, gcx: &GlobalCtxt, items: &[Id<Item>]) {
        fn helper(this: &mut Parentage, gcx: &GlobalCtxt, node: Node) {
            let id = node.id(gcx);
            match node {
                Node::Item(item) => match gcx.arenas.ast.item(item).kind {
                    ItemKind::Value(ty, expr) => {
                        this.map.insert(Node::Ty(ty).id(gcx), id);
                        this.map.insert(Node::Expr(expr).id(gcx), id);

                        helper(this, gcx, Node::Ty(ty));
                        helper(this, gcx, Node::Expr(expr));
                    }
                },
                Node::Expr(expr) => match gcx.arenas.ast.expr(expr).kind {
                    ExprKind::Unit => {}
                    ExprKind::Name(_) => {}
                    ExprKind::Number(_) => {}
                    ExprKind::Apply(func, arg) => {
                        this.map.insert(Node::Expr(func).id(gcx), id);
                        this.map.insert(Node::Expr(arg).id(gcx), id);

                        helper(this, gcx, Node::Expr(func));
                        helper(this, gcx, Node::Expr(arg));
                    }
                    ExprKind::Lambda(_, expr) => {
                        this.map.insert(Node::Expr(expr).id(gcx), id);

                        helper(this, gcx, Node::Expr(expr));
                    }
                    ExprKind::Let(_, ty, val, expr_in) => {
                        if let Some(ty) = ty {
                            this.map.insert(Node::Ty(ty).id(gcx), id);

                            helper(this, gcx, Node::Ty(ty));
                        }

                        this.map.insert(Node::Expr(val).id(gcx), id);
                        this.map.insert(Node::Expr(expr_in).id(gcx), id);

                        helper(this, gcx, Node::Expr(val));
                        helper(this, gcx, Node::Expr(expr_in));
                    }
                    ExprKind::Err => {}
                },
                Node::Ty(ty) => match gcx.arenas.ast.ty(ty).kind {
                    TyKind::Unit => {}
                    TyKind::Name(_) => {}
                    TyKind::Arrow(ty_a, ty_b) => {
                        this.map.insert(Node::Ty(ty_a).id(gcx), id);
                        this.map.insert(Node::Ty(ty_b).id(gcx), id);

                        helper(this, gcx, Node::Ty(ty_a));
                        helper(this, gcx, Node::Ty(ty_b));
                    }
                    TyKind::Forall(_, ty) => {
                        this.map.insert(Node::Ty(ty).id(gcx), id);

                        helper(this, gcx, Node::Ty(ty));
                    }
                    TyKind::Err => {}
                },
            }
        }

        items
            .iter()
            .for_each(move |id| helper(self, gcx, Node::Item(*id)));
    }
}
