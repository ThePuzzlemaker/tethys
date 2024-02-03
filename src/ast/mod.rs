//! This module implements Tethys's AST.

use std::{
    borrow::Cow,
    cell::{Cell, RefCell},
    collections::HashMap,
};

use calypso_base::symbol::Ident;
use id_arena::{Arena, Id};

use crate::{ctxt::GlobalCtxt, parse::Span, resolve::ResolutionData};

pub const DUMMY_AST_ID: AstId = AstId { _raw: 0 };

pub mod pretty;

index_vec::define_index_type! {
    pub struct AstId = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
    DEBUG_FORMAT = "AstId({})";
    DISPLAY_FORMAT = "{}";
    IMPL_RAW_CONVERSIONS = true;
}

#[derive(Clone, Debug)]
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

#[derive(Clone, Debug)]
pub enum ItemKind {
    /// A value definition, as defined by `def`.
    Value(Id<Ty>, Id<Expr>),
    /// A type alias, as defined by `type`.
    TyAlias(Id<Ty>),
    /// An enum, as defined by `enum`.
    Enum(
        im::Vector<Ident>,
        im::Vector<(Ident, im::Vector<Id<Ty>>)>,
        Span,
    ),
}

#[derive(Clone, Debug)]
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

#[derive(Clone, Debug)]
pub enum ExprKind {
    Unit,
    Name(Ident),
    Apply(Id<Expr>, Id<Expr>),
    Lambda(Ident, Id<Expr>),
    Let(Ident, Recursive, Option<Id<Ty>>, Id<Expr>, Id<Expr>),
    Number(i64),
    BinaryOp {
        left: Id<Expr>,
        kind: BinOpKind,
        right: Id<Expr>,
    },
    UnaryMinus(Id<Expr>),
    UnaryNot(Id<Expr>),
    Boolean(bool),
    If(Id<Expr>, Id<Expr>, Id<Expr>),
    /// Tuples, excluding unit, which is [`ExprKind::Unit`].
    Tuple(im::Vector<Id<Expr>>),
    TupleProj(Id<Expr>, u64),
    /// A placeholder for an expression that was not syntactically
    /// well-formed.
    Err,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum BinOpKind {
    Power,
    Multiply,
    Divide,
    Modulo,
    Add,
    Subtract,
    BitShiftLeft,
    BitShiftRight,
    BitAnd,
    BitXor,
    BitOr,
    Equal,
    NotEqual,
    LessThan,
    GreaterThan,
    LessEqual,
    GreaterEqual,
    LogicalAnd,
    LogicalOr,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Recursive {
    NotRecursive,
    Recursive(Span),
}

#[derive(Clone, Debug)]
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

#[derive(Clone, Debug)]
pub enum TyKind {
    Unit,
    Name(Ident),
    Data(Ident, im::Vector<Id<Ty>>),
    Arrow(Id<Ty>, Id<Ty>),
    Forall(Ident, Id<Ty>),
    /// Tuples, excluding 0-tuples which are [`TyKind::Unit`]
    Tuple(im::Vector<Id<Ty>>),
    /// A placeholder for a type that was not syntactically
    /// well-formed
    Err,
}

impl TyKind {
    pub fn description(&'_ self) -> Cow<'_, str> {
        match self {
            TyKind::Unit => "unit".into(),
            TyKind::Name(..) => "type".into(),
            TyKind::Arrow(..) => "arrow".into(),
            TyKind::Forall(..) => "forall".into(),
            TyKind::Data(..) => "type".into(),
            TyKind::Tuple(..) => "tuple".into(),
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
    /// A generic parameter.
    ///
    /// Similarly to [`Res::Local`], the [`AstId`] here refers to the
    /// datatype definition where the type variable is declared.
    ///
    /// **Belongs to the type namespace.**
    Generic(AstId, usize),
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
            Res::Defn(_, id) | Res::Local(id) | Res::TyVar(id) | Res::Generic(id, _) => Some(id),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum PrimTy {
    Integer,
    Boolean,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum PrimFunc {
    Add,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum DefnKind {
    Primitive,
    Value,
    TyAlias,
    Enum,
    EnumConstructor(usize),
    EnumRecursor,
    Generic(usize),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Node {
    Item(Id<Item>),
    Expr(Id<Expr>),
    Ty(Id<Ty>),
    Syn(Id<Synthetic>),
}
impl Node {
    pub fn span(self, gcx: &GlobalCtxt) -> Span {
        match self {
            Self::Item(id) => gcx.arenas.ast.item(id).span,
            Self::Expr(id) => gcx.arenas.ast.expr(id).span,
            Self::Ty(id) => gcx.arenas.ast.ty(id).span,
            Self::Syn(id) => gcx.arenas.ast.syn(id).span,
        }
    }

    pub fn ident(self, gcx: &GlobalCtxt) -> Option<Ident> {
        match self {
            Self::Item(id) => Some(gcx.arenas.ast.item(id).ident),
            Self::Expr(id) => match gcx.arenas.ast.expr(id).kind {
                ExprKind::Unit
                | ExprKind::Apply(_, _)
                | ExprKind::Err
                | ExprKind::Number(_)
                | ExprKind::BinaryOp { .. }
                | ExprKind::UnaryMinus(_)
                | ExprKind::UnaryNot(_)
                | ExprKind::Boolean(_)
                | ExprKind::If(..)
                | ExprKind::Tuple(_)
                | ExprKind::TupleProj(..) => None,
                ExprKind::Name(ident)
                | ExprKind::Lambda(ident, _)
                | ExprKind::Let(ident, _, _, _, _) => Some(ident),
            },
            Self::Ty(id) => match gcx.arenas.ast.ty(id).kind {
                TyKind::Unit | TyKind::Arrow(_, _) | TyKind::Err | TyKind::Tuple(_) => None,
                TyKind::Name(ident) | TyKind::Forall(ident, _) | TyKind::Data(ident, _) => {
                    Some(ident)
                }
            },
            Self::Syn(id) => gcx.arenas.ast.syn(id).ident,
        }
    }

    pub fn id(self, gcx: &GlobalCtxt) -> AstId {
        match self {
            Self::Item(id) => gcx.arenas.ast.item(id).id,
            Self::Expr(id) => gcx.arenas.ast.expr(id).id,
            Self::Ty(id) => gcx.arenas.ast.ty(id).id,
            Self::Syn(syn) => gcx.arenas.ast.syn(syn).id,
        }
    }
}

#[derive(Debug)]
pub struct AstArenas {
    pub expr: RefCell<Arena<Expr>>,
    pub item: RefCell<Arena<Item>>,
    pub ty: RefCell<Arena<Ty>>,
    pub res_data: RefCell<ResolutionData>,
    pub syn: RefCell<Arena<Synthetic>>,
    next_ast_id: Cell<u32>,
    ast_id_to_node: RefCell<HashMap<AstId, Node>>,
}

/// HACK: make IR ids and use that instead of AstIds in
/// (V)TyKind::Forall
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Synthetic {
    pub id: AstId,
    pub span: Span,
    pub ident: Option<Ident>,
}

impl Synthetic {
    pub fn new(gcx: &GlobalCtxt, span: Span, ident: Option<Ident>) -> Id<Self> {
        let id = gcx.arenas.ast.next_ast_id();
        let syn = gcx
            .arenas
            .ast
            .syn
            .borrow_mut()
            .alloc(Synthetic { id, span, ident });
        gcx.arenas
            .ast
            .ast_id_to_node
            .borrow_mut()
            .insert(id, Node::Syn(syn));
        syn
    }
}

impl AstArenas {
    pub fn clear(&self) {
        self.res_data.borrow_mut().clear();
        self.next_ast_id.replace(1);
        self.ast_id_to_node.borrow_mut().clear();
    }

    pub fn expr(&self, id: Id<Expr>) -> Expr {
        self.expr.borrow()[id].clone()
    }

    pub fn item(&self, id: Id<Item>) -> Item {
        self.item.borrow()[id].clone()
    }

    pub fn ty(&self, id: Id<Ty>) -> Ty {
        self.ty.borrow()[id].clone()
    }

    pub fn syn(&self, id: Id<Synthetic>) -> Synthetic {
        self.syn.borrow()[id]
    }

    pub fn next_ast_id(&self) -> AstId {
        let id = self.next_ast_id.get();
        assert!(id < u32::MAX);
        self.next_ast_id.replace(id + 1);
        AstId::from_raw(id)
    }

    pub fn get_node_by_id(&self, id: AstId) -> Option<Node> {
        self.ast_id_to_node.borrow().get(&id).copied()
    }

    pub fn into_iter_nodes(&self) -> impl Iterator<Item = Node> {
        let v = self.ast_id_to_node.borrow();
        v.values().copied().collect::<Vec<_>>().into_iter()
    }

    pub(crate) fn insert_node(&self, id: AstId, node: Node) {
        self.ast_id_to_node.borrow_mut().insert(id, node);
    }

    // pub fn count_binders_between_tys(&self, root_binder: AstId, bound_var: AstId) -> usize {
    //     let mut binders = 0;

    //     let mut parentage = self.parentage.borrow();
    //     println!("{:#?}", self);

    //     let mut node = bound_var;
    //     loop {
    //         println!("count: {:?} {:?}", node, root_binder);
    //         if node == root_binder {
    //             break;
    //         }

    //         if let Some(parent) = parentage.scope_map.get(&node) {
    //             match self.ast_id_to_node.borrow().get(&node) {
    //                 Some(Node::Item(item)) => { /* does not bind types */ }
    //                 Some(Node::Expr(expr)) => { /* does not bind types */ }
    //                 Some(Node::Ty(ty)) => match self.ty(*ty).kind {
    //                     ast::TyKind::Unit => {}
    //                     ast::TyKind::Name(_) => {}
    //                     ast::TyKind::Arrow(_, _) => {}
    //                     ast::TyKind::Forall(_, _) => binders += 1,
    //                     ast::TyKind::Err => {}
    //                 },
    //                 None => unreachable!(),
    //             }

    //             node = *parent;
    //         } else {
    //             panic!("count_binders_between_tys: root_binder was not an ancestor of bound_var");
    //         }
    //     }

    //     binders
    // }
}

impl Default for AstArenas {
    fn default() -> Self {
        Self {
            expr: Default::default(),
            item: Default::default(),
            ty: Default::default(),
            syn: Default::default(),
            res_data: RefCell::new(ResolutionData::default()),
            next_ast_id: Cell::new(1),
            ast_id_to_node: RefCell::new(std::collections::HashMap::new()),
        }
    }
}
