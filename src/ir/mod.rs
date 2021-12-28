use calypso_base::symbol::{Ident, Symbol};
use index_vec::IndexVec;

mod index;
mod map;

pub use index::{DefnId, IrId, LocalId};
pub use map::Map;

use crate::parse::Span;

#[derive(Debug)]
pub struct CodeUnit<'ir> {
    pub owners: IndexVec<DefnId, OwnerNodes<'ir>>,
}

#[derive(Debug)]
pub struct OwnerNodes<'ir> {
    pub nodes: IndexVec<LocalId, ParentedNode<'ir>>,
}

#[derive(Clone, Debug)]
pub struct ParentedNode<'ir> {
    pub parent: IrId,
    pub node: Node<'ir>,
}

#[derive(Debug)]
pub enum OwnerNode<'ir> {
    Item(&'ir Item<'ir>),
}

#[derive(Copy, Clone, Debug)]
pub enum Node<'ir> {
    Item(&'ir Item<'ir>),
    Expr(&'ir Expr<'ir>),
    Ty(&'ir Ty<'ir>),
}

#[derive(Debug)]
pub struct Item<'ir> {
    pub ir_id: IrId,
    pub kind: ItemKind<'ir>,
    pub span: Span,
}

#[derive(Debug)]
pub enum ItemKind<'ir> {
    /// A value definition, as defined by `def`.
    Value(Ident, &'ir Ty<'ir>, &'ir Expr<'ir>),
}

#[derive(Debug)]
pub struct Expr<'ir> {
    pub ir_id: IrId,
    pub kind: ExprKind<'ir>,
    pub span: Span,
}

#[derive(Debug)]
pub enum ExprKind<'ir> {
    Unit,
    Path(Path),
    Apply(&'ir Expr<'ir>, &'ir Expr<'ir>),
    Lambda(Ident, &'ir Expr<'ir>),
    Let(Ident, Option<&'ir Ty<'ir>>, &'ir Expr<'ir>, &'ir Expr<'ir>),
    /// A placeholder for an expression that was not syntactically well-formed.
    Err,
}

#[derive(Debug)]
pub struct Ty<'ir> {
    pub ir_id: IrId,
    pub kind: TyKind<'ir>,
    pub span: Span,
}

#[derive(Debug)]
pub enum TyKind<'ir> {
    Path(Path),
    Arrow(&'ir Ty<'ir>, &'ir Ty<'ir>),
    Forall(Ident, &'ir Ty<'ir>),
    /// A placeholder for a type that was not syntactically well-formed.
    Err,
}

// this will be expanded once modules are implemented
#[derive(Copy, Clone, Debug)]
pub struct Path {
    pub span: Span,
    pub res: Res,
    pub symbol: Symbol,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Res {
    /// A primitive type, e.g. `Int`.
    ///
    /// **Belongs to the type namespace.**
    PrimTy(PrimTy),
    /// Corresponds to something defined in user code, with a unique
    /// [`DefnId`].
    ///
    /// **Does not belong to a specific namespace.**
    Defn(DefnKind, DefnId),
    /// A local definition, in a `let`- or lambda-expression.
    ///
    /// The [`IrId`] here refers to the `let`- or lambda-expression where the
    /// value is declared.
    ///
    /// **Belongs to the value namespace.**
    Local(IrId),
    /// A type variable.
    ///
    /// Similarly to [`Res::Local`], the [`IrId`] here refers to the
    /// `forall`-type where the type variable is declared.
    ///
    /// **Belongs to the type namespace.**
    TyVar(IrId),
    /// A dummy [`Res`] variant representing a resolution error, so compilation
    /// can continue to gather further errors before crashing.
    ///
    /// **Does not belong to a specific namespace.**
    Err,
}

// No primitive types except unit at the moment, and that's represented elsewhere
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum PrimTy {}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum DefnKind {
    Value,
}
