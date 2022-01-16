//! This module implements Tethys's IR, also called its core language.
//!
//! It is ~~stolen~~ heavily inspired by rustc's HIR (high-level intermediate
//! representation). For more information [see the rustc dev guide][1].
//!
//! [1]: https://rustc-dev-guide.rust-lang.org/hir.html
//!
//! The main structure of the IR is the [`CodeUnit`], which at the moment is
//! the term for the AST/IR for a file of code. This contains a map from
//! [`DefnId`]s to [`OwnerNodes`], which themselves contain a map from
//! [`LocalId`]s to [`ParentedNode`]s (a [`Node`] associated with its parent).
//!
//! The concept of an owner is important in this structure. Each node in the IR
//! has a parent and an owner. The meaning of a node's parent is fairly self-
//! explanatory: it refers to the node which has the current node as its child.
//! The concept of an owner is perhaps a bit less self-explanatory--the owner
//! of a node is the definition (indexed by [`DefnId`]) that contains the
//! current node (indexed by [`LocalId`]). Currently, the only nodes that are
//! owners are items (i.e.: `def`, later this will include typedefs and similar
//! constructs), but at some point this will also include modules, and at that
//! point the IR's handling of ownership will be slightly tweaked to make
//! dealing with nested owners easier.
//!
//! The IR makes use of various indexes, using [`index_vec`]. These indexes are
//! as follows:
//! - [`DefnId`]: The identifier of a definition within the local code unit. In
//!     the future, this will be extended to support modules/packages.
//! - [`LocalId`]: The identifier of a node local to an owner. Typically, the
//!     owner is at index `0`. These identifiers are usually densely clustered
//!     near `0`.
//! - [`IrId`]: A combination of a [`DefnId`] and a [`LocalId`], this
//!     identifier unambiguously refers to a node in the local code unit.
//!
//! To look up identifiers, construct a [`Map`] from a
//! [`crate::ctxt::TyCtxt`] and use the functions provided on that structure.
//!
//! For the process of lowering from AST to IR, see [`crate::lowering`].
//!
//! // TODO(@ThePuzzlemaker: ir): actually work on IR map
//!
//! // TODO(@ThePuzzlemaker: doc): better document the structures/enums within
//!     this module, beyond this basic overview

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

impl<'ir> OwnerNodes<'ir> {
    pub fn node(&self) -> OwnerNode<'ir> {
        self.nodes
            .get(LocalId::from_raw(0))
            .expect("owner node in OwnerNodes")
            .node
            .as_owner()
            .expect("node 0 is owner")
    }
}

#[derive(Clone, Debug)]
pub struct ParentedNode<'ir> {
    pub parent: LocalId,
    pub node: Node<'ir>,
}

#[derive(Copy, Clone, Debug)]
pub enum OwnerNode<'ir> {
    Item(&'ir Item<'ir>),
}

impl<'ir> OwnerNode<'ir> {
    pub fn expect_item(self) -> &'ir Item<'ir> {
        match self {
            OwnerNode::Item(item) => item,
        }
    }

    pub fn span(self) -> Span {
        match self {
            OwnerNode::Item(Item { span, .. }) => *span,
        }
    }

    pub fn ident(self) -> Option<Ident> {
        match self {
            OwnerNode::Item(Item { ident, .. }) => Some(*ident),
        }
    }
}

impl<'ir> From<OwnerNode<'ir>> for Node<'ir> {
    fn from(node: OwnerNode<'ir>) -> Self {
        match node {
            OwnerNode::Item(item) => Node::Item(item),
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Node<'ir> {
    Item(&'ir Item<'ir>),
    Expr(&'ir Expr<'ir>),
    Ty(&'ir Ty<'ir>),
}

impl<'ir> Node<'ir> {
    pub fn as_owner(self) -> Option<OwnerNode<'ir>> {
        match self {
            Node::Item(item) => Some(OwnerNode::Item(item)),
            _ => None,
        }
    }

    pub fn span(self) -> Span {
        *match self {
            Self::Item(Item { span, .. }) => span,
            Self::Expr(Expr { span, .. }) => span,
            Self::Ty(Ty { span, .. }) => span,
        }
    }

    pub fn ident(self) -> Option<Ident> {
        match self {
            Self::Item(Item { ident, .. }) => Some(*ident),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub struct Item<'ir> {
    pub ir_id: IrId,
    pub ident: Ident,
    pub kind: ItemKind<'ir>,
    pub span: Span,
}

#[derive(Debug)]
pub enum ItemKind<'ir> {
    /// A value definition, as defined by `def`.
    Value(&'ir Ty<'ir>, &'ir Expr<'ir>),
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
    /// N.B. This will eventually be generalized to tuples
    Unit,
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

/// No primitive types except unit at the moment, and that's represented
/// elsewhere
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum PrimTy {}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum DefnKind {
    Value,
}
