use std::cell::{Cell, RefCell};

use index_vec::IndexVec;
use typed_arena::Arena;

use crate::{
    ast::{self, AstId, Node},
    diag::DiagReportCtxt,
};

pub struct TyCtxt<'tcx> {
    pub arenas: &'tcx Arenas<'tcx>,
    pub intern: Interners<'tcx>,
    pub drcx: RefCell<DiagReportCtxt>,
}

pub struct AstArenas<'tcx> {
    pub expr: Arena<ast::Expr<'tcx>>,
    pub item: Arena<ast::Item<'tcx>>,
    pub ty: Arena<ast::Ty<'tcx>>,
    next_ast_id: Cell<u32>,
    ast_id_to_node: RefCell<IndexVec<AstId, Node<'tcx>>>,
}

impl<'tcx> Default for AstArenas<'tcx> {
    fn default() -> Self {
        Self {
            expr: Default::default(),
            item: Default::default(),
            ty: Default::default(),
            next_ast_id: Cell::new(1),
            ast_id_to_node: RefCell::new(IndexVec::new()),
        }
    }
}

impl<'tcx> AstArenas<'tcx> {
    pub fn next_ast_id(&self) -> AstId {
        let id = self.next_ast_id.get();
        assert!(id < u32::MAX);
        self.next_ast_id.replace(id + 1);
        AstId::from_raw(id)
    }

    pub fn get_node_by_id(&self, id: AstId) -> Option<Node<'tcx>> {
        self.ast_id_to_node.borrow().get(id).copied()
    }

    pub(crate) fn insert_node(&self, id: AstId, node: Node<'tcx>) {
        self.ast_id_to_node.borrow_mut().insert(id, node)
    }
}

#[derive(Default)]
pub struct Arenas<'tcx> {
    pub ast: AstArenas<'tcx>,
}

pub struct Interners<'tcx> {
    /// The arena that interned objects are allocated from.
    pub(crate) arenas: &'tcx Arenas<'tcx>,
}

impl<'tcx> Interners<'tcx> {
    pub fn new(arenas: &'tcx Arenas<'tcx>) -> Self {
        Self { arenas }
    }
}
