use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
};

use index_vec::IndexVec;
use stable_vec::InlineStableVec;
use typed_arena::Arena;

use crate::{
    ast::{self, AstId, Node},
    diag::DiagReportCtxt,
    resolve::ResolutionData,
};

pub struct TyCtxt<'tcx> {
    pub arenas: &'tcx Arenas<'tcx>,
    pub intern: Interners<'tcx>,
    pub drcx: RefCell<DiagReportCtxt>,
}

impl<'tcx> TyCtxt<'tcx> {
    pub fn clear(&self) {
        self.arenas.clear();
        self.intern.clear();
        self.drcx.borrow_mut().clear();
    }
}

pub struct AstArenas<'tcx> {
    pub expr: Arena<ast::Expr<'tcx>>,
    pub item: Arena<ast::Item<'tcx>>,
    pub ty: Arena<ast::Ty<'tcx>>,
    pub foo: Arena<ast::Node<'tcx>>,
    pub res_data: RefCell<ResolutionData>,
    next_ast_id: Cell<u32>,
    ast_id_to_node: RefCell<HashMap<AstId, Node<'tcx>>>,
}

impl<'tcx> AstArenas<'tcx> {
    pub fn clear(&self) {
        self.res_data.borrow_mut().clear();
        self.next_ast_id.replace(1);
        self.ast_id_to_node.borrow_mut().clear();
    }
}

impl<'tcx> Default for AstArenas<'tcx> {
    fn default() -> Self {
        Self {
            expr: Default::default(),
            item: Default::default(),
            ty: Default::default(),
            foo: Default::default(),
            res_data: RefCell::new(ResolutionData::default()),
            next_ast_id: Cell::new(1),
            ast_id_to_node: RefCell::new(std::collections::HashMap::new()),
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
        self.ast_id_to_node.borrow().get(&id).copied()
    }

    pub fn into_iter_nodes(&'tcx self) -> impl Iterator<Item = Node<'tcx>> {
        let v = self.ast_id_to_node.borrow();
        v.values().copied().collect::<Vec<_>>().into_iter()
    }

    pub(crate) fn insert_node(&'tcx self, id: AstId, node: Node<'tcx>) {
        self.ast_id_to_node.borrow_mut().insert(id, node);
    }
}

#[derive(Default)]
pub struct Arenas<'tcx> {
    pub ast: AstArenas<'tcx>,
}

impl<'tcx> Arenas<'tcx> {
    pub fn clear(&self) {
        self.ast.clear();
    }
}

pub struct Interners<'tcx> {
    /// The arena that interned objects are allocated from.
    pub(crate) arenas: &'tcx Arenas<'tcx>,
}

impl<'tcx> Interners<'tcx> {
    pub fn new(arenas: &'tcx Arenas<'tcx>) -> Self {
        Self { arenas }
    }

    pub fn clear(&self) {}
}
