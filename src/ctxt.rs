use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
};

use id_arena::{Arena, Id};

use crate::{
    ast::{self, AstId, Node},
    diag::DiagReportCtxt,
    resolve::ResolutionData,
};

#[derive(Default)]
pub struct TyCtxt {
    pub arenas: Arenas,
    pub drcx: RefCell<DiagReportCtxt>,
}

impl TyCtxt {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn clear(&self) {
        self.arenas.clear();
        self.drcx.borrow_mut().clear();
    }
}

pub struct AstArenas {
    pub expr: RefCell<Arena<ast::Expr>>,
    pub item: RefCell<Arena<ast::Item>>,
    pub ty: RefCell<Arena<ast::Ty>>,
    pub res_data: RefCell<ResolutionData>,
    next_ast_id: Cell<u32>,
    ast_id_to_node: RefCell<HashMap<AstId, Node>>,
}

impl AstArenas {
    pub fn clear(&self) {
        self.res_data.borrow_mut().clear();
        self.next_ast_id.replace(1);
        self.ast_id_to_node.borrow_mut().clear();
    }

    pub fn expr(&self, id: Id<ast::Expr>) -> ast::Expr {
        self.expr.borrow()[id]
    }

    pub fn item(&self, id: Id<ast::Item>) -> ast::Item {
        self.item.borrow()[id]
    }

    pub fn ty(&self, id: Id<ast::Ty>) -> ast::Ty {
        self.ty.borrow()[id]
    }
}

impl Default for AstArenas {
    fn default() -> Self {
        Self {
            expr: Default::default(),
            item: Default::default(),
            ty: Default::default(),
            res_data: RefCell::new(ResolutionData::default()),
            next_ast_id: Cell::new(1),
            ast_id_to_node: RefCell::new(std::collections::HashMap::new()),
        }
    }
}

impl AstArenas {
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
}

#[derive(Default)]
pub struct Arenas {
    pub ast: AstArenas,
}

impl Arenas {
    pub fn clear(&self) {
        self.ast.clear();
    }
}
