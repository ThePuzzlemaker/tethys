use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
};

use calypso_base::symbol::Symbol;
use id_arena::{Arena, Id};

use crate::{
    ast::{self, AstId, Node, Parentage},
    diag::DiagReportCtxt,
    intern::Interner,
    resolve::ResolutionData,
    typeck::facade::{self, TyS},
};

#[derive(Default, Debug)]
pub struct GlobalCtxt {
    pub arenas: Arenas,
    pub drcx: RefCell<DiagReportCtxt>,
}

impl GlobalCtxt {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn clear(&self) {
        self.arenas.clear();
        self.drcx.borrow_mut().clear();
    }
}

#[derive(Debug)]
pub struct AstArenas {
    pub expr: RefCell<Arena<ast::Expr>>,
    pub item: RefCell<Arena<ast::Item>>,
    pub ty: RefCell<Arena<ast::Ty>>,
    pub res_data: RefCell<ResolutionData>,
    pub parentage: RefCell<Parentage>,
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
            res_data: RefCell::new(ResolutionData::default()),
            parentage: RefCell::new(Parentage::default()),
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

#[derive(Debug)]
pub struct TyckArenas {
    tys_arena: RefCell<Arena<facade::TyS>>,
    tys_interner: Interner<facade::TyS>,
    pub expr: RefCell<Arena<facade::Expr>>,
    common_tys: Option<CommonTys>,
}

#[derive(Copy, Clone, Debug)]
pub struct CommonTys {
    pub unit: facade::Ty,
    pub err: facade::Ty,
    pub integer: facade::Ty,
}

impl Default for TyckArenas {
    fn default() -> Self {
        let mut res = Self {
            tys_arena: Default::default(),
            tys_interner: Default::default(),
            expr: Default::default(),
            common_tys: None,
        };

        res.common_tys = Some(CommonTys {
            unit: res.intern_ty(facade::TyKind::Unit),
            err: res.intern_ty(facade::TyKind::Err),
            integer: res.intern_ty(facade::TyKind::Free(Symbol::intern_static("Integer"))),
        });

        res
    }
}

impl TyckArenas {
    pub fn clear(&self) {}

    pub fn intern_ty(&self, kind: facade::TyKind) -> facade::Ty {
        facade::Ty(
            self.tys_interner
                .intern(&mut *self.tys_arena.borrow_mut(), facade::TyS { kind }),
        )
    }

    pub fn common_tys(&self) -> CommonTys {
        self.common_tys.unwrap()
    }

    pub(crate) fn tys(&self, id: Id<TyS>) -> TyS {
        self.tys_arena.borrow()[id].clone()
    }

    pub fn expr(&self, id: Id<facade::Expr>) -> facade::Expr {
        self.expr.borrow()[id]
    }
}

#[derive(Default, Debug)]
pub struct Arenas {
    pub ast: AstArenas,
    pub tyck: TyckArenas,
}

impl Arenas {
    pub fn clear(&self) {
        self.ast.clear();
        self.tyck.clear();
    }
}
