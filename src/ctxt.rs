use std::cell::RefCell;




use crate::{
    ast::AstArenas,
    diag::DiagReportCtxt,
    typeck::{ast::CoreAstArenas, norm::TyckArenas},
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

#[derive(Default, Debug)]
pub struct Arenas {
    pub ast: AstArenas,
    pub core: CoreAstArenas,
    pub tyck: TyckArenas,
}

impl Arenas {
    pub fn clear(&self) {
        self.ast.clear();
        self.core.clear();
        self.tyck.clear();
    }
}
