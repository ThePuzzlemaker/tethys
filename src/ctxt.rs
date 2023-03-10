use std::cell::RefCell;

use calypso_base::symbol::Symbol;
use id_arena::{Arena, Id};

use crate::{
    ast::AstArenas,
    diag::DiagReportCtxt,
    intern::Interner,
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
