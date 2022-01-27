use std::cell::RefCell;

use typed_arena::Arena;

use crate::{diag::DiagReportCtxt, ir};

pub struct TyCtxt<'tcx> {
    pub arenas: &'tcx Arenas<'tcx>,
    pub intern: Interners<'tcx>,
    pub drcx: RefCell<DiagReportCtxt>,
}

#[derive(Default)]
pub struct IrArenas<'tcx> {
    pub expr: Arena<ir::Expr<'tcx>>,
    pub code_unit: Arena<ir::CodeUnit<'tcx>>,
    pub ty: Arena<ir::Ty<'tcx>>,
    pub item: Arena<ir::Item<'tcx>>,
}

#[derive(Default)]
pub struct Arenas<'tcx> {
    pub ir: IrArenas<'tcx>,
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
