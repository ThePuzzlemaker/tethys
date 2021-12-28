use typed_arena::Arena;

use crate::ir;

#[derive(Copy, Clone)]
pub struct TyCtxt<'tcx> {
    pub arena: &'tcx Arenas<'tcx>,
    pub intern: Interners<'tcx>,
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

#[derive(Copy, Clone)]
pub struct Interners<'tcx> {
    /// The arena that interned objects are allocated from.
    pub(crate) arena: &'tcx Arenas<'tcx>,
}
