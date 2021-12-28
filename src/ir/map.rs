#[derive(Copy, Clone)]
pub struct Map<'tcx> {
    pub(super) tcx: crate::ctxt::TyCtxt<'tcx>,
}
