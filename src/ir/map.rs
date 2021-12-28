use super::OwnerNode;

#[derive(Copy, Clone)]
pub struct Map<'tcx> {
    pub(super) tcx: &'tcx crate::ctxt::TyCtxt<'tcx>,
}
