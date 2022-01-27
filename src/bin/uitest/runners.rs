use tethys::ctxt::{Arenas, TyCtxt};

use crate::header::{UitestHeader, UitestMode};

pub fn run_test(path: &str, header: UitestHeader, code: String) -> Option<Vec<String>> {
    let arenas = Arenas::default();
    let tcx = tethys::get_tcx(&arenas);
    header.run(&tcx, code);
    header.verify(&tcx)
}

impl UitestHeader {
    fn run<'tcx>(&self, tcx: &'tcx TyCtxt<'tcx>, code: String) {
        match self.mode {
            // Check-pass and diag both just run typechecking, but the verification is different
            UitestMode::CheckPass | UitestMode::Diag => {
                let _ = tethys::run(&code, tcx, false);
            }
        }
    }

    fn verify<'tcx>(&self, _tcx: &'tcx TyCtxt<'tcx>) -> Option<Vec<String>> {
        todo!()
    }
}
