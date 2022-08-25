use tethys::ctxt::TyCtxt;

use crate::header::{UitestHeader, UitestMode};

pub fn run_test(path: &str, header: UitestHeader, code: String) -> Option<Vec<String>> {
    let tcx = TyCtxt::default();
    header.run(&tcx, code);
    header.verify(&tcx)
}

impl UitestHeader {
    fn run(&self, tcx: &TyCtxt, code: String) {
        match self.mode {
            // Check-pass and diag both just run typechecking, but the verification is different
            UitestMode::CheckPass | UitestMode::Diag => {
                let _ = tethys::run(&code, tcx, false);
            }
        }
    }

    fn verify(&self, _tcx: &TyCtxt) -> Option<Vec<String>> {
        todo!()
    }
}
