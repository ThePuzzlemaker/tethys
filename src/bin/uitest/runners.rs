use tethys::ctxt::GlobalCtxt;

use crate::header::{UitestHeader, UitestMode};

pub fn run_test(path: &str, header: UitestHeader, code: String) -> Option<Vec<String>> {
    let gcx = GlobalCtxt::default();
    header.run(&gcx, code);
    header.verify(&gcx)
}

impl UitestHeader {
    fn run(&self, gcx: &GlobalCtxt, code: String) {
        match self.mode {
            // Check-pass and diag both just run typechecking, but the verification is different
            UitestMode::CheckPass | UitestMode::Diag => {
                let _ = tethys::run(&code, gcx, false);
            }
        }
    }

    fn verify(&self, _gcx: &GlobalCtxt) -> Option<Vec<String>> {
        todo!()
    }
}
