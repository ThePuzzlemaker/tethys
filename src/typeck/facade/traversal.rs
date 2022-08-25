use std::fmt;

use crate::ctxt::TyCtxt;

use super::{Ty, TyKind};

pub trait TyFoldable<'tcx>: fmt::Debug + Clone {
    fn try_default_fold_with<F: TyFolder<'tcx>>(self, folder: &mut F) -> Result<Self, F::Error>;

    fn try_fold_with<F: TyFolder<'tcx>>(self, folder: &mut F) -> Result<Self, F::Error> {
        self.try_default_fold_with(folder)
    }
}

pub trait TyFolder<'tcx>: Sized {
    type Error;

    fn tcx<'a>(&'a self) -> &'tcx TyCtxt<'tcx>;

    fn try_fold_ty(&mut self, t: Ty<'tcx>) -> Result<Ty<'tcx>, Self::Error> {
        t.try_default_fold_with(self)
    }
}

impl<'tcx> TyFoldable<'tcx> for Ty<'tcx> {
    fn try_default_fold_with<F: TyFolder<'tcx>>(self, folder: &mut F) -> Result<Self, F::Error> {
        let kind = match *self.kind() {
            TyKind::Unit | TyKind::Err => todo!(),
            TyKind::TyVar(_, _) => todo!(),
            TyKind::Free(_) => todo!(),
            TyKind::Arrow(inp, out) => {
                TyKind::Arrow(inp.try_fold_with(folder)?, out.try_fold_with(folder)?)
            }
            TyKind::Forall(_, _) => todo!(),
        };

        Ok(if *self.kind() == kind {
            self
        } else {
            folder.tcx().arenas.tyck.intern_ty(kind)
        })
    }

    fn try_fold_with<F: TyFolder<'tcx>>(self, folder: &mut F) -> Result<Self, F::Error> {
        folder.try_fold_ty(self)
    }
}
