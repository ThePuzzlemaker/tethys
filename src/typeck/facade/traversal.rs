use std::fmt;

use crate::ctxt::GlobalCtxt;

use super::{Ty, TyKind};

pub trait TyFoldable: fmt::Debug + Clone {
    fn try_default_fold_with<F: TyFolder>(self, folder: &mut F) -> Result<Self, F::Error>;

    fn try_fold_with<F: TyFolder>(self, folder: &mut F) -> Result<Self, F::Error> {
        self.try_default_fold_with(folder)
    }
}

pub trait TyFolder: Sized {
    type Error;

    fn gcx(&'_ self) -> &'_ GlobalCtxt;

    fn try_fold_ty(&mut self, t: Ty) -> Result<Ty, Self::Error> {
        t.try_default_fold_with(self)
    }
}

impl TyFoldable for Ty {
    fn try_default_fold_with<F: TyFolder>(self, folder: &mut F) -> Result<Self, F::Error> {
        let self_kind = self.kind(folder.gcx());
        let kind = match self_kind {
            TyKind::Unit | TyKind::Err => todo!(),
            TyKind::Rigid(_) => todo!(),
            TyKind::Free(_) => todo!(),
            TyKind::Arrow(inp, out) => {
                TyKind::Arrow(inp.try_fold_with(folder)?, out.try_fold_with(folder)?)
            }
            TyKind::Hole(_) => todo!(),
            TyKind::Forall(_, _) => todo!(),
            TyKind::Bound(_) => todo!(),
        };

        Ok(if self_kind == kind {
            self
        } else {
            folder.gcx().arenas.tyck.intern_ty(kind)
        })
    }

    fn try_fold_with<F: TyFolder>(self, folder: &mut F) -> Result<Self, F::Error> {
        folder.try_fold_ty(self)
    }
}
