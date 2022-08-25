//! This module defines the AST "facade" that typechecking operates on. Instead
//!  of fully representing source code, like the AST does, this facade may be
//!  smaller (or larger) than the original source code, as typechecking and
//!  inference continues. This means that not all nodes in this facade may
//!  represent actual source code! Many of them are generated, or normalized,
//!  during typechecking--specifically, mostly types.
//!
//! Another important thing to note is that many of the structures representing
//!  types and whatnot are interned. This way, they can be cheaply generated
//!  and manipulated without fear of insane memory usage--this is especially
//!  useful as many types generated will be the same! In many cases, they will
//!  just be hole types or functions that may be common, e.g.
//!  `Int -> Int -> Int`, which is common *at least* with a few integer
//!  operations. This interning is helpful so that each of these nodes don't
//!  take up however many bytes times however many times it shows up.
//!
//! Note that many of these structures won't contain span or
//!  [`crate::ast::AstId`] information. This means that when handling these
//!  types, you must be careful to correlate IDs when possible to make
//!  diagnostic information better.

pub mod traversal;

use std::collections::HashMap;

use calypso_base::symbol::Symbol;

use crate::{ast, ctxt::TyCtxt, intern::Interned};

index_vec::define_index_type! {
    pub struct DeBruijnIdx = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
    DEBUG_FORMAT = "DebruijnIdx({})";
    DISPLAY_FORMAT = "{}";
    IMPL_RAW_CONVERSIONS = true;
}

index_vec::define_index_type! {
    pub struct DeBruijnLvl = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
    DEBUG_FORMAT = "DebruijnLvl({})";
    DISPLAY_FORMAT = "{}";
    IMPL_RAW_CONVERSIONS = true;
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Ty<'tcx>(pub(crate) Interned<'tcx, TyS<'tcx>>);

impl<'tcx> Ty<'tcx>
where
    Self: 'tcx,
{
    #[inline]
    pub fn kind(self) -> &'tcx TyKind<'tcx> {
        &self.0 .0.kind
    }
}

/// The internal struct that represents a type.
///
/// # Important Notes
///
/// - You should not use this type in general.
/// - Values of this type are always interned and unique, stored as an [`Interned<'tcx, TyS<'tcx>>`].
/// - Instead, use the interned [`Ty`], which also provides all the methods you will need to use it.
#[derive(Debug, Hash)]
pub(crate) struct TyS<'tcx> {
    /// Do not use this field directly, instead use [`Ty::kind`].
    pub(crate) kind: TyKind<'tcx>,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum TyKind<'tcx> {
    Unit,
    /// A bound variable under a `forall`-binder.
    Bound(DeBruijnIdx, Symbol),
    /// A rigid type variable generated when traversing universally
    ///  quantified types.
    Rigid(DeBruijnLvl),
    Free(Symbol),
    Arrow(Ty<'tcx>, Ty<'tcx>),
    Forall(Symbol, SubstableForall<'tcx>),
    Err,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct SubstableForall<'tcx> {
    env: Vec<(Symbol, Ty<'tcx>)>,
    ty: &'tcx ast::Ty<'tcx>,
}

impl<'tcx> SubstableForall<'tcx> {
    pub fn instantiate(
        mut self,
        tcx: &'tcx TyCtxt<'tcx>,
        symbol: Symbol,
        ty: Ty<'tcx>,
    ) -> Ty<'tcx> {
        self.env.push((symbol, ty));
        eval(tcx, &mut self.env, self.ty)
    }
}

pub(crate) fn eval<'tcx>(
    tcx: &'tcx TyCtxt<'tcx>,
    env: &mut Vec<(Symbol, Ty<'tcx>)>,
    ty: &'tcx ast::Ty<'tcx>,
) -> Ty<'tcx> {
    match ty.kind {
        ast::TyKind::Unit => tcx.arenas.tyck.common_tys().unit,
        ast::TyKind::Name(name) => {
            let elem = env.iter().find(|&&(sym, ty)| sym == name.symbol);
            elem.map(|(_, ty)| ty)
                .copied()
                .unwrap_or_else(|| tcx.arenas.tyck.intern_ty(TyKind::Free(name.symbol)))
        }
        ast::TyKind::Arrow(a, b) => tcx
            .arenas
            .tyck
            .intern_ty(TyKind::Arrow(eval(tcx, env, a), eval(tcx, env, b))),
        ast::TyKind::Forall(name, ty) => tcx.arenas.tyck.intern_ty(TyKind::Forall(
            name.symbol,
            SubstableForall {
                env: env.clone(),
                ty,
            },
        )),
        ast::TyKind::Err => tcx.arenas.tyck.common_tys().err,
    }
}
