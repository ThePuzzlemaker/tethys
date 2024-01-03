use std::{cmp::Ordering, rc::Rc};

use calypso_base::symbol::Symbol;
use id_arena::Id;

use crate::{ast::PrimTy, ctxt::GlobalCtxt, parse::Span, typeck::fresh_meta};

use super::{
    ast::{CoreAstId, DeBruijnLvl, MetaEntry, MetaVar, Ty, TyKind},
    norm::{apply_ty_closure, force, lvl2ix, FlexTuple, VSpine, VTy, VTyKind},
};

#[derive(Clone, Debug)]
struct PartialRenaming {
    dom: DeBruijnLvl,
    cod: DeBruijnLvl,
    ren: im::HashMap<DeBruijnLvl, DeBruijnLvl>,
}

fn lift_ren(PartialRenaming { dom, cod, mut ren }: PartialRenaming) -> PartialRenaming {
    ren.insert(cod, dom);
    PartialRenaming {
        dom: dom + 1,
        cod: cod + 1,
        ren,
    }
}

/// Create a partial renaming to convert a spine such as `[4, 6, 5]`
/// (where all are `Rigid`) into `[0, 1, 2]`.
fn invert(gcx: &GlobalCtxt, gamma: DeBruijnLvl, sp: VSpine) -> PartialRenaming {
    let mut d = DeBruijnLvl::from(0usize);
    let mut r = im::HashMap::new();

    // println!(
    //     "{:#?}",
    //     sp.iter()
    //         .map(|x| gcx.arenas.tyck.vty(*x).kind)
    //         .collect::<Vec<_>>()
    // );
    // TODO: why does `rev` make this work
    for t in sp.into_iter().rev() {
        match gcx.arenas.tyck.vty(force(gcx, t)).kind {
            VTyKind::Rigid(_, x) if !r.contains_key(&x) => {
                r.insert(x, d);
                d += 1;
            }
            _ => panic!("invert"),
        }
    }

    PartialRenaming {
        dom: d,
        cod: gamma,
        ren: r,
    }
}

fn rename_spine(
    gcx: &GlobalCtxt,
    m: MetaVar,
    pren: PartialRenaming,
    sp: VSpine,
) -> Result<im::Vector<Id<Ty>>, UnifyError> {
    sp.into_iter()
        .map(move |a| rename(gcx, m.clone(), pren.clone(), a))
        .collect()
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum UnifyError {
    Occurs,
    Scope(CoreAstId, DeBruijnLvl),
    SpineMismatch,
    RigidMismatch,
}

fn rename(
    gcx: &GlobalCtxt,
    m: MetaVar,
    pren: PartialRenaming,
    t: Id<VTy>,
) -> Result<Id<Ty>, UnifyError> {
    use VTyKind::*;
    let t = force(gcx, t);
    let t = gcx.arenas.tyck.vty(t);
    Ok(match t.kind {
        Flex(m1, _) if Rc::ptr_eq(&m1.0, &m.0) => return Err(UnifyError::Occurs),
        Flex(m1, sp) => Ty::new(
            gcx,
            gcx.arenas.core.next_id(),
            TyKind::Meta(m1, rename_spine(gcx, m, pren, sp)?),
            t.span,
        ),
        Rigid(x, l) => match pren.ren.get(&l) {
            None => return Err(UnifyError::Scope(x, l)),
            Some(l1) => Ty::new(
                gcx,
                gcx.arenas.core.next_id(),
                TyKind::Var(x, lvl2ix(pren.dom, *l1)),
                t.span,
            ),
        },
        Unit => Ty::new(gcx, t.id, TyKind::Unit, t.span),
        Arrow(a, b) => Ty::new(
            gcx,
            gcx.arenas.core.next_id(),
            TyKind::Arrow(
                rename(gcx, m.clone(), pren.clone(), a)?,
                rename(gcx, m, pren, b)?,
            ),
            t.span,
        ),
        Free(x) => Ty::new(gcx, gcx.arenas.core.next_id(), TyKind::Free(x), t.span),
        Forall(x, i, c) => {
            let vc = apply_ty_closure(
                gcx,
                c,
                VTy::rigid(gcx, gcx.arenas.core.next_id(), x, pren.cod),
            );
            Ty::new(
                gcx,
                gcx.arenas.core.next_id(),
                TyKind::Forall(x, i, rename(gcx, m, lift_ren(pren), vc)?),
                t.span,
            )
        }
        Enum(x, spine) => Ty::new(
            gcx,
            gcx.arenas.core.next_id(),
            TyKind::Enum(x, rename_spine(gcx, m, pren, spine)?),
            t.span,
        ),
        Primitive(prim) => Ty::new(
            gcx,
            gcx.arenas.core.next_id(),
            TyKind::Primitive(prim),
            t.span,
        ),
        Tuple(spine) => Ty::new(
            gcx,
            gcx.arenas.core.next_id(),
            TyKind::Tuple(rename_spine(gcx, m, pren, spine)?),
            t.span,
        ),
        TupleFlex(spine) => match &*spine.borrow() {
            FlexTuple::Flex(spine) => Ty::new(
                gcx,
                gcx.arenas.core.next_id(),
                TyKind::TupleFlex(rename_spine(gcx, m, pren, spine.clone())?),
                t.span,
            ),
            _ => unreachable!(),
        },
    })
}

fn solve(
    gcx: &GlobalCtxt,
    gamma: DeBruijnLvl,
    m: MetaVar,
    sp: VSpine,
    rhs: Id<VTy>,
) -> Result<(), UnifyError> {
    let pren = invert(gcx, gamma, sp);
    // println!("gamma={gamma:?}, pren={pren:?}");
    let sol = rename(gcx, m.clone(), pren, rhs)?;
    m.0.borrow_mut().0 = MetaEntry::Solved(sol);
    Ok(())
}

fn unify_spine(
    gcx: &GlobalCtxt,
    l: DeBruijnLvl,
    sp1: VSpine,
    sp2: VSpine,
) -> Result<(), UnifyError> {
    if sp1.len() != sp2.len() {
        return Err(UnifyError::SpineMismatch);
    }
    for (t1, t2) in sp1.into_iter().zip(sp2.into_iter()) {
        unify(gcx, l, t1, t2)?;
    }
    Ok(())
}

pub fn unify(gcx: &GlobalCtxt, l: DeBruijnLvl, t: Id<VTy>, u: Id<VTy>) -> Result<(), UnifyError> {
    // {
    //     let mut w = Vec::new();
    //     let t = quote_ty(gcx, l, t);
    //     let u = quote_ty(gcx, l, u);
    //     let doc = crate::typeck::pretty::pp_ty(0, gcx, t);
    //     doc.render(80, &mut w).unwrap();
    //     let mut w1 = Vec::new();
    //     let doc = crate::typeck::pretty::pp_ty(0, gcx, u);
    //     doc.render(80, &mut w1).unwrap();

    //     println!(
    //         "unify: {} vs {}",
    //         String::from_utf8(w).unwrap(),
    //         String::from_utf8(w1).unwrap()
    //     );
    // }
    use VTyKind::*;
    let t = force(gcx, t);
    let u = force(gcx, u);
    let vt = gcx.arenas.tyck.vty(t);
    let vu = gcx.arenas.tyck.vty(u);

    match (vt.kind.clone(), vu.kind.clone()) {
        (Flex(m1, sp1), Flex(m2, sp2)) if Rc::ptr_eq(&m1.0, &m2.0) => {
            unify_spine(gcx, l, sp1, sp2)?;
        }
        (Flex(m1, sp1), _) => solve(gcx, l, m1, sp1, u)?,
        (_, Flex(m2, sp2)) => solve(gcx, l, m2, sp2, t)?,
        (Rigid(_, x1), Rigid(_, x2)) if x1 == x2 => {}
        (Unit, Unit) => {}
        (Arrow(a1, b1), Arrow(a2, b2)) => {
            unify(gcx, l, a1, a2)?;
            unify(gcx, l, b1, b2)?;
        }
        (Forall(x1, _, t1), Forall(x2, _, t2)) => {
            let c1 = apply_ty_closure(gcx, t1, VTy::rigid(gcx, gcx.arenas.core.next_id(), x1, l));
            let c2 = apply_ty_closure(gcx, t2, VTy::rigid(gcx, gcx.arenas.core.next_id(), x2, l));
            unify(gcx, l + 1, c1, c2)?;
        }
        (Free(n1), Free(n2)) if n1 == n2 => {}
        (Enum(x1, sp1), Enum(x2, sp2)) if x1 == x2 => {
            unify_spine(gcx, l, sp1, sp2)?;
        }
        (Primitive(p1), Primitive(p2)) if p1 == p2 => {}
        (Tuple(t1), Tuple(t2)) => {
            unify_spine(gcx, l, t1, t2)?;
        }
        (TupleFlex(t1), TupleFlex(t2)) => match (&*t1.borrow(), &*t2.borrow()) {
            (FlexTuple::Flex(sp1), FlexTuple::Flex(sp2)) => match sp1.len().cmp(&sp2.len()) {
                Ordering::Less => {
                    // (A, B, ...) `unify` (X, Y, Z, ...)
                    // LH side (t1) := RH side (sp2)
                    // unify spines, truncated:
                    // A `unify` X, B `unify` Y

                    let sp1 = sp1.clone();
                    let mut sp2 = sp2.clone();
                    *t1.borrow_mut() = FlexTuple::Flex(sp2.clone());

                    sp2.truncate(sp1.len());
                    unify_spine(gcx, l, sp1, sp2)?;
                }
                Ordering::Equal => {
                    // (A, B, ...) `unify` (X, Y, ...)
                    // no need to change flex constraints
                    // unify spines, no truncation necessary:
                    // A `unify` X, B `unify` Y
                    unify_spine(gcx, l, sp1.clone(), sp2.clone())?;
                }
                Ordering::Greater => {
                    // (A, B, C, ...) `unify` (X, Y, ...)
                    // RH side (t2) := LH side (sp1)
                    // unify spines, truncated:
                    // A `unify` X, B `unify` Y

                    let mut sp1 = sp1.clone();
                    let sp2 = sp2.clone();
                    *t2.borrow_mut() = FlexTuple::Flex(sp1.clone());

                    sp1.truncate(sp2.len());
                    unify_spine(gcx, l, sp1, sp2)?;
                }
            },
            _ => unreachable!(), // force
        },
        (TupleFlex(t1), Tuple(sp2)) => {
            let borrow = t1.borrow();
            match &*borrow {
                FlexTuple::Flex(sp1) => {
                    // (A, B, ...) `unify` (X, Y, Z)
                    // truncate and unify spines:
                    // A `unify` X, B `unify` Z
                    let mut sp2_trunc = sp2.clone();
                    sp2_trunc.truncate(sp1.len());

                    unify_spine(gcx, l, sp1.clone(), sp2_trunc)?;
                    // If we succeeded (no rigid mismatch), update ourselves.
                    // t1 := RH side (sp2)
                    drop(borrow);
                    *t1.borrow_mut() = FlexTuple::Rigid(sp2);
                }
                _ => unreachable!(), // force
            };
        }
        (Tuple(sp1), TupleFlex(t2)) => {
            let borrow = t2.borrow();
            match &*borrow {
                FlexTuple::Flex(sp2) => {
                    // (A, B, C) `unify` (X, Y, ...)
                    // truncate and unify spines:
                    // A `unify` X, B `unify` Z
                    let mut sp1_trunc = sp1.clone();
                    sp1_trunc.truncate(sp2.len());

                    unify_spine(gcx, l, sp1_trunc, sp2.clone())?;
                    // If we succeeded (no rigid mismatch), update ourselves.
                    // t2 := LH side (sp1)
                    drop(borrow);
                    *t2.borrow_mut() = FlexTuple::Rigid(sp1);
                }
                _ => unreachable!(), // force
            };
        }
        _ => {
            return Err(UnifyError::RigidMismatch);
        }
    }
    Ok(())
}
