use std::{cell::RefCell, rc::Rc};

use calypso_base::symbol::Symbol;
use id_arena::Id;

use crate::{
    ast::{self, ExprKind},
    ctxt::GlobalCtxt,
    typeck::facade::{Hole, TyKind},
};

use self::facade::{DeBruijnLvl, HoleRef, Ty};

pub mod facade;

#[derive(Debug)]
pub(crate) struct TypeckCtxt {
    bound_tys: im::Vector<Symbol>,
    ty_lvl: DeBruijnLvl,
    bound_vars: im::Vector<(Symbol, Ty)>,
}

impl TypeckCtxt {
    pub fn new() -> Self {
        Self {
            bound_tys: im::Vector::new(),
            ty_lvl: DeBruijnLvl::from_raw(0),
            bound_vars: im::Vector::new(),
        }
    }

    // Γ, T
    pub fn push_ty(&mut self, symbol: Symbol) -> &mut Self {
        self.ty_lvl += 1;
        self.bound_tys.push_back(symbol);
        self
    }

    pub fn pop_ty(&mut self) -> &mut Self {
        self.ty_lvl -= 1;
        self.bound_tys.pop_back();
        self
    }

    // Γ, x : T
    pub fn push_var(&mut self, symbol: Symbol, ty: Ty) -> &mut Self {
        self.bound_vars.push_back((symbol, ty));
        self
    }

    pub fn pop_var(&mut self) -> &mut Self {
        self.bound_vars.pop_back();
        self
    }

    pub fn lookup_var(&self, symbol: Symbol) -> Ty {
        self.bound_vars
            .iter()
            .find(|&&(s, _)| s == symbol)
            .unwrap()
            .1
    }
}

fn unify_hole_prechecks(
    tyck: &mut TypeckCtxt,
    gcx: &GlobalCtxt,
    hole: HoleRef,
    scope: DeBruijnLvl,
    ty: Ty,
) {
    fn helper(
        tyck: &mut TypeckCtxt,
        gcx: &GlobalCtxt,
        hole: HoleRef,
        scope: DeBruijnLvl,
        ty: Ty,
        initial_lvl: DeBruijnLvl,
    ) {
        match ty.deref(gcx).kind(gcx) {
            TyKind::Bound(_, _) => unreachable!("TyKind::Bound in unify_hole_prechecks"),
            TyKind::Rigid(lvl) => {
                if lvl >= scope && lvl < initial_lvl {
                    panic!("type variable (TODO) escaping its scope");
                }
            }
            TyKind::Arrow(a, b) => {
                helper(tyck, gcx, hole.clone(), scope, a, initial_lvl);
                helper(tyck, gcx, hole, scope, b, initial_lvl);
            }
            TyKind::Forall(n, a) => {
                tyck.push_ty(n);
                let ty = a.instantiate(
                    gcx,
                    n,
                    gcx.arenas.tyck.intern_ty(TyKind::Rigid(tyck.ty_lvl)),
                );
                helper(tyck, gcx, hole, scope, ty, initial_lvl);
                tyck.pop_ty();
            }
            TyKind::Hole(this_hole) => {
                if let Hole::Empty(l) = *this_hole.0.borrow() {
                    if this_hole == hole {
                        panic!("occurs check: can't make infinite type");
                    } else if l > scope {
                        // TODO: not sure why exactly we do this, have to look
                        // into that later
                        *this_hole.0.borrow_mut() = Hole::Empty(scope)
                    }
                } else {
                    panic!("unify_hole_prechecks: cannot unify with a filled hole");
                }
            }
            TyKind::Free(_) => todo!(),
            TyKind::Err | TyKind::Unit => {}
        }
    }
    let initial_lvl = tyck.ty_lvl;
    helper(tyck, gcx, hole, scope, ty, initial_lvl);
}

fn unify(tyck: &mut TypeckCtxt, gcx: &GlobalCtxt, a: Ty, b: Ty) {
    match (a.deref(gcx).kind(gcx), b.deref(gcx).kind(gcx)) {
        (TyKind::Hole(hole_a), _) => unify_hole_ty(tyck, gcx, hole_a, b),
        (_, TyKind::Hole(hole_b)) => unify_hole_ty(tyck, gcx, hole_b, a),
        (TyKind::Rigid(lvl_a), TyKind::Rigid(lvl_b)) if lvl_a == lvl_b => {}
        (TyKind::Arrow(a1, a2), TyKind::Arrow(b1, b2)) => {
            unify(tyck, gcx, a1, b1);
            unify(tyck, gcx, a2, b2);
        }
        (TyKind::Forall(n_a, a_fun), TyKind::Forall(n_b, b_fun)) => {
            tyck.push_ty(n_a);
            let var_ty = gcx.arenas.tyck.intern_ty(TyKind::Rigid(tyck.ty_lvl));
            // the name matters for these instantiations, but not for the
            // push_ty above.
            let a_fun = a_fun.instantiate(gcx, n_a, var_ty);
            let b_fun = b_fun.instantiate(gcx, n_b, var_ty);
            unify(tyck, gcx, a_fun, b_fun);
            tyck.pop_ty();
        }
        _ => panic!("unification error"),
    }
}

fn unify_hole_ty(tyck: &mut TypeckCtxt, gcx: &GlobalCtxt, hole: HoleRef, ty: Ty) {
    match *hole.0.borrow() {
        Hole::Empty(scope) => {
            // if ty is this hole, don't bother.
            if ty.hole(gcx) == Some(hole.clone()) {
                unify_hole_prechecks(tyck, gcx, hole.clone(), scope, ty);
                *hole.0.borrow_mut() = Hole::Filled(ty);
            }
        }
        Hole::Filled(_) => panic!("unify_hole_ty: cannot unify with a filled hole"),
    }
}

fn eagerly_instantiate(tyck: &mut TypeckCtxt, gcx: &GlobalCtxt, ty: Ty) -> Ty {
    if let TyKind::Forall(n, a) = ty.kind(gcx) {
        let new_hole = Rc::new(RefCell::new(Hole::Empty(tyck.ty_lvl)));
        let ty = a.instantiate(
            gcx,
            n,
            gcx.arenas.tyck.intern_ty(TyKind::Hole(HoleRef(new_hole))),
        );
        eagerly_instantiate(tyck, gcx, ty)
    } else {
        ty
    }
}

pub(crate) fn check(tyck: &mut TypeckCtxt, gcx: &GlobalCtxt, term: Id<ast::Expr>, ty: Ty) {
    match (gcx.arenas.ast.expr(term).kind, ty.deref(gcx).kind(gcx)) {
        (_, TyKind::Forall(n, a)) => {
            tyck.push_ty(n);
            let ty = a.instantiate(
                gcx,
                n,
                gcx.arenas.tyck.intern_ty(TyKind::Rigid(tyck.ty_lvl)),
            );
            check(tyck, gcx, term, ty);
            tyck.pop_ty();
        }
        (ExprKind::Lambda(var, body), TyKind::Arrow(a, b)) => {
            tyck.push_var(var.symbol, a);
            check(tyck, gcx, body, b);
            tyck.pop_var();
        }
        (ExprKind::Let(..), _) => todo!(),
        _ => {
            let inferred_ty = infer_and_inst(tyck, gcx, term);
            unify(tyck, gcx, inferred_ty, ty);
        }
    }
}

pub(crate) fn infer(tyck: &mut TypeckCtxt, gcx: &GlobalCtxt, term: Id<ast::Expr>) -> Ty {
    println!("{:#?}", gcx.arenas.ast.expr(term).kind);
    match gcx.arenas.ast.expr(term).kind {
        ExprKind::Unit => gcx.arenas.tyck.common_tys().unit,
        ExprKind::Name(name) => tyck.lookup_var(name.symbol),
        ExprKind::Apply(f, arg) => {
            let f_ty = infer_and_inst(tyck, gcx, f);
            match f_ty.deref(gcx).kind(gcx) {
                TyKind::Arrow(a, b) => {
                    check(tyck, gcx, arg, a);
                    b
                }
                TyKind::Hole(hole) => {
                    if let Hole::Empty(scope) = *hole.0.borrow() {
                        let a = gcx.arenas.tyck.intern_ty(TyKind::Hole(HoleRef(Rc::new(
                            RefCell::new(Hole::Empty(scope)),
                        ))));
                        let b = gcx.arenas.tyck.intern_ty(TyKind::Hole(HoleRef(Rc::new(
                            RefCell::new(Hole::Empty(scope)),
                        ))));
                        *hole.0.borrow_mut() =
                            Hole::Filled(gcx.arenas.tyck.intern_ty(TyKind::Arrow(a, b)));
                        check(tyck, gcx, arg, a);
                        b
                    } else {
                        unreachable!()
                    }
                }
                _ => panic!("infer: not a function type"),
            }
        }
        ExprKind::Lambda(var, body) => {
            let arg_ty = gcx
                .arenas
                .tyck
                .intern_ty(TyKind::Hole(HoleRef(Rc::new(RefCell::new(Hole::Empty(
                    tyck.ty_lvl,
                ))))));
            tyck.push_var(var.symbol, arg_ty);
            let res_ty = infer_and_inst(tyck, gcx, body);
            tyck.pop_var();
            gcx.arenas.tyck.intern_ty(TyKind::Arrow(arg_ty, res_ty))
        }
        ExprKind::Let(..) => todo!(),
        _ => todo!(),
    }
}

fn infer_and_inst(tyck: &mut TypeckCtxt, gcx: &GlobalCtxt, term: Id<ast::Expr>) -> Ty {
    let ty = infer(tyck, gcx, term);
    eagerly_instantiate(tyck, gcx, ty)
}
