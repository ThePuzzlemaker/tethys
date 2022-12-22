use std::{cell::RefCell, rc::Rc};

use calypso_base::symbol::Symbol;
use id_arena::Id;

use crate::{
    ast::{self, AstId},
    ctxt::GlobalCtxt,
    typeck::facade::{
        ast_expr_to_facade, ast_item_to_facade, instantiate, instantiate_in_term, Hole, TyKind,
    },
    TyPp,
};

use self::facade::{ast_ty_to_facade, DeBruijnLvl, ExprKind, HoleRef, Ty};

pub mod facade;

#[derive(Debug)]
pub(crate) struct TypeckCtxt {
    bound_tys: im::Vector<AstId>,
    ty_lvl: DeBruijnLvl,
    bound_vars: im::Vector<(Symbol, Ty)>,
}
// TODO: Just clone the context, which will make the checking and inference
// functions (potentially) tail-recursive in some cases. We're using im::Vector
// anyway so Clone is cheap for that, and DeBruijnLvl is just a number.

impl TypeckCtxt {
    pub fn new(gcx: &GlobalCtxt) -> Self {
        let int_ty = gcx.arenas.tyck.common_tys().integer;
        let add_func_ty = gcx.arenas.tyck.intern_ty(TyKind::Arrow(
            int_ty,
            gcx.arenas.tyck.intern_ty(TyKind::Arrow(int_ty, int_ty)),
        ));
        Self {
            bound_tys: im::Vector::new(),
            ty_lvl: DeBruijnLvl::from_raw(0),
            bound_vars: [(Symbol::intern_static("add"), add_func_ty)]
                .into_iter()
                .collect(),
        }
    }

    // Γ, T
    pub fn push_ty(&mut self, binder: AstId) -> &mut Self {
        self.ty_lvl += 1;
        self.bound_tys.push_back(binder);
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

/*
basically, my understanding is that:

- When we unify, we obviously don't want to substitute with things
that aren't captured where the hole is defined. (capture-avoiding
substitution, iirc?)

- DeBruijn levels count the number of binders (foralls, at the type
level in this system) till the given variable, outside-in.

- So consider, for example: ∀foo. ∀bar. ∀baz. ∀bad1. ∀bad2. baz. The
variable baz is at level 2 (because there are two binders before it,
and it's 0-based), and when it is traversed for typechecking, the
rigid type variable baz is replaced with a flexible empty ?hole, with
its scope set at level 2.

- When we traverse further, going into the bad1 and bad2 binders
respectively, those are replaced with other holes, with their scopes
at levels 3 and 4 respectively.

∀foo0. ∀bad1. foo0
∀bad1. ?hole0@2
?hole0 ≡ ∀x2. ∀y3. x2

∀5.∀6.7@5
∀6.?gen_5@7
?gen_5@7 ≡ ∀0.∀1.2@0


- Then consider that in our typechecking we try to unify ?hole with
∀x. ∀y. x → y → x. Notice that when we traverse this type, these
binders are given levels 5 and 6 respectively.

- So to make sure our substituted variables don't escape scope, we
need to make sure that they're either

- 1. defined outside of the hole (thus having a lower level—it's
non-obvious potentially, but we need to make sure it doesn't have the
same level, as otherwise we might accidentally replace ?hole
(generated from baz) with baz, which is... not good, as that could
cause our algorithm to infinitely loop, potentially)

- 2. defined after the the hole is used (thus having a greater or
equal level to the level at which the hole is used). So before we
traverse the type that is to be filled in the hole, we make note of
the level at which the hole is used, in this case 5 as the last binder
we defined was bad2 at 4. Then if the level of the variables unified
(e.g. x at 5 and y and 6) is greater than or equal to the level at
which the hole is used that we stored earlier, we are good!

Addendum:

- The reason why it's bad for bad1 or bad2 to be unified with baz is
because, for example, you could end up with something like this:
∀baz. baz -> (∀bad1. ∀bad2. baz), and so if you had bad1 or bad2
unified with baz, it would be invalid scope-wise on the left, even
though it's valid on the right! i.e., something like ∀baz. bad1 →
(∀bad1. ∀bad2. bad1). Notice that bad1 is not defined on the left,
even though it is on the right.

- However, it's always sound to substitute with variables bound in the
type to be unified, as there is no way for those to be mentioned
before the hole itself.
*/

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
            TyKind::Bound(_) => unreachable!("TyKind::Bound in unify_hole_prechecks"),
            TyKind::Rigid(lvl) => {
                if lvl >= scope && lvl < initial_lvl {
                    panic!("type variable (TODO) escaping its scope");
                }
            }
            TyKind::Arrow(a, b) => {
                helper(tyck, gcx, hole.clone(), scope, a, initial_lvl);
                helper(tyck, gcx, hole, scope, b, initial_lvl);
            }
            TyKind::Forall(id, ty) => {
                tyck.push_ty(id);
                let ty = instantiate(
                    gcx,
                    ty,
                    id,
                    gcx.arenas.tyck.intern_ty(TyKind::Rigid(tyck.ty_lvl)),
                );
                helper(tyck, gcx, hole, scope, ty, initial_lvl);
                tyck.pop_ty();
                // todo!();
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
            TyKind::Free(_) => {}
            TyKind::Err | TyKind::Unit => {}
        }
    }
    let initial_lvl = tyck.ty_lvl;
    helper(tyck, gcx, hole, scope, ty, initial_lvl);
}

fn unify(tyck: &mut TypeckCtxt, gcx: &GlobalCtxt, a: Ty, b: Ty) {
    // println!("unify a: {:#?}\nb: {:#?}", TyPp(gcx, a), TyPp(gcx, b));
    match (a.deref(gcx).kind(gcx), b.deref(gcx).kind(gcx)) {
        (TyKind::Hole(hole_a), _) => unify_hole_ty(tyck, gcx, hole_a, b),
        (_, TyKind::Hole(hole_b)) => unify_hole_ty(tyck, gcx, hole_b, a),
        (TyKind::Rigid(lvl_a), TyKind::Rigid(lvl_b)) if lvl_a == lvl_b => {}
        (TyKind::Arrow(a1, a2), TyKind::Arrow(b1, b2)) => {
            unify(tyck, gcx, a1, b1);
            unify(tyck, gcx, a2, b2);
        }
        (TyKind::Forall(id_a, a_fun), TyKind::Forall(id_b, b_fun)) => {
            tyck.push_ty(id_a);
            // TODO
            let var_ty = gcx.arenas.tyck.intern_ty(TyKind::Rigid(tyck.ty_lvl));
            // the id matters for these instantiations, but not for
            // the push_ty above.
            let a_fun = instantiate(gcx, a_fun, id_a, var_ty);
            let b_fun = instantiate(gcx, b_fun, id_b, var_ty);
            unify(tyck, gcx, a_fun, b_fun);
            tyck.pop_ty();
        }
        (TyKind::Bound(a), TyKind::Bound(b)) if a == b => {}
        (TyKind::Unit, TyKind::Unit) => {}
        (TyKind::Free(a), TyKind::Free(b)) if a == b => {}
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
    if let TyKind::Forall(id, a) = ty.kind(gcx) {
        let new_hole = Rc::new(RefCell::new(Hole::Empty(tyck.ty_lvl)));
        let hole_ty = gcx.arenas.tyck.intern_ty(TyKind::Hole(HoleRef(new_hole)));
        let ty = instantiate(gcx, a, id, hole_ty);
        eagerly_instantiate(tyck, gcx, ty)
    } else {
        ty
    }
}

pub(crate) fn check(tyck: &mut TypeckCtxt, gcx: &GlobalCtxt, term: Id<facade::Expr>, ty: Ty) {
    let ty = ty.deref(gcx);
    match (gcx.arenas.tyck.expr(term).kind, ty.kind(gcx)) {
        (_, TyKind::Forall(id, a)) => {
            tyck.push_ty(id);
            let ty = instantiate(
                gcx,
                a,
                id,
                gcx.arenas.tyck.intern_ty(TyKind::Rigid(tyck.ty_lvl)),
            );
            let term = instantiate_in_term(
                gcx,
                term,
                id,
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
        (ExprKind::Let(name, None, val, in_expr), _) => {
            let val_ty = infer(tyck, gcx, val);
            tyck.push_var(name.symbol, val_ty);
            check(tyck, gcx, in_expr, ty);
            tyck.pop_var();
        }
        (ExprKind::Let(name, Some(val_ty), val, in_expr), _) => {
            check(tyck, gcx, val, val_ty);
            tyck.push_var(name.symbol, val_ty);
            check(tyck, gcx, in_expr, ty);
            tyck.pop_var();
        }
        _ => {
            let inferred_ty = infer_and_inst(tyck, gcx, term);
            unify(tyck, gcx, inferred_ty, ty);
        }
    }
}

pub(crate) fn infer(tyck: &mut TypeckCtxt, gcx: &GlobalCtxt, term: Id<facade::Expr>) -> Ty {
    // println!("{:#?}", gcx.arenas.ast.expr(term).kind);
    match gcx.arenas.tyck.expr(term).kind {
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
        ExprKind::Let(name, None, val, in_expr) => {
            let val_ty = infer(tyck, gcx, val);
            tyck.push_var(name.symbol, val_ty);
            let expr_ty = infer(tyck, gcx, in_expr);
            tyck.pop_var();
            expr_ty
        }
        ExprKind::Let(name, Some(val_ty), val, in_expr) => {
            check(tyck, gcx, val, val_ty);
            tyck.push_var(name.symbol, val_ty);
            let expr_ty = infer(tyck, gcx, in_expr);
            tyck.pop_var();
            expr_ty
        }
        ExprKind::Def(_, ty, val) => {
            check(tyck, gcx, val, ty);
            ty
        }
        ExprKind::Number(_) => gcx.arenas.tyck.common_tys().integer,
        _ => todo!(),
    }
}

fn infer_and_inst(tyck: &mut TypeckCtxt, gcx: &GlobalCtxt, term: Id<facade::Expr>) -> Ty {
    let ty = infer(tyck, gcx, term);
    eagerly_instantiate(tyck, gcx, ty)
}

pub(crate) fn check_item(tyck: &mut TypeckCtxt, gcx: &GlobalCtxt, item: Id<ast::Item>) {
    let expr = ast_item_to_facade(gcx, item);
    let ExprKind::Def(_, ty, _) = gcx.arenas.tyck.expr(expr).kind else { unreachable!() };
    println!("inferred: {:#?}", TyPp(gcx, infer(tyck, gcx, expr)));
    println!("expected: {:#?}", TyPp(gcx, ty));
    check(tyck, gcx, expr, ty);

    // match gcx.arenas.ast.item(item).kind {
    //     ast::ItemKind::Value(ty, expr) => {
    //         // println!("\n{:#?}\n", gcx);

    //         let mut ty = ast_ty_to_facade(gcx, ty);
    //         let mut expr = ast_expr_to_facade(gcx, expr);
    //         if let TyKind::Forall(id, inner_ty) = ty.kind(gcx) {
    //             tyck.push_ty(id);
    //             ty = instantiate(
    //                 gcx,
    //                 inner_ty,
    //                 id,
    //                 gcx.arenas.tyck.intern_ty(TyKind::Rigid(tyck.ty_lvl)),
    //             );
    //             expr = instantiate_in_term(
    //                 gcx,
    //                 expr,
    //                 id,
    //                 gcx.arenas.tyck.intern_ty(TyKind::Rigid(tyck.ty_lvl)),
    //             )
    //         };

    //         println!("inferred: {:#?}", TyPp(gcx, infer(tyck, gcx, expr)));
    //         println!("expected: {:#?}", TyPp(gcx, ty));
    //         check(tyck, gcx, expr, ty);
    //         tyck.pop_ty();
    //     }
    // }
}
