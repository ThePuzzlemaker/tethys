use std::{
    collections::HashMap,
    rc::{Rc, Weak},
};

use calypso_base::symbol::Ident;
use id_arena::Id;

use crate::{
    ast::{AstId, ItemKind, Node},
    ctxt::GlobalCtxt,
    parse::Span,
    typeck::{
        ast::{CoreAstId, DeBruijnLvl, Expr, ExprKind},
        norm::lvl2ix,
    },
};

pub mod pretty;

pub type Env = im::Vector<Rc<VExpr>>;
#[derive(Clone, Debug)]
pub struct Closure(pub Env, pub Id<Expr>);

#[derive(Debug)]
pub enum VExpr {
    Unit,
    Var(CoreAstId, DeBruijnLvl),
    Lam(CoreAstId, Ident, Closure),
    App(Rc<VExpr>, Rc<VExpr>),
    EnumConstructor {
        id: AstId,
        branch: usize,
        branch_total: usize,
        vector: im::Vector<Rc<VExpr>>,
    },
    EnumValue(AstId, usize, im::Vector<Rc<VExpr>>),
    EnumRecursor(AstId),
    EnumRecursorEval {
        id: AstId,
        branch: usize,
        desired_branch: usize,
        stored_value: Option<Rc<VExpr>>,
        total_branches: usize,
        branch_len: usize,
        original_spine: im::Vector<Rc<VExpr>>,
        spine: im::Vector<Rc<VExpr>>,
    },
    Free(AstId),
    RecursionBarrier(AstId, Weak<VExpr>),
}

fn apply_closure(
    gcx: &GlobalCtxt,
    ecx: &mut EvalCtx,
    Closure(mut env, e1): Closure,
    e2: &Rc<VExpr>,
) -> Rc<VExpr> {
    env.push_back(e2.clone());
    eval_expr(gcx, ecx, env, e1)
}

fn eval_app(
    gcx: &GlobalCtxt,
    ecx: &mut EvalCtx,
    env: Env,
    e1: &Rc<VExpr>,
    e2: &Rc<VExpr>,
) -> Rc<VExpr> {
    match (&**e1, &**e2) {
        (VExpr::RecursionBarrier(_, v), _) if !ecx.norec => {
            eval_app(gcx, ecx, env, &v.upgrade().unwrap(), e2)
        }
        (VExpr::Lam(_, _, c), _) => apply_closure(gcx, ecx, c.clone(), e2),
        (
            &VExpr::EnumConstructor {
                id,
                branch,
                branch_total,
                ref vector,
            },
            _,
        ) => {
            let mut vector = vector.clone();
            vector.push_back(e2.clone());
            if vector.len() == branch_total {
                Rc::new(VExpr::EnumValue(id, branch, vector))
            } else {
                Rc::new(VExpr::EnumConstructor {
                    id,
                    branch,
                    branch_total,
                    vector,
                })
            }
        }
        (VExpr::EnumRecursor(id1), VExpr::EnumValue(id2, branch, spine)) if id1 == id2 => {
            let Node::Item(i) = gcx.arenas.ast.get_node_by_id(*id1).unwrap() else {
                unreachable!()
            };
            let ItemKind::Enum(_, cons, _) = gcx.arenas.ast.item(i).kind else {
                unreachable!()
            };

            let branch_len = cons.get(*branch).unwrap().1.len();

            Rc::new(VExpr::EnumRecursorEval {
                id: *id1,
                branch: 0,
                desired_branch: *branch,
                stored_value: None,
                total_branches: cons.len(),
                branch_len,
                spine: spine.clone(),
                original_spine: im::vector![Rc::new(VExpr::EnumValue(
                    *id2,
                    *branch,
                    spine.clone()
                ))],
            })
        }
        (
            &VExpr::EnumRecursorEval {
                branch,
                desired_branch,
                ref stored_value,
                total_branches,
                branch_len,
                ref spine,
                ref original_spine,
                id,
            },
            _,
        ) => {
            let mut original_spine = original_spine.clone();
            original_spine.push_back(e2.clone());
            if branch < desired_branch {
                Rc::new(VExpr::EnumRecursorEval {
                    id,
                    branch: branch + 1,
                    desired_branch,
                    stored_value: None,
                    total_branches,
                    branch_len,
                    spine: spine.clone(),
                    original_spine,
                })
            } else if branch == desired_branch && branch + 1 != total_branches {
                Rc::new(VExpr::EnumRecursorEval {
                    id,
                    branch: branch + 1,
                    desired_branch,
                    stored_value: Some(recursor_spine(gcx, ecx, env, spine.clone(), e2)),
                    total_branches,
                    branch_len,
                    spine: im::Vector::new(),
                    original_spine,
                })
            } else if branch == desired_branch && branch + 1 == total_branches {
                recursor_spine(gcx, ecx, env, spine.clone(), e2)
            } else if branch + 1 == total_branches {
                stored_value.clone().unwrap()
            } else {
                unreachable!()
            }
        }
        (_, _) => Rc::new(VExpr::App(e1.clone(), e2.clone())),
    }
}

fn recursor_spine(
    gcx: &GlobalCtxt,
    ecx: &mut EvalCtx,
    env: Env,
    spine: im::Vector<Rc<VExpr>>,
    e2: &Rc<VExpr>,
) -> Rc<VExpr> {
    if spine.is_empty() {
        e2.clone()
    } else {
        let mut head = e2.clone();
        for val in spine {
            head = eval_app(gcx, ecx, env.clone(), &head, &val);
        }
        head
    }
}

#[derive(Debug, Default)]
pub struct EvalCtx {
    pub free: HashMap<AstId, Id<Expr>>,
    pub free_eval: HashMap<AstId, Rc<VExpr>>,
    pub norec: bool,
}

fn force_barrier(ecx: &mut EvalCtx, e1: Rc<VExpr>) -> Rc<VExpr> {
    match &*e1 {
        VExpr::RecursionBarrier(_, v) if !ecx.norec => force_barrier(ecx, v.upgrade().unwrap()),
        _ => e1.clone(),
    }
}

// TODO: small-step so infinite loops don't overflow stack
pub fn eval_expr(gcx: &GlobalCtxt, ecx: &mut EvalCtx, env: Env, expr: Id<Expr>) -> Rc<VExpr> {
    match gcx.arenas.core.expr(expr).kind {
        ExprKind::Unit => Rc::new(VExpr::Unit),
        ExprKind::Var(_, i) => env.get(i.index()).unwrap().clone(),
        ExprKind::Lam(x, i, b) => Rc::new(VExpr::Lam(x, i, Closure(env.clone(), b))),
        ExprKind::App(f, x) => {
            let f = eval_expr(gcx, ecx, env.clone(), f);
            let x = eval_expr(gcx, ecx, env.clone(), x);
            let x = force_barrier(ecx, x);
            eval_app(gcx, ecx, env.clone(), &f, &x)
        }
        ExprKind::Let(x, i, _, e1, e2) => {
            let e1 = eval_expr(gcx, ecx, env.clone(), e1);
            let e1 = force_barrier(ecx, e1);
            eval_app(
                gcx,
                ecx,
                env.clone(),
                &Rc::new(VExpr::Lam(x, i, Closure(env.clone(), e2))),
                &e1,
            )
        }
        ExprKind::Fix(_, _, _) => todo!(),
        ExprKind::TyAbs(_, _, e) | ExprKind::TyApp(e, _) => eval_expr(gcx, ecx, env, e),
        ExprKind::Free(id) => {
            if ecx.norec {
                return Rc::new(VExpr::Free(id));
            }
            if let Some(val) = ecx.free_eval.get(&id) {
                Rc::new(VExpr::RecursionBarrier(id, Rc::downgrade(val)))
            } else if let Some(val) = ecx.free.get(&id) {
                let v = eval_expr(gcx, ecx, im::Vector::new(), *val);
                ecx.free_eval.insert(id, v.clone());
                Rc::new(VExpr::RecursionBarrier(id, Rc::downgrade(&v)))
            } else {
                unreachable!()
            }
        }
        ExprKind::EnumConstructor(id, branch) => {
            let Node::Item(i) = gcx.arenas.ast.get_node_by_id(id).unwrap() else {
                unreachable!()
            };
            let ItemKind::Enum(_, cons, _) = gcx.arenas.ast.item(i).kind else {
                unreachable!()
            };

            let branch_total = cons.get(branch).unwrap().1.len();

            if branch_total == 0 {
                Rc::new(VExpr::EnumValue(id, branch, im::Vector::new()))
            } else {
                Rc::new(VExpr::EnumConstructor {
                    id,
                    branch,
                    vector: im::Vector::new(),
                    branch_total,
                })
            }
        }

        ExprKind::EnumRecursor(id) => Rc::new(VExpr::EnumRecursor(id)),
        ExprKind::Err(_) => todo!(),
    }
}

pub fn quote_expr(
    gcx: &GlobalCtxt,
    ecx: &mut EvalCtx,
    l: DeBruijnLvl,
    expr: Rc<VExpr>,
) -> Id<Expr> {
    let sp = Span((u32::MAX..u32::MAX).into());
    match &*expr {
        VExpr::Unit => Expr::new(gcx, gcx.arenas.core.next_id(), ExprKind::Unit, sp),
        VExpr::Var(id, lvl) => Expr::new(
            gcx,
            gcx.arenas.core.next_id(),
            ExprKind::Var(*id, lvl2ix(l, *lvl)),
            sp,
        ),
        VExpr::Lam(x, i, b) => {
            ecx.norec = true;
            let b = apply_closure(gcx, ecx, b.clone(), &Rc::new(VExpr::Var(*x, l)));
            ecx.norec = false;
            Expr::new(
                gcx,
                gcx.arenas.core.next_id(),
                ExprKind::Lam(*x, *i, quote_expr(gcx, ecx, l + 1, b)),
                sp,
            )
        }
        VExpr::App(f, x) => {
            let f = quote_expr(gcx, ecx, l, f.clone());
            let x = quote_expr(gcx, ecx, l, x.clone());
            Expr::new(gcx, gcx.arenas.core.next_id(), ExprKind::App(f, x), sp)
        }
        VExpr::EnumConstructor {
            id, branch, vector, ..
        }
        | VExpr::EnumValue(id, branch, vector) => vector.iter().cloned().fold(
            Expr::new(
                gcx,
                gcx.arenas.core.next_id(),
                ExprKind::EnumConstructor(*id, *branch),
                sp,
            ),
            |acc, x| {
                Expr::new(
                    gcx,
                    gcx.arenas.core.next_id(),
                    ExprKind::App(acc, quote_expr(gcx, ecx, l, x)),
                    sp,
                )
            },
        ),
        VExpr::EnumRecursor(id) => Expr::new(
            gcx,
            gcx.arenas.core.next_id(),
            ExprKind::EnumRecursor(*id),
            sp,
        ),
        VExpr::EnumRecursorEval {
            id, original_spine, ..
        } => original_spine.iter().cloned().fold(
            Expr::new(
                gcx,
                gcx.arenas.core.next_id(),
                ExprKind::EnumRecursor(*id),
                sp,
            ),
            |acc, x| {
                Expr::new(
                    gcx,
                    gcx.arenas.core.next_id(),
                    ExprKind::App(acc, quote_expr(gcx, ecx, l, x)),
                    sp,
                )
            },
        ),
        VExpr::Free(id) => Expr::new(gcx, gcx.arenas.core.next_id(), ExprKind::Free(*id), sp),
        VExpr::RecursionBarrier(id, v) => {
            let _ = v.upgrade().unwrap();
            Expr::new(gcx, gcx.arenas.core.next_id(), ExprKind::Free(*id), sp)
        }
    }
}
