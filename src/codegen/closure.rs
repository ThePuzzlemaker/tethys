//! Closure conversion (and lambda lifting) for lambda values.
//!
//! Converts expressions such as `λx.λy.λz.x+y+z+a` into (ML-like
//! syntax) `let f a x y z = x+y+z+a in (f a)` where `f a` is a struct
//! containing a code pointer and a list of already-applied arguments,
//! and `a` is a free value used by the lambda.
//!
//! A more complex example is as follows, using ML-like syntax:
//! ```
//! let incr a xs = map (\x. x + a) xs
//! ```
//! becomes
//! ```
//! let aux a x = x + a
//! let incr a xs = map (aux a) xs
//! ```
//!
//! With even more free variables:
//! ```
//! let incr2 a b xs = map (\x. x + a + b) xs
//! ```
//! becomes
//! ```
//! let aux a b xs = x + a + b
//! let incr2 a b xs = map (aux a b) xs
//! ```
//!
//! Frankly, I'll be honest: I don't entirely know why this works. But
//! it does, so I'm not gonna prod at it cause that will only bring
//! pain.

use std::collections::HashMap;

use id_arena::Id;

use crate::{
    ast::Recursive,
    ctxt::GlobalCtxt,
    parse::Span,
    typeck::{
        ast::{CoreAstId, DeBruijnIdx, DeBruijnLvl, Expr, ExprKind},
        norm::{self, VTy, VTyKind},
        pretty::pp_ty,
    },
};

struct ConvCtxt {
    lifted: Vec<Id<Expr>>,
    scopes: Vec<Scope>,
    env: Vec<CoreAstId>,
    letrec: HashMap<CoreAstId, CoreAstId>,
}

impl ConvCtxt {}

pub fn closure_convert(gcx: &GlobalCtxt, term: Id<Expr>) -> (Vec<Id<Expr>>, Id<Expr>) {
    let mut ctx = ConvCtxt {
        lifted: vec![],
        env: vec![],
        scopes: vec![],
        letrec: HashMap::new(),
    };

    let res = convert(gcx, &mut ctx, term, 0, Mode::Root);
    (ctx.lifted, res)
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Scope {
    offset: usize,
    len: usize,
    free: im::Vector<CoreAstId>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Mode {
    Collect,
    Traverse,
    Root,
    LetRec(CoreAstId),
}

// TODO: this could be made way simpler if I didn't unfold lambdas

#[allow(clippy::only_used_in_recursion)]
fn convert(
    gcx: &GlobalCtxt,
    ctx: &mut ConvCtxt,
    term: Id<Expr>,
    scope_ix: usize,
    mode: Mode,
) -> Id<Expr> {
    let sp = gcx.arenas.core.expr(term).span;
    let id = gcx.arenas.core.expr(term).id;
    let ty = gcx.arenas.core.ty_of_expr(id);
    match gcx.arenas.core.expr(term).kind {
        ExprKind::Var(id) => {
            if let Some(new_id) = ctx.letrec.get(&id) {
                Expr::new(
                    gcx,
                    gcx.arenas.core.next_id(),
                    ExprKind::LiftedLamRef(*new_id),
                    sp,
                    Some(ty),
                )
            } else {
                let scope = &mut ctx.scopes[scope_ix];
                let lvl = ctx
                    .env
                    .iter()
                    .copied()
                    .enumerate()
                    .find_map(|(ix, x)| (x == id).then_some(ix))
                    .unwrap();
                if lvl < scope.offset {
                    let i = ctx.env[lvl];
                    scope.free.push_back(i);
                    Expr::new(
                        gcx,
                        gcx.arenas.core.next_id(),
                        ExprKind::LiftedFree(id),
                        sp,
                        Some(ty),
                    )
                } else {
                    Expr::new(
                        gcx,
                        gcx.arenas.core.next_id(),
                        ExprKind::LiftedVar(id),
                        sp,
                        Some(ty),
                    )
                }
            }
        }
        ExprKind::Lam(i, _, body) if mode == Mode::Collect => {
            let scope = &mut ctx.scopes[scope_ix];
            scope.len += 1;
            ctx.env.push(i);

            convert(gcx, ctx, body, scope_ix, Mode::Collect)
        }
        ExprKind::Lam(i, _, body)
            if mode == Mode::Traverse || mode == Mode::Root || matches!(mode, Mode::LetRec(..)) =>
        {
            let mut scope = Scope {
                offset: ctx.env.len(),
                ..Scope::default()
            };
            scope.len += 1;
            ctx.env.push(i);
            ctx.scopes.push(scope);

            let next_scope_ix = if ctx.scopes.len() == 1 {
                scope_ix
            } else {
                scope_ix + 1
            };

            let res = convert(gcx, ctx, body, next_scope_ix, Mode::Collect);

            let vars = &ctx.env[ctx.scopes[next_scope_ix].offset
                ..ctx.scopes[next_scope_ix].offset + ctx.scopes[next_scope_ix].len];
            let ids = ctx.scopes[next_scope_ix]
                .free
                .iter()
                .chain(vars.iter())
                .copied()
                .collect();
            let base_ty = gcx.arenas.core.ty_of_expr(vars[0]);
            let ty = ctx.scopes[next_scope_ix]
                .free
                .iter()
                .fold(base_ty, |acc, x| {
                    let VTyKind::Arrow(a, _) =
                        gcx.arenas.tyck.vty(gcx.arenas.core.ty_of_expr(*x)).kind
                    else {
                        unreachable!()
                    };

                    VTy::new(
                        gcx,
                        gcx.arenas.core.next_id(),
                        VTyKind::Arrow(a, acc),
                        Span((0..0).into()),
                    )
                });
            println!(
                "base ty: {}",
                pp_ty(
                    0,
                    gcx,
                    0usize.into(),
                    im::Vector::new(),
                    norm::quote_ty(gcx, 0usize.into(), base_ty)
                )
                .group()
                .pretty(80)
            );
            println!(
                "accum ty: {}",
                pp_ty(
                    0,
                    gcx,
                    0usize.into(),
                    im::Vector::new(),
                    norm::quote_ty(gcx, 0usize.into(), ty)
                )
                .group()
                .pretty(80)
            );
            let new_id = if let Mode::LetRec(id) = mode {
                id
            } else {
                gcx.arenas.core.next_id()
            };
            let res = Expr::new(gcx, new_id, ExprKind::LiftedLam(ids, res), sp, Some(ty));
            if mode != Mode::Root {
                ctx.lifted.push(res);
            }
            let res_ref = if mode == Mode::Root {
                res
            } else {
                Expr::new(
                    gcx,
                    gcx.arenas.core.next_id(),
                    ExprKind::LiftedLamRef(new_id),
                    sp,
                    Some(ty),
                )
            };

            let xs = ctx.scopes[next_scope_ix]
                .free
                .clone()
                .iter()
                .map(|id| {
                    let mut free_ix = None;
                    let mut free_scope_ix = None;

                    for (scope_ix, scope) in ctx.scopes.iter().take(next_scope_ix).enumerate() {
                        if let Some(x) = ctx.env[scope.offset..scope.offset + scope.len]
                            .iter()
                            .rev()
                            .enumerate()
                            .find_map(|(x, i)| (i == id).then_some(x))
                        {
                            free_ix = Some(x);
                            free_scope_ix = Some(scope_ix);
                        };
                    }

                    if ctx.scopes.len() != 1 {
                        for scope in free_scope_ix.unwrap() + 1..next_scope_ix {
                            let scope_offset = ctx.scopes[scope].offset;
                            let scope_len = ctx.scopes[scope].len;
                            ctx.scopes[scope].free.push_back(
                                ctx.env[ctx.env.len() + scope_len
                                    - free_ix.unwrap()
                                    - scope_offset
                                    - 1],
                            );
                        }
                    }

                    let VTyKind::Arrow(a, _) =
                        gcx.arenas.tyck.vty(gcx.arenas.core.ty_of_expr(*id)).kind
                    else {
                        unreachable!()
                    };

                    Expr::new(
                        gcx,
                        gcx.arenas.core.next_id(),
                        ExprKind::LiftedVar(*id),
                        sp,
                        Some(a),
                    )
                })
                .collect::<im::Vector<_>>();

            let res = if xs.is_empty() {
                res_ref
            } else {
                Expr::new(
                    gcx,
                    gcx.arenas.core.next_id(),
                    ExprKind::LiftedApp(res_ref, xs),
                    sp,
                    Some(base_ty),
                )
            };

            ctx.env
                .truncate(ctx.env.len() - ctx.scopes[next_scope_ix].len);
            ctx.scopes.pop();

            res
        }
        ExprKind::App(f, x) => {
            let f = convert(gcx, ctx, f, scope_ix, Mode::Traverse);
            let x = convert(gcx, ctx, x, scope_ix, Mode::Traverse);
            Expr::new(
                gcx,
                gcx.arenas.core.next_id(),
                ExprKind::App(f, x),
                sp,
                Some(ty),
            )
        }
        ExprKind::TyApp(e, _) | ExprKind::TyAbs(_, _, e) => {
            convert(gcx, ctx, e, scope_ix, Mode::Traverse)
        }
        // TODO: lower `let`s elsewhere?
        ExprKind::Let(x, i, Recursive::NotRecursive, t, e1, e2) => {
            let e1 = convert(gcx, ctx, e1, scope_ix, Mode::Traverse);

            let mut scope = Scope {
                offset: ctx.env.len(),
                ..Scope::default()
            };
            scope.len += 1;
            ctx.env.push(x);
            ctx.scopes.push(scope);

            let e2 = convert(gcx, ctx, e2, scope_ix, Mode::Traverse);
            ctx.scopes.pop();
            ctx.env.pop();
            Expr::new(
                gcx,
                gcx.arenas.core.next_id(),
                ExprKind::Let(x, i, Recursive::NotRecursive, t, e1, e2),
                sp,
                Some(ty),
            )
        }
        ExprKind::Let(x, i, Recursive::Recursive(sp), t, e1, e2) => {
            let new_id = gcx.arenas.core.next_id();
            ctx.letrec.insert(x, new_id);
            let e1 = convert(gcx, ctx, e1, scope_ix, Mode::LetRec(new_id));
            convert(gcx, ctx, e2, scope_ix, Mode::Traverse)
        }

        ExprKind::BinaryOp { left, kind, right } => {
            let left = convert(gcx, ctx, left, scope_ix, Mode::Traverse);
            let right = convert(gcx, ctx, right, scope_ix, Mode::Traverse);
            Expr::new(
                gcx,
                gcx.arenas.core.next_id(),
                ExprKind::BinaryOp { left, kind, right },
                sp,
                Some(ty),
            )
        }
        ExprKind::If(cond, then, then_else) => {
            let cond = convert(gcx, ctx, cond, scope_ix, Mode::Traverse);
            let then = convert(gcx, ctx, then, scope_ix, Mode::Traverse);
            let then_else = convert(gcx, ctx, then_else, scope_ix, Mode::Traverse);
            Expr::new(
                gcx,
                gcx.arenas.core.next_id(),
                ExprKind::If(cond, then, then_else),
                sp,
                Some(ty),
            )
        }
        ExprKind::Tuple(v) => Expr::new(
            gcx,
            gcx.arenas.core.next_id(),
            ExprKind::Tuple(
                v.into_iter()
                    .map(|x| convert(gcx, ctx, x, scope_ix, Mode::Traverse))
                    .collect(),
            ),
            sp,
            Some(ty),
        ),
        ExprKind::TupleProj(x, n) => {
            let x = convert(gcx, ctx, x, scope_ix, Mode::Traverse);
            Expr::new(
                gcx,
                gcx.arenas.core.next_id(),
                ExprKind::TupleProj(x, n),
                sp,
                Some(ty),
            )
        }
        // Free with respect to the global context. These are
        // represented as global values, so we don't need to worry
        // about lifting them
        ExprKind::Free(_) => term,
        _ => term,
    }
}
