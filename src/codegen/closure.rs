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

use id_arena::Id;

use crate::{
    ctxt::GlobalCtxt,
    eval::EvalCtx,
    typeck::ast::{CoreAstId, DeBruijnIdx, DeBruijnLvl, Expr, ExprKind},
};

struct ConvCtxt {
    lifted: Vec<Id<Expr>>,
    scopes: Vec<Scope>,
    env: Vec<CoreAstId>,
}

impl ConvCtxt {}

pub fn closure_convert(gcx: &GlobalCtxt, term: Id<Expr>) -> (Vec<Id<Expr>>, Id<Expr>) {
    let mut ctx = ConvCtxt {
        lifted: vec![],
        env: vec![],
        scopes: vec![],
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
    match gcx.arenas.core.expr(term).kind {
        ExprKind::Var(_, ix) => {
            let scope = &mut ctx.scopes[scope_ix];
            let lvl = DeBruijnLvl::from(ctx.env.len() - ix.index() - 1);
            if lvl < scope.offset {
                let i = ctx.env[lvl.index()];
                scope.free.push_back(i);
                Expr::new(
                    gcx,
                    gcx.arenas.core.next_id(),
                    ExprKind::LiftedFree(DeBruijnLvl::from(scope.free.len() - 1)),
                    sp,
                    None,
                )
            } else {
                Expr::new(
                    gcx,
                    gcx.arenas.core.next_id(),
                    ExprKind::LiftedVar(DeBruijnIdx::from(ix.index())),
                    sp,
                    None,
                )
            }
        }
        ExprKind::Lam(i, _, body) if mode == Mode::Collect => {
            let scope = &mut ctx.scopes[scope_ix];
            scope.len += 1;
            ctx.env.push(i);

            convert(gcx, ctx, body, scope_ix, Mode::Collect)
        }
        ExprKind::Lam(i, _, body) if mode == Mode::Traverse || mode == Mode::Root => {
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
            let res = Expr::new(
                gcx,
                gcx.arenas.core.next_id(),
                ExprKind::LiftedLam(
                    ctx.scopes[next_scope_ix]
                        .free
                        .iter()
                        .chain(vars.iter())
                        .copied()
                        .collect(),
                    res,
                ),
                sp,
                None,
            );
            if mode != Mode::Root {
                ctx.lifted.push(res);
            }

            let xs = ctx.scopes[next_scope_ix]
                .free
                .clone()
                .iter()
                .map(|id| {
                    let mut free_scope = None;
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
                            free_scope = Some(scope.clone());
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

                    Expr::new(
                        gcx,
                        gcx.arenas.core.next_id(),
                        ExprKind::LiftedVar(DeBruijnIdx::from(
                            free_ix.unwrap() - free_scope.unwrap().offset,
                        )),
                        sp,
                        None,
                    )
                })
                .collect::<im::Vector<_>>();

            let res = if xs.is_empty() {
                res
            } else {
                Expr::new(
                    gcx,
                    gcx.arenas.core.next_id(),
                    ExprKind::LiftedApp(res, xs),
                    sp,
                    None,
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
                None,
            )
        }
        ExprKind::TyApp(e, _) | ExprKind::TyAbs(_, _, e) => {
            convert(gcx, ctx, e, scope_ix, Mode::Traverse)
        }
        // TODO: lower `let`s elsewhere?
        ExprKind::Let(x, i, _, e1, e2) => {
            let e2 = Expr::new(
                gcx,
                gcx.arenas.core.next_id(),
                ExprKind::App(
                    Expr::new(
                        gcx,
                        gcx.arenas.core.next_id(),
                        ExprKind::Lam(x, i, e2),
                        sp,
                        None,
                    ),
                    e1,
                ),
                sp,
                None,
            );
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
                None,
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
                None,
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
            None,
        ),
        ExprKind::TupleProj(x, n) => {
            let x = convert(gcx, ctx, x, scope_ix, Mode::Traverse);
            Expr::new(
                gcx,
                gcx.arenas.core.next_id(),
                ExprKind::TupleProj(x, n),
                sp,
                None,
            )
        }
        // Free with respect to the global context. These are
        // represented as global values, so we don't need to worry
        // about lifting them
        ExprKind::Free(_) => term,
        _ => term,
    }
}
