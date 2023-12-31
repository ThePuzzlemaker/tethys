use calypso_base::symbol::Symbol;
use id_arena::Id;
use pretty::{DocAllocator, RcAllocator, RcDoc};

use crate::{
    ast::{ItemKind, Node},
    ctxt::GlobalCtxt,
};

use super::{
    ast::{DeBruijnLvl, Expr, ExprKind, MetaInfo, Ty, TyKind},
    norm::{eval_ty, nf_ty_force, quote_ty, VTy},
};

const PREC_TY_PRIMARY: usize = 3;
const PREC_TY_ARROW: usize = 2;
const PREC_TY_FORALL: usize = 1;

fn maybe_paren(x: usize, y: usize, doc: RcDoc<'_>) -> RcDoc<'_> {
    if y < x {
        RcDoc::text("(").append(doc).append(")").group()
    } else {
        doc
    }
}

pub fn pp_ty(
    prec: usize,
    gcx: &GlobalCtxt,
    l: DeBruijnLvl,
    mut e: im::Vector<Id<VTy>>,
    ty: Id<Ty>,
) -> RcDoc<'_> {
    // TODO: nf/force
    match gcx.arenas.core.ty(nf_ty_force(gcx, l, e.clone(), ty)).kind {
        TyKind::Unit => RcDoc::text("()"),
        TyKind::Var(id, _) => RcDoc::text(
            gcx.arenas
                .ast
                .get_node_by_id(id)
                .unwrap()
                .ident(gcx)
                .unwrap()
                .as_str(),
        ),
        TyKind::Free(id) => RcDoc::text(
            gcx.arenas
                .ast
                .get_node_by_id(id)
                .unwrap()
                .ident(gcx)
                .unwrap()
                .as_str(),
        ),
        TyKind::Enum(id) => RcDoc::text(
            gcx.arenas
                .ast
                .get_node_by_id(id)
                .unwrap()
                .ident(gcx)
                .unwrap()
                .as_str(),
        ),
        TyKind::Arrow(a, b) => {
            let a = pp_ty(PREC_TY_PRIMARY, gcx, l, e.clone(), a);
            let b = pp_ty(PREC_TY_FORALL, gcx, l, e, b);
            maybe_paren(
                prec,
                PREC_TY_ARROW,
                a.append(RcDoc::line())
                    .append("->")
                    .append(RcDoc::space())
                    .append(b)
                    .group(),
            )
        }
        TyKind::Forall(x, a) => {
            e.push_back(VTy::rigid(gcx, x, l));
            let a = pp_ty(PREC_TY_FORALL, gcx, l + 1, e, a);
            maybe_paren(
                prec,
                PREC_TY_FORALL,
                RcAllocator
                    .text("forall ")
                    .append(
                        gcx.arenas
                            .ast
                            .get_node_by_id(x)
                            .unwrap()
                            .ident(gcx)
                            .unwrap()
                            .as_str(),
                    )
                    .append(".")
                    .append(RcDoc::line())
                    .append(a.group())
                    .group()
                    .align()
                    .into_doc(),
            )
        }
        TyKind::Meta(x, sp) => {
            let MetaInfo { name, .. } = x.0.borrow().1;
            let sp = sp
                .into_iter()
                .map(|t| pp_ty(PREC_TY_PRIMARY, gcx, l, e.clone(), t))
                .collect::<Vec<_>>();
            (if sp.is_empty() {
                RcDoc::nil()
            } else {
                RcDoc::text("(")
            })
            .append(RcDoc::text(name.as_str()))
            .append(sp.iter().fold(RcDoc::nil(), |acc, x| {
                acc.append(RcDoc::space()).append(x.clone())
            }))
            .append(if sp.is_empty() {
                RcDoc::nil()
            } else {
                RcDoc::text(")")
            })
        }
        TyKind::InsertedMeta(x) => {
            let MetaInfo { name, .. } = x.0.borrow().1;
            let sp = e
                .clone()
                .into_iter()
                .map(|t| quote_ty(gcx, l, t))
                .map(|t| pp_ty(PREC_TY_PRIMARY, gcx, l, e.clone(), t))
                .collect::<Vec<_>>();
            (if sp.is_empty() {
                RcDoc::nil()
            } else {
                RcDoc::text("(")
            })
            .append(RcDoc::text(name.as_str()))
            .append(if sp.is_empty() {
                RcDoc::nil()
            } else {
                RcDoc::space()
            })
            .append(sp.iter().fold(RcDoc::nil(), |acc, x| acc.append(x.clone())))
            .append(if sp.is_empty() {
                RcDoc::nil()
            } else {
                RcDoc::text(")")
            })
        }
    }
}

const PREC_EXPR_PRIMARY: usize = 4;
const PREC_EXPR_APPL: usize = 3;
const PREC_EXPR_LAMBDA: usize = 2;
const PREC_EXPR_LET: usize = 1;

pub fn pp_expr(
    prec: usize,
    gcx: &GlobalCtxt,
    l: DeBruijnLvl,
    mut e: im::Vector<Id<VTy>>,
    expr: Id<Expr>,
) -> RcDoc<'_> {
    match gcx.arenas.core.expr(expr).kind {
        ExprKind::Unit => RcDoc::text("()"),
        ExprKind::Var(id, _) | ExprKind::Free(id) | ExprKind::EnumRecursor(id) => RcDoc::text(
            gcx.arenas
                .ast
                .get_node_by_id(id)
                .unwrap()
                .ident(gcx)
                .unwrap()
                .as_str(),
        ),
        ExprKind::EnumConstructor(id, branch) => {
            let Node::Item(i) = gcx.arenas.ast.get_node_by_id(id).unwrap() else {
                unreachable!()
            };
            let ItemKind::Enum(cons) = gcx.arenas.ast.item(i).kind else {
                unreachable!()
            };

            let &(ident, _) = cons.get(branch).unwrap();

            RcDoc::text(ident.as_str())
        }
        ExprKind::Lam(x, body) => {
            let body = pp_expr(PREC_EXPR_LET, gcx, l, e, body);
            maybe_paren(
                prec,
                PREC_EXPR_LAMBDA,
                RcDoc::text("λ")
                    .append(
                        gcx.arenas
                            .ast
                            .get_node_by_id(x)
                            .unwrap()
                            .ident(gcx)
                            .unwrap()
                            .as_str(),
                    )
                    .append(".")
                    .append(body),
            )
        }
        ExprKind::App(f, x) => {
            let f = pp_expr(PREC_EXPR_APPL, gcx, l, e.clone(), f);
            let x = pp_expr(PREC_EXPR_PRIMARY, gcx, l, e, x);
            maybe_paren(
                prec,
                PREC_EXPR_APPL,
                (RcAllocator.nil().append(f).append(RcDoc::line()))
                    .align()
                    .append(RcAllocator.nil().append(x))
                    .align()
                    .group()
                    .into_doc(),
            )
        }
        ExprKind::Let(x, t, e1, e2) => {
            let t = pp_ty(PREC_TY_FORALL, gcx, l, e.clone(), t);
            let e1 = pp_expr(PREC_EXPR_LET, gcx, l, e.clone(), e1);
            let e2 = pp_expr(PREC_EXPR_LET, gcx, l, e, e2);
            let t = RcAllocator
                .text(":")
                .append(RcDoc::space())
                .append(RcAllocator.nil().append(t).align())
                .append(RcDoc::line())
                .append("=")
                .append(RcDoc::space())
                .append(e1);
            maybe_paren(
                prec,
                PREC_EXPR_LET,
                RcAllocator
                    .text("let")
                    .append(RcDoc::space())
                    .append(
                        gcx.arenas
                            .ast
                            .get_node_by_id(x)
                            .unwrap()
                            .ident(gcx)
                            .unwrap()
                            .as_str(),
                    )
                    .append(RcDoc::space())
                    .append(t.align())
                    .append(RcDoc::space())
                    .append("in")
                    .append(RcDoc::line())
                    .append(e2)
                    .align()
                    .into_doc(),
            )
        }
        ExprKind::TyApp(f, t) => {
            let f = pp_expr(PREC_EXPR_APPL, gcx, l, e.clone(), f);
            let t = pp_ty(PREC_TY_PRIMARY, gcx, l, e, t);
            maybe_paren(
                prec,
                PREC_EXPR_APPL,
                RcAllocator
                    .nil()
                    .append(f)
                    .append(RcDoc::line())
                    .align()
                    .append("@")
                    .append(t)
                    .group()
                    .into_doc(),
            )
        }
        ExprKind::TyAbs(x, body) => {
            e.push_back(VTy::rigid(gcx, x, l));
            let body = pp_expr(PREC_EXPR_LET, gcx, l + 1, e, body);
            maybe_paren(
                prec,
                PREC_EXPR_LAMBDA,
                RcDoc::text("Λ")
                    .append(
                        gcx.arenas
                            .ast
                            .get_node_by_id(x)
                            .unwrap()
                            .ident(gcx)
                            .unwrap()
                            .as_str(),
                    )
                    .append(".")
                    .append(body),
            )
        }
        ExprKind::Fix(_, _) => todo!(),
        ExprKind::Err(_) => RcDoc::text("<error>"),
    }
}

pub fn pp_expr_no_norm(prec: usize, gcx: &GlobalCtxt, expr: Id<Expr>) -> RcDoc<'_> {
    match gcx.arenas.core.expr(expr).kind {
        ExprKind::Unit => RcDoc::text("()"),
        ExprKind::Var(id, _) | ExprKind::Free(id) | ExprKind::EnumRecursor(id) => RcDoc::text(
            gcx.arenas
                .ast
                .get_node_by_id(id)
                .unwrap()
                .ident(gcx)
                .unwrap()
                .as_str(),
        ),
        ExprKind::EnumConstructor(id, branch) => {
            let Node::Item(i) = gcx.arenas.ast.get_node_by_id(id).unwrap() else {
                unreachable!()
            };
            let ItemKind::Enum(cons) = gcx.arenas.ast.item(i).kind else {
                unreachable!()
            };

            let &(ident, _) = cons.get(branch).unwrap();

            RcDoc::text(ident.as_str())
        }
        ExprKind::Lam(x, body) => {
            let body = pp_expr_no_norm(PREC_EXPR_LET, gcx, body);
            maybe_paren(
                prec,
                PREC_EXPR_LAMBDA,
                RcDoc::text("λ")
                    .append(
                        gcx.arenas
                            .ast
                            .get_node_by_id(x)
                            .unwrap()
                            .ident(gcx)
                            .unwrap()
                            .as_str(),
                    )
                    .append(".")
                    .append(body),
            )
        }
        ExprKind::App(f, x) => {
            let f = pp_expr_no_norm(PREC_EXPR_APPL, gcx, f);
            let x = pp_expr_no_norm(PREC_EXPR_PRIMARY, gcx, x);
            maybe_paren(
                prec,
                PREC_EXPR_APPL,
                (RcAllocator.nil().append(f).append(RcDoc::line()))
                    .align()
                    .append(RcAllocator.nil().append(x))
                    .align()
                    .group()
                    .into_doc(),
            )
        }
        ExprKind::Let(x, t, e1, e2) => {
            let t = pp_ty_no_norm(PREC_TY_FORALL, gcx, t);
            let e1 = pp_expr_no_norm(PREC_EXPR_LET, gcx, e1);
            let e2 = pp_expr_no_norm(PREC_EXPR_LET, gcx, e2);
            let t = RcAllocator
                .text(":")
                .append(RcDoc::space())
                .append(RcAllocator.nil().append(t).align())
                .append(RcDoc::line())
                .append("=")
                .append(RcDoc::space())
                .append(e1);
            maybe_paren(
                prec,
                PREC_EXPR_LET,
                RcAllocator
                    .text("let")
                    .append(RcDoc::space())
                    .append(
                        gcx.arenas
                            .ast
                            .get_node_by_id(x)
                            .unwrap()
                            .ident(gcx)
                            .unwrap()
                            .as_str(),
                    )
                    .append(RcDoc::space())
                    .append(t.align())
                    .append(RcDoc::space())
                    .append("in")
                    .append(RcDoc::line())
                    .append(e2)
                    .align()
                    .into_doc(),
            )
        }
        ExprKind::TyApp(f, t) => {
            let f = pp_expr_no_norm(PREC_EXPR_APPL, gcx, f);
            let t = pp_ty_no_norm(PREC_TY_PRIMARY, gcx, t);
            maybe_paren(
                prec,
                PREC_EXPR_APPL,
                RcAllocator
                    .nil()
                    .append(f)
                    .append(RcDoc::line())
                    .align()
                    .append("@")
                    .append(t)
                    .group()
                    .into_doc(),
            )
        }
        ExprKind::TyAbs(x, body) => {
            let body = pp_expr_no_norm(PREC_EXPR_LET, gcx, body);
            maybe_paren(
                prec,
                PREC_EXPR_LAMBDA,
                RcDoc::text("Λ")
                    .append(
                        gcx.arenas
                            .ast
                            .get_node_by_id(x)
                            .unwrap()
                            .ident(gcx)
                            .unwrap()
                            .as_str(),
                    )
                    .append(".")
                    .append(body),
            )
        }
        ExprKind::Fix(_, _) => todo!(),
        ExprKind::Err(_) => RcDoc::text("<error>"),
    }
}

pub fn pp_ty_no_norm(prec: usize, gcx: &GlobalCtxt, ty: Id<Ty>) -> RcDoc<'_> {
    // TODO: nf/force
    match gcx.arenas.core.ty(ty).kind {
        TyKind::Unit => RcDoc::text("()"),
        TyKind::Var(id, _) => RcDoc::text(
            gcx.arenas
                .ast
                .get_node_by_id(id)
                .unwrap()
                .ident(gcx)
                .unwrap()
                .as_str(),
        ),
        TyKind::Free(id) => RcDoc::text(
            gcx.arenas
                .ast
                .get_node_by_id(id)
                .unwrap()
                .ident(gcx)
                .unwrap()
                .as_str(),
        ),
        TyKind::Enum(id) => RcDoc::text(
            gcx.arenas
                .ast
                .get_node_by_id(id)
                .unwrap()
                .ident(gcx)
                .unwrap()
                .as_str(),
        ),
        TyKind::Arrow(a, b) => {
            let a = pp_ty_no_norm(PREC_TY_PRIMARY, gcx, a);
            let b = pp_ty_no_norm(PREC_TY_FORALL, gcx, b);
            maybe_paren(
                prec,
                PREC_TY_ARROW,
                a.append(RcDoc::line())
                    .append("->")
                    .append(RcDoc::space())
                    .append(b)
                    .group(),
            )
        }
        TyKind::Forall(x, a) => {
            let a = pp_ty_no_norm(PREC_TY_FORALL, gcx, a);
            maybe_paren(
                prec,
                PREC_TY_FORALL,
                RcAllocator
                    .text("forall ")
                    .append(
                        gcx.arenas
                            .ast
                            .get_node_by_id(x)
                            .unwrap()
                            .ident(gcx)
                            .unwrap()
                            .as_str(),
                    )
                    .append(".")
                    .append(RcDoc::line())
                    .append(a.group())
                    .group()
                    .align()
                    .into_doc(),
            )
        }
        TyKind::Meta(x, sp) => {
            let MetaInfo { name, .. } = x.0.borrow().1;
            let sp = sp
                .into_iter()
                .map(|t| pp_ty_no_norm(PREC_TY_PRIMARY, gcx, t))
                .collect::<Vec<_>>();
            (if sp.is_empty() {
                RcDoc::nil()
            } else {
                RcDoc::text("(")
            })
            .append(RcDoc::text(name.as_str()))
            .append(sp.iter().fold(RcDoc::nil(), |acc, x| {
                acc.append(RcDoc::space()).append(x.clone())
            }))
            .append(if sp.is_empty() {
                RcDoc::nil()
            } else {
                RcDoc::text(")")
            })
        }
        TyKind::InsertedMeta(x) => {
            let MetaInfo { name, .. } = x.0.borrow().1;
            // let sp = e
            //     .clone()
            //     .into_iter()
            //     .map(|t| quote_ty(gcx, l, t))
            //     .map(|t| pp_ty(PREC_TY_PRIMARY, gcx, l, e.clone(), t))
            //     .collect::<Vec<_>>();
            let sp: Vec<RcDoc<'_>> = vec![];
            (if sp.is_empty() {
                RcDoc::nil()
            } else {
                RcDoc::text("(")
            })
            .append(RcDoc::text(name.as_str()))
            .append(if sp.is_empty() {
                RcDoc::nil()
            } else {
                RcDoc::space()
            })
            .append(sp.iter().fold(RcDoc::nil(), |acc, x| acc.append(x.clone())))
            .append(if sp.is_empty() {
                RcDoc::nil()
            } else {
                RcDoc::text(")")
            })
        }
    }
}
