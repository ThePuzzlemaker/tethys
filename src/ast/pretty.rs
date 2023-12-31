use id_arena::Id;
use pretty::{DocAllocator, RcAllocator, RcDoc};

use crate::ctxt::GlobalCtxt;

use super::{Expr, ExprKind, Item, ItemKind, Ty, TyKind};

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

pub fn pp_ty(prec: usize, gcx: &GlobalCtxt, ty: Id<Ty>) -> RcDoc<'_> {
    match gcx.arenas.ast.ty(ty).kind {
        TyKind::Unit => RcDoc::text("()"),
        TyKind::Name(nm) => RcDoc::text(nm.as_str()),
        TyKind::Arrow(a, b) => {
            let a = pp_ty(PREC_TY_PRIMARY, gcx, a);
            let b = pp_ty(PREC_TY_FORALL, gcx, b);
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
            let a = pp_ty(PREC_TY_FORALL, gcx, a);
            maybe_paren(
                prec,
                PREC_TY_FORALL,
                RcAllocator
                    .text("forall ")
                    .append(x.as_str())
                    .append(".")
                    .append(RcDoc::line())
                    .append(a.group())
                    .group()
                    .align()
                    .into_doc(),
            )
        }
        TyKind::Err => RcDoc::text("<syntax error>"),
    }
}

const PREC_EXPR_PRIMARY: usize = 4;
const PREC_EXPR_APPL: usize = 3;
const PREC_EXPR_LAMBDA: usize = 2;
const PREC_EXPR_LET: usize = 1;

pub fn pp_expr(prec: usize, gcx: &GlobalCtxt, expr: Id<Expr>) -> RcDoc<'_> {
    match gcx.arenas.ast.expr(expr).kind {
        ExprKind::Unit => RcDoc::text("()"),
        ExprKind::Name(n) => RcDoc::text(n.as_str()),
        ExprKind::Lambda(x, body) => {
            let body = pp_expr(PREC_EXPR_LET, gcx, body);
            maybe_paren(
                prec,
                PREC_EXPR_LAMBDA,
                RcDoc::text("λ").append(x.as_str()).append(".").append(body),
            )
        }
        ExprKind::Apply(f, x) => {
            let f = pp_expr(PREC_EXPR_APPL, gcx, f);
            let x = pp_expr(PREC_EXPR_PRIMARY, gcx, x);
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
        ExprKind::Let(x, _, t, e1, e2) => {
            let t = t.map(|t| pp_ty(PREC_TY_FORALL, gcx, t));
            let e1 = pp_expr(PREC_EXPR_LET, gcx, e1);
            let e2 = pp_expr(PREC_EXPR_LET, gcx, e2);
            let t = match t {
                Some(t) => RcAllocator
                    .text(":")
                    .append(RcDoc::space())
                    .append(RcAllocator.nil().append(t).align())
                    // TODO: add some kind of heuristic to make this a
                    // line for more complex inner values
                    .append(RcDoc::softline())
                    .append("=")
                    .append(RcDoc::space())
                    .append(e1),
                None => RcAllocator.text("=").append(RcDoc::space()).append(e1),
            };
            maybe_paren(
                prec,
                PREC_EXPR_LET,
                RcAllocator
                    .text("let")
                    .append(RcDoc::space())
                    .append(x.as_str())
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
        ExprKind::Number(n) => RcDoc::text(n.to_string()),
        ExprKind::Err => RcDoc::text("<syntax error>"),
    }
}

pub fn pp_item(gcx: &GlobalCtxt, item: Id<Item>) -> RcDoc<'_> {
    let item = gcx.arenas.ast.item(item);
    match item.kind {
        ItemKind::Value(t, e) => {
            let t = pp_ty(0, gcx, t);
            let e = pp_expr(0, gcx, e);
            let t = RcAllocator
                .text(":")
                .append(RcDoc::space())
                .append(RcAllocator.nil().append(t).align())
                .append(RcDoc::line())
                .append("=")
                .append(RcDoc::space())
                .append(e);
            RcAllocator
                .text("def")
                .append(RcDoc::space())
                .append(item.ident.as_str())
                .append(RcDoc::space())
                .append(t.align())
                .into_doc()
        }
        ItemKind::TyAlias(t) => {
            let t = pp_ty(0, gcx, t);
            RcAllocator
                .text("type")
                .append(RcDoc::space())
                .append(item.ident.as_str())
                .append(RcDoc::space())
                .append("=")
                .append(RcDoc::space())
                .append(t)
                .into_doc()
        }
        ItemKind::Enum(cons) => {
            let doc = if cons.is_empty() {
                RcAllocator.text("|")
            } else {
                let mut doc = RcAllocator.nil().align();
                let mut sep = RcAllocator.nil();
                for (id, tys) in cons {
                    doc = doc
                        .append(sep.clone())
                        .append(id.as_str())
                        .append(RcDoc::space())
                        .append(RcAllocator.intersperse(
                            tys.into_iter().map(|t| pp_ty(PREC_TY_PRIMARY, gcx, t)),
                            RcDoc::space(),
                        ));
                    sep = RcAllocator.line().append("|").append(RcDoc::space());
                }
                doc
            };

            RcAllocator
                .text("enum")
                .append(RcDoc::space())
                .append(item.ident.as_str())
                .append(RcDoc::space())
                .append(
                    RcAllocator
                        .text("=")
                        .append(RcDoc::space())
                        .append(doc)
                        .align(),
                )
                .into_doc()
        }
    }
}
