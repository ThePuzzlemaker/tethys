use std::rc::Rc;

use id_arena::Id;
use pretty::{DocAllocator, RcAllocator, RcDoc};

use crate::ctxt::GlobalCtxt;

use super::{apply_closure, EvalCtx, VExpr};

fn maybe_paren(x: usize, y: usize, doc: RcDoc<'_>) -> RcDoc<'_> {
    if y < x {
        RcDoc::text("(").append(doc).append(")").group()
    } else {
        doc
    }
}

const PREC_EXPR_PRIMARY: usize = 4;
const PREC_EXPR_APPL: usize = 3;
const PREC_EXPR_LAMBDA: usize = 2;
const PREC_EXPR_LET: usize = 1;

pub fn pp_expr<'a>(
    prec: usize,
    gcx: &'a GlobalCtxt,
    ecx: &mut EvalCtx,
    expr: Rc<VExpr>,
) -> RcDoc<'a> {
    match &*expr {
        VExpr::Unit => RcDoc::text("()"),
        VExpr::EnumRecursor(id) => RcDoc::text(
            gcx.arenas
                .ast
                .get_node_by_id(*id)
                .unwrap()
                .ident(gcx)
                .unwrap()
                .as_str(),
        ),
        VExpr::EnumConstructor {
            id, branch, vector, ..
        } => RcDoc::text(format!("<id={id},branch={branch},vector={vector:?}>")),
        VExpr::Free(ident) => RcDoc::text(ident.as_str()),
        VExpr::Lam(x, body) => {
            let body = crate::typeck::pretty::pp_expr_no_norm(PREC_EXPR_LET, gcx, body.1);
            maybe_paren(
                prec,
                PREC_EXPR_LAMBDA,
                RcDoc::text("λ")
                    .append(
                        gcx.arenas
                            .ast
                            .get_node_by_id(*x)
                            .unwrap()
                            .ident(gcx)
                            .unwrap()
                            .as_str(),
                    )
                    .append(".")
                    .append(body),
            )
        }
        VExpr::App(f, x) => {
            let f = pp_expr(PREC_EXPR_APPL, gcx, ecx, f.clone());
            let x = pp_expr(PREC_EXPR_PRIMARY, gcx, ecx, x.clone());
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
        _ => todo!("{:#?}", expr),
    }
}
