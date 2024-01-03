use std::iter;

use calypso_base::symbol::Symbol;
use id_arena::Id;
use pretty::{DocAllocator, RcAllocator, RcDoc};

use crate::{
    ast::{
        pretty::{
            prec_binop, PREC_EXPR_APPL, PREC_EXPR_IF, PREC_EXPR_LAMBDA, PREC_EXPR_LET,
            PREC_EXPR_PRIMARY, PREC_EXPR_TUPLE_PROJ, PREC_EXPR_UNARY,
        },
        BinOpKind, ItemKind, Node, PrimTy,
    },
    ctxt::GlobalCtxt,
};

use super::{
    ast::{DeBruijnLvl, Expr, ExprKind, MetaInfo, Ty, TyKind},
    norm::{nf_ty_force, quote_ty, VTy},
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
                .core
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
        TyKind::Enum(id, generics) => RcDoc::text(
            gcx.arenas
                .ast
                .get_node_by_id(id)
                .unwrap()
                .ident(gcx)
                .unwrap()
                .as_str(),
        )
        .append({
            let doc = RcAllocator.intersperse(
                generics
                    .iter()
                    .copied()
                    .map(|x| pp_ty(PREC_TY_FORALL, gcx, l, e.clone(), x)),
                RcDoc::text(",").append(RcDoc::space()),
            );
            if generics.is_empty() {
                RcAllocator.nil()
            } else {
                doc.brackets()
            }
        }),
        TyKind::Arrow(a, b) => {
            let a = pp_ty(PREC_TY_PRIMARY, gcx, l, e.clone(), a);
            let b = pp_ty(PREC_TY_FORALL, gcx, l, e, b);
            maybe_paren(
                prec,
                PREC_TY_ARROW,
                a.append(RcDoc::line())
                    .append("->")
                    .append(RcDoc::space())
                    .append(b),
            )
        }
        TyKind::Forall(x, i, a) => {
            e.push_back(VTy::rigid(gcx, gcx.arenas.core.next_id(), x, l));
            let a = pp_ty(PREC_TY_FORALL, gcx, l + 1, e, a);
            maybe_paren(
                prec,
                PREC_TY_FORALL,
                RcAllocator
                    .text("forall ")
                    .append(i.as_str())
                    .append(".")
                    .append(RcDoc::line())
                    .append(a.group())
                    .group()
                    .align()
                    .into_doc(),
            )
        }
        TyKind::Meta(m, _) | TyKind::InsertedMeta(m)
            if m.0.borrow().1.name == Symbol::intern_static("?_") =>
        {
            // TODO: find a less hacky way to do this
            RcDoc::text("_")
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
        TyKind::Primitive(PrimTy::Integer) => RcDoc::text("Integer"),
        TyKind::Primitive(PrimTy::Boolean) => RcDoc::text("Boolean"),

        TyKind::Tuple(v) => {
            let v_multi = v.iter().copied().map(|x| {
                RcAllocator
                    .nil()
                    .append(pp_ty(PREC_TY_FORALL, gcx, l, e.clone(), x))
                    .nest(2)
                    .append(",")
                    .append(RcDoc::line())
            });
            let v_flat = if v.len() > 1 {
                RcAllocator
                    .intersperse(
                        v.iter()
                            .copied()
                            .map(|x| {
                                RcAllocator
                                    .nil()
                                    .append(pp_ty(PREC_TY_FORALL, gcx, l, e.clone(), x))
                                    .nest(2)
                            })
                            .collect::<Vec<_>>(),
                        RcAllocator.text(",").append(" "),
                    )
                    .parens()
            } else {
                RcAllocator
                    .nil()
                    .append(pp_ty(PREC_TY_FORALL, gcx, l, e.clone(), v[0]).nest(2))
                    .append(",")
                    .parens()
            };
            RcAllocator
                .text("(")
                .append(RcDoc::line())
                .append(RcAllocator.intersperse(v_multi, RcDoc::nil()).indent(4))
                .append(")")
                .flat_alt(v_flat)
                .group()
                .into_doc()
        }
        TyKind::TupleFlex(v) => {
            let v_multi = v
                .iter()
                .copied()
                .map(|x| {
                    RcAllocator
                        .nil()
                        .append(pp_ty(PREC_TY_FORALL, gcx, l, e.clone(), x))
                        .nest(2)
                        .append(",")
                        .append(RcDoc::line())
                })
                .chain(iter::once(RcAllocator.text("...").append(RcDoc::line())));
            let v_flat = if v.len() > 1 {
                RcAllocator
                    .intersperse(
                        v.iter()
                            .copied()
                            .map(|x| {
                                RcAllocator
                                    .nil()
                                    .append(pp_ty(PREC_TY_FORALL, gcx, l, e.clone(), x))
                                    .nest(2)
                            })
                            .chain(iter::once(RcAllocator.text("...")))
                            .collect::<Vec<_>>(),
                        RcAllocator.text(",").append(" "),
                    )
                    .parens()
            } else {
                RcAllocator
                    .nil()
                    .append(pp_ty(PREC_TY_FORALL, gcx, l, e.clone(), v[0]).nest(2))
                    .append(",")
                    .append(RcDoc::space())
                    .append("...")
                    .parens()
            };
            RcAllocator
                .text("(")
                .append(RcDoc::line())
                .append(RcAllocator.intersperse(v_multi, RcDoc::nil()).indent(4))
                .append(")")
                .flat_alt(v_flat)
                .group()
                .into_doc()
        }
    }
}

pub fn pp_expr(
    prec: usize,
    gcx: &GlobalCtxt,
    l: DeBruijnLvl,
    mut e: im::Vector<Id<VTy>>,
    expr: Id<Expr>,
) -> RcDoc<'_> {
    match gcx.arenas.core.expr(expr).kind {
        ExprKind::Unit => RcDoc::text("()"),
        ExprKind::Var(id, _) => RcDoc::text(
            gcx.arenas
                .core
                .get_node_by_id(id)
                .unwrap()
                .ident(gcx)
                .unwrap()
                .as_str(),
        ),
        ExprKind::TupleProj(expr, ix) => {
            let expr = pp_expr(PREC_EXPR_TUPLE_PROJ, gcx, l, e, expr);
            maybe_paren(
                prec,
                PREC_EXPR_TUPLE_PROJ,
                expr.append(".").append(ix.to_string()),
            )
        }
        ExprKind::Free(id) | ExprKind::EnumRecursor(id) => RcDoc::text(
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
            let ItemKind::Enum(_, cons, _) = gcx.arenas.ast.item(i).kind else {
                unreachable!()
            };

            let &(ident, _) = cons.get(branch).unwrap();

            RcDoc::text(ident.as_str())
        }
        ExprKind::Lam(_, i, body) => {
            let body = pp_expr(PREC_EXPR_LET, gcx, l, e, body);
            maybe_paren(
                prec,
                PREC_EXPR_LAMBDA,
                RcDoc::text("λ").append(i.as_str()).append(".").append(body),
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
        ExprKind::Let(_, i, t, e1, e2) => {
            let t = pp_ty(PREC_TY_FORALL, gcx, l, e.clone(), t);
            let e1 = pp_expr(PREC_EXPR_LET, gcx, l, e.clone(), e1);
            let e2 = pp_expr(PREC_EXPR_LET, gcx, l, e, e2);
            let t = RcAllocator
                .text(":")
                .append(RcDoc::space())
                .append(RcAllocator.nil().append(t).align().group())
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
                    .append(i.as_str())
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
                    .append(t.group())
                    .group()
                    .into_doc(),
            )
        }
        ExprKind::TyAbs(x, i, body) => {
            e.push_back(VTy::rigid(gcx, gcx.arenas.core.next_id(), x, l));
            let body = pp_expr(PREC_EXPR_LET, gcx, l + 1, e, body);
            maybe_paren(
                prec,
                PREC_EXPR_LAMBDA,
                RcDoc::text("Λ").append(i.as_str()).append(".").append(body),
            )
        }
        ExprKind::Fix(_, _, _) => todo!(),
        ExprKind::Err(_) => RcDoc::text("<error>"),
        ExprKind::Number(v) => RcDoc::text(v.to_string()),
        ExprKind::Boolean(b) => RcDoc::text(b.to_string()),
        ExprKind::BinaryOp { left, kind, right } => {
            // TODO: precedence
            let left = pp_expr(prec_binop(kind), gcx, l, e.clone(), left);
            let right = pp_expr(prec_binop(kind), gcx, l, e, right);
            maybe_paren(
                prec,
                prec_binop(kind),
                left.append(RcDoc::space())
                    .append(match kind {
                        BinOpKind::LogicalOr => "||",
                        BinOpKind::LogicalAnd => "&&",
                        BinOpKind::BitOr => "|",
                        BinOpKind::BitAnd => "&",
                        BinOpKind::BitXor => "^",
                        BinOpKind::Equal => "==",
                        BinOpKind::NotEqual => "!=",
                        BinOpKind::LessThan => "<",
                        BinOpKind::GreaterThan => ">",
                        BinOpKind::LessEqual => "<=",
                        BinOpKind::GreaterEqual => ">=",
                        BinOpKind::BitShiftLeft => "<<",
                        BinOpKind::BitShiftRight => ">>",
                        BinOpKind::Add => "+",
                        BinOpKind::Subtract => "-",
                        BinOpKind::Multiply => "*",
                        BinOpKind::Divide => "/",
                        BinOpKind::Modulo => "%",
                        BinOpKind::Power => "**",
                    })
                    .append(RcDoc::space())
                    .append(right),
            )
        }

        ExprKind::If(cond, then, then_else) => {
            let cond = pp_expr(PREC_EXPR_LAMBDA, gcx, l, e.clone(), cond);
            let then = pp_expr(PREC_EXPR_LET, gcx, l, e.clone(), then);
            let then_else = pp_expr(PREC_EXPR_LET, gcx, l, e, then_else);

            maybe_paren(
                prec,
                PREC_EXPR_IF,
                RcAllocator
                    .text("if")
                    .append(RcDoc::space())
                    .append(cond)
                    .append(RcDoc::softline())
                    .append(
                        RcAllocator
                            .text("then")
                            .append(RcDoc::space())
                            .append(then)
                            .into_doc(),
                    )
                    .align()
                    .append(RcDoc::softline())
                    .append(
                        RcAllocator
                            .text("else")
                            .append(RcDoc::space())
                            .append(then_else)
                            .into_doc(),
                    )
                    .align()
                    .into_doc(),
            )
        }
        ExprKind::Tuple(v) => {
            let v_multi = v.iter().copied().map(|x| {
                RcAllocator
                    .nil()
                    .append(pp_expr(PREC_EXPR_LET, gcx, l, e.clone(), x))
                    .nest(2)
                    .append(",")
                    .append(RcDoc::line())
            });
            let v_flat = if v.len() > 1 {
                RcAllocator
                    .intersperse(
                        v.iter()
                            .copied()
                            .map(|x| {
                                RcAllocator
                                    .nil()
                                    .append(pp_expr(PREC_EXPR_LET, gcx, l, e.clone(), x))
                                    .nest(2)
                            })
                            .collect::<Vec<_>>(),
                        RcAllocator.text(",").append(" "),
                    )
                    .parens()
            } else {
                RcAllocator
                    .nil()
                    .append(pp_expr(PREC_EXPR_LET, gcx, l, e.clone(), v[0]).nest(2))
                    .append(",")
                    .parens()
            };
            RcAllocator
                .text("(")
                .append(RcDoc::line())
                .append(RcAllocator.intersperse(v_multi, RcDoc::nil()).indent(4))
                .append(")")
                .flat_alt(v_flat)
                .group()
                .into_doc()
        } // ExprKind::UnaryMinus(expr) => maybe_paren(
          //     prec,
          //     PREC_EXPR_UNARY,
          //     RcAllocator
          //         .text("-")
          //         .append(pp_expr(PREC_EXPR_UNARY, gcx, l, e, expr))
          //         .into_doc(),
          // ),

          // ExprKind::UnaryNot(expr) => maybe_paren(
          //     prec,
          //     PREC_EXPR_UNARY,
          //     RcAllocator
          //         .text("!")
          //         .append(pp_expr(PREC_EXPR_UNARY, gcx, l, e, expr))
          //         .into_doc(),
          // ),
    }
}
