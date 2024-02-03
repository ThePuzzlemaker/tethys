use id_arena::Id;
use pretty::{DocAllocator, RcAllocator, RcDoc};

use crate::ctxt::GlobalCtxt;

use super::{BinOpKind, Expr, ExprKind, Item, ItemKind, Recursive, Ty, TyKind};

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
        TyKind::Data(nm, generics) => RcAllocator
            .text(nm.as_str())
            .append(
                RcAllocator
                    .intersperse(
                        generics
                            .iter()
                            .copied()
                            .map(|x| pp_ty(PREC_TY_FORALL, gcx, x)),
                        RcDoc::text(",").append(RcDoc::space()),
                    )
                    .brackets(),
            )
            .into_doc(),
        TyKind::Arrow(a, b) => {
            let a = pp_ty(PREC_TY_PRIMARY, gcx, a);
            let b = pp_ty(PREC_TY_FORALL, gcx, b);
            maybe_paren(
                prec,
                PREC_TY_ARROW,
                a.append(RcDoc::line())
                    .append("->")
                    .append(RcDoc::space())
                    .append(b),
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
        TyKind::Tuple(v) => {
            let v_multi = v.iter().copied().map(|x| {
                RcAllocator
                    .nil()
                    .append(pp_ty(PREC_TY_FORALL, gcx, x))
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
                                    .append(pp_ty(PREC_TY_FORALL, gcx, x))
                                    .nest(2)
                            })
                            .collect::<Vec<_>>(),
                        RcAllocator.text(",").append(" "),
                    )
                    .parens()
            } else {
                RcAllocator
                    .nil()
                    .append(pp_ty(PREC_TY_FORALL, gcx, v[0]).nest(2))
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
        TyKind::Err => RcDoc::text("<syntax error>"),
    }
}

pub const PREC_EXPR_PRIMARY: usize = 150;
pub const PREC_EXPR_TUPLE_PROJ: usize = 145;
pub const PREC_EXPR_APPL: usize = 140;
pub const PREC_EXPR_UNARY: usize = 120;
pub const PREC_EXPR_LAMBDA: usize = 20;
pub const PREC_EXPR_IF: usize = 15;
pub const PREC_EXPR_LET: usize = 10;

pub fn prec_binop(kind: BinOpKind) -> usize {
    match kind {
        BinOpKind::LogicalOr => 30,
        BinOpKind::LogicalAnd => 40,
        BinOpKind::Equal
        | BinOpKind::NotEqual
        | BinOpKind::LessThan
        | BinOpKind::LessEqual
        | BinOpKind::GreaterThan
        | BinOpKind::GreaterEqual => 50,
        BinOpKind::BitOr => 60,
        BinOpKind::BitXor => 70,
        BinOpKind::BitAnd => 80,
        BinOpKind::BitShiftLeft | BinOpKind::BitShiftRight => 90,
        BinOpKind::Add | BinOpKind::Subtract => 100,
        BinOpKind::Multiply | BinOpKind::Divide | BinOpKind::Modulo => 110,
        BinOpKind::Power => 130,
    }
}

pub fn pp_expr(prec: usize, gcx: &GlobalCtxt, expr: Id<Expr>) -> RcDoc<'_> {
    match gcx.arenas.ast.expr(expr).kind {
        ExprKind::Unit => RcDoc::text("()"),
        ExprKind::Name(n) => RcDoc::text(n.as_str()),
        ExprKind::TupleProj(expr, ix) => {
            let expr = pp_expr(PREC_EXPR_TUPLE_PROJ, gcx, expr);
            maybe_paren(
                prec,
                PREC_EXPR_TUPLE_PROJ,
                expr.append(".").append(ix.to_string()),
            )
        }
        ExprKind::Tuple(v) => {
            let v_multi = v.iter().copied().map(|x| {
                RcAllocator
                    .nil()
                    .append(pp_expr(PREC_EXPR_LET, gcx, x))
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
                                    .append(pp_expr(PREC_EXPR_LET, gcx, x))
                                    .nest(2)
                            })
                            .collect::<Vec<_>>(),
                        RcAllocator.text(",").append(" "),
                    )
                    .parens()
            } else {
                RcAllocator
                    .nil()
                    .append(pp_expr(PREC_EXPR_LET, gcx, v[0]).nest(2))
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
        ExprKind::BinaryOp { left, kind, right } => {
            // TODO: precedence
            let left = pp_expr(prec_binop(kind), gcx, left);
            let right = pp_expr(prec_binop(kind), gcx, right);
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
        ExprKind::UnaryMinus(expr) => maybe_paren(
            prec,
            PREC_EXPR_UNARY,
            RcAllocator
                .text("-")
                .append(pp_expr(PREC_EXPR_UNARY, gcx, expr))
                .into_doc(),
        ),

        ExprKind::UnaryNot(expr) => maybe_paren(
            prec,
            PREC_EXPR_UNARY,
            RcAllocator
                .text("!")
                .append(pp_expr(PREC_EXPR_UNARY, gcx, expr))
                .into_doc(),
        ),
        ExprKind::If(cond, then, then_else) => {
            let cond = pp_expr(PREC_EXPR_LAMBDA, gcx, cond);
            let then = pp_expr(PREC_EXPR_LET, gcx, then);
            let then_else = pp_expr(PREC_EXPR_LET, gcx, then_else);

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
        ExprKind::Let(x, rec, t, e1, e2) => {
            let t = t.map(|t| pp_ty(PREC_TY_FORALL, gcx, t));
            let e1 = pp_expr(PREC_EXPR_LET, gcx, e1);
            let e2 = pp_expr(PREC_EXPR_LET, gcx, e2);
            let t = match t {
                Some(t) => RcAllocator
                    .text(":")
                    .append(RcDoc::space())
                    .append(RcAllocator.nil().append(t).align().group())
                    // TODO: add some kind of heuristic to make this a
                    // line for more complex inner values (flat_alt?)
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
                    .append(if rec != Recursive::NotRecursive {
                        RcDoc::space().append("rec")
                    } else {
                        RcDoc::nil()
                    })
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
        ExprKind::Boolean(b) => RcDoc::text(b.to_string()),
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
                .append(RcAllocator.nil().append(t).align().group())
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
        ItemKind::Enum(generics, cons, _) => {
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
                .append({
                    let doc = RcAllocator.intersperse(
                        generics.iter().copied().map(|x| RcDoc::text(x.as_str())),
                        RcDoc::text(",").append(RcDoc::space()),
                    );
                    if generics.is_empty() {
                        RcAllocator.nil()
                    } else {
                        doc.brackets()
                    }
                })
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
