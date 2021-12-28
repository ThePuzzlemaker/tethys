use std::{cell::RefCell, rc::Rc};

use calypso_base::symbol::{Ident, Symbol};
use pretty::DocAllocator;

use crate::parse::Span;

pub type Ty<'tcx> = &'tcx TyS<'tcx>;

#[derive(Clone, Debug)]
pub struct TyS<'tcx> {
    pub span: Span,
    pub kind: TyKind<'tcx>,
}

type DocBuilder<'a> = pretty::DocBuilder<'a, pretty::Arena<'a>>;

fn maybe_parens(doc: DocBuilder<'_>, parens: bool) -> DocBuilder<'_> {
    if parens {
        doc.parens()
    } else {
        doc
    }
}

fn freshen_name(name: Ident, ctx: &[Ident]) -> Ident {
    let mut n = 1;
    let mut name1 = name;
    loop {
        if ctx.iter().any(|x| x.symbol == name1.symbol) {
            name1 = Ident {
                span: name1.span,
                symbol: Symbol::intern(&format!("{}{}", *name, n)),
            };
            n += 1;
        } else {
            break;
        }
    }
    name1
}

impl<'tcx> TyS<'tcx> {
    pub fn pretty<'a>(&'tcx self, arena: &'a pretty::Arena<'a>) -> DocBuilder<'a> {
        fn helper<'tcx, 'a>(
            ctx: &mut Vec<Ident>,
            ty: Ty<'tcx>,
            parens: bool,
            arena: &'a pretty::Arena<'a>,
        ) -> DocBuilder<'a> {
            // TODO: Deref hole here
            match ty.kind {
                TyKind::Unit => arena.text("()"),
                TyKind::Var(idx) => {
                    let sym = ctx.get(ctx.len() - idx - 1).unwrap();
                    arena.text(sym.as_str())
                }
                TyKind::Arrow(inp, out) => {
                    let inp = helper(ctx, inp, true, arena);
                    let out = helper(ctx, out, false, arena);
                    let doc = inp + arena.space() + arena.text("->") + arena.space() + out;
                    maybe_parens(doc, parens)
                }
                TyKind::Forall(name, body) => {
                    let name = freshen_name(name, ctx);
                    ctx.push(name);
                    let body = helper(ctx, body, false, arena);
                    ctx.pop();
                    maybe_parens(
                        arena.text("forall")
                            + arena.space()
                            + arena.text(name.as_str())
                            + arena.text(".")
                            + arena.space()
                            + body,
                        parens,
                    )
                }
                TyKind::Free(_) => {
                    todo!("free types")
                }
                TyKind::Hole(ref hole) => {
                    let hole = Rc::clone(hole);
                    let hole = hole.borrow();
                    if let Hole::Empty(lvl) = &*hole {
                        arena.text(format!("?[at lvl {}]", lvl))
                    } else {
                        todo!("deref holes in prettyprint");
                    }
                }
            }
        }
        helper(&mut vec![], self, false, arena)
    }
}

#[derive(Clone, Debug)]
pub enum TyKind<'tcx> {
    Unit,
    Var(Index),
    Free(Decl<'tcx>),
    Arrow(Ty<'tcx>, Ty<'tcx>),
    Forall(Ident, Ty<'tcx>),
    Hole(Rc<RefCell<Hole<'tcx>>>),
}

pub type Expr<'tcx> = &'tcx ExprS<'tcx>;

#[derive(Clone, Debug)]
pub struct ExprS<'tcx> {
    pub span: Span,
    pub kind: ExprKind<'tcx>,
}

impl<'tcx> ExprS<'tcx> {
    pub fn pretty<'a>(&'tcx self, arena: &'a pretty::Arena<'a>) -> DocBuilder<'a> {
        fn helper<'tcx, 'a>(
            ctx: &mut Vec<Ident>,
            expr: Expr<'tcx>,
            parens: bool,
            arena: &'a pretty::Arena<'a>,
        ) -> DocBuilder<'a> {
            // TODO: Deref hole here
            match expr.kind {
                ExprKind::Unit => arena.text("()"),
                ExprKind::Var(idx) => {
                    let sym = ctx.get(ctx.len() - idx - 1).unwrap();
                    arena.text(sym.as_str())
                }
                ExprKind::Free(DeclS {
                    kind: DeclKind::Defn(name, _, _),
                    ..
                }) => arena.text(name.as_str()),
                ExprKind::Apply(f, x) => {
                    let f = helper(ctx, f, !matches!(f.kind, ExprKind::Apply(..)), arena);
                    let x = helper(ctx, x, true, arena);
                    let doc = f + arena.space() + x;
                    maybe_parens(doc, parens)
                }
                ExprKind::Lambda(name, body) => {
                    let name = freshen_name(name, ctx);
                    ctx.push(name);
                    let body = helper(ctx, body, false, arena);
                    ctx.pop();
                    maybe_parens(
                        arena.text("\\")
                            + arena.text(name.as_str())
                            + arena.text(".")
                            + arena.space()
                            + body,
                        parens,
                    )
                }
                ExprKind::Let(name, ty, expr, inn) => {
                    let name = freshen_name(name, ctx);
                    ctx.push(name);
                    let inn = helper(ctx, inn, false, arena);
                    ctx.pop();
                    let ty = if let Some(ty) = ty {
                        arena.text(":") + arena.space() + ty.pretty(arena) + arena.space()
                    } else {
                        arena.nil()
                    };
                    maybe_parens(
                        arena.text("let")
                            + arena.space()
                            + arena.text(name.as_str())
                            + arena.space()
                            + ty
                            + arena.text("=")
                            + arena.space()
                            + helper(ctx, expr, false, arena)
                            + arena.space()
                            + arena.text("in")
                            + arena.space()
                            + inn,
                        parens,
                    )
                }
            }
        }
        helper(&mut vec![], self, false, arena)
    }
}

#[derive(Clone, Debug)]
pub enum ExprKind<'tcx> {
    Unit,
    Var(Index),
    Free(Decl<'tcx>),
    Apply(Expr<'tcx>, Expr<'tcx>),
    Lambda(Ident, Expr<'tcx>),
    Let(Ident, Option<Ty<'tcx>>, Expr<'tcx>, Expr<'tcx>),
}

pub type Decl<'tcx> = &'tcx DeclS<'tcx>;

#[derive(Clone, Debug)]
pub struct DeclS<'tcx> {
    pub span: Span,
    pub kind: DeclKind<'tcx>,
}

#[derive(Clone, Debug)]
pub enum DeclKind<'tcx> {
    Defn(Ident, Ty<'tcx>, Expr<'tcx>),
}

pub type Level = usize;
pub type Index = usize;

#[derive(Clone, Debug)]
pub enum Hole<'tcx> {
    Empty(Level),
    Filled(Ty<'tcx>),
}
