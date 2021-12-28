pub mod ast;

use std::collections::HashMap;

use calypso_base::symbol::{Ident, Symbol};
use color_eyre::eyre::{self, bail};
use typed_arena::Arena;

use crate::parse::ast as parse;

impl parse::Decl {
    pub fn resolve<'rcx>(self, rcx: &mut ResCtxt<'rcx>) -> eyre::Result<Vec<ast::Decl<'rcx>>> {
        let mut decls = vec![];
        let mut cur = self;
        loop {
            match cur.kind {
                parse::DeclKind::Defn(name, ty, expr, next) => {
                    let ty = ty.resolve(rcx)?;
                    let expr = expr.resolve(rcx)?;
                    let decl = rcx.decl.alloc(ast::DeclS {
                        span: cur.span,
                        kind: ast::DeclKind::Defn(name, ty, expr),
                    });
                    rcx.decls.insert(*name, decl);
                    decls.push(&*decl);
                    if let Some(next) = next {
                        cur = *next;
                    } else {
                        break;
                    }
                }
            }
        }
        Ok(decls)
    }
}

impl parse::Expr {
    pub fn resolve<'rcx>(self, rcx: &mut ResCtxt<'rcx>) -> eyre::Result<ast::Expr<'rcx>> {
        Ok(rcx.expr.alloc(ast::ExprS {
            span: self.span,
            kind: match self.kind {
                parse::ExprKind::Unit => ast::ExprKind::Unit,
                parse::ExprKind::Var(name) => {
                    if let Some(pos) = rcx
                        .expr_names
                        .iter()
                        .rev()
                        .position(|name1| name == name1.symbol)
                    {
                        ast::ExprKind::Var(pos)
                    } else if let Some(decl) = rcx.decls.get(&name) {
                        ast::ExprKind::Free(decl)
                    } else {
                        bail!("Resolution error: name `{}` not found", &name);
                    }
                }
                parse::ExprKind::Apply(f, x) => {
                    let f = f.resolve(rcx)?;
                    let x = x.resolve(rcx)?;
                    ast::ExprKind::Apply(f, x)
                }
                parse::ExprKind::Lambda(name, body) => {
                    rcx.expr_names.push(name);
                    let body = body.resolve(rcx)?;
                    rcx.expr_names.pop();
                    ast::ExprKind::Lambda(name, body)
                }
                parse::ExprKind::Let(name, ty, expr, next) => {
                    let ty = ty.map(|x| x.resolve(rcx)).transpose()?;
                    let expr = expr.resolve(rcx)?;
                    rcx.expr_names.push(name);
                    let next = next.resolve(rcx)?;
                    rcx.expr_names.pop();
                    ast::ExprKind::Let(name, ty, expr, next)
                }
            },
        }))
    }
}

impl parse::Ty {
    pub fn resolve<'rcx>(self, rcx: &mut ResCtxt<'rcx>) -> eyre::Result<ast::Ty<'rcx>> {
        Ok(rcx.ty.alloc(ast::TyS {
            span: self.span,
            kind: match self.kind {
                parse::TyKind::Unit => ast::TyKind::Unit,
                parse::TyKind::Var(name) => {
                    if let Some(idx) = rcx
                        .ty_names
                        .iter()
                        .rev()
                        .position(|name1| name == name1.symbol)
                    {
                        ast::TyKind::Var(idx)
                    } else {
                        bail!("Resolution error: type variable `{}` not found", name);
                    }
                }
                parse::TyKind::Free(_name) => {
                    panic!("Free types are not supported yet")
                }
                parse::TyKind::Arrow(inp, out) => {
                    let inp = inp.resolve(rcx)?;
                    let out = out.resolve(rcx)?;
                    ast::TyKind::Arrow(inp, out)
                }
                parse::TyKind::Forall(name, body) => {
                    rcx.ty_names.push(name);
                    let body = body.resolve(rcx)?;
                    rcx.ty_names.pop();
                    ast::TyKind::Forall(name, body)
                }
            },
        }))
    }
}

#[derive(Clone)]
pub struct ResCtxt<'rcx> {
    pub ty: &'rcx Arena<ast::TyS<'rcx>>,
    pub expr: &'rcx Arena<ast::ExprS<'rcx>>,
    pub decl: &'rcx Arena<ast::DeclS<'rcx>>,
    pub decls: HashMap<Symbol, ast::Decl<'rcx>>,
    pub ty_names: Vec<Ident>,
    pub expr_names: Vec<Ident>,
}
