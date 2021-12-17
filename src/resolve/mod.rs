// pub mod ast;

// use std::collections::HashMap;

// use color_eyre::eyre::{self, bail};
// use typed_arena::Arena;

// use crate::ast::{Decl, Expr, NamedDecl, NamedExpr, NamedTy, Ty};

// impl NamedDecl {
//     pub fn resolve<'rcx>(self, rcx: &mut ResCtxt<'rcx>) -> eyre::Result<Vec<&'rcx Decl<'rcx>>> {
//         let mut decls = vec![];
//         let mut cur = self;
//         loop {
//             match cur {
//                 NamedDecl::Defn(name, ty, expr, next) => {
//                     let ty = ty.resolve(rcx)?;
//                     let expr = expr.resolve(rcx)?;
//                     let decl = rcx.decl.alloc(Decl::Defn(name.clone(), ty, expr));
//                     rcx.decls.insert(name, decl);
//                     decls.push(&*decl);
//                     if let Some(next) = next {
//                         cur = *next;
//                     } else {
//                         break;
//                     }
//                 }
//             }
//         }
//         Ok(decls)
//     }
// }

// impl NamedExpr {
//     pub fn resolve<'rcx>(self, rcx: &mut ResCtxt<'rcx>) -> eyre::Result<&'rcx Expr<'rcx>> {
//         Ok(rcx.expr.alloc(match self {
//             NamedExpr::Unit => Expr::Unit,
//             NamedExpr::Var(name) => {
//                 if let Some(pos) = rcx.expr_names.iter().rev().position(|name1| &name == name1) {
//                     Expr::Var(pos)
//                 } else if let Some(decl) = rcx.decls.get(&name) {
//                     Expr::Free(decl)
//                 } else {
//                     bail!("Resolution error: name `{}` not found", &name);
//                 }
//             }
//             NamedExpr::Apply(f, x) => {
//                 let f = f.resolve(rcx)?;
//                 let x = x.resolve(rcx)?;
//                 Expr::Apply(f, x)
//             }
//             NamedExpr::Lambda(name, body) => {
//                 rcx.expr_names.push(name);
//                 let body = body.resolve(rcx)?;
//                 rcx.expr_names.pop();
//                 Expr::Lambda(body)
//             }
//             NamedExpr::Let(name, ty, expr, next) => {
//                 let ty = ty.map(|x| x.resolve(rcx)).transpose()?;
//                 let expr = expr.resolve(rcx)?;
//                 rcx.expr_names.push(name);
//                 let next = next.resolve(rcx)?;
//                 rcx.expr_names.pop();
//                 Expr::Let(ty, expr, next)
//             }
//         }))
//     }
// }

// impl NamedTy {
//     pub fn resolve<'rcx>(self, rcx: &mut ResCtxt<'rcx>) -> eyre::Result<&'rcx Ty<'rcx>> {
//         Ok(self.resolve_(rcx, false)?.unwrap())
//     }

//     fn resolve_<'rcx>(
//         self,
//         rcx: &mut ResCtxt<'rcx>,
//         bare_forall: bool,
//     ) -> eyre::Result<Result<&'rcx Ty<'rcx>, (&'rcx Ty<'rcx>, Vec<Ty<'rcx>>)>> {
//         match self {
//             NamedTy::Unit => Ok(Ok(rcx.ty.alloc(Ty::Unit))),
//             NamedTy::Var(name) => {
//                 if let Some(idx) = rcx.ty_names.iter().rev().position(|name1| &name == name1) {
//                     Ok(Ok(rcx.ty.alloc(Ty::Var(idx))))
//                 } else {
//                     bail!("Resolution error: type variable `{}` not found", name);
//                 }
//             }
//             NamedTy::Free(_name) => {
//                 panic!("Free types are not supported yet")
//             }
//             NamedTy::Arrow(inp, out) => {
//                 let inp = inp.resolve(rcx)?;
//                 let out = out.resolve(rcx)?;
//                 Ok(Ok(rcx.ty.alloc(Ty::Arrow(inp, out))))
//             }
//             NamedTy::Forall(name, body) => {
//                 rcx.ty_names.push(name);
//                 let mut substs = vec![Ty::Var(0)];
//                 let body = match body.resolve_(rcx, true)? {
//                     Ok(body) => body,
//                     Err((body, substs1)) => {
//                         substs.extend(substs1.into_iter().map(|x| {
//                             if let Ty::Var(x) = x {
//                                 Ty::Var(x + 1)
//                             } else {
//                                 x
//                             }
//                         }));
//                         body
//                     }
//                 };
//                 rcx.ty_names.pop();
//                 Ok(if bare_forall {
//                     Err((body, substs))
//                 } else {
//                     Ok(rcx.ty.alloc(Ty::Forall(
//                         body,
//                         substs.into_iter().map(|t| &*rcx.ty.alloc(t)).collect(),
//                     )))
//                 })
//             }
//         }
//     }
// }

// #[derive(Clone)]
// pub struct ResCtxt<'rcx> {
//     pub ty: &'rcx Arena<Ty<'rcx>>,
//     pub expr: &'rcx Arena<Expr<'rcx>>,
//     pub decl: &'rcx Arena<Decl<'rcx>>,
//     pub decls: HashMap<String, &'rcx Decl<'rcx>>,
//     pub ty_names: Vec<String>,
//     pub expr_names: Vec<String>,
// }

// trait SubstExt<'rcx> {
//     fn lift(self, rcx: &mut ResCtxt<'rcx>, n: usize) -> Self;
// }

// impl<'rcx> SubstExt<'rcx> for Vec<&'rcx Ty<'rcx>> {
//     fn lift(self, rcx: &mut ResCtxt<'rcx>, n: usize) -> Self {
//         self.into_iter()
//             .map(|x| {
//                 if let Ty::Var(x) = x {
//                     rcx.ty.alloc(Ty::Var(x + n))
//                 } else {
//                     x
//                 }
//             })
//             .collect()
//     }
// }
