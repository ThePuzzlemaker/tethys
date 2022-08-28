use std::{fmt, rc::Rc};

use ariadne::Source;
use ctxt::GlobalCtxt;
use error::TysResult;
use typeck::facade::{Hole, HoleRef, SubstableForall, Ty, TyKind};

use crate::typeck::TypeckCtxt;

pub mod ast;
pub mod ctxt;
pub mod diag;
pub mod error;
pub mod infer;
mod intern;
pub mod parse;
pub mod resolve;
mod typeck;

pub fn run(src: &str, gcx: &GlobalCtxt, suppress_output: bool) -> TysResult<()> {
    let items = parse::run(src, gcx);

    let _rd = resolve::resolve_code_unit(gcx, &items)?;
    // let cu = lowering::lower_code_unit(gcx, decls)?;

    if !suppress_output {
        let drcx = gcx.drcx.borrow();
        for err in drcx.errors() {
            err.eprint(Source::from(&src))?;
        }

        if let Some(fatal) = drcx.fatal() {
            fatal.eprint(Source::from(&src))?;
        }

        println!("{:#?}", items);
        println!("{:#?}", gcx.arenas.ast.res_data.borrow().to_hash_map());
        println!("\n{:#?}", gcx);

        let item = gcx.arenas.ast.item(*items.first().unwrap());
        let mut tyck = TypeckCtxt::new();
        match item.kind {
            ast::ItemKind::Value(ty, expr) => {
                println!(
                    "inferred: {:#?}",
                    TyPp(gcx, typeck::infer(&mut tyck, gcx, expr))
                );
                let ty = typeck::facade::ast_ty_to_facade(gcx, &mut Vec::new(), ty);
                println!("expected: {:#?}", TyPp(gcx, ty));
                typeck::check(&mut tyck, gcx, expr, ty);
            }
        }
        println!("\n{:#?}", gcx);
        println!("\n{:#?}", tyck);
    }

    Ok(())

    // let tya = Arena::new();
    // let expra = Arena::new();
    // let decla = Arena::new();
    // let mut rcx = ResCtxt {
    //     ty: &tya,
    //     expr: &expra,
    //     decl: &decla,
    //     decls: HashMap::new(),
    //     expr_names: vec![],
    //     ty_names: vec![],
    // };
    // let ast = *ast.unwrap().resolve(&mut rcx)?.get(1).unwrap();
    // let ppa = pretty::Arena::new();
    // match ast.kind {
    //     DeclKind::Defn(_, ty, expr) => {
    //         println!("{}", ty.pretty(&ppa).pretty(80));
    //         println!("{}", expr.pretty(&ppa).pretty(80));
    //     }
    // }
}

struct HolePp<'a>(&'a GlobalCtxt, HoleRef);
impl<'a> fmt::Debug for HolePp<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self.1 .0.borrow() {
            Hole::Empty(lvl) => f.debug_tuple("Empty").field(&lvl).finish(),
            Hole::Filled(ty) => f.debug_tuple("Filled").field(&TyPp(self.0, ty)).finish(),
        }
    }
}

struct SubstPp<'a>(&'a GlobalCtxt, SubstableForall);
impl<'a> fmt::Debug for SubstPp<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ty = typeck::facade::ast_ty_to_facade(self.0, &mut Vec::new(), self.1.ty);
        f.debug_struct("SubstableForall")
            .field(
                "env",
                &self
                    .1
                    .env
                    .iter()
                    .map(|(sym, ty)| (*sym, TyPp(self.0, *ty)))
                    .collect::<Vec<_>>(),
            )
            .field("ty", &TyPp(self.0, ty))
            .finish()
    }
}

struct TyPp<'a>(&'a GlobalCtxt, Ty);
impl<'a> fmt::Debug for TyPp<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.1.kind(self.0) {
            TyKind::Unit => f.debug_tuple("Unit").finish(),
            TyKind::Bound(idx, symbol) => {
                f.debug_tuple("Bound").field(&idx).field(&symbol).finish()
            }
            TyKind::Rigid(lvl) => f.debug_tuple("Rigid").field(&lvl).finish(),
            TyKind::Hole(h) => f
                .debug_tuple("Hole")
                .field(&Rc::as_ptr(&h.0))
                .field(&HolePp(self.0, h))
                .finish(),
            TyKind::Free(name) => f.debug_tuple("Free").field(&name).finish(),
            TyKind::Arrow(a, b) => f
                .debug_tuple("Arrow")
                .field(&TyPp(self.0, a))
                .field(&TyPp(self.0, b))
                .finish(),
            TyKind::Forall(n, s) => f
                .debug_tuple("Forall")
                .field(&n)
                .field(&SubstPp(self.0, s))
                .finish(),
            TyKind::Err => f.debug_tuple("Err").finish(),
        }
    }
}

// fn print_decl(decl: Decl, n: &mut usize, r: ReportBuilder<Span>) -> ReportBuilder<Span> {
//     *n += 1;
//     let span = decl.span;
//     let r = r
//         .with_label(Label::new(span.shrink_to_lo().into()).with_message(format!(
//             "decl {} ({}) start",
//             n,
//             decl.kind.description()
//         )))
//         .with_label(Label::new(span.shrink_to_hi().into()).with_message(format!(
//             "decl {} ({}) end",
//             n,
//             decl.kind.description()
//         )));
//     match decl.kind {
//         DeclKind::Defn(name, ty, expr, next) => {
//             let r = print_ident(name, n, r);
//             let r = print_ty(*ty, n, r);
//             let r = print_expr(*expr, n, r);
//             if let Some(next) = next {
//                 print_decl(*next, n, r)
//             } else {
//                 r
//             }
//         }
//     }
// }
// fn print_ty(ty: Ty, n: &mut usize, r: ReportBuilder<Span>) -> ReportBuilder<Span> {
//     *n += 1;
//     let span = ty.span;
//     let r = r
//         .with_label(Label::new(span.shrink_to_lo().into()).with_message(format!(
//             "ty {} ({}) start",
//             n,
//             ty.kind.description()
//         )))
//         .with_label(Label::new(span.shrink_to_hi().into()).with_message(format!(
//             "ty {} ({}) end",
//             n,
//             ty.kind.description()
//         )));
//     match ty.kind {
//         TyKind::Unit | TyKind::Var(_) | TyKind::Free(_) => r,
//         TyKind::Arrow(inp, out) => {
//             let r = print_ty(*inp, n, r);
//             print_ty(*out, n, r)
//         }
//         TyKind::Forall(name, body) => {
//             let r = print_ident(name, n, r);
//             print_ty(*body, n, r)
//         }
//     }
// }
// fn print_expr(expr: Expr, n: &mut usize, r: ReportBuilder<Span>) -> ReportBuilder<Span> {
//     *n += 1;
//     let span = expr.span;
//     let r = r
//         .with_label(Label::new(span.shrink_to_lo().into()).with_message(format!(
//             "expr {} ({}) start",
//             n,
//             expr.kind.description()
//         )))
//         .with_label(Label::new(span.shrink_to_hi().into()).with_message(format!(
//             "expr {} ({}) end",
//             n,
//             expr.kind.description()
//         )));
//     match expr.kind {
//         ExprKind::Unit | ExprKind::Var(_) => r,
//         ExprKind::Apply(f, x) => {
//             let r = print_expr(*f, n, r);
//             print_expr(*x, n, r)
//         }
//         ExprKind::Lambda(name, body) => {
//             let r = print_ident(name, n, r);
//             print_expr(*body, n, r)
//         }
//         ExprKind::Let(name, ty, val, inn) => {
//             let r = print_ident(name, n, r);
//             let r = if let Some(ty) = ty {
//                 print_ty(*ty, n, r)
//             } else {
//                 r
//             };
//             let r = print_expr(*val, n, r);
//             print_expr(*inn, n, r)
//         }
//     }
// }
// fn print_ident(ident: Ident, n: &mut usize, r: ReportBuilder<Span>) -> ReportBuilder<Span> {
//     *n += 1;
//     let span = ident.span;
//     r.with_label(
//         Label::new(span.shrink_to_lo().into()).with_message(format!("ident {} start", n)),
//     )
//     .with_label(Label::new(span.shrink_to_hi().into()).with_message(format!("ident {} end", n)))
// }

// let report = Report::build(ReportKind::Advice, (), 0).with_message("");
// let mut i = 1;
// let report = print_decl(ast.unwrap(), &mut i, report);
// report
//     .with_config(
//         Config::default()
//             .with_label_attach(ariadne::LabelAttach::Start)
//             .with_compact(true),
//     )
//     .finish()
//     .print(Source::from(src))
//     .unwrap();
