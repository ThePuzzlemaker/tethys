use std::cell::RefCell;

use ariadne::Source;
use ctxt::TyCtxt;
use error::TysResult;

use crate::{ctxt::Arenas, diag::DiagReportCtxt};

pub mod ast;
pub mod ctxt;
pub mod diag;
pub mod error;
pub mod infer;
pub mod parse;
pub mod resolve;

pub fn get_tcx<'tcx>(arenas: &'tcx Arenas<'tcx>) -> TyCtxt<'tcx> {
    TyCtxt {
        arenas,
        intern: ctxt::Interners::new(arenas),
        drcx: RefCell::new(DiagReportCtxt::new()),
    }
}

pub fn run<'tcx>(src: &str, tcx: &'tcx TyCtxt<'tcx>, suppress_output: bool) -> TysResult<()> {
    let items = parse::run(src, tcx);

    let _rd = resolve::resolve_code_unit(tcx, &items)?;
    // let cu = lowering::lower_code_unit(tcx, decls)?;

    if !suppress_output {
        let drcx = tcx.drcx.borrow();
        for err in drcx.errors() {
            err.eprint(Source::from(&src))?;
        }

        if let Some(fatal) = drcx.fatal() {
            fatal.eprint(Source::from(&src))?;
        }

        println!("{:#?}", items);
        println!("{:#?}", tcx.arenas.ast.res_data.borrow().to_hash_map());
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
