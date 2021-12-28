use std::{collections::HashMap, env, fs};

use ariadne::{Color, Config, Fmt, Label, Report, ReportBuilder, ReportKind, Source};
use calypso_base::{span, symbol::Ident};
use chumsky::{Parser, Stream};
use color_eyre::eyre;
use logos::Logos;
use parse::{parser, Token};
use typed_arena::Arena;

use crate::parse::Span;
use crate::resolve::ast::{Decl, DeclKind, Expr, ExprKind, Ty, TyKind};
use crate::resolve::ResCtxt;
// use resolve::ResCtxt;
// use typed_arena::Arena;

pub mod ctxt;
pub mod infer;
pub mod intern;
pub mod ir;
pub mod parse;
pub mod resolve;

fn main() -> eyre::Result<()> {
    tracing_subscriber::fmt::init();
    color_eyre::install()?;
    let src = fs::read_to_string(env::args().nth(1).expect("Expected file argument"))
        .expect("Failed to read file");

    let lex = Token::lexer(&src).spanned().map(|(x, sp)| {
        (
            x,
            parse::Span((sp.start.try_into().unwrap()..sp.end.try_into().unwrap()).into()),
        )
    });
    let srclen = src.len().try_into().unwrap();
    let stream = Stream::from_iter(parse::Span(span::Span::new(srclen, srclen + 1)), lex);
    let (ast, parse_errs) = parser().parse_recovery(stream);

    parse_errs
        .into_iter()
        .map(|e| e.map(|tok| tok.description().to_string()))
        .for_each(|e| {
            let report = Report::build(ReportKind::Error, (), e.span().lo() as usize);

            let report = match e.reason() {
                chumsky::error::SimpleReason::Unclosed { span, delimiter } => report
                    .with_message(format!(
                        "Unclosed delimiter {}",
                        delimiter.fg(Color::Yellow)
                    ))
                    .with_label(
                        Label::new(*span)
                            .with_message(format!(
                                "Unclosed delimiter {}",
                                delimiter.fg(Color::Yellow)
                            ))
                            .with_color(Color::Yellow),
                    )
                    .with_label(
                        Label::new(e.span())
                            .with_message(format!(
                                "Must be closed before this {}",
                                e.found()
                                    .unwrap_or(&"end of file".to_string())
                                    .fg(Color::Red)
                            ))
                            .with_color(Color::Red),
                    ),
                chumsky::error::SimpleReason::Unexpected => report
                    .with_message(format!(
                        "{}, expected {}",
                        if e.found().is_some() {
                            "Unexpected token in input"
                        } else {
                            "Unexpected end of input"
                        },
                        if e.expected().len() == 0 {
                            "end of input".to_string()
                        } else {
                            e.expected()
                                .map(|x| {
                                    x.as_ref()
                                        .map(|x| x.to_string())
                                        .unwrap_or_else(|| "end of input".to_string())
                                })
                                .collect::<Vec<_>>()
                                .join(", ")
                        }
                    ))
                    .with_label(
                        Label::new(e.span())
                            .with_message(format!(
                                "Unexpected token {}",
                                e.found()
                                    .unwrap_or(&"end of file".to_string())
                                    .fg(Color::Red)
                            ))
                            .with_color(Color::Red),
                    ),
                chumsky::error::SimpleReason::Custom(msg) => report.with_message(msg).with_label(
                    Label::new(e.span())
                        .with_message(format!("{}", msg.fg(Color::Red)))
                        .with_color(Color::Red),
                ),
            };

            report.finish().print(Source::from(&src)).unwrap();
        });
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
    // TODO: better errors

    let tya = Arena::new();
    let expra = Arena::new();
    let decla = Arena::new();
    let mut rcx = ResCtxt {
        ty: &tya,
        expr: &expra,
        decl: &decla,
        decls: HashMap::new(),
        expr_names: vec![],
        ty_names: vec![],
    };
    let ast = *ast.unwrap().resolve(&mut rcx)?.get(1).unwrap();
    let ppa = pretty::Arena::new();
    match ast.kind {
        DeclKind::Defn(_, ty, expr) => {
            println!("{}", ty.pretty(&ppa).pretty(80));
            println!("{}", expr.pretty(&ppa).pretty(80));
        }
    }

    Ok(())
}
