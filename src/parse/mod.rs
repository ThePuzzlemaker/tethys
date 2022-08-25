use std::{fmt, iter};

use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use chumsky::{prelude::*, Stream};
use id_arena::Id;
use logos::{Lexer, Logos};

use calypso_base::{
    span,
    symbol::{special::EMPTY, Ident, Symbol},
};

use crate::ast::{Expr, ExprKind, Item, ItemKind, Ty, TyKind};

use crate::ctxt::TyCtxt;

pub type SyntaxError = Simple<Token, Span>;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, derive_more::Deref)]
#[repr(transparent)]
pub struct Span(pub span::Span);

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Span({}..{})", self.0.lo(), self.0.hi())
    }
}

impl From<span::Span> for Span {
    fn from(sp: span::Span) -> Self {
        Self(sp)
    }
}

impl chumsky::Span for Span {
    type Context = ();

    type Offset = u32;

    fn new(_context: (), range: std::ops::Range<Self::Offset>) -> Self {
        Self(span::Span::new(range.start, range.end))
    }

    fn context(&self) -> Self::Context {}

    fn start(&self) -> Self::Offset {
        self.0.lo()
    }

    fn end(&self) -> Self::Offset {
        self.0.hi()
    }
}

impl ariadne::Span for Span {
    type SourceId = ();

    fn source(&self) -> &Self::SourceId {
        &()
    }

    fn start(&self) -> usize {
        self.0.lo() as usize
    }

    fn end(&self) -> usize {
        self.0.hi() as usize
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Logos)]
pub enum Token {
    #[token("def")]
    Def,
    #[token("forall")]
    Forall,
    #[token("let")]
    Let,
    #[token("in")]
    In,

    #[token("\\")]
    Backslash,
    #[token(".")]
    Dot,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token(":")]
    Colon,
    #[token("=")]
    Eq,
    #[token("->")]
    Arrow,

    #[regex("_[A-Za-z0-9_]+|[A-Za-z][A-Za-z0-9_]*", intern)]
    Ident(Symbol),
    #[regex("'_[A-Za-z0-9_]+|'[A-Za-z][A-Za-z0-9_]*", intern)]
    TyVar(Symbol),

    #[regex("[ \t\r\n]+", logos::skip)]
    #[regex("#(.*)\n?", logos::skip)]
    #[error]
    Error,
}

fn intern(lex: &mut Lexer<Token>) -> Symbol {
    Symbol::intern(lex.slice())
}

impl Token {
    pub fn description(&self) -> &'static str {
        match self {
            Token::Def => "`def`",
            Token::Forall => "`forall`",
            Token::Let => "`let`",
            Token::In => "`in`",
            Token::Backslash => "`\\`",
            Token::Dot => "`.`",
            Token::LParen => "`(`",
            Token::RParen => "`)`",
            Token::Colon => "`:`",
            Token::Eq => "`=`",
            Token::Arrow => "`->`",
            Token::Ident(_) => "ident",
            Token::TyVar(_) => "type variable",
            Token::Error => "invalid token",
        }
    }
}

pub fn parser(
    tcx: &'_ TyCtxt,
) -> impl Parser<Token, Vec<Id<Item>>, Error = Simple<Token, Span>> + Clone + '_ {
    let ident = filter_map(|span: Span, tok| {
        if let Token::Ident(s) = tok {
            Ok(Ident {
                symbol: s,
                span: span.0,
            })
        } else {
            Err(Simple::expected_input_found(
                span,
                iter::once(Some(Token::Ident(*EMPTY))),
                Some(tok),
            ))
        }
    });

    let tyvar = filter_map(|span: Span, tok| {
        if let Token::TyVar(s) = tok {
            Ok(Ident {
                symbol: s,
                span: span.0,
            })
        } else {
            Err(Simple::expected_input_found(
                span,
                iter::once(Some(Token::TyVar(*EMPTY))),
                Some(tok),
            ))
        }
    });

    let ty = recursive(|ty| {
        let primary = ident
            .map_with_span(|ident, span| Ty::new(tcx, TyKind::Name(ident), span))
            .or(just([Token::LParen, Token::RParen])
                .map_with_span(|_, span| Ty::new(tcx, TyKind::Unit, span)))
            .or(ty
                .clone()
                .delimited_by(just(Token::LParen), just(Token::RParen)))
            .or(tyvar.map_with_span(|ident, span| Ty::new(tcx, TyKind::Name(ident), span)));

        let arrow = primary
            .clone()
            .then(just(Token::Arrow).ignore_then(ty).repeated())
            .foldl(|lhs, rhs| {
                let sp = tcx
                    .arenas
                    .ast
                    .ty(lhs)
                    .span
                    .with_hi(tcx.arenas.ast.ty(rhs).span.hi());
                Ty::new(tcx, TyKind::Arrow(lhs, rhs), sp.into())
            });

        let forall = just(Token::Forall)
            .map_with_span(|_, sp| sp)
            .then(tyvar.repeated())
            .then_ignore(just(Token::Dot))
            .then(arrow.clone())
            .map(|((sp, vars), ty)| (vars, (sp, ty)))
            .foldr(|var, (sp, ty)| {
                let sp = sp.with_hi(tcx.arenas.ast.ty(ty).span.hi()).into();
                (sp, Ty::new(tcx, TyKind::Forall(var, ty), sp))
            })
            .map(|(_, ty)| ty);

        forall.or(arrow)
    });

    let expr = recursive(|expr| {
        let primary = ident
            .map_with_span(|ident, span| Expr::new(tcx, ExprKind::Name(ident), span))
            .or(just([Token::LParen, Token::RParen])
                .map_with_span(|_, span| Expr::new(tcx, ExprKind::Unit, span)))
            .or(expr
                .clone()
                .delimited_by(just(Token::LParen), just(Token::RParen)));

        let appl = primary
            .clone()
            .then(primary.repeated())
            .map(|(lhs, rhs)| (rhs.into_iter().rev(), lhs))
            .foldr(|rhs, lhs| {
                let sp = tcx
                    .arenas
                    .ast
                    .expr(lhs)
                    .span
                    .with_hi(tcx.arenas.ast.expr(rhs).span.hi());
                Expr::new(tcx, ExprKind::Apply(lhs, rhs), sp.into())
            });

        let lambda = just(Token::Backslash)
            .map_with_span(|_, span| span)
            .then(ident.repeated())
            .then_ignore(just(Token::Dot))
            .then(expr.clone())
            .map(|((sp, vars), expr)| (vars, (sp, expr)))
            .foldr(|var, (sp, expr)| {
                let sp = sp.with_hi(tcx.arenas.ast.expr(expr).span.hi()).into();
                (sp, Expr::new(tcx, ExprKind::Lambda(var, expr), sp))
            })
            .map(|(_, expr)| expr)
            .or(appl.clone());

        just(Token::Let)
            .map_with_span(|_, span| span)
            .then(ident)
            .then(just(Token::Colon).ignore_then(ty.clone()).or_not())
            .then_ignore(just(Token::Eq))
            .then(expr.clone())
            .then_ignore(just(Token::In))
            .then(expr)
            .map(|((((sp, ident), ty), expr), inn)| {
                let sp = sp.with_hi(tcx.arenas.ast.expr(inn).span.hi()).into();
                Expr::new(tcx, ExprKind::Let(ident, ty, expr, inn), sp)
            })
            .or(lambda)
    });

    let item = just(Token::Def)
        .map_with_span(|_, span| span)
        .then(ident)
        .then_ignore(just(Token::Colon))
        .then(ty)
        .then_ignore(just(Token::Eq))
        .then(expr)
        .repeated()
        .map(|vec| {
            vec.into_iter()
                .map(|(((sp, name), ty), expr)| {
                    let sp = sp.with_hi(tcx.arenas.ast.expr(expr).span.hi()).into();
                    Item::new(tcx, name, ItemKind::Value(ty, expr), sp)
                })
                .collect::<Vec<_>>()
        });

    item.then_ignore(end())
}

// TODO(@ThePuzzlemaker: diag): actually use DRCX for this
pub fn run(src: &str, tcx: &TyCtxt) -> Vec<Id<Item>> {
    let lex = Token::lexer(src).spanned().map(|(x, sp)| {
        (
            x,
            Span((sp.start.try_into().unwrap()..sp.end.try_into().unwrap()).into()),
        )
    });
    let srclen = src.len().try_into().unwrap();
    let stream = Stream::from_iter(Span(span::Span::new(srclen, srclen + 1)), lex);
    let (decls, parse_errs) = parser(tcx).parse_recovery(stream);

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
    decls.unwrap_or_default()
}
