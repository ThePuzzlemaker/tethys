use std::{borrow::Cow, fmt, iter};

use ariadne::{Color, Fmt, Label, Report, ReportBuilder, ReportKind, Source};
use chumsky::zero_copy::{
    error::{Error, RichReason},
    extra::Full,
    input::{BoxedStream, Stream},
    input::{Input, Spanned as ChumskySpanned},
    prelude::*,
};
use id_arena::Id;
use logos::{Lexer, Logos};

use calypso_base::{
    span,
    symbol::{special::EMPTY, Ident, Symbol},
};

use crate::ast::{Expr, ExprKind, Item, ItemKind, Ty, TyKind};

use crate::ctxt::GlobalCtxt;

pub type SyntaxError<'a, 'b> = Rich<'a, TysInput<'a, 'b>>;

pub type TysInput<'a, 'b> = ChumskySpanned<Token, Span, &'a BoxedStream<'b, (Token, Span)>>;

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

impl chumsky::zero_copy::span::Span for Span {
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

    #[regex("-?[0-9]+", |lex| parse_number(lex, 10))]
    #[regex("0b[01]+", |lex| parse_number(lex, 2))]
    #[regex("0x[0-9A-Fa-f]+", |lex| parse_number(lex, 16))]
    #[regex("0d[0-9]+", |lex| parse_number(lex, 10))]
    #[regex("0o[0-7]+", |lex| parse_number(lex, 8))]
    Number(i64),

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

fn parse_number(lex: &mut Lexer<Token>, radix: u32) -> Result<i64, Token> {
    i64::from_str_radix(lex.slice(), radix).map_err(|_| Token::Error)
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
            Token::Number(_) => "number",
            Token::Error => "invalid token",
        }
    }
}

pub fn parser<'a, 'b: 'a>(
    gcx: &'a GlobalCtxt,
) -> impl Parser<'a, TysInput<'a, 'b>, Vec<Id<Item>>, Full<SyntaxError<'a, 'b>, (), ()>> + Clone + 'a
{
    let ident = any().try_map(|tok, span: Span| {
        if let Token::Ident(s) = tok {
            Ok(Ident {
                symbol: s,
                span: span.0,
            })
        } else {
            Err(Rich::expected_found(
                iter::once(Some(Token::Ident(*EMPTY))),
                Some(tok),
                span,
            ))
        }
    });

    let tyvar = any().try_map(|tok, span: Span| {
        if let Token::TyVar(s) = tok {
            Ok(Ident {
                symbol: s,
                span: span.0,
            })
        } else {
            Err(Rich::expected_found(
                iter::once(Some(Token::TyVar(*EMPTY))),
                Some(tok),
                span,
            ))
        }
    });

    let number = any().try_map(|tok: Token, span: Span| {
        if let Token::Number(n) = tok {
            Ok(n)
        } else {
            Err(Rich::expected_found(
                iter::once(Some(Token::TyVar(*EMPTY))),
                Some(tok),
                span,
            ))
        }
    });

    let ty = recursive(|ty| {
        let primary = choice((
            ident.map_with_span(|ident, span| Ty::new(gcx, TyKind::Name(ident), span)),
            just([Token::LParen, Token::RParen])
                .map_with_span(|_, span| Ty::new(gcx, TyKind::Unit, span)),
            ty.clone()
                .delimited_by(just(Token::LParen), just(Token::RParen)),
            tyvar.map_with_span(|ident, span| Ty::new(gcx, TyKind::Name(ident), span)),
        ));

        let arrow =
            primary
                .clone()
                .foldl(just(Token::Arrow).ignore_then(ty).repeated(), |lhs, rhs| {
                    let sp = gcx
                        .arenas
                        .ast
                        .ty(lhs)
                        .span
                        .with_hi(gcx.arenas.ast.ty(rhs).span.hi());
                    Ty::new(gcx, TyKind::Arrow(lhs, rhs), sp.into())
                });

        let forall = just(Token::Forall)
            .map_with_span(|_, sp: Span| sp)
            .then(tyvar.repeated().collect::<Vec<_>>())
            .then_ignore(just(Token::Dot))
            .then(arrow.clone())
            .map(|((sp, vars), ty)| {
                vars.into_iter()
                    .rfold((sp, ty), |(sp, ty), var| {
                        let sp = sp.with_hi(gcx.arenas.ast.ty(ty).span.hi()).into();
                        (sp, Ty::new(gcx, TyKind::Forall(var, ty), sp))
                    })
                    .1
            });

        forall.or(arrow)
    });

    let expr = recursive(|expr| {
        let primary = choice((
            ident.map_with_span(|ident, span| Expr::new(gcx, ExprKind::Name(ident), span)),
            just([Token::LParen, Token::RParen])
                .map_with_span(|_, span| Expr::new(gcx, ExprKind::Unit, span)),
            number.map_with_span(|num, span| Expr::new(gcx, ExprKind::Number(num), span)),
            expr.clone()
                .delimited_by(just(Token::LParen), just(Token::RParen)),
        ));

        let appl = primary.clone().foldl(primary.repeated(), |lhs, rhs| {
            let sp = gcx
                .arenas
                .ast
                .expr(lhs)
                .span
                .with_hi(gcx.arenas.ast.expr(rhs).span.hi());
            Expr::new(gcx, ExprKind::Apply(lhs, rhs), sp.into())
        });

        let lambda = just(Token::Backslash)
            .map_with_span(|_, span: Span| span)
            .then(ident.repeated().collect::<Vec<_>>())
            .then_ignore(just(Token::Dot))
            .then(expr.clone())
            .map(|((sp, vars), expr)| {
                vars.into_iter()
                    .rfold((sp, expr), |(sp, expr), var| {
                        let sp = sp.with_hi(gcx.arenas.ast.expr(expr).span.hi()).into();
                        (sp, Expr::new(gcx, ExprKind::Lambda(var, expr), sp))
                    })
                    .1
            })
            .or(appl.clone());

        just(Token::Let)
            .map_with_span(|_, span: Span| span)
            .then(ident)
            .then(just(Token::Colon).ignore_then(ty.clone()).or_not())
            .then_ignore(just(Token::Eq))
            .then(expr.clone())
            .then_ignore(just(Token::In))
            .then(expr)
            .map(|((((sp, ident), ty), expr), inn)| {
                let sp = sp.with_hi(gcx.arenas.ast.expr(inn).span.hi()).into();
                Expr::new(gcx, ExprKind::Let(ident, ty, expr, inn), sp)
            })
            .or(lambda)
    });

    let item = just(Token::Def)
        .map_with_span(|_, span: Span| span)
        .then(ident)
        .then_ignore(just(Token::Colon))
        .then(ty)
        .then_ignore(just(Token::Eq))
        .then(expr)
        .repeated()
        .collect::<Vec<_>>()
        .map(|vec| {
            vec.into_iter()
                .map(|(((sp, name), ty), expr)| {
                    let sp = sp.with_hi(gcx.arenas.ast.expr(expr).span.hi()).into();
                    Item::new(gcx, name, ItemKind::Value(ty, expr), sp)
                })
                .collect::<Vec<_>>()
        });

    item.then_ignore(end())
}

// TODO(@ThePuzzlemaker: diag): actually use DRCX for this
pub fn run<'a>(src: &'a str, gcx: &'a GlobalCtxt) -> Vec<Id<Item>> {
    let lex = Token::lexer(src).spanned().map(|(x, sp)| {
        (
            x,
            Span((sp.start.try_into().unwrap()..sp.end.try_into().unwrap()).into()),
        )
    });
    let srclen = src.len().try_into().unwrap();
    let stream = Stream::from_iter(lex).boxed();
    let stream = stream.spanned(Span(span::Span::new(srclen, srclen + 1)));
    let (decls, parse_errs) = parser(gcx).parse(stream).into_output_errors();

    parse_errs.into_iter().for_each(|e| {
        let mut report = Report::build(ReportKind::Error, (), e.span().lo() as usize);

        report = render_diagnostic(e.reason(), e.span(), report);

        report.finish().print(Source::from(&src)).unwrap();
    });
    decls.unwrap_or_default()
}

fn render_diagnostic<'a, 'b: 'a>(
    e: &RichReason<'a, TysInput<'a, 'b>>,
    span: Span,
    mut report: ReportBuilder<Span>,
) -> ReportBuilder<Span> {
    match e {
        RichReason::Custom(msg) => report.with_message(msg).with_label(
            Label::new(span)
                .with_message(format!("{}", msg.fg(Color::Red)))
                .with_color(Color::Red),
        ),
        RichReason::ExpectedFound { expected, found } => report
            .with_message(format!(
                "{}, expected one of: [{}]",
                if let Some(found) = found {
                    Cow::from(format!("Unexpected token `{}`", found.description()))
                } else {
                    Cow::from("Unexpected end of input")
                },
                if expected.is_empty() {
                    Cow::from("end of input")
                } else {
                    Cow::from(
                        expected
                            .into_iter()
                            .map(|x| {
                                x.as_ref()
                                    .map(|x| x.description().to_string())
                                    .unwrap_or_else(|| "end of input".to_string())
                            })
                            .collect::<Vec<_>>()
                            .join(", "),
                    )
                },
            ))
            .with_label(
                Label::new(span)
                    .with_message("didn't expect this token".fg(Color::Red))
                    .with_color(Color::Red),
            ),
        RichReason::Many(vec) => {
            for reason in vec {
                report = render_diagnostic(&reason, span, report);
            }
            report
        }
    }
}
