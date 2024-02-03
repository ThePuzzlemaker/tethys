use std::{borrow::Cow, fmt, iter};

use ariadne::{Color, Fmt, Label, Report, ReportBuilder, ReportKind, Source};
use chumsky::{
    error::{Error, RichReason},
    extra::Full,
    input::{BoxedStream, Stream},
    input::{Input, MapExtra, SpannedInput},
    pratt::{infix, left, prefix, right},
    prelude::*,
    util::MaybeRef,
};
use id_arena::Id;
use logos::{Lexer, Logos};

use calypso_base::{
    span,
    symbol::{special::EMPTY, Ident, Symbol},
};

use crate::ast::{BinOpKind, Expr, ExprKind, Item, ItemKind, Recursive, Ty, TyKind};

use crate::ctxt::GlobalCtxt;

pub type SyntaxError<'src> = Rich<'src, Token, Span>;
pub type TysInput<'src> = SpannedInput<Token, Span, BoxedStream<'src, (Token, Span)>>;
pub type Extra<'src> = Full<SyntaxError<'src>, &'src GlobalCtxt, ()>;

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

impl chumsky::span::Span for Span {
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
    #[regex("(forall)|∀")]
    Forall,
    #[token("let")]
    Let,
    #[token("in")]
    In,
    #[token("type")]
    Type,
    #[token("enum")]
    Enum,
    #[token("true")]
    True,
    #[token("false")]
    False,
    #[token("if")]
    If,
    #[token("then")]
    Then,
    #[token("else")]
    Else,
    #[token("rec")]
    Rec,

    #[regex("\\\\|λ")]
    Lambda,
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
    #[token("|")]
    Pipe,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token(",")]
    Comma,

    #[token("**")]
    StarStar,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("%")]
    Percent,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("<<")]
    LtLt,
    #[token(">>")]
    GtGt,
    #[token("&")]
    And,
    #[token("^")]
    Caret,
    #[token("==")]
    EqEq,
    #[token("!=")]
    BangEq,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,
    #[token("<=")]
    LtEq,
    #[token(">=")]
    GtEq,
    #[token("&&")]
    AndAnd,
    #[token("||")]
    PipePipe,
    #[token("!")]
    Bang,

    #[regex("[0-9]+", |lex| parse_number(lex, 10))]
    Number(i64),
    #[regex("0b[01]+", |lex| parse_number(lex, 2))]
    #[regex("0x[0-9A-Fa-f]+", |lex| parse_number(lex, 16))]
    #[regex("0d[0-9]+", |lex| parse_number(lex, 10))]
    #[regex("0o[0-7]+", |lex| parse_number(lex, 8))]
    RadixNumber(i64),

    #[regex("_|_[A-Za-z0-9_]+|[A-Za-z][A-Za-z0-9_]*", intern)]
    Ident(Symbol),
    #[regex("'_|'_[A-Za-z0-9_]+|'[A-Za-z][A-Za-z0-9_]*", intern)]
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

fn binop(lhs: Id<Expr>, op: Token, rhs: Id<Expr>, span: Span, gcx: &GlobalCtxt) -> Id<Expr> {
    Expr::new(
        gcx,
        ExprKind::BinaryOp {
            left: lhs,
            kind: match op {
                Token::StarStar => BinOpKind::Power,
                Token::Star => BinOpKind::Multiply,
                Token::Slash => BinOpKind::Divide,
                Token::Percent => BinOpKind::Modulo,
                Token::Plus => BinOpKind::Add,
                Token::Minus => BinOpKind::Subtract,
                Token::LtLt => BinOpKind::BitShiftLeft,
                Token::GtGt => BinOpKind::BitShiftRight,
                Token::And => BinOpKind::BitAnd,
                Token::Caret => BinOpKind::BitXor,
                Token::Pipe => BinOpKind::BitOr,
                Token::EqEq => BinOpKind::Equal,
                Token::BangEq => BinOpKind::NotEqual,
                Token::Lt => BinOpKind::LessThan,
                Token::Gt => BinOpKind::GreaterThan,
                Token::LtEq => BinOpKind::LessEqual,
                Token::GtEq => BinOpKind::GreaterEqual,
                Token::AndAnd => BinOpKind::LogicalAnd,
                Token::PipePipe => BinOpKind::LogicalOr,
                _ => unreachable!(),
            },
            right: rhs,
        },
        span,
    )
}

impl Token {
    pub fn description(&self) -> &'static str {
        match self {
            Token::Def => "`def`",
            Token::Forall => "`forall`",
            Token::Let => "`let`",
            Token::In => "`in`",
            Token::Type => "`type`",
            Token::Enum => "`enum`",
            Token::True => "`true`",
            Token::False => "`false`",
            Token::If => "`if`",
            Token::Then => "`then`",
            Token::Else => "`else`",
            Token::Rec => "`rec`",
            Token::Lambda => "`\\` or `λ`",
            Token::Dot => "`.`",
            Token::LParen => "`(`",
            Token::RParen => "`)`",
            Token::LBracket => "`[`",
            Token::RBracket => "`]`",
            Token::Comma => "`,`",
            Token::Colon => "`:`",
            Token::Eq => "`=`",
            Token::Arrow => "`->`",
            Token::Pipe => "`|`",
            Token::StarStar => "`**`",
            Token::Star => "`*`",
            Token::Slash => "`/`",
            Token::Percent => "`%`",
            Token::Minus => "`-`",
            Token::LtLt => "`<<`",
            Token::GtGt => "`>>`",
            Token::And => "`&`",
            Token::Caret => "`^`",
            Token::EqEq => "`==`",
            Token::BangEq => "`!=`",
            Token::Lt => "`<`",
            Token::Gt => "`>`",
            Token::LtEq => "`<=`",
            Token::GtEq => "`>=`",
            Token::AndAnd => "`&&`",
            Token::PipePipe => "`||`",
            Token::Plus => "`+`",
            Token::Bang => "`!`",
            Token::Ident(_) => "ident",
            Token::TyVar(_) => "type variable",
            Token::Number(_) | Token::RadixNumber(_) => "number",
            Token::Error => "invalid token",
        }
    }
}

#[allow(clippy::explicit_auto_deref)]
pub fn parser<'src>() -> impl Parser<'src, TysInput<'src>, Vec<Id<Item>>, Extra<'src>> + Clone + 'src
{
    let ident = any().try_map(|tok, span: Span| {
        if let Token::Ident(s) = tok {
            Ok(Ident {
                symbol: s,
                span: span.0,
            })
        } else {
            Err(<Rich<'_, _, _> as Error<'_, TysInput<'_>>>::expected_found(
                iter::once(Some(MaybeRef::Val(Token::Ident(*EMPTY)))),
                Some(MaybeRef::Val(tok)),
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
            Err(<Rich<'_, _, _> as Error<'_, TysInput<'_>>>::expected_found(
                iter::once(Some(MaybeRef::Val(Token::TyVar(*EMPTY)))),
                Some(MaybeRef::Val(tok)),
                span,
            ))
        }
    });

    let number = any().try_map(|tok: Token, span: Span| {
        if let Token::Number(n) = tok {
            Ok(n)
        } else if let Token::RadixNumber(n) = tok {
            Ok(n)
        } else {
            Err(<Rich<'_, _, _> as Error<'_, TysInput<'_>>>::expected_found(
                iter::once(Some(MaybeRef::Val(Token::TyVar(*EMPTY)))),
                Some(MaybeRef::Val(tok)),
                span,
            ))
        }
    });

    let number_no_radix = any().try_map(|tok: Token, span: Span| {
        if let Token::Number(n) = tok {
            Ok(n)
        } else {
            Err(<Rich<'_, _, _> as Error<'_, TysInput<'_>>>::expected_found(
                iter::once(Some(MaybeRef::Val(Token::TyVar(*EMPTY)))),
                Some(MaybeRef::Val(tok)),
                span,
            ))
        }
    });

    let ty = recursive(|ty| {
        let primary = choice((
            just(Token::LParen)
                .map_with(|_, extra| extra.span())
                .then(ty.clone())
                .then(just(Token::RParen).map_with(|_, extra| extra.span()))
                .map_with(
                    |((lo, x), hi): ((Span, _), Span),
                     extra: &mut MapExtra<'_, '_, TysInput<'_>, Extra<'_>>| {
                        let gcx = *extra.state();
                        Ty::new(gcx, gcx.arenas.ast.ty(x).kind, Span(lo.with_hi(hi.hi())))
                    },
                ),
            just(Token::LParen)
                .ignore_then(
                    ty.clone()
                        .separated_by(just(Token::Comma))
                        .allow_trailing()
                        .at_least(1)
                        .collect::<Vec<_>>(),
                )
                .then_ignore(just(Token::RParen))
                .map_with(|x, extra: &mut MapExtra<'_, '_, TysInput<'_>, Extra<'_>>| {
                    let span = extra.span();
                    Ty::new(*extra.state(), TyKind::Tuple(x.into()), span)
                }),
            ident
                .then_ignore(just(Token::LBracket))
                .then(
                    ty.clone()
                        .separated_by(just(Token::Comma))
                        .collect::<Vec<_>>()
                        .map(im::Vector::from),
                )
                .then_ignore(just(Token::RBracket))
                .map_with(
                    |(ident, tys), extra: &mut MapExtra<'_, '_, TysInput<'_>, Extra<'_>>| {
                        let span = extra.span();
                        Ty::new(*extra.state(), TyKind::Data(ident, tys), span)
                    },
                ),
            ident.map_with(
                |ident, extra: &mut MapExtra<'_, '_, TysInput<'_>, Extra<'_>>| {
                    let span = extra.span();
                    Ty::new(*extra.state(), TyKind::Name(ident), span)
                },
            ),
            just([Token::LParen, Token::RParen]).map_with(
                |_, extra: &mut MapExtra<'_, '_, TysInput<'_>, Extra<'_>>| {
                    let span = extra.span();
                    Ty::new(*extra.state(), TyKind::Unit, span)
                },
            ),
            tyvar.map_with(
                |ident, extra: &mut MapExtra<'_, '_, TysInput<'_>, Extra<'_>>| {
                    let span = extra.span();
                    Ty::new(*extra.state(), TyKind::Name(ident), span)
                },
            ),
        ))
        .boxed();

        let arrow = primary
            .clone()
            .foldl_with(
                just(Token::Arrow).ignore_then(ty.clone()).repeated(),
                |lhs, rhs, extra| {
                    let gcx: &mut &GlobalCtxt = extra.state();
                    let sp = gcx
                        .arenas
                        .ast
                        .ty(lhs)
                        .span
                        .with_hi(gcx.arenas.ast.ty(rhs).span.hi());
                    Ty::new(gcx, TyKind::Arrow(lhs, rhs), sp.into())
                },
            )
            .boxed();

        let forall = just(Token::Forall)
            .map_with(|_, extra| extra.span())
            .then(tyvar.repeated().collect::<Vec<_>>())
            .then_ignore(just(Token::Dot))
            .then(ty.clone())
            .map_with(|((sp, vars), ty), extra| {
                let gcx: &mut &GlobalCtxt = extra.state();
                vars.into_iter()
                    .rfold((sp, ty), |(sp, ty): (Span, _), var| {
                        let sp = sp.with_hi(gcx.arenas.ast.ty(ty).span.hi()).into();
                        (sp, Ty::new(gcx, TyKind::Forall(var, ty), sp))
                    })
                    .1
            });

        forall.or(arrow)
    });

    let expr =
        recursive(|expr| {
            // 150
            let primary = choice((
                just(Token::LParen)
                    .map_with(|_, extra| extra.span())
                    .then(expr.clone())
                    .then(just(Token::RParen).map_with(|_, extra| -> Span { extra.span() }))
                    .map_with(|((lo, x), hi): ((Span, _), _), extra| {
                        let gcx: &mut &GlobalCtxt = extra.state();
                        Expr::new(gcx, gcx.arenas.ast.expr(x).kind, Span(lo.with_hi(hi.hi())))
                    }),
                just(Token::LParen)
                    .ignore_then(
                        expr.clone()
                            .separated_by(just(Token::Comma))
                            .allow_trailing()
                            .at_least(1)
                            .collect::<Vec<_>>(),
                    )
                    .then_ignore(just(Token::RParen))
                    .map_with(|x, extra| {
                        Expr::new(*extra.state(), ExprKind::Tuple(x.into()), extra.span())
                    }),
                just(Token::True).map_with(|_, extra| {
                    Expr::new(*extra.state(), ExprKind::Boolean(true), extra.span())
                }),
                just(Token::False).map_with(|_, extra| {
                    Expr::new(*extra.state(), ExprKind::Boolean(false), extra.span())
                }),
                ident.map_with(|ident, extra| {
                    Expr::new(*extra.state(), ExprKind::Name(ident), extra.span())
                }),
                just([Token::LParen, Token::RParen])
                    .map_with(|_, extra| Expr::new(*extra.state(), ExprKind::Unit, extra.span())),
                number.map_with(|num, extra| {
                    Expr::new(*extra.state(), ExprKind::Number(num), extra.span())
                }),
            ));

            // 145
            let tuple_proj = primary.clone().foldl_with(
                just(Token::Dot).ignore_then(number_no_radix).repeated(),
                |lhs, number, extra| {
                    Expr::new(
                        *extra.state(),
                        ExprKind::TupleProj(lhs, number as u64),
                        extra.span(),
                    )
                },
            );

            // 140
            let appl = tuple_proj.clone().foldl_with(
                tuple_proj.repeated(),
                |lhs, rhs, extra: &mut MapExtra<'_, '_, TysInput<'_>, Extra<'_>>| {
                    let gcx: &GlobalCtxt = *extra.state();
                    let sp = gcx
                        .arenas
                        .ast
                        .expr(lhs)
                        .span
                        .with_hi(gcx.arenas.ast.expr(rhs).span.hi());
                    Expr::new(gcx, ExprKind::Apply(lhs, rhs), sp.into())
                },
            );

            let pratt = appl.clone().pratt((
		infix(
                right(130),
                just(Token::StarStar),
                    |lhs, op, rhs, extra: &mut MapExtra<'src, '_, TysInput<'src>, Extra<'src>>| {
			binop(lhs, op, rhs, extra.span(), *extra.state())
                    },
		),
		prefix(
                    120,
                    one_of([Token::Minus, Token::Bang]),
                    |op, rhs, extra: &mut MapExtra<'src, '_, TysInput<'src>, Extra<'src>>| {
			let span = extra.span();
			Expr::new(
                            *extra.state(),
                            match op {
				Token::Minus => ExprKind::UnaryMinus(rhs),
				Token::Bang => ExprKind::UnaryNot(rhs),
				_ => unreachable!(),
                            },
                            span,
			)
                    },
		),
		infix(
                    left(110),
                    one_of([Token::Star, Token::Slash, Token::Percent]),
                    |lhs, op, rhs, extra: &mut MapExtra<'src, '_, TysInput<'src>, Extra<'src>>| {
			binop(lhs, op, rhs, extra.span(), *extra.state())
                    },
		),
		infix(
                    left(100),
                    one_of([Token::Plus, Token::Minus]),
                    |lhs, op, rhs, extra: &mut MapExtra<'src, '_, TysInput<'src>, Extra<'src>>| {
			binop(lhs, op, rhs, extra.span(), *extra.state())
                    },
		),
		infix(
                    left(90),
                    one_of([Token::LtLt, Token::GtGt]),
                    |lhs, op, rhs, extra: &mut MapExtra<'src, '_, TysInput<'src>, Extra<'src>>| {
			binop(lhs, op, rhs, extra.span(), *extra.state())
                    },
		),
		infix(
                    left(80),
                    just(Token::And),
                    |lhs, op, rhs, extra: &mut MapExtra<'src, '_, TysInput<'src>, Extra<'src>>| {
			binop(lhs, op, rhs, extra.span(), *extra.state())
                    },
		),
		infix(
                    left(70),
                    just(Token::Caret),
                    |lhs, op, rhs, extra: &mut MapExtra<'src, '_, TysInput<'src>, Extra<'src>>| {
			binop(lhs, op, rhs, extra.span(), *extra.state())
                    },
		),
		infix(
                    left(60),
                    just(Token::Pipe),
                    |lhs, op, rhs, extra: &mut MapExtra<'src, '_, TysInput<'src>, Extra<'src>>| {
			binop(lhs, op, rhs, extra.span(), *extra.state())
                    },
		),
		infix(
                    left(50),
                    one_of([
			Token::EqEq,
			Token::BangEq,
			Token::Lt,
			Token::LtEq,
			Token::Gt,
			Token::GtEq,
                    ]),
                    |lhs, op, rhs, extra: &mut MapExtra<'src, '_, TysInput<'src>, Extra<'src>>| {
			binop(lhs, op, rhs, extra.span(), *extra.state())
                    },
		),
		infix(
                    left(40),
                    just(Token::AndAnd),
                    |lhs, op, rhs, extra: &mut MapExtra<'src, '_, TysInput<'src>, Extra<'src>>| {
			binop(lhs, op, rhs, extra.span(), *extra.state())
                    },
		),
		infix(
                    left(30),
                    just(Token::PipePipe),
                    |lhs, op, rhs, extra: &mut MapExtra<'src, '_, TysInput<'src>, Extra<'src>>| {
			binop(lhs, op, rhs, extra.span(), *extra.state())
                    },
		),
            )).boxed();

            // 20
            let lambda = just(Token::Lambda)
                .map_with(|_, extra| extra.span())
                .then(ident.repeated().collect::<Vec<_>>())
                .then_ignore(just(Token::Dot))
                .then(expr.clone())
                .map_with(
                    |((sp, vars), expr), extra: &mut MapExtra<'_, '_, TysInput<'_>, Extra<'_>>| {
                        let gcx: &mut &GlobalCtxt = extra.state();
                        vars.into_iter()
                            .rfold((sp, expr), |(sp, expr): (Span, _), var| {
                                let sp = sp.with_hi(gcx.arenas.ast.expr(expr).span.hi()).into();
                                (sp, Expr::new(gcx, ExprKind::Lambda(var, expr), sp))
                            })
                            .1
                    },
                )
                .or(pratt.clone());

            // 15
            let r#if = just(Token::If)
                .ignore_then(lambda.clone())
                .then_ignore(just(Token::Then))
                .then(expr.clone())
                .then_ignore(just(Token::Else))
                .then(expr.clone())
                .map_with(|((cond, then), else_then), extra| {
                    Expr::new(
                        *extra.state(),
                        ExprKind::If(cond, then, else_then),
                        extra.span(),
                    )
                })
                .or(lambda.clone());

            // 10
            just(Token::Let)
                .map_with(|_, extra| -> Span { extra.span() })
                .then(
                    just(Token::Rec)
                        .map_with(|_, extra| -> Span { extra.span() })
                        .or_not(),
                )
                .then(ident)
                .then(just(Token::Colon).ignore_then(ty.clone()).or_not())
                .then_ignore(just(Token::Eq))
                .then(expr.clone())
                .then_ignore(just(Token::In))
                .then(expr)
                .map_with(|(((((sp, rec), ident), ty), expr), inn), extra| {
                    let gcx: &mut &GlobalCtxt = extra.state();
                    let sp = sp.with_hi(gcx.arenas.ast.expr(inn).span.hi()).into();
                    Expr::new(
                        gcx,
                        ExprKind::Let(
                            ident,
                            rec.map(Recursive::Recursive)
                                .unwrap_or(Recursive::NotRecursive),
                            ty,
                            expr,
                            inn,
                        ),
                        sp,
                    )
                })
                .or(r#if)
        });

    let def = just(Token::Def)
        .map_with(
            |_, extra: &mut MapExtra<'_, '_, TysInput<'_>, Extra<'_>>| -> Span { extra.span() },
        )
        .then(ident)
        .then_ignore(just(Token::Colon))
        .then(ty.clone())
        .then_ignore(just(Token::Eq))
        .then(expr)
        .map_with(
            |(((sp, name), ty), expr), extra: &mut MapExtra<'_, '_, TysInput<'_>, Extra<'_>>| {
                let gcx: &mut &GlobalCtxt = extra.state();
                let sp = sp.with_hi(gcx.arenas.ast.expr(expr).span.hi()).into();
                Item::new(gcx, name, ItemKind::Value(ty, expr), sp)
            },
        );

    let ty_alias = just(Token::Type)
        .map_with(|_, extra: &mut MapExtra<'_, '_, TysInput<'_>, Extra<'_>>| extra.span())
        .then(ident)
        .then_ignore(just(Token::Eq))
        .then(ty.clone())
        .map_with(
            |((sp, name), ty): ((Span, _), _),
             extra: &mut MapExtra<'_, '_, TysInput<'_>, Extra<'_>>| {
                let gcx: &mut &GlobalCtxt = extra.state();
                let sp = sp.with_hi(gcx.arenas.ast.ty(ty).span.hi()).into();
                Item::new(gcx, name, ItemKind::TyAlias(ty), sp)
            },
        );

    let r#enum = just(Token::Enum)
        .map_with(
            |_, extra: &mut MapExtra<'_, '_, TysInput<'_>, Extra<'_>>| -> Span { extra.span() },
        )
        .then(ident)
        .then(
            just(Token::LBracket)
                .ignore_then(
                    tyvar
                        .separated_by(just(Token::Comma))
                        .collect::<Vec<_>>()
                        .map(im::Vector::from),
                )
                .then_ignore(just(Token::RBracket))
                .or_not()
                .map_with(|x, extra: &mut MapExtra<'_, '_, TysInput<'_>, Extra<'_>>| {
                    (x.unwrap_or_default(), extra.span())
                }),
        )
        .then_ignore(just(Token::Eq))
        .then(
            just(Token::Pipe).or_not().ignore_then(
                ident
                    .then(ty.clone().repeated().collect::<Vec<_>>())
                    .separated_by(just(Token::Pipe))
                    .collect::<Vec<_>>(),
            ),
        )
        .map_with(
            |(((sp, name), (generics, generics_list_span)), tys),
             extra: &mut MapExtra<'_, '_, TysInput<'_>, Extra<'_>>| {
                let gcx: &GlobalCtxt = *extra.state();
                let sp2: Span = extra.span();
                let sp = sp.with_hi(sp2.hi()).into();
                Item::new(
                    gcx,
                    name,
                    ItemKind::Enum(
                        generics,
                        tys.into_iter().map(|(x, y)| (x, y.into())).collect(),
                        generics_list_span,
                    ),
                    sp,
                )
            },
        );

    let item = choice((def, ty_alias, r#enum))
        .repeated()
        .collect::<Vec<_>>();

    item.then_ignore(end())
}

// TODO(@ThePuzzlemaker: diag): actually use DRCX for this
pub fn run<'a>(src: &'a str, mut gcx: &'a GlobalCtxt) -> Vec<Id<Item>> {
    let lex = Token::lexer(src).spanned().map(|(x, sp)| {
        // TODO: make this more efficient
        let lo = src
            .char_indices()
            .enumerate()
            .find_map(|(pos, (off, _))| if off == sp.start { Some(pos) } else { None })
            .unwrap();
        let hi = src
            .char_indices()
            .enumerate()
            .find_map(|(pos, (off, _))| if off == sp.end { Some(pos) } else { None })
            .unwrap();
        (x, Span((lo as u32..hi as u32).into()))
    });
    let srclen = src.len().try_into().unwrap();
    let stream = Stream::from_iter(lex).boxed();
    let stream = stream.spanned(Span(span::Span::new(srclen, srclen)));
    let (decls, parse_errs) = parser()
        .parse_with_state(stream, &mut gcx)
        .into_output_errors();

    parse_errs.into_iter().for_each(|e| {
        let mut report = Report::build(ReportKind::Error, (), e.span().lo() as usize);

        report = render_diagnostic(e.reason(), *e.span(), report);

        report.finish().print(Source::from(&src)).unwrap();
    });
    decls.unwrap_or_default()
}

fn render_diagnostic(
    e: &RichReason<'_, Token>,
    span: Span,
    mut report: ReportBuilder<'static, Span>,
) -> ReportBuilder<'static, Span> {
    match e {
        RichReason::Custom(msg) => report.with_message(msg).with_label(
            Label::new(span)
                .with_message(format!("{}", msg.fg(Color::Red)))
                .with_color(Color::Red),
        ),
        RichReason::ExpectedFound { expected, found } => report
            .with_message(format!(
                "{}, expected: {}",
                if let Some(found) = found {
                    Cow::from(format!("Unexpected token {}", found.description()))
                } else {
                    Cow::from("Unexpected end of input")
                },
                if expected.is_empty() {
                    Cow::from("end of input")
                } else {
                    Cow::from(
                        expected
                            .iter()
                            .map(|x| match x {
                                chumsky::error::RichPattern::Token(tok) => {
                                    Cow::from(tok.description())
                                }
                                chumsky::error::RichPattern::Label(l) => Cow::from(*l),
                                chumsky::error::RichPattern::EndOfInput => {
                                    Cow::from("end of input")
                                }
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
                report = render_diagnostic(reason, span, report);
            }
            report
        }
    }
}
