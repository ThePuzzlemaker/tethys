pub mod ast;
use std::{
    fmt::{self, Display},
    iter,
};

use chumsky::prelude::*;
use logos::{Lexer, Logos};

use calypso_base::{
    span,
    symbol::{special::EMPTY, Ident, Symbol},
};

use ast::{Decl, DeclKind, Expr, ExprKind, Ty, TyKind};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, derive_more::Deref)]
#[repr(transparent)]
pub struct Span(pub span::Span);

impl From<span::Span> for Span {
    fn from(sp: span::Span) -> Self {
        Self(sp)
    }
}

impl chumsky::Span for Span {
    type Context = ();

    type Offset = u32;

    fn new(context: (), range: std::ops::Range<Self::Offset>) -> Self {
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

    #[regex("_[A-Za-z0-9_]+|[A-Za-z][A-Za-z0-9_]*", ident)]
    Ident(Symbol),
    #[regex("'_[A-Za-z0-9_]+|'[A-Za-z][A-Za-z0-9_]*", ident)]
    TyVar(Symbol),

    #[regex("#(.*)\n?", logos::skip)]
    #[regex("[ \t\r\n]+", logos::skip)]
    #[error]
    Error,
}

fn ident(lex: &mut Lexer<Token>) -> Symbol {
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

pub fn parser() -> impl Parser<Token, ast::Decl, Error = Simple<Token, Span>> + Clone {
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
            .map_with_span(|ident, span| Ty::new(TyKind::Free(ident.symbol), span))
            .or(just([Token::LParen, Token::RParen])
                .map_with_span(|_, span| Ty::new(TyKind::Unit, span)))
            .or(ty.clone().delimited_by(Token::LParen, Token::RParen))
            .or(tyvar.map_with_span(|ident, span| Ty::new(TyKind::Var(ident.symbol), span)));

        let arrow = primary
            .clone()
            .then(just(Token::Arrow).ignore_then(ty).repeated())
            .foldl(|lhs, rhs| {
                let sp = lhs.span.with_hi(rhs.span.hi());
                Ty::new(TyKind::Arrow(Box::new(lhs), Box::new(rhs)), sp.into())
            });

        let forall = just(Token::Forall)
            .map_with_span(|_, sp| sp)
            .then(tyvar.repeated())
            .then_ignore(just(Token::Dot))
            .then(arrow.clone())
            .map(|((sp, vars), ty)| (vars, (sp, ty)))
            .foldr(|var, (sp, ty)| {
                let sp = sp.with_hi(ty.span.hi()).into();
                (sp, Ty::new(TyKind::Forall(var, Box::new(ty)), sp))
            })
            .map(|(sp, ty)| ty);

        forall.or(arrow)
    });

    let expr = recursive(|expr| {
        let primary = ident
            .map_with_span(|ident, span| Expr::new(ExprKind::Var(ident.symbol), span))
            .or(just([Token::LParen, Token::RParen])
                .map_with_span(|_, span| Expr::new(ExprKind::Unit, span)))
            .or(expr.clone().delimited_by(Token::LParen, Token::RParen));

        let appl = primary
            .clone()
            .then(primary.repeated())
            .map(|(lhs, rhs)| (rhs.into_iter().rev(), lhs))
            .foldr(|rhs, lhs| {
                let sp = lhs.span.with_hi(rhs.span.hi());
                Expr::new(ExprKind::Apply(Box::new(lhs), Box::new(rhs)), sp.into())
            });

        let lambda = just(Token::Backslash)
            .map_with_span(|_, span| span)
            .then(ident.repeated())
            .then_ignore(just(Token::Dot))
            .then(appl.clone())
            .map(|((sp, vars), expr)| (vars, (sp, expr)))
            .foldr(|var, (sp, expr)| {
                let sp = sp.with_hi(expr.span.hi()).into();
                (sp, Expr::new(ExprKind::Lambda(var, Box::new(expr)), sp))
            })
            .map(|(sp, expr)| expr)
            .or(appl);

        just(Token::Let)
            .map_with_span(|_, span| span)
            .then(ident)
            .then(just(Token::Colon).ignore_then(ty.clone()).or_not())
            .then_ignore(just(Token::Eq))
            .then(lambda.clone())
            .then_ignore(just(Token::In))
            .then(expr)
            .map(|((((sp, ident), ty), expr), inn)| {
                let sp = sp.with_hi(inn.span.hi()).into();
                Expr::new(
                    ExprKind::Let(ident, ty.map(Box::new), Box::new(expr), Box::new(inn)),
                    sp,
                )
            })
            .or(lambda)
    });

    let decl = recursive(|decl| {
        just(Token::Def)
            .map_with_span(|_, span| span)
            .then(ident)
            .then_ignore(just(Token::Colon))
            .then(ty)
            .then_ignore(just(Token::Eq))
            .then(expr)
            .then(decl.or_not())
            .map(|((((sp, name), ty), expr), decl)| {
                let sp = sp.with_hi(expr.span.hi()).into();
                Decl::new(
                    DeclKind::Defn(name, Box::new(ty), Box::new(expr), decl.map(Box::new)),
                    sp,
                )
            })
    });

    decl.then_ignore(end())
}
