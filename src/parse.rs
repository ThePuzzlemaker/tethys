use std::{
    fmt::{self, Display},
    iter,
};

use chumsky::prelude::*;
use logos::{Lexer, Logos};

use crate::ast::{NamedDecl, NamedExpr, NamedTy};

/// This isn't the most efficient, but it works.
pub type Span = std::ops::Range<usize>;
pub type Spanned<T> = (T, Span);

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
    Ident(String),
    #[regex("'_[A-Za-z0-9_]+|'[A-Za-z][A-Za-z0-9_]*", ident)]
    TyVar(String),

    #[regex("#(.*)\n?", logos::skip)]
    #[regex("[ \t\r\n]+", logos::skip)]
    #[error]
    Error,
}

fn ident(lex: &mut Lexer<Token>) -> String {
    lex.source()[lex.span()].to_string()
}

impl Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Def => write!(f, "`def`"),
            Token::Forall => write!(f, "`forall`"),
            Token::Let => write!(f, "`let`"),
            Token::In => write!(f, "`in`"),
            Token::Backslash => write!(f, "`\\`"),
            Token::Dot => write!(f, "`.`"),
            Token::LParen => write!(f, "`(`"),
            Token::RParen => write!(f, "`)`"),
            Token::Colon => write!(f, "`:`"),
            Token::Eq => write!(f, "`=`"),
            Token::Arrow => write!(f, "`->`"),
            Token::Ident(_) => write!(f, "ident"),
            Token::TyVar(_) => write!(f, "type variable"),
            Token::Error => write!(f, "invalid token"),
        }
    }
}

pub fn parser() -> impl Parser<Token, Spanned<NamedDecl>, Error = Simple<Token>> + Clone {
    let ident = filter_map(|span, tok| {
        if let Token::Ident(s) = tok {
            Ok(s)
        } else {
            Err(Simple::expected_input_found(
                span,
                iter::once(Token::Ident(String::new())),
                Some(tok),
            ))
        }
    });

    let tyvar = filter_map(|span, tok| {
        if let Token::TyVar(s) = tok {
            Ok(s)
        } else {
            Err(Simple::expected_input_found(
                span,
                iter::once(Token::TyVar(String::new())),
                Some(tok),
            ))
        }
    });

    let ty = recursive(|ty| {
        let primary = ident
            .map(NamedTy::Free)
            .or(seq([Token::LParen, Token::RParen].into_iter()).map(|_| NamedTy::Unit))
            .or(ty.clone().delimited_by(Token::LParen, Token::RParen))
            .or(tyvar.map(NamedTy::Var));

        let arrow = primary
            .clone()
            .then(just(Token::Arrow).ignore_then(ty).repeated())
            .foldl(|lhs, rhs| NamedTy::Arrow(Box::new(lhs), Box::new(rhs)));

        just(Token::Forall)
            .ignore_then(tyvar.repeated())
            .then_ignore(just(Token::Dot))
            .or_not()
            .then(arrow)
            .map(|(vars, ty)| (vars.unwrap_or_default(), ty))
            .foldr(|var, ty| NamedTy::Forall(var, Box::new(ty)))
    });

    let expr = recursive(|expr| {
        let primary = ident
            .map(NamedExpr::Var)
            .or(seq([Token::LParen, Token::RParen].into_iter()).map(|_| NamedExpr::Unit))
            .or(expr.clone().delimited_by(Token::LParen, Token::RParen));

        let appl = primary
            .clone()
            .then(primary.repeated())
            .map(|(lhs, rhs)| (rhs.into_iter().rev(), lhs))
            .foldr(|rhs, lhs| NamedExpr::Apply(Box::new(lhs), Box::new(rhs)));

        let lambda = just(Token::Backslash)
            .ignore_then(ident.repeated())
            .then_ignore(just(Token::Dot))
            .or_not()
            .then(appl)
            .map(|(vars, expr)| (vars.unwrap_or_default(), expr))
            .foldr(|var, expr| NamedExpr::Lambda(var, Box::new(expr)));

        just(Token::Let)
            .ignore_then(ident)
            .then(just(Token::Colon).ignore_then(ty.clone()).or_not())
            .then_ignore(just(Token::Eq))
            .then(lambda.clone())
            .then_ignore(just(Token::In))
            .then(expr)
            .map(|(((ident, ty), expr), inn)| {
                NamedExpr::Let(ident, ty.map(Box::new), Box::new(expr), Box::new(inn))
            })
            .or(lambda)
    });

    let decl = recursive(|decl| {
        just(Token::Def)
            .ignore_then(ident)
            .then_ignore(just(Token::Colon))
            .then(ty)
            .then_ignore(just(Token::Eq))
            .then(expr)
            .then(decl.or_not())
            .map(|(((name, ty), expr), decl)| {
                NamedDecl::Defn(name, Box::new(ty), Box::new(expr), decl.map(Box::new))
            })
    });

    decl.then_ignore(end()).map_with_span(|x, s| (x, s))
}
