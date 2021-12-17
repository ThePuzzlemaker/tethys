use calypso_base::symbol::{Ident, Symbol};

use super::Span;

#[derive(Clone, Debug)]
pub struct Ty {
    pub span: Span,
    pub kind: TyKind,
}

impl Ty {
    pub fn new(kind: TyKind, span: Span) -> Self {
        Self { kind, span }
    }
}

#[derive(Clone, Debug)]
pub enum TyKind {
    Unit,
    Var(Symbol),
    Free(Symbol),
    Arrow(Box<Ty>, Box<Ty>),
    Forall(Ident, Box<Ty>),
}

impl TyKind {
    pub fn description(&self) -> &'static str {
        match self {
            TyKind::Unit => "unit",
            TyKind::Var(..) => "type variable",
            TyKind::Free(..) => "name",
            TyKind::Arrow(..) => "arrow",
            TyKind::Forall(..) => "forall",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

impl Expr {
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Self { kind, span }
    }
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Unit,
    Var(Symbol),
    Apply(Box<Expr>, Box<Expr>),
    Lambda(Ident, Box<Expr>),
    Let(Ident, Option<Box<Ty>>, Box<Expr>, Box<Expr>),
}

impl ExprKind {
    pub fn description(&self) -> &'static str {
        match self {
            ExprKind::Unit => "unit",
            ExprKind::Var(..) => "name",
            ExprKind::Apply(..) => "application",
            ExprKind::Lambda(..) => "lambda",
            ExprKind::Let(..) => "let-expression",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Decl {
    pub span: Span,
    pub kind: DeclKind,
}

impl Decl {
    pub fn new(kind: DeclKind, span: Span) -> Self {
        Self { kind, span }
    }
}

#[derive(Clone, Debug)]
pub enum DeclKind {
    Defn(Ident, Box<Ty>, Box<Expr>, Option<Box<Decl>>),
}

impl DeclKind {
    pub fn description(&self) -> &'static str {
        match self {
            DeclKind::Defn(..) => "definition",
        }
    }
}
