use crate::infer::HoleId;

#[derive(Clone, Debug)]
pub enum NamedTy {
    Unit,
    Var(String),
    Free(String),
    Arrow(Box<NamedTy>, Box<NamedTy>),
    Forall(String, Box<NamedTy>),
}

#[derive(Clone, Debug)]
pub enum NamedExpr {
    Unit,
    Var(String),
    Apply(Box<NamedExpr>, Box<NamedExpr>),
    Lambda(String, Box<NamedExpr>),
    Let(String, Option<Box<NamedTy>>, Box<NamedExpr>, Box<NamedExpr>),
}

#[derive(Clone, Debug)]
pub enum NamedDecl {
    Defn(String, Box<NamedTy>, Box<NamedExpr>, Option<Box<NamedDecl>>),
}

#[derive(Clone, Debug)]
pub enum Ty<'tcx> {
    Unit,
    Var(Level),
    Free(&'tcx Decl<'tcx>),
    Arrow(&'tcx Ty<'tcx>, &'tcx Ty<'tcx>),
    Forall(&'tcx Ty<'tcx>, Vec<&'tcx Ty<'tcx>>),
    Hole(HoleId),
}

#[derive(Clone, Debug)]
pub enum Expr<'tcx> {
    Unit,
    Var(Level),
    Free(&'tcx Decl<'tcx>),
    Apply(&'tcx Expr<'tcx>, &'tcx Expr<'tcx>),
    Lambda(&'tcx Expr<'tcx>),
    Let(Option<&'tcx Ty<'tcx>>, &'tcx Expr<'tcx>, &'tcx Expr<'tcx>),
}

#[derive(Clone, Debug)]
pub enum Decl<'tcx> {
    Defn(String, &'tcx Ty<'tcx>, &'tcx Expr<'tcx>),
}

pub type Level = usize;

#[derive(Clone, Debug)]
pub enum Hole<'tcx> {
    Empty(Level),
    Filled(&'tcx Ty<'tcx>),
}
