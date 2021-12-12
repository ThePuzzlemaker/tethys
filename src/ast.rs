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
    Annotate(Box<NamedExpr>, Box<NamedTy>),
    Lambda(String, Box<NamedExpr>),
    Let(String, Box<NamedExpr>, Box<NamedExpr>),
}

#[derive(Clone, Debug)]
pub enum NamedDecl {
    Defn(String, Box<NamedTy>, Box<NamedExpr>, Option<Box<NamedDecl>>),
}

#[derive(Clone, Debug)]
pub enum Ty<'tcx> {
    Unit,
    Var(Level),
    Arrow(&'tcx Ty<'tcx>, &'tcx Ty<'tcx>),
    Forall(&'tcx Ty<'tcx>, Vec<&'tcx Ty<'tcx>>),
    Hole(HoleId),
}

#[derive(Clone, Debug)]
pub enum Expr<'tcx> {
    Unit,
    Var(Level),
    Apply(Box<Expr<'tcx>>, Box<Expr<'tcx>>),
    Annotate(Box<Expr<'tcx>>, &'tcx Ty<'tcx>),
    Lambda(Box<Expr<'tcx>>),
    Let(Box<Expr<'tcx>>, Box<Expr<'tcx>>),
}

pub type Level = usize;

#[derive(Clone, Debug)]
pub enum Hole<'tcx> {
    Empty(Level),
    Filled(&'tcx Ty<'tcx>),
}
