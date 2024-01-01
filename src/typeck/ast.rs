use std::{
    cell::RefCell,
    hash::{self, Hash},
    rc::Rc,
};

use ariadne::{Color, Label, Report, ReportBuilder, ReportKind};
use calypso_base::symbol::Symbol;
use id_arena::{Arena, Id};

use crate::{ast::AstId, ctxt::GlobalCtxt, parse::Span};

use super::{
    norm::{eval_ty, nf_ty_force},
    TypeckCtxt,
};

index_vec::define_index_type! {
    pub struct DeBruijnIdx = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
    DEBUG_FORMAT = "DebruijnIdx({})";
    DISPLAY_FORMAT = "{}";
    IMPL_RAW_CONVERSIONS = true;
}

index_vec::define_index_type! {
    pub struct DeBruijnLvl = u32;

    DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
    DEBUG_FORMAT = "DebruijnLvl({})";
    DISPLAY_FORMAT = "{}";
    IMPL_RAW_CONVERSIONS = true;
}

#[derive(Clone, Debug)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

impl Ty {
    pub fn new(gcx: &GlobalCtxt, kind: TyKind, span: Span) -> Id<Ty> {
        gcx.arenas.core.ty.borrow_mut().alloc(Ty { kind, span })
    }
}

#[derive(Clone, Debug)]
pub enum TyKind {
    Unit,
    Var(AstId, DeBruijnIdx),
    Arrow(Id<Ty>, Id<Ty>),
    Forall(AstId, Id<Ty>),
    Meta(MetaVar, im::Vector<Id<Ty>>),
    InsertedMeta(MetaVar),
    Free(AstId),
    Enum(AstId, im::Vector<Id<Ty>>),
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    pub fn new(gcx: &GlobalCtxt, kind: ExprKind, span: Span) -> Id<Expr> {
        gcx.arenas.core.expr.borrow_mut().alloc(Expr { kind, span })
    }
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Unit,
    Var(AstId, DeBruijnIdx),
    Lam(AstId, Id<Expr>),
    App(Id<Expr>, Id<Expr>),
    TyApp(Id<Expr>, Id<Ty>),
    Let(AstId, Id<Ty>, Id<Expr>, Id<Expr>),
    Fix(AstId, Id<Expr>),
    TyAbs(AstId, Id<Expr>),
    Free(AstId),
    EnumConstructor(AstId, usize),
    EnumRecursor(AstId),
    Err(ExprDeferredError),
}

#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum ExprDeferredError {
    Discarded(Id<Ty>, TypeckCtxt),
}

impl ExprDeferredError {
    pub fn build(self, gcx: &GlobalCtxt, span: Span) -> Report<'static, Span> {
        if let ExprDeferredError::Discarded(t, tcx) = self {
            let mut w = Vec::new();
            let t = nf_ty_force(gcx, tcx.lvl, tcx.env.clone(), t);
            let doc = super::pretty::pp_ty(0, gcx, tcx.lvl, tcx.env, t);
            doc.render(80, &mut w).unwrap();
            let t = String::from_utf8(w).unwrap();

            let report = Report::build(ReportKind::Error, (), span.lo() as usize)
                .with_message("invalid identifier `_`")
                .with_label(
                    Label::new(span)
                        .with_message("invalid identifier here")
                        .with_color(Color::Blue),
                )
                .with_help(format!("this value was expected to be of type {t}"))
                .with_note(
                    "`_` is only valid on the left-hand side of a variable definition, e.g. `λ_.x`",
                );

            report.finish()
        } else {
            todo!()
        }
    }
}

impl Expr {
    pub fn report_deferred(e: Id<Expr>, gcx: &GlobalCtxt) {
        match gcx.arenas.core.expr(e).kind {
            ExprKind::Lam(_, x) => Self::report_deferred(x, gcx),
            ExprKind::App(f, x) => {
                Self::report_deferred(f, gcx);
                Self::report_deferred(x, gcx);
            }
            ExprKind::TyApp(f, _) => Self::report_deferred(f, gcx),
            ExprKind::Let(_, _, e1, e2) => {
                Self::report_deferred(e1, gcx);
                Self::report_deferred(e2, gcx);
            }
            ExprKind::Fix(_, x) => Self::report_deferred(x, gcx),
            ExprKind::TyAbs(_, x) => Self::report_deferred(x, gcx),
            ExprKind::Err(err) => {
                gcx.drcx
                    .borrow_mut()
                    .report_syncd(err.build(gcx, gcx.arenas.core.expr(e).span));
            }
            _ => {}
        }
    }
}

#[derive(Clone, Debug)]
pub struct MetaVar(pub Rc<RefCell<(MetaEntry, MetaInfo)>>);

#[derive(Debug)]
pub enum MetaEntry {
    Solved(Id<Ty>),
    Unsolved,
}

#[derive(Debug)]
pub struct MetaInfo {
    pub level: DeBruijnLvl,
    pub name: Symbol,
    pub span: Span,
}

#[derive(Debug)]
pub struct CoreAstArenas {
    pub expr: RefCell<Arena<Expr>>,
    pub ty: RefCell<Arena<Ty>>,
}

impl CoreAstArenas {
    pub fn clear(&self) {}

    pub fn expr(&self, id: Id<Expr>) -> Expr {
        self.expr.borrow()[id].clone()
    }

    pub fn ty(&self, id: Id<Ty>) -> Ty {
        self.ty.borrow()[id].clone()
    }
}

impl Default for CoreAstArenas {
    fn default() -> Self {
        Self {
            expr: Default::default(),
            ty: Default::default(),
        }
    }
}
