//! This module implements name resolution within the AST (see [`crate::ast`]).
//!
//! The data generated from this resolution process are not stored within the AST
//! itself--as that would mean re-allocating many things in the AST which is
//! not only time-inefficient but also space-inefficient. Instead, the data
//! are stored within the [`TyCtxt`] itself, within the
//! [`crate::ctxt::AstArenas`] structure.

use ariadne::{Label, ReportKind};
use calypso_base::symbol::Symbol;
use hashbrown::HashMap;

use crate::{
    ast::{AstId, DefnKind, Expr, ExprKind, Item, ItemKind, Res, Ty, TyKind},
    ctxt::{AstArenas, TyCtxt},
    diag::Diagnostic,
    error::TysResult,
    parse::Span,
};

pub fn resolve_code_unit<'tcx>(
    tcx: &'tcx TyCtxt<'tcx>,
    items: &[&'tcx Item<'tcx>],
) -> TysResult<()> {
    let arena = &tcx.arenas.ast;
    let mut rcx = ResolutionCtxt {
        tcx,
        arena,
        defn_names: HashMap::new(),
        defn_id_to_span: HashMap::new(),
        ty_stack: vec![],
        expr_stack: vec![],
    };
    rcx.lower_code_unit(items)?;
    // todo!("resolution data")
    Ok(())
}

struct ResolutionCtxt<'tcx> {
    tcx: &'tcx TyCtxt<'tcx>,
    arena: &'tcx AstArenas<'tcx>,
    // N.B. this will be robust once modules are implemented
    defn_names: HashMap<Symbol, AstId>,
    defn_id_to_span: HashMap<AstId, Span>,
    /// A stack of `forall`-binders that we're under at the moment.
    /// `Vec<(AstId of forall, name of bound variable)>`
    ty_stack: Vec<(AstId, Symbol)>,
    /// Similar to [`ty_stack`], just for expressions (i.e. `let`- and
    /// lambda-binders)
    expr_stack: Vec<(AstId, Symbol)>,
}

impl<'tcx> ResolutionCtxt<'tcx> {
    fn lower_code_unit(&mut self, items: &[&'tcx Item<'tcx>]) -> TysResult<()> {
        for item in items {
            self.lower_item(item)?;
        }
        self.clear();
        Ok(())
    }

    fn lower_item(&mut self, item: &'tcx Item<'tcx>) -> TysResult<()> {
        match item.kind {
            ItemKind::Value(ty, expr) => {
                if let Some(defn_id) = self.defn_names.get(&item.ident.symbol) {
                    // TODO(@ThePuzzlemaker: diag): this could be better
                    let ident_span = self
                        .arena
                        .get_node_by_id(*defn_id)
                        .expect("defn_id in nodes")
                        .span();
                    let span: Span = self.defn_id_to_span[defn_id]
                        .with_hi(ident_span.hi())
                        .into();
                    let report = Diagnostic::build(ReportKind::Error, (), span.lo() as usize)
                        .with_message(format!(
                            "the name `{}` is defined multiple times",
                            item.ident.symbol
                        ))
                        .with_label(Label::new(span).with_message("first defined here"))
                        .with_label(
                            Label::new(item.span.with_hi(item.ident.span.hi()).into())
                                .with_message("redefined here"),
                        )
                        .with_note("top-level `def`initions must have unique names")
                        .finish();
                    let mut drcx = self.tcx.drcx.borrow_mut();
                    drcx.report_syncd(report);
                } else {
                    self.defn_names.insert(item.ident.symbol, item.id);
                }
                self.defn_id_to_span.insert(item.id, item.span);
                let plus = self.lower_ty(ty)?;
                self.ty_stack.extend(&plus);
                self.lower_expr(expr)?;
                self.ty_stack.truncate(self.ty_stack.len() - plus.len());
            }
        };
        Ok(())
    }

    fn lower_ty(&mut self, ty: &'tcx Ty<'tcx>) -> TysResult<Vec<(AstId, Symbol)>> {
        fn inner<'tcx>(
            rcx: &mut ResolutionCtxt<'tcx>,
            ty: &'tcx Ty<'tcx>,
            is_outer_forall: bool,
        ) -> TysResult<Vec<(AstId, Symbol)>> {
            let mut plus = vec![];
            match ty.kind {
                TyKind::Unit => (),
                TyKind::Name(var) => {
                    // We reverse here because we want the closest binder, not the
                    // furthest, and we push at the back.
                    let res = if let Some((id, _)) = rcx
                        .ty_stack
                        .iter()
                        .rev()
                        .find(|(_, sym)| *sym == var.symbol)
                    {
                        Res::TyVar(*id)
                    } else {
                        let report =
                            Diagnostic::build(ReportKind::Error, (), ty.span.lo() as usize)
                                .with_message(format!(
                                    "cannot find type `{}` in this scope",
                                    var.symbol
                                ))
                                .with_label(
                                    Label::new(ty.span).with_message("not found in this scope"),
                                )
                                .finish();
                        let mut drcx = rcx.tcx.drcx.borrow_mut();
                        drcx.report_syncd(report);
                        drop(drcx);
                        Res::Err
                    };
                    // TODO: give res to resolve data
                }
                TyKind::Arrow(t1, t2) => {
                    let _ = inner(rcx, t1, false)?;
                    let _ = inner(rcx, t2, false)?;
                }
                TyKind::Forall(var, inner_ty) => {
                    rcx.ty_stack.push((ty.id, var.symbol));
                    let plus2 = inner(rcx, inner_ty, true)?;
                    plus.extend(plus2);
                    if is_outer_forall {
                        plus.push((ty.id, var.symbol));
                    }
                    rcx.ty_stack.pop();
                }
                TyKind::Err => (),
            };
            Ok(plus)
        }
        inner(self, ty, true)
    }

    fn lower_expr(&mut self, expr: &'tcx Expr<'tcx>) -> TysResult<()> {
        match expr.kind {
            ExprKind::Unit => (),
            ExprKind::Name(var) => {
                // we reverse here because we want the closest binder, not the
                // furthest, and we push at the back.
                let res = if let Some((id, _)) = self
                    .expr_stack
                    .iter()
                    .rev()
                    .find(|(_, sym)| *sym == var.symbol)
                {
                    Res::Local(*id)
                } else if let Some(defn) = self.defn_names.get(&var) {
                    Res::Defn(DefnKind::Value, *defn)
                } else {
                    let report = Diagnostic::build(ReportKind::Error, (), expr.span.lo() as usize)
                        .with_message(format!("cannot find value `{}` in this scope", var.symbol))
                        .with_label(Label::new(expr.span).with_message("not found in this scope"))
                        .finish();
                    let mut drcx = self.tcx.drcx.borrow_mut();
                    drcx.report_syncd(report);
                    drop(drcx);
                    Res::Err
                };
                // TODO: insert Res into resolve data
            }
            ExprKind::Apply(f, x) => {
                self.lower_expr(f)?;
                self.lower_expr(x)?;
            }
            ExprKind::Lambda(var, body) => {
                self.expr_stack.push((expr.id, var.symbol));
                self.lower_expr(body)?;
                self.expr_stack.pop();
            }
            ExprKind::Let(var, ty, inner_expr, inn) => {
                let ty = ty.map(|x| self.lower_ty(x)).transpose()?;
                if let Some(plus) = &ty {
                    self.ty_stack.extend(plus);
                }
                self.lower_expr(inner_expr)?;
                if let Some(plus) = &ty {
                    self.ty_stack.truncate(self.ty_stack.len() - plus.len());
                }
                self.expr_stack.push((expr.id, var.symbol));
                self.lower_expr(inn)?;
                self.expr_stack.pop();
            }
            ExprKind::Err => (),
        };
        Ok(())
    }

    fn clear(&mut self) {
        self.defn_names.clear();
        self.defn_id_to_span.clear();
        self.ty_stack.clear();
        self.expr_stack.clear();
    }
}

#[derive(Debug)]
pub struct ResolutionData {}
