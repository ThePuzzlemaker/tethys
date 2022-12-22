//! This module implements name resolution within the AST (see [`crate::ast`]).
//!
//! The data generated from this resolution process are not stored within the AST
//! itself--as that would mean re-allocating many things in the AST which is
//! not only time-inefficient but also space-inefficient. Instead, the data
//! are stored within the [`TyCtxt`] itself, within the
//! [`crate::ctxt::AstArenas`] structure.

use ariadne::{Label, ReportKind};
use calypso_base::symbol::Symbol;
use id_arena::Id;
use std::collections::HashMap;

use crate::{
    ast::{AstId, DefnKind, Expr, ExprKind, Item, ItemKind, PrimFunc, PrimTy, Res, Ty, TyKind},
    ctxt::{AstArenas, GlobalCtxt},
    diag::Diagnostic,
    error::TysResult,
    parse::Span,
};

/// Resolved name mappings generated during a resolution pass.
///
/// As multiple [`AstId`]s can map to a single resolved name, such as in `\x.f x
/// x`, where each `x` has a different id, but refers to the same definition,
/// this data structure uses a vector and map-to-vector-index to prevent wasting
/// space--in the future, [`Res`]olution data will likely be slightly more
/// expensive to store (due to module paths and whatnot, which will likely be
/// added at some point in the future).
///
/// Note that only ids referring to [`ExprKind::Name`] or [`TyKind::Name`] are
/// assigned resolution data.
#[derive(Debug, Default)]
pub struct ResolutionData {
    ast_id_to_res_idx: HashMap<AstId, usize>,
    res_data: Vec<Res>,
}

impl ResolutionData {
    pub fn clear(&mut self) {
        self.ast_id_to_res_idx.clear();
        self.res_data.clear();
    }

    pub(crate) fn insert(&mut self, id: AstId, res: Res) {
        let idx = self
            .res_data
            .iter()
            .enumerate()
            .find_map(|(idx, res1)| (res1 == &res).then(|| idx))
            .unwrap_or_else(|| {
                let idx = self.res_data.len();
                self.res_data.push(res);
                idx
            });
        self.ast_id_to_res_idx.insert(id, idx);
    }

    pub fn get_by_id(&'_ self, id: AstId) -> Option<&'_ Res> {
        self.ast_id_to_res_idx
            .get(&id)
            .and_then(|idx| self.res_data.get(*idx))
    }

    pub fn to_hash_map(&'_ self) -> HashMap<AstId, &'_ Res> {
        self.ast_id_to_res_idx
            .iter()
            .flat_map(|(&id, &idx)| Some((id, self.res_data.get(idx)?)))
            .collect()
    }
}

pub fn resolve_code_unit(gcx: &GlobalCtxt, items: &[Id<Item>]) -> TysResult<()> {
    let arena = &gcx.arenas.ast;
    let mut rcx = ResolutionCtxt {
        gcx,
        arena,
        defn_names: HashMap::new(),
        defn_id_to_span: HashMap::new(),
        ty_stack: vec![],
        expr_stack: vec![],
    };
    rcx.lower_code_unit(items)?;
    Ok(())
}

struct ResolutionCtxt<'gcx> {
    gcx: &'gcx GlobalCtxt,
    arena: &'gcx AstArenas,
    // N.B. this will be robust once modules are implemented
    defn_names: HashMap<Symbol, AstId>,
    defn_id_to_span: HashMap<AstId, Span>,
    /// A stack of `forall`-binders that we're under at the moment. `Vec<(AstId
    /// of forall, name of bound variable)>`
    ty_stack: Vec<(AstId, Symbol)>,
    /// Similar to [`ty_stack`], just for expressions (i.e. `let`- and
    /// lambda-binders)
    expr_stack: Vec<(AstId, Symbol)>,
}

impl<'gcx> ResolutionCtxt<'gcx> {
    fn lower_code_unit(&mut self, items: &[Id<Item>]) -> TysResult<()> {
        for item in items {
            self.lower_item(*item)?;
        }
        self.clear();
        Ok(())
    }

    fn lower_item(&mut self, item: Id<Item>) -> TysResult<()> {
        let item = self.arena.item(item);
        match item.kind {
            ItemKind::Value(ty, expr) => {
                if let Some(defn_id) = self.defn_names.get(&item.ident.symbol) {
                    // TODO(@ThePuzzlemaker: diag): this could be better
                    let ident_span = self
                        .arena
                        .get_node_by_id(*defn_id)
                        .expect("defn_id in nodes")
                        .span(self.gcx);
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
                    let mut drcx = self.gcx.drcx.borrow_mut();
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

    fn lower_ty(&mut self, ty: Id<Ty>) -> TysResult<Vec<(AstId, Symbol)>> {
        fn inner(
            rcx: &mut ResolutionCtxt,
            ty: Id<Ty>,
            is_outer_forall: bool,
        ) -> TysResult<Vec<(AstId, Symbol)>> {
            let mut plus = vec![];
            let ty = rcx.arena.ty(ty);
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
                    } else if var.as_str() == "Integer" {
                        Res::PrimTy(PrimTy::Integer)
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
                        let mut drcx = rcx.gcx.drcx.borrow_mut();
                        drcx.report_syncd(report);
                        drop(drcx);
                        Res::Err
                    };
                    rcx.arena.res_data.borrow_mut().insert(ty.id, res);
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

    fn lower_expr(&mut self, expr: Id<Expr>) -> TysResult<()> {
        let expr = self.arena.expr(expr);
        match expr.kind {
            ExprKind::Unit => (),
            ExprKind::Number(_) => (),
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
                } else if var.as_str() == "add" {
                    Res::PrimFunc(PrimFunc::Add)
                } else {
                    let report = Diagnostic::build(ReportKind::Error, (), expr.span.lo() as usize)
                        .with_message(format!("cannot find value `{}` in this scope", var.symbol))
                        .with_label(Label::new(expr.span).with_message("not found in this scope"))
                        .finish();
                    let mut drcx = self.gcx.drcx.borrow_mut();
                    drcx.report_syncd(report);
                    drop(drcx);
                    Res::Err
                };
                self.arena.res_data.borrow_mut().insert(expr.id, res);
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
