//! This module implements name resolution within the AST (see [`crate::ast`]).
//!
//! The data generated from this resolution process are not stored within the AST
//! itself--as that would mean re-allocating many things in the AST which is
//! not only time-inefficient but also space-inefficient. Instead, the data
//! are stored within the [`TyCtxt`] itself, within the
//! [`crate::ctxt::AstArenas`] structure.

use ariadne::{Color, Config, Label, LabelAttach, ReportKind};
use calypso_base::symbol::{Ident, Symbol};
use id_arena::Id;
use im::HashSet;
use std::collections::HashMap;

use crate::{
    ast::{
        AstArenas, AstId, DefnKind, Expr, ExprKind, Item, ItemKind, Node, PrimFunc, PrimTy,
        Recursive, Res, Ty, TyKind,
    },
    ctxt::GlobalCtxt,
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
            .find_map(|(idx, res1)| (res1 == &res).then_some(idx))
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
        expr_ns: HashMap::new(),
        type_ns: HashMap::new(),
        defn_id_to_span: HashMap::new(),
        ty_stack: vec![],
        expr_stack: vec![],
        gen_ty_stack: vec![],
    };
    rcx.collect(items)?;
    rcx.lower_code_unit(items)?;
    Ok(())
}

struct ResolutionCtxt<'gcx> {
    gcx: &'gcx GlobalCtxt,
    arena: &'gcx AstArenas,
    // N.B. this will be robust once modules are implemented
    expr_ns: HashMap<Symbol, (AstId, DefnKind)>,
    type_ns: HashMap<Symbol, (AstId, DefnKind)>,
    defn_id_to_span: HashMap<AstId, Span>,
    /// A stack of `forall`-binders that we're under at the moment. `Vec<(AstId
    /// of forall, name of bound variable)>`
    ty_stack: Vec<(AstId, Symbol)>,
    /// A stack of generic types that we're under at the moment.
    gen_ty_stack: Vec<(AstId, usize, Symbol)>,
    /// Similar to [`ty_stack`], just for expressions (i.e. `let`- and
    /// lambda-binders)
    expr_stack: Vec<(AstId, Symbol)>,
}

impl<'gcx> ResolutionCtxt<'gcx> {
    fn report_duplicate_name(
        &self,
        item: Item,
        ident: Ident,
        kind: DefnKind,
        duplicate: AstId,
        dup_kind: DefnKind,
    ) {
        let ident_span = self
            .arena
            .get_node_by_id(duplicate)
            .expect("defn_id in nodes")
            .ident(self.gcx)
            .unwrap()
            .span;
        let ident_span = if let DefnKind::EnumConstructor(branch) = dup_kind {
            let Node::Item(i) = self.arena.get_node_by_id(duplicate).unwrap() else {
                unreachable!()
            };
            let ItemKind::Enum(_, cons, _) = self.arena.item(i).kind else {
                unreachable!()
            };
            cons.get(branch).unwrap().0.span
        } else if let DefnKind::Generic(ix) = dup_kind {
            let Node::Item(i) = self.arena.get_node_by_id(duplicate).unwrap() else {
                unreachable!()
            };
            let ItemKind::Enum(generics, _, _) = self.arena.item(i).kind else {
                unreachable!()
            };
            generics.get(ix).unwrap().span
        } else {
            ident_span
        };

        let span: Span = ident_span.into();
        let report = Diagnostic::build(ReportKind::Error, (), span.lo() as usize)
            .with_message(match (kind, dup_kind) {
                (DefnKind::Generic(_), DefnKind::Generic(_)) => {
                    format!(
                        "the generic parameter `{}` is defined multiple times",
                        ident.symbol
                    )
                }
                (DefnKind::Generic(_), _) => {
                    format!(
                        "the generic parameter `{}` shadows an existing type",
                        ident.symbol
                    )
                }
                _ => format!("the name `{}` is defined multiple times", ident.symbol),
            })
            .with_label(
                Label::new(span)
                    .with_message("first defined here")
                    .with_color(Color::Blue),
            )
            .with_label(
                Label::new(ident.span.into())
                    .with_message("redefined here")
                    .with_color(Color::Red),
            )
            .with_note(match (kind, dup_kind) {
                (DefnKind::Value, _) => "top-level `def`initions must have unique names",
                (DefnKind::TyAlias, DefnKind::TyAlias) => "`type` aliases must have unique names",
                (DefnKind::EnumConstructor(_), _) => "`enum` constructors must have unique names",
                (DefnKind::Enum, _) => "`enum`s must have unique names",
                (DefnKind::EnumRecursor, _) => {
                    // TODO: until I get pattern matching
                    "`enum`s must have unique names in the value namespace"
                }
                (DefnKind::Generic(_), DefnKind::Generic(_)) => {
                    "datatype generics must have unique names"
                }
                (DefnKind::Generic(_), _) => "datatype generics must not shadow existing types",
                _ => unreachable!(),
            })
            .with_config(Config::default().with_label_attach(LabelAttach::End))
            .finish();

        let mut drcx = self.gcx.drcx.borrow_mut();
        drcx.report_syncd(report);
    }

    fn collect(&mut self, items: &[Id<Item>]) -> TysResult<()> {
        for item in items {
            let item = self.arena.item(*item);
            match item.kind {
                ItemKind::Value(_, _) => {
                    if let Some(&(defn_id, defn_kind)) = self.expr_ns.get(&item.ident.symbol) {
                        self.report_duplicate_name(
                            item.clone(),
                            item.ident,
                            DefnKind::Value,
                            defn_id,
                            defn_kind,
                        );
                    } else {
                        self.expr_ns
                            .insert(item.ident.symbol, (item.id, DefnKind::Value));
                    }
                    self.defn_id_to_span.insert(item.id, item.span);
                }
                ItemKind::TyAlias(_) => {
                    if let Some(&(defn_id, defn_kind)) = self.type_ns.get(&item.ident.symbol) {
                        self.report_duplicate_name(
                            item.clone(),
                            item.ident,
                            DefnKind::TyAlias,
                            defn_id,
                            defn_kind,
                        )
                    } else {
                        self.type_ns
                            .insert(item.ident.symbol, (item.id, DefnKind::TyAlias));
                    }
                    self.defn_id_to_span.insert(item.id, item.span);
                }
                ItemKind::Enum(ref generics, ref cons, _) => {
                    if let Some(&(defn_id, defn_kind)) = self.type_ns.get(&item.ident.symbol) {
                        self.report_duplicate_name(
                            item.clone(),
                            item.ident,
                            DefnKind::Enum,
                            defn_id,
                            defn_kind,
                        )
                    } else {
                        self.type_ns
                            .insert(item.ident.symbol, (item.id, DefnKind::Enum));
                    }

                    if let Some(&(defn_id, defn_kind)) = self.expr_ns.get(&item.ident.symbol) {
                        self.report_duplicate_name(
                            item.clone(),
                            item.ident,
                            DefnKind::EnumRecursor,
                            defn_id,
                            defn_kind,
                        )
                    } else {
                        self.expr_ns
                            .insert(item.ident.symbol, (item.id, DefnKind::EnumRecursor));
                    }
                    self.defn_id_to_span.insert(item.id, item.span);

                    for (ix, (ident, _)) in cons.iter().enumerate() {
                        // TODO: name span
                        if let Some(&(defn_id, defn_kind)) = self.expr_ns.get(&ident.symbol) {
                            self.report_duplicate_name(
                                item.clone(),
                                *ident,
                                DefnKind::EnumConstructor(ix),
                                defn_id,
                                defn_kind,
                            );
                        } else {
                            self.expr_ns
                                .insert(ident.symbol, (item.id, DefnKind::EnumConstructor(ix)));
                        }
                    }
                }
            }
        }

        Ok(())
    }

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
                let plus = self.lower_ty(ty)?;
                self.ty_stack.extend(&plus);
                self.lower_expr(expr)?;
                self.ty_stack.truncate(self.ty_stack.len() - plus.len());
            }

            ItemKind::TyAlias(ty) => {
                self.lower_ty(ty)?;
            }

            ItemKind::Enum(ref generics, ref cons, _) => {
                let mut set = HashMap::new();
                for (ix, ident) in generics.iter().enumerate() {
                    if let Some(&(defn_id, defn_kind)) = self.type_ns.get(&ident.symbol) {
                        self.report_duplicate_name(
                            item.clone(),
                            *ident,
                            DefnKind::Generic(ix),
                            defn_id,
                            defn_kind,
                        );
                    } else if let Some(dup_ix) = set.get(&ident.symbol) {
                        self.report_duplicate_name(
                            item.clone(),
                            *ident,
                            DefnKind::Generic(ix),
                            item.id,
                            DefnKind::Generic(*dup_ix),
                        );
                    } else {
                        set.insert(ident.symbol, ix);
                    }
                }

                let plus = generics
                    .iter()
                    .copied()
                    .enumerate()
                    .map(|(ix, x)| (item.id, ix, x.symbol))
                    .collect::<Vec<_>>();
                for (_, tys) in cons {
                    for ty in tys {
                        self.gen_ty_stack.extend(plus.iter());
                        self.lower_ty(*ty)?;
                        self.gen_ty_stack
                            .truncate(self.gen_ty_stack.len() - generics.len());
                    }
                }
            }
        };
        Ok(())
    }

    fn lower_ty_name(&mut self, var: Ident, span: Span, id: AstId) {
        // We reverse here because we want the closest binder, not the
        // furthest, and we push at the back.
        let res = if let Some((id, _)) = self
            .ty_stack
            .iter()
            .rev()
            .find(|(_, sym)| *sym == var.symbol)
        {
            Res::TyVar(*id)
        } else if let Some((id, ix, _)) = self
            .gen_ty_stack
            .iter()
            .rev()
            .find(|(_, _, sym)| *sym == var.symbol)
        {
            Res::Generic(*id, *ix)
        } else if let Some((defn, defn_kind)) = self.type_ns.get(&var) {
            Res::Defn(*defn_kind, *defn)
        } else if var.as_str() == "Integer" {
            Res::PrimTy(PrimTy::Integer)
        } else if var.as_str() == "_" || var.as_str() == "'_" {
            Res::Err
        } else {
            let report = Diagnostic::build(ReportKind::Error, (), span.lo() as usize)
                .with_message(format!("cannot find type `{}` in this scope", var.symbol))
                .with_label(
                    Label::new(span)
                        .with_message("not found in this scope")
                        .with_color(Color::Red),
                )
                .finish();
            let mut drcx = self.gcx.drcx.borrow_mut();
            drcx.report_syncd(report);
            drop(drcx);
            Res::Err
        };
        self.arena.res_data.borrow_mut().insert(id, res);
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
                TyKind::Name(var) => rcx.lower_ty_name(var, ty.span, ty.id),
                TyKind::Data(var, spine) => {
                    rcx.lower_ty_name(var, var.span.into(), ty.id);
                    for ty in spine {
                        rcx.lower_ty(ty)?;
                    }
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
                } else if let Some(&(defn, defn_kind)) = self.expr_ns.get(&var) {
                    Res::Defn(defn_kind, defn)
                } else if var.as_str() == "add" {
                    Res::PrimFunc(PrimFunc::Add)
                } else if var.as_str() == "_" {
                    Res::Err
                } else {
                    let report = Diagnostic::build(ReportKind::Error, (), expr.span.lo() as usize)
                        .with_message(format!("cannot find value `{}` in this scope", var.symbol))
                        .with_label(
                            Label::new(expr.span)
                                .with_message("not found in this scope")
                                .with_color(Color::Red),
                        )
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
            ExprKind::Let(var, Recursive::NotRecursive, ty, inner_expr, inn) => {
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
            _ => todo!(),
        };
        Ok(())
    }

    fn clear(&mut self) {
        self.expr_ns.clear();
        self.type_ns.clear();
        self.defn_id_to_span.clear();
        self.ty_stack.clear();
        self.expr_stack.clear();
    }
}
