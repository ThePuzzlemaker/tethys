//! This module implements lowering from the surface language (i.e.,
//! [`crate::parse::ast`]), to Tethys's core language (i.e., [`crate::ir`]).
//!
//! At the moment, this lowering is very simple, just performing name
//! resolution, but as Tethys becomes more complex (and it surely will), this
//! lowering will become more complex, and may even end up being intertwined
//! with typechecking/inference.
//!
//! A good place to start for this module is [`lower_code_unit`].

use std::mem;

use ariadne::{Label, ReportKind};
use calypso_base::symbol::Symbol;
use hashbrown::HashMap;
use index_vec::{index_vec, IndexVec};

use crate::ctxt::IrArenas;
use crate::diag::Diagnostic;
use crate::error::TysResult;
use crate::ir::{
    CodeUnit, DefnId, Expr, ExprKind, IrId, Item, ItemKind, LocalId, Node, OwnerNodes,
    ParentedNode, Ty, TyKind,
};
use crate::parse::Span;
use crate::{ctxt::TyCtxt, parse::ast};

pub fn lower_code_unit<'tcx>(
    tcx: &'tcx TyCtxt<'tcx>,
    decls: Vec<ast::Decl>,
) -> TysResult<&'tcx CodeUnit<'tcx>> {
    let arena = &tcx.arenas.ir;
    let mut lcx = LoweringCtxt {
        tcx,
        arena,
        owners: IndexVec::new(),
        current_owner_id: DefnId::from_raw(0),
        local_id_counter: LocalId::from_raw(0),
        defn_names: HashMap::new(),
        defn_id_to_span: IndexVec::new(),
    };
    lcx.lower_code_unit(decls)
}

struct LoweringCtxt<'tcx> {
    tcx: &'tcx TyCtxt<'tcx>,
    arena: &'tcx IrArenas<'tcx>,
    owners: IndexVec<DefnId, OwnerNodes<'tcx>>,
    current_owner_id: DefnId,
    local_id_counter: LocalId,
    // In the future, this will be a bit more robust, supporting module paths
    // and such
    defn_names: HashMap<Symbol, DefnId>,
    defn_id_to_span: IndexVec<DefnId, Span>,
}

impl<'tcx> LoweringCtxt<'tcx> {
    fn lower_code_unit(&mut self, decls: Vec<ast::Decl>) -> TysResult<&'tcx CodeUnit<'tcx>> {
        for decl in decls {
            self.lower_decl(decl)?;
        }
        let owners = mem::take(&mut self.owners);
        self.clear();
        Ok(&*self.arena.code_unit.alloc(CodeUnit { owners }))
    }

    fn lower_decl(&mut self, decl: ast::Decl) -> TysResult<&'tcx Item<'tcx>> {
        let ir_id = self.current_id();
        let ident;
        let kind = match decl.kind {
            ast::DeclKind::Defn(name, ty, expr) => {
                if let Some(defn_id) = self.defn_names.get(&name.symbol) {
                    let ident_span = self
                        .owners
                        .get(*defn_id)
                        .expect("defn_id in owners")
                        .node()
                        .ident()
                        .expect("owner has ident")
                        .span;
                    let span: Span = self.defn_id_to_span[*defn_id]
                        .with_hi(ident_span.hi())
                        .into();
                    let report = Diagnostic::build(ReportKind::Error, (), span.lo() as usize);
                    let report = report
                        .with_message(format!(
                            "the name `{}` is defined multiple times",
                            name.symbol
                        ))
                        .with_label(Label::new(span).with_message("first defined here"))
                        .with_label(
                            Label::new(decl.span.with_hi(name.span.hi()).into())
                                .with_message("redefined here"),
                        )
                        .with_note("top-level `def`initions must have unique names")
                        .finish();
                    let mut drcx = self.tcx.drcx.borrow_mut();
                    drcx.report_syncd(report);
                } else {
                    self.defn_names.insert(name.symbol, self.current_owner_id);
                }
                self.defn_id_to_span
                    .insert(self.current_owner_id, decl.span);
                self.bump_local();
                let ty = self.lower_ty(*ty)?;
                let expr = self.lower_expr(*expr)?;
                ident = name;
                ItemKind::Value(ty, expr)
            }
        };
        self.bump_owner();
        let item = &*self.arena.item.alloc(Item {
            ident,
            ir_id,
            span: decl.span,
            kind,
        });
        self.owners.insert(
            ir_id.owner,
            OwnerNodes {
                nodes: index_vec![ParentedNode {
                    parent: LocalId::from_raw(u32::MAX),
                    node: Node::Item(item)
                }],
            },
        );
        Ok(item)
    }

    fn lower_ty(&mut self, ty: ast::Ty) -> TysResult<&'tcx Ty<'tcx>> {
        // TODO
        Ok(&*self.arena.ty.alloc(Ty {
            ir_id: self.current_id(),
            span: calypso_base::span::Span::new_dummy().into(),
            kind: TyKind::Err,
        }))
    }

    fn lower_expr(&mut self, expr: ast::Expr) -> TysResult<&'tcx Expr<'tcx>> {
        // TODO
        Ok(&*self.arena.expr.alloc(Expr {
            ir_id: self.current_id(),
            span: calypso_base::span::Span::new_dummy().into(),
            kind: ExprKind::Err,
        }))
    }

    fn clear(&mut self) {
        self.owners.clear();
        self.defn_names.clear();
        self.defn_id_to_span.clear();
        self.current_owner_id = DefnId::from_raw(0);
        self.local_id_counter = LocalId::from_raw(0);
    }

    fn bump_owner(&mut self) {
        self.current_owner_id += 1;
        self.local_id_counter = LocalId::from_raw(0);
    }

    fn bump_local(&mut self) {
        self.local_id_counter += 1;
    }

    fn current_id(&self) -> IrId {
        IrId {
            local_id: self.local_id_counter,
            owner: self.current_owner_id,
        }
    }
}
