use std::{cell::RefCell, rc::Rc};

use ariadne::{Color, Config, Label, LabelAttach, Report, ReportKind};
use calypso_base::symbol::{Ident, Symbol};
use id_arena::Id;

pub use crate::ast as surf;
use crate::{
    ast::{AstId, DefnKind, ItemKind, Node, PrimTy, Recursive, Res},
    ctxt::GlobalCtxt,
    parse::Span,
    resolve,
    typeck::{
        ast::{DeBruijnIdx, ExprDeferredError},
        norm::{quote_ty, Closure},
    },
};

use self::{
    ast::{DeBruijnLvl, MetaEntry, MetaInfo, MetaVar},
    norm::{apply_ty_closure, eval_ty, force, Env, VTy, VTyKind},
    unify::UnifyError,
};

pub mod ast;
pub mod norm;
pub mod pretty;
pub mod unify;

#[derive(Clone, Debug)]
pub struct TypeckCtxt {
    env: Env,
    lvl: DeBruijnLvl,
    vals: im::Vector<(AstId, Id<VTy>)>,
    tys: im::Vector<AstId>,
    ty_aliases: im::Vector<(AstId, Span)>,
}

impl Default for TypeckCtxt {
    fn default() -> Self {
        Self {
            env: Default::default(),
            lvl: DeBruijnLvl::from(0usize),
            vals: Default::default(),
            tys: Default::default(),
            ty_aliases: Default::default(),
        }
    }
}

impl TypeckCtxt {
    pub fn bind_ty(mut self, gcx: &GlobalCtxt, id: AstId) -> Self {
        self.env.push_back(VTy::rigid(gcx, id, self.lvl));
        self.lvl += 1;
        self.tys.push_back(id);
        self
    }

    pub fn bind_val(mut self, id: AstId, ty: Id<VTy>) -> Self {
        self.vals.push_back((id, ty));
        self
    }
}

pub fn surf_ty_to_core(
    gcx: &GlobalCtxt,
    mut tcx: TypeckCtxt,
    t: Id<surf::Ty>,
) -> Result<Id<ast::Ty>, ()> {
    // {
    //     let mut w = Vec::new();
    //     let doc = crate::ast::pretty::pp_ty(0, gcx, t);
    //     doc.render(80, &mut w).unwrap();
    //     println!(
    //         "\n{tcx:?}\nsurf_ty_to_core {}",
    //         String::from_utf8(w).unwrap()
    //     );
    // }

    use ast::TyKind as CT;
    use surf::TyKind as ST;
    let t = gcx.arenas.ast.ty(t);
    Ok(match t.kind {
        ST::Unit => ast::Ty::new(gcx, CT::Unit, t.span),
        ST::Name(Ident { symbol, span }) => {
            if symbol.as_str() == "_" {
                return Ok(fresh_meta(
                    gcx,
                    tcx.lvl,
                    Symbol::intern_static("?_"),
                    Span(span),
                    Span(span),
                ));
            } else if symbol.as_str() == "'_" {
                let report = Report::build(ReportKind::Error, (), span.lo() as usize)
                    .with_message("invalid identifier `'_`")
                    .with_label(
                        Label::new(Span(span))
                            .with_color(Color::Red)
                            .with_message("`'_` is not a valid identifier"),
                    )
                    .with_note(
                        "`'_` is only allowed on the left-hand side of a forall, e.g. `forall '_.T`",
                    )
                    .finish();
                gcx.drcx.borrow_mut().report_syncd(report);

                return Ok(fresh_meta(
                    gcx,
                    tcx.lvl,
                    Symbol::intern_static("?'_"),
                    Span(span),
                    Span(span),
                ));
            }

            let res_data = gcx.arenas.ast.res_data.borrow();
            let res = res_data.get_by_id(t.id).unwrap();
            match res {
                Res::PrimTy(PrimTy::Integer) => todo!(),
                Res::Defn(DefnKind::Enum, id) => ast::Ty::new(gcx, CT::Enum(*id), t.span),
                Res::Defn(DefnKind::TyAlias, id) => {
                    let Some(Node::Item(i)) = gcx.arenas.ast.get_node_by_id(*id) else {
                        unreachable!()
                    };
                    let i = gcx.arenas.ast.item(i);
                    let ItemKind::TyAlias(aliased) = i.kind else {
                        unreachable!()
                    };
                    if tcx.ty_aliases.iter().any(|(x, _)| x == id) {
                        let mut drcx = gcx.drcx.borrow_mut();
                        let mut diags = vec![];
                        for (ix, (id, span)) in tcx.ty_aliases.iter().enumerate() {
                            if ix == 0 {
                                diags.push(
                                    Report::build(ReportKind::Error, (), 0)
                                        .with_message(format!(
                                            "cycle detected while expanding type alias `{}`",
                                            i.ident.as_str()
                                        ))
                                        .with_label(
                                            Label::new(*span)
                                                .with_color(Color::Red)
                                                .with_message("referenced here"),
                                        )
                                        .finish(),
                                );
                            } else {
                                diags.push(
                                    Report::build(ReportKind::Custom("Help", Color::Blue), (), 0)
                                        .with_message(format!(
                                            "...which references `{}`",
                                            gcx.arenas
                                                .ast
                                                .get_node_by_id(*id)
                                                .unwrap()
                                                .ident(gcx)
                                                .unwrap()
                                                .as_str()
                                        ))
                                        .with_label(
                                            Label::new(*span)
                                                .with_color(Color::Blue)
                                                .with_message("referenced here"),
                                        )
                                        .finish(),
                                );
                            }
                        }
                        diags.push(
                            Report::build(ReportKind::Custom("Help", Color::Blue), (), 0)
                                .with_message("...which creates a cycle")
                                .with_label(
                                    Label::new(t.span).with_color(Color::Blue).with_message(
                                        format!(
                                            "references `{}`, creating a cycle",
                                            i.ident.as_str()
                                        ),
                                    ),
                                )
                                .with_note("recursive `type` aliases are not allowed")
                                .finish(),
                        );
                        for diag in diags {
                            // TODO: bring back EnsembleDiagnostic
                            // TODO: make this not reference the usage span
                            drcx.report_syncd(diag);
                        }
                        // TODO: error this
                        return Err(());
                    } else {
                        tcx.ty_aliases.push_back((*id, t.span));
                    }
                    // recreate the Ty with our span so we don't point
                    // unnecessarily to the expanded alias
                    ast::Ty::new(
                        gcx,
                        gcx.arenas.core.ty(surf_ty_to_core(gcx, tcx, aliased)?).kind,
                        t.span,
                    )
                }
                Res::TyVar(id) => {
                    let pos = tcx
                        .tys
                        .iter()
                        .enumerate()
                        .find_map(|(i, x)| if x == id { Some(i) } else { None })
                        .unwrap();
                    ast::Ty::new(gcx, CT::Var(*id, DeBruijnIdx::from(pos)), t.span)
                }
                _ => unreachable!("{res:#?}"),
            }
        }
        ST::Forall(_, b) => ast::Ty::new(
            gcx,
            CT::Forall(t.id, surf_ty_to_core(gcx, tcx.bind_ty(gcx, t.id), b)?),
            t.span,
        ),
        ST::Arrow(a, b) => ast::Ty::new(
            gcx,
            CT::Arrow(
                surf_ty_to_core(gcx, tcx.clone(), a)?,
                surf_ty_to_core(gcx, tcx, b)?,
            ),
            t.span,
        ),
        ST::Err => panic!("ill-formed type"),
    })
}

// TODO: remove this
#[inline]
pub fn unify_check(
    gcx: &GlobalCtxt,
    tcx: TypeckCtxt,
    vt: Id<VTy>,
    vu: Id<VTy>,
) -> Result<(), UnifyError> {
    unify::unify(gcx, tcx.lvl, vt, vu)
}

pub fn check(
    gcx: &GlobalCtxt,
    tcx: TypeckCtxt,
    ie: Id<surf::Expr>,
    it: Id<VTy>,
    type_expectation: TypeExpectation,
) -> Result<Id<ast::Expr>, ()> {
    use ast::ExprKind as CE;
    use ast::TyKind as CT;
    use surf::ExprKind as SE;
    use VTyKind as VT;
    let it = force(gcx, it);

    // {
    //     let mut w = Vec::new();
    //     let doc = crate::ast::pretty::pp_expr(0, gcx, ie);
    //     doc.render(80, &mut w).unwrap();

    //     let mut w2 = Vec::new();
    //     let expected = quote_ty(gcx, tcx.lvl, it);
    //     let doc = crate::typeck::pretty::pp_ty(0, gcx, expected);
    //     doc.render(80, &mut w2).unwrap();

    //     println!(
    //         "\n{tcx:?}\ncheck {} <= {}",
    //         String::from_utf8(w).unwrap(),
    //         String::from_utf8(w2).unwrap()
    //     );
    // }
    let t = gcx.arenas.tyck.vty(it);
    let e = gcx.arenas.ast.expr(ie);
    Ok(match (e.kind, t.kind) {
        (_, VT::Forall(x, a)) => {
            let a = apply_ty_closure(gcx, a, VTy::rigid(gcx, x, tcx.lvl));
            let e1 = check(gcx, tcx.bind_ty(gcx, x), ie, a, type_expectation)?;
            ast::Expr::new(gcx, CE::TyAbs(x, e1), e.span)
        }

        (SE::Lambda(_, e1), VT::Arrow(a, b)) => {
            let e1 = check(gcx, tcx.bind_val(e.id, a), e1, b, type_expectation)?;
            ast::Expr::new(gcx, CE::Lam(e.id, e1), e.span)
        }
        (SE::Let(_, Recursive::NotRecursive, None, e1, e2), _) => {
            let (e1, vt_e1) = infer(gcx, tcx.clone(), e1)?;
            let e2 = check(
                gcx,
                tcx.clone().bind_val(e.id, vt_e1),
                e2,
                it,
                type_expectation,
            )?;
            let t_e1 = quote_ty(gcx, tcx.lvl, vt_e1);

            ast::Expr::new(gcx, CE::Let(e.id, t_e1, e1, e2), e.span)
        }
        (SE::Let(_, Recursive::NotRecursive, Some(t_e1), e1, e2), _) => {
            let t_e1 = surf_ty_to_core(gcx, tcx.clone(), t_e1)?;
            let vt_e1 = eval_ty(gcx, tcx.env.clone(), t_e1);
            let e1 = check(
                gcx,
                tcx.clone(),
                e1,
                vt_e1,
                TypeExpectation::Definition(gcx.arenas.core.ty(t_e1).span),
            )?;
            let e2 = check(
                gcx,
                tcx.clone().bind_val(e.id, vt_e1),
                e2,
                it,
                type_expectation,
            )?;

            ast::Expr::new(gcx, CE::Let(e.id, t_e1, e1, e2), e.span)
        }
        (_, _) => {
            let (e, inferred) = infer_and_inst(gcx, tcx.clone(), ie)?;

            if let Err(err) = unify_check(gcx, tcx.clone(), it, inferred) {
                let mut w = Vec::new();
                let inferred = quote_ty(gcx, tcx.lvl, inferred);
                let doc = crate::typeck::pretty::pp_ty(0, gcx, tcx.lvl, tcx.env.clone(), inferred);
                doc.render(80, &mut w).unwrap();
                let inferred_s = String::from_utf8(w).unwrap();

                let mut w = Vec::new();
                let expected = quote_ty(gcx, tcx.lvl, it);
                let doc = crate::typeck::pretty::pp_ty(0, gcx, tcx.lvl, tcx.env.clone(), expected);
                doc.render(80, &mut w).unwrap();
                let expected_s = String::from_utf8(w).unwrap();

                let span = gcx.arenas.core.expr(e).span;
                let report = Report::build(ReportKind::Error, (), span.lo() as usize)
                    .with_message("mismatched types")
                    .with_label(
                        Label::new(span)
                            .with_color(Color::Red)
                            .with_message(format!("found type {inferred_s}"))
                            .with_order(0),
                    );

                let mut report = match type_expectation {
                    TypeExpectation::Definition(span) => report.with_label(
                        Label::new(span)
                            .with_color(Color::Blue)
                            .with_message(format!("expected type {expected_s}"))
                            .with_order(1),
                    ),
                    TypeExpectation::FunctionApp(span, f_span) => report
                        .with_label(
                            Label::new(span)
                                .with_color(Color::Blue)
                                .with_message(format!(
                                    "this function expected argument type {expected_s}"
                                ))
                                .with_order(1),
                        )
                        .with_label(
                            Label::new(f_span)
                                .with_color(Color::Green)
                                .with_message("argument type defined here"),
                        ),
                };

                match err {
                    UnifyError::Occurs => {
                        report.set_message("occurs check failed: cannot create recursive type")
                    }
                    UnifyError::Scope(id, _) => {
                        report
                            .set_message("could not match types: type variable would escape scope");
                        report.set_help("try adding a type annotation with a `forall` quantifier");
                        report.add_label(
                            Label::new(
                                gcx.arenas
                                    .ast
                                    .get_node_by_id(id)
                                    .unwrap()
                                    .span(gcx)
                                    .with_hi(
                                        gcx.arenas
                                            .ast
                                            .get_node_by_id(id)
                                            .unwrap()
                                            .ident(gcx)
                                            .unwrap()
                                            .span
                                            .hi(),
                                    )
                                    .into(),
                            )
                            .with_color(Color::Blue)
                            .with_message("type variable defined here was not in scope"),
                        );
                    }
                    UnifyError::SpineMismatch => {}
                    UnifyError::RigidMismatch => {}
                }
                let report = report.finish();
                gcx.drcx.borrow_mut().report_syncd(report);

                if let CT::Meta(mv, _) | CT::InsertedMeta(mv) = gcx.arenas.core.ty(inferred).kind {
                    let mv = mv.0.borrow();
                    let report = Report::build(
                        ReportKind::Custom("Help", Color::Blue),
                        (),
                        mv.1.span.lo() as usize,
                    )
                    .with_message(format!(
                        "{} was a type hole, generated from this expression",
                        mv.1.name.as_str()
                    ))
                    .with_label(Label::new(mv.1.span).with_color(Color::Blue))
                    .finish();
                    gcx.drcx.borrow_mut().report_syncd(report);
                }

                if let CT::Meta(mv, _) | CT::InsertedMeta(mv) = gcx.arenas.core.ty(expected).kind {
                    let mv = mv.0.borrow();
                    let report = Report::build(
                        ReportKind::Custom("Help", Color::Blue),
                        (),
                        mv.1.span.lo() as usize,
                    )
                    .with_message(format!(
                        "{} was a type hole, generated from this expression",
                        mv.1.name.as_str()
                    ))
                    .with_label(Label::new(mv.1.span).with_color(Color::Blue))
                    .finish();
                    gcx.drcx.borrow_mut().report_syncd(report);
                }

                return Err(());
            }
            e
        }
    })
}

pub enum TypeExpectation {
    Definition(Span),
    FunctionApp(Span, Span),
}

pub fn infer(
    gcx: &GlobalCtxt,
    tcx: TypeckCtxt,
    ie: Id<surf::Expr>,
) -> Result<(Id<ast::Expr>, Id<VTy>), ()> {
    // {
    //     let mut w = Vec::new();
    //     let doc = crate::ast::pretty::pp_expr(0, gcx, ie);
    //     doc.render(80, &mut w).unwrap();

    //     println!("\n{tcx:?}\ninfer {}", String::from_utf8(w).unwrap(),);
    // }
    use ast::ExprKind as CE;
    use ast::TyKind as CT;
    use surf::ExprKind as SE;
    use VTyKind as VT;
    let e = gcx.arenas.ast.expr(ie);
    Ok(match e.kind {
        SE::Unit => (
            ast::Expr::new(gcx, CE::Unit, e.span),
            VTy::new(gcx, VT::Unit, e.span),
        ),
        SE::Name(Ident { symbol, span }) => {
            if symbol.as_str() == "_" {
                let ma = fresh_meta(
                    gcx,
                    tcx.lvl,
                    Symbol::intern_static("?'_"),
                    e.span,
                    Span((u32::MAX..u32::MAX).into()),
                );

                return Ok((
                    ast::Expr::new(
                        gcx,
                        CE::Err(ExprDeferredError::Discarded(ma, tcx.clone())),
                        Span(span),
                    ),
                    eval_ty(gcx, tcx.env, ma),
                ));
            }

            let res_data = gcx.arenas.ast.res_data.borrow();
            let res = *res_data.get_by_id(e.id).unwrap();
            drop(res_data);
            match &res {
                Res::PrimFunc(_) => todo!(),
                Res::Defn(DefnKind::EnumConstructor(branch), id) => {
                    let Some(Node::Item(i)) = gcx.arenas.ast.get_node_by_id(*id) else {
                        unreachable!()
                    };
                    let ItemKind::Enum(cons) = gcx.arenas.ast.item(i).kind else {
                        unreachable!()
                    };

                    let (_, branch_tys) = cons.get(*branch).unwrap();
                    let branch_tys = branch_tys
                        .into_iter()
                        .map(|t| -> Result<_, _> {
                            Ok(eval_ty(
                                gcx,
                                im::Vector::new(),
                                surf_ty_to_core(gcx, TypeckCtxt::default(), *t)?,
                            ))
                        })
                        .collect::<Result<Vec<_>, _>>()?;

                    (
                        ast::Expr::new(gcx, CE::EnumConstructor(*id, *branch), e.span),
                        if branch_tys.is_empty() {
                            // TODO: branch spans
                            VTy::new(gcx, VTyKind::Enum(*id), Span((u32::MAX..u32::MAX).into()))
                        } else {
                            branch_tys.into_iter().rfold(
                                VTy::new(
                                    gcx,
                                    VTyKind::Enum(*id),
                                    Span((u32::MAX..u32::MAX).into()),
                                ),
                                |acc, x| {
                                    VTy::new(
                                        gcx,
                                        VTyKind::Arrow(x, acc),
                                        Span((u32::MAX..u32::MAX).into()),
                                    )
                                },
                            )
                        },
                    )
                }
                Res::Defn(DefnKind::EnumRecursor, id) => {
                    let Some(Node::Item(i)) = gcx.arenas.ast.get_node_by_id(*id) else {
                        unreachable!()
                    };
                    let ItemKind::Enum(cons) = gcx.arenas.ast.item(i).kind else {
                        unreachable!()
                    };

                    let dummy_span = Span((u32::MAX..u32::MAX).into());

                    let id = *id;

                    let this = ast::Ty::new(gcx, CT::Enum(id), dummy_span);
                    let var_id = Ident {
                        symbol: Symbol::intern_static("'a"),
                        span: *dummy_span,
                    };
                    // HACK: i hate this, use IR IDs
                    let syn_id = gcx
                        .arenas
                        .ast
                        .syn(surf::Synthetic::new(gcx, dummy_span, Some(var_id)))
                        .id;

                    let var =
                        ast::Ty::new(gcx, CT::Var(syn_id, DeBruijnIdx::from(0usize)), dummy_span);

                    let t = cons
                        .into_iter()
                        .map(|(_, t)| -> Result<_, _> {
                            Ok(t.into_iter()
                                .map(|x| surf_ty_to_core(gcx, TypeckCtxt::default(), x))
                                .collect::<Result<Vec<_>, _>>()?
                                .into_iter()
                                .rfold(var, |acc, x| {
                                    ast::Ty::new(gcx, CT::Arrow(x, acc), dummy_span)
                                }))
                        })
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .rfold(var, |acc, x| {
                            ast::Ty::new(gcx, CT::Arrow(x, acc), dummy_span)
                        });

                    let t = VTy::new(
                        gcx,
                        VT::Forall(
                            syn_id,
                            Closure(
                                im::Vector::new(),
                                ast::Ty::new(gcx, CT::Arrow(this, t), dummy_span),
                            ),
                        ),
                        dummy_span,
                    );

                    (ast::Expr::new(gcx, CE::EnumRecursor(id), e.span), t)
                }
                Res::Defn(DefnKind::Value, id) => {
                    let Some(Node::Item(i)) = gcx.arenas.ast.get_node_by_id(*id) else {
                        unreachable!()
                    };
                    let ItemKind::Value(t, _) = gcx.arenas.ast.item(i).kind else {
                        unreachable!()
                    };
                    // TODO: memoize the surf_ty_to_core operation
                    (
                        ast::Expr::new(gcx, CE::Free(*id), e.span),
                        eval_ty(
                            gcx,
                            im::Vector::new(),
                            surf_ty_to_core(gcx, TypeckCtxt::default(), t)?,
                        ),
                    )
                }
                Res::Local(id) => {
                    let (pos, vt) = tcx
                        .vals
                        .iter()
                        .enumerate()
                        .find_map(|(i, (x, t))| if x == id { Some((i, t)) } else { None })
                        .unwrap();
                    (
                        ast::Expr::new(gcx, CE::Var(*id, DeBruijnIdx::from(pos)), e.span),
                        *vt,
                    )
                }
                _ => unreachable!(),
            }
        }
        SE::Apply(t, u) => {
            let (t, tty) = infer(gcx, tcx.clone(), t)?;
            let tty = force(gcx, tty);
            let (a, b, mv) = match gcx.arenas.tyck.vty(tty).kind {
                VT::Arrow(a, b) => (a, b, im::Vector::new()),
                _ => {
                    let ma = fresh_meta(
                        gcx,
                        tcx.lvl,
                        Symbol::intern_static("?arg"),
                        e.span,
                        Span((u32::MAX..u32::MAX).into()),
                    );

                    let mb = fresh_meta(
                        gcx,
                        tcx.lvl,
                        Symbol::intern_static("?res"),
                        e.span,
                        Span((u32::MAX..u32::MAX).into()),
                    );

                    let a = eval_ty(gcx, tcx.env.clone(), ma);
                    let b = eval_ty(gcx, tcx.env.clone(), mb);

                    let (tty, mv) = eagerly_instantiate(gcx, tcx.clone(), tty, e.span);
                    if unify_check(
                        gcx,
                        tcx.clone(),
                        VTy::new(gcx, VT::Arrow(a, b), Span((u32::MAX..u32::MAX).into())),
                        tty,
                    )
                    .is_err()
                    {
                        let mut w = Vec::new();
                        let inferred = quote_ty(gcx, tcx.lvl, tty);
                        let doc = crate::typeck::pretty::pp_ty(
                            0,
                            gcx,
                            tcx.lvl,
                            tcx.env.clone(),
                            inferred,
                        );
                        doc.render(80, &mut w).unwrap();
                        let inferred = String::from_utf8(w).unwrap();

                        let span = gcx.arenas.core.expr(t).span;
                        let report = Report::build(ReportKind::Error, (), span.lo() as usize)
                            .with_message("mismatched types")
                            .with_label(
                                Label::new(span)
                                    .with_color(Color::Red)
                                    .with_message(format!("found type {inferred}"))
                                    .with_order(1),
                            )
                            .with_label(
                                Label::new(e.span)
                                    .with_color(Color::Blue)
                                    .with_message("expected function due to this application")
                                    .with_order(0),
                            )
                            .with_config(Config::default().with_label_attach(LabelAttach::End))
                            .finish();
                        gcx.drcx.borrow_mut().report_syncd(report);

                        return Err(());
                    }
                    (a, b, mv)
                }
            };
            let u = check(
                gcx,
                tcx,
                u,
                a,
                TypeExpectation::FunctionApp(
                    gcx.arenas.core.expr(t).span,
                    gcx.arenas.tyck.vty(a).span,
                ),
            )?;
            (
                ast::Expr::new(
                    gcx,
                    CE::App(
                        mv.into_iter()
                            .fold(t, |acc, x| ast::Expr::new(gcx, CE::TyApp(acc, x), e.span)),
                        u,
                    ),
                    e.span,
                ),
                b,
            )
        }
        SE::Lambda(x, body) => {
            let ma = fresh_meta(
                gcx,
                tcx.lvl,
                Symbol::intern(&format!("?{}", x.as_str())),
                e.span,
                Span((u32::MAX..u32::MAX).into()),
            );
            let a = eval_ty(gcx, tcx.env.clone(), ma);

            let (expr, b) = infer(gcx, tcx.bind_val(e.id, a), body)?;
            (
                ast::Expr::new(gcx, CE::Lam(e.id, expr), e.span),
                VTy::new(gcx, VT::Arrow(a, b), Span((u32::MAX..u32::MAX).into())),
            )
        }
        SE::Let(_, Recursive::NotRecursive, None, e1, e2) => {
            let (e1, vt_e1) = infer(gcx, tcx.clone(), e1)?;
            let (e2, vt_e2) = infer(gcx, tcx.clone().bind_val(e.id, vt_e1), e2)?;
            let t_e1 = quote_ty(gcx, tcx.lvl, vt_e1);

            (
                ast::Expr::new(gcx, CE::Let(e.id, t_e1, e1, e2), e.span),
                vt_e2,
            )
        }
        SE::Let(_, Recursive::NotRecursive, Some(t_e1), e1, e2) => {
            let t_e1 = surf_ty_to_core(gcx, tcx.clone(), t_e1)?;
            let vt_e1 = eval_ty(gcx, tcx.env.clone(), t_e1);
            let e1 = check(
                gcx,
                tcx.clone(),
                e1,
                vt_e1,
                TypeExpectation::Definition(gcx.arenas.core.ty(t_e1).span),
            )?;
            let (e2, vt_e2) = infer(gcx, tcx.clone().bind_val(e.id, vt_e1), e2)?;

            (
                ast::Expr::new(gcx, CE::Let(e.id, t_e1, e1, e2), e.span),
                vt_e2,
            )
        }
        _ => todo!("{:#?}", e),
    })
}

pub fn infer_and_inst(
    gcx: &GlobalCtxt,
    tcx: TypeckCtxt,
    ie: Id<surf::Expr>,
) -> Result<(Id<ast::Expr>, Id<VTy>), ()> {
    let (e, t) = infer(gcx, tcx.clone(), ie)?;
    let sp = gcx.arenas.core.expr(e).span;
    let (t, mv) = eagerly_instantiate(gcx, tcx, t, sp);

    Ok((
        mv.into_iter().fold(e, |acc, x| {
            ast::Expr::new(gcx, ast::ExprKind::TyApp(acc, x), sp)
        }),
        t,
    ))
}

pub fn eagerly_instantiate(
    gcx: &GlobalCtxt,
    tcx: TypeckCtxt,
    it: Id<VTy>,
    sp: Span,
) -> (Id<VTy>, im::Vector<Id<ast::Ty>>) {
    let it = force(gcx, it);
    let t = gcx.arenas.tyck.vty(it);
    match t.kind {
        VTyKind::Forall(x, c) => {
            let mv = fresh_meta(
                gcx,
                tcx.lvl,
                Symbol::intern(&format!(
                    "?{}",
                    gcx.arenas
                        .ast
                        .get_node_by_id(x)
                        .unwrap()
                        .ident(gcx)
                        .unwrap()
                        .as_str()
                )),
                sp,
                t.span,
            );
            let m = eval_ty(gcx, tcx.env.clone(), mv);
            let c = apply_ty_closure(gcx, c, m);
            // TODO: tail recursive
            let (t, mut mvs) = eagerly_instantiate(gcx, tcx, c, sp);
            mvs.push_back(mv);
            (t, mvs)
        }
        _ => (it, im::Vector::new()),
    }
}

fn fresh_meta(
    gcx: &GlobalCtxt,
    level: DeBruijnLvl,
    name: Symbol,
    span: Span,
    ty_span: Span,
) -> Id<ast::Ty> {
    let m = MetaVar(Rc::new(RefCell::new((
        MetaEntry::Unsolved,
        MetaInfo { level, name, span },
    ))));
    ast::Ty::new(gcx, ast::TyKind::InsertedMeta(m), ty_span)
}
