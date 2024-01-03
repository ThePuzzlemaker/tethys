use std::{cell::RefCell, rc::Rc};

use ariadne::{Color, Config, Label, LabelAttach, Report, ReportKind};
use calypso_base::symbol::{Ident, Symbol};
use id_arena::Id;

pub use crate::ast as surf;
use crate::{
    ast::{AstId, BinOpKind, DefnKind, ItemKind, Node, PrimTy, Recursive, Res},
    ctxt::GlobalCtxt,
    parse::Span,
    typeck::{
        ast::{DeBruijnIdx, ExprDeferredError},
        norm::{quote_ty, FlexTuple},
    },
};

use self::{
    ast::{CoreAstId, DeBruijnLvl, MetaEntry, MetaInfo, MetaVar},
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
    vals: im::Vector<(CoreAstId, Id<VTy>)>,
    tys: im::Vector<CoreAstId>,
    ty_aliases: im::Vector<(AstId, Span)>,
    generic_params: im::Vector<(AstId, usize, Id<ast::Ty>)>,
}

impl Default for TypeckCtxt {
    fn default() -> Self {
        Self {
            env: Default::default(),
            lvl: DeBruijnLvl::from(0usize),
            vals: Default::default(),
            tys: Default::default(),
            ty_aliases: Default::default(),
            generic_params: Default::default(),
        }
    }
}

impl TypeckCtxt {
    pub fn bind_ty(mut self, gcx: &GlobalCtxt, id: CoreAstId) -> Self {
        self.env
            .push_back(VTy::rigid(gcx, gcx.arenas.core.next_id(), id, self.lvl));
        self.lvl += 1;
        self.tys.push_back(id);
        self
    }

    pub fn bind_val(mut self, id: CoreAstId, ty: Id<VTy>) -> Self {
        self.vals.push_back((id, ty));
        self
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct ElabError;

fn lower_ty(gcx: &GlobalCtxt, id: AstId, f: impl FnOnce(CoreAstId) -> Id<ast::Ty>) -> Id<ast::Ty> {
    let id = gcx.arenas.core.lower_id(id);
    gcx.arenas
        .core
        .get_node_by_id(id)
        .map(|x| match x {
            ast::Node::Ty(t) => t,
            _ => panic!(),
        })
        .unwrap_or_else(|| f(id))
}

fn try_lower_ty(
    gcx: &GlobalCtxt,
    id: AstId,
    f: impl FnOnce(CoreAstId) -> Result<Id<ast::Ty>, ElabError>,
) -> Result<Id<ast::Ty>, ElabError> {
    let id = gcx.arenas.core.lower_id(id);
    gcx.arenas
        .core
        .get_node_by_id(id)
        .map(|x| match x {
            ast::Node::Ty(t) => Ok(t),
            _ => panic!(),
        })
        .unwrap_or_else(|| f(id))
}

pub fn surf_ty_to_core(
    gcx: &GlobalCtxt,
    mut tcx: TypeckCtxt,
    t: Id<surf::Ty>,
) -> Result<Id<ast::Ty>, ElabError> {
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
        // TODO: make proper use of lower_ty and try_lower_ty so we
        // don't recurse if we don't need to
        ST::Unit => lower_ty(gcx, t.id, |id| ast::Ty::new(gcx, id, CT::Unit, t.span)),
        ST::Tuple(tys) => try_lower_ty(gcx, t.id, |cid| {
            let tys = tys
                .into_iter()
                .map(|x| surf_ty_to_core(gcx, tcx.clone(), x))
                .collect::<Result<im::Vector<_>, _>>()?;

            Ok(ast::Ty::new(gcx, cid, CT::Tuple(tys), t.span))
        })?,
        ST::Data(Ident { symbol, span }, spine) => {
            if symbol.as_str() == "_" {
                let report = Report::build(ReportKind::Error, (), span.lo() as usize)
                    .with_message("invalid identifier `_`")
                    .with_label(
                        Label::new(Span(span))
                            .with_color(Color::Red)
                            .with_message("`_` is not a valid identifier here"),
                    )
                    .with_note("`_` is only allowed inside a generic parameter list")
                    .finish();
                gcx.drcx.borrow_mut().report_syncd(report);

                return Err(ElabError);
            }

            let res_data = gcx.arenas.ast.res_data.borrow();
            let res = res_data.get_by_id(t.id).unwrap();
            match res {
                Res::Defn(DefnKind::Enum, id) => {
                    let Node::Item(i) = gcx.arenas.ast.get_node_by_id(*id).unwrap() else {
                        unreachable!()
                    };
                    let ItemKind::Enum(generics, _, generics_list_span) =
                        gcx.arenas.ast.item(i).kind
                    else {
                        unreachable!()
                    };

                    if generics.is_empty() {
                        let report = Report::build(ReportKind::Error, (), t.span.lo() as usize)
                            .with_message("enum provided generic parameters but did not have any")
                            .with_label(
                                Label::new(t.span)
                                    .with_color(Color::Red)
                                    .with_message("generic parameters provided here"),
                            )
                            .with_label(
                                Label::new(
                                    gcx.arenas
                                        .ast
                                        .item(i)
                                        .span
                                        .with_hi(generics_list_span.hi())
                                        .into(),
                                )
                                .with_message("enum defined here, with no generic parameters")
                                .with_color(Color::Blue),
                            )
                            .with_help(format!(
                                "remove the generic parameters: `{}`",
                                gcx.arenas.ast.item(i).ident.as_str(),
                            ));

                        gcx.drcx.borrow_mut().report_syncd(report.finish());

                        return Ok(lower_ty(gcx, t.id, |cid| {
                            ast::Ty::new(gcx, cid, CT::Enum(*id, im::Vector::new()), t.span)
                        }));
                    }

                    let mut spine = spine
                        .clone()
                        .into_iter()
                        .map(|x| surf_ty_to_core(gcx, tcx.clone(), x))
                        .collect::<Result<im::Vector<_>, _>>()?;
                    if spine.len() > generics.len() {
                        let spine_docs = spine.clone().into_iter().map(|x| {
                            let mut w = Vec::new();
                            let doc =
                                crate::typeck::pretty::pp_ty(0, gcx, tcx.lvl, tcx.env.clone(), x);
                            doc.render(usize::MAX, &mut w).unwrap();
                            String::from_utf8(w).unwrap()
                        });

                        let plural = if generics.len() != 1 { "s" } else { "" };
                        let an = if spine.len() - generics.len() == 1 {
                            "an "
                        } else {
                            ""
                        };
                        let provided = spine.len();
                        let provided_plural = if provided != 1 { "s" } else { "" };
                        let excess_plural = if spine.len() - generics.len() != 1 {
                            "s"
                        } else {
                            ""
                        };

                        spine.truncate(generics.len());

                        let report = Report::build(ReportKind::Error, (), t.span.lo() as usize)
                            .with_message(format!(
                                "enum provided {an}extra generic parameter{excess_plural}"
                            ))
                            .with_label(Label::new(t.span).with_color(Color::Red).with_message(
                                format!("{provided} generic parameter{provided_plural} provided"),
                            ))
                            .with_label(
                                Label::new(
                                    gcx.arenas
                                        .ast
                                        .item(i)
                                        .span
                                        .with_hi(generics_list_span.hi())
                                        .into(),
                                )
                                .with_message(format!(
                                    "enum defined here, with {} generic parameter{plural}",
                                    generics.len(),
                                ))
                                .with_color(Color::Blue),
                            )
                            .with_help(format!(
                                // TODO: get overall type and insert into it
                                "remove the extra generic parameters: `{}[{}]`",
                                gcx.arenas.ast.item(i).ident.as_str(),
                                spine_docs
                                    .take(generics.len())
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            ));

                        gcx.drcx.borrow_mut().report_syncd(report.finish());
                    } else if spine.len() != generics.len() {
                        let spine_docs = spine.clone().into_iter().map(|x| {
                            let mut w = Vec::new();
                            let doc =
                                crate::typeck::pretty::pp_ty(0, gcx, tcx.lvl, tcx.env.clone(), x);
                            doc.render(usize::MAX, &mut w).unwrap();
                            String::from_utf8(w).unwrap()
                        });

                        let plural = if generics.len() != 1 { "s" } else { "" };
                        let a = if generics.len() == 1 { "a " } else { "" };
                        let rest = generics.len() - spine.len();
                        let rest_plural = if rest != 1 { "s" } else { "" };

                        let report = Report::build(ReportKind::Error, (), t.span.lo() as usize)
                            .with_message(format!("enum required {a}generic parameter{plural}"))
                            .with_label(Label::new(t.span).with_color(Color::Red).with_message(
                                format!(
                                    "{rest} remaining generic parameter{rest_plural} not provided"
                                ),
                            ))
                            .with_label(
                                Label::new(
                                    gcx.arenas
                                        .ast
                                        .item(i)
                                        .span
                                        .with_hi(generics_list_span.hi())
                                        .into(),
                                )
                                .with_message(format!(
                                    "enum defined here, with {} generic parameter{plural}",
                                    generics.len(),
                                ))
                                .with_color(Color::Blue),
                            )
                            .with_help(format!(
                                // TODO: get overall type and insert into it
                                "if you wanted inferred parameters, try `{}[{}]`",
                                gcx.arenas.ast.item(i).ident.as_str(),
                                spine_docs
                                    .chain(
                                        std::iter::repeat(String::from("_"))
                                            .take(generics.len() - spine.len())
                                    )
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            ));

                        gcx.drcx.borrow_mut().report_syncd(report.finish());

                        for i in generics.iter().skip(spine.len()) {
                            let mv = fresh_meta(
                                gcx,
                                tcx.lvl,
                                gcx.arenas.core.next_id(),
                                Symbol::intern(&format!("?{}", i.as_str())),
                                t.span,
                                t.span,
                            );
                            spine.push_back(mv);
                        }
                    }

                    // Never memoize this, by creating a new type every time.
                    // This way generic params aren't fixed forever.
                    // TODO: find a way to *sometimes* memoize so we
                    // can have proper AstId->CoreAstId mappings
                    ast::Ty::new(gcx, gcx.arenas.core.next_id(), CT::Enum(*id, spine), t.span)
                }
                _ => {
                    todo!()
                }
            }
        }
        ST::Name(Ident { symbol, span }) => {
            if symbol.as_str() == "_" {
                return Ok(lower_ty(gcx, t.id, |cid| {
                    fresh_meta(
                        gcx,
                        tcx.lvl,
                        cid,
                        Symbol::intern_static("?_"),
                        Span(span),
                        Span(span),
                    )
                }));
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

                return Ok(lower_ty(gcx, t.id, |cid| {
                    fresh_meta(
                        gcx,
                        tcx.lvl,
                        cid,
                        Symbol::intern_static("?'_"),
                        Span(span),
                        Span(span),
                    )
                }));
            }

            let res_data = gcx.arenas.ast.res_data.borrow();
            let res = res_data.get_by_id(t.id).unwrap();
            match res {
                Res::PrimTy(prim) => lower_ty(gcx, t.id, |cid| {
                    ast::Ty::new(gcx, cid, CT::Primitive(*prim), t.span)
                }),
                Res::Generic(id, ix) => tcx
                    .generic_params
                    .iter()
                    .find_map(|(id1, ix1, t)| {
                        if id == id1 && ix == ix1 {
                            Some(*t)
                        } else {
                            None
                        }
                    })
                    .unwrap(),
                Res::Defn(DefnKind::Enum, id) => {
                    let Node::Item(i) = gcx.arenas.ast.get_node_by_id(*id).unwrap() else {
                        unreachable!()
                    };
                    let ItemKind::Enum(generics, _, generics_list_span) =
                        gcx.arenas.ast.item(i).kind
                    else {
                        unreachable!()
                    };

                    let mut vec = im::Vector::new();
                    if !generics.is_empty() {
                        let plural = if generics.len() != 1 { "s" } else { "" };
                        let a = if generics.len() == 1 { "a " } else { "" };

                        let report =
                            Report::build(ReportKind::Error, (), t.span.lo() as usize)
                                .with_message(format!("enum required {a}generic parameter{plural}"))
                                .with_label(Label::new(t.span).with_color(Color::Red).with_message(
                                    format!("generic parameter{plural} not provided"),
                                ))
                                .with_label(
                                    Label::new(
                                        gcx.arenas
                                            .ast
                                            .item(i)
                                            .span
                                            .with_hi(generics_list_span.hi())
                                            .into(),
                                    )
                                    .with_message(format!(
                                        "enum defined here, with {} generic parameter{plural}",
                                        generics.len(),
                                    ))
                                    .with_color(Color::Blue),
                                )
                                .with_help(format!(
                                    "if you wanted inferred parameters, try `{}[{}]`",
                                    gcx.arenas.ast.item(i).ident.as_str(),
                                    std::iter::repeat("_")
                                        .take(generics.len())
                                        .collect::<Vec<_>>()
                                        .join(", ")
                                ));

                        gcx.drcx.borrow_mut().report_syncd(report.finish());

                        for i in generics {
                            let mv = fresh_meta(
                                gcx,
                                tcx.lvl,
                                gcx.arenas.core.next_id(),
                                Symbol::intern(&format!("?{}", i.as_str())),
                                t.span,
                                t.span,
                            );
                            vec.push_back(mv);
                        }
                    };

                    lower_ty(gcx, t.id, |cid| {
                        ast::Ty::new(gcx, cid, CT::Enum(*id, vec), t.span)
                    })
                }
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
                        return Err(ElabError);
                    } else {
                        tcx.ty_aliases.push_back((*id, t.span));
                    }
                    // recreate the Ty with our span so we don't point
                    // unnecessarily to the expanded alias
                    try_lower_ty(gcx, t.id, |cid| {
                        Ok(ast::Ty::new(
                            gcx,
                            cid,
                            gcx.arenas.core.ty(surf_ty_to_core(gcx, tcx, aliased)?).kind,
                            t.span,
                        ))
                    })?
                }
                Res::TyVar(id) => {
                    let id = gcx.arenas.core.lower_id(*id);
                    let pos = tcx
                        .tys
                        .iter()
                        .enumerate()
                        .find_map(|(i, x)| if *x == id { Some(i) } else { None })
                        .unwrap();
                    lower_ty(gcx, t.id, |cid| {
                        ast::Ty::new(gcx, cid, CT::Var(id, DeBruijnIdx::from(pos)), t.span)
                    })
                }
                _ => unreachable!("{res:#?}"),
            }
        }
        ST::Forall(i, b) => try_lower_ty(gcx, t.id, |cid| {
            Ok(ast::Ty::new(
                gcx,
                cid,
                CT::Forall(cid, i, surf_ty_to_core(gcx, tcx.bind_ty(gcx, cid), b)?),
                t.span,
            ))
        })?,
        ST::Arrow(a, b) => try_lower_ty(gcx, t.id, |cid| {
            Ok(ast::Ty::new(
                gcx,
                cid,
                CT::Arrow(
                    surf_ty_to_core(gcx, tcx.clone(), a)?,
                    surf_ty_to_core(gcx, tcx, b)?,
                ),
                t.span,
            ))
        })?,
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

fn unify_error(
    gcx: &GlobalCtxt,
    tcx: TypeckCtxt,
    inferred: Id<VTy>,
    e: Id<ast::Expr>,
    it: Id<VTy>,
    type_expectation: TypeExpectation,
    err: UnifyError,
) -> Result<Id<ast::Expr>, ElabError> {
    use ast::TyKind as CT;
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
                .with_message(format!("found type `{inferred_s}`"))
                .with_order(0),
        );

    let mut report = match type_expectation {
        TypeExpectation::Definition(span) => report.with_label(
            Label::new(span)
                .with_color(Color::Blue)
                .with_message(format!("expected type `{expected_s}`"))
                .with_order(1),
        ),
        TypeExpectation::FunctionApp(span, f_span) => report
            .with_label(
                Label::new(span)
                    .with_color(Color::Blue)
                    .with_message(format!(
                        "this function expected argument type `{expected_s}`"
                    ))
                    .with_order(1),
            )
            .with_label(
                Label::new(f_span)
                    .with_color(Color::Green)
                    .with_message("argument type defined here"),
            ),
        TypeExpectation::BinaryOp(span, op_type) => report
            .with_label(
                Label::new(span)
                    .with_color(Color::Blue)
                    .with_message(format!("this operation had type `{op_type}`"))
                    .with_order(-1),
            )
            .with_config(Config::default().with_label_attach(LabelAttach::End)),
        TypeExpectation::IfCondition(if_span) => report.with_label(
            Label::new(if_span.with_hi(span.hi()).into())
                .with_color(Color::Blue)
                .with_message("expected type `Boolean` due to this `if`"),
        ),
        TypeExpectation::IfElse(span) => report
            .with_label(
                Label::new(span)
                    .with_color(Color::Blue)
                    .with_message(format!("expected type `{expected_s}`"))
                    .with_order(1),
            )
            .with_note("`if` branches must have the same type"),
        TypeExpectation::TupleProj(span, _) => report
            .with_label(
                Label::new(span)
                    .with_color(Color::Blue)
                    // TODO: defer this error
                    .with_message(format!(
                        "expected tuple `{expected_s}` due to this projection",
                    ))
                    .with_order(1),
            )
            .with_config(Config::default().with_label_attach(LabelAttach::End)),
    };

    match err {
        UnifyError::Occurs => {
            report.set_message("occurs check failed: cannot create recursive type")
        }
        UnifyError::Scope(id, _) => {
            report.set_message("could not match types: type variable would escape scope");
            report.set_help("try adding a type annotation with a `forall` quantifier");
            report.add_label(
                Label::new(
                    gcx.arenas
                        .core
                        .get_node_by_id(id)
                        .unwrap()
                        .span(gcx)
                        .with_hi(
                            gcx.arenas
                                .core
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

    Ok(e)
}

pub fn check(
    gcx: &GlobalCtxt,
    tcx: TypeckCtxt,
    ie: Id<surf::Expr>,
    it: Id<VTy>,
    type_expectation: TypeExpectation,
) -> Result<Id<ast::Expr>, ElabError> {
    use ast::ExprKind as CE;
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
        (_, VT::Forall(x, i, a)) => {
            let a = apply_ty_closure(
                gcx,
                a,
                VTy::rigid(gcx, gcx.arenas.core.next_id(), x, tcx.lvl),
            );
            let e1 = check(gcx, tcx.bind_ty(gcx, x), ie, a, type_expectation)?;
            ast::Expr::new(gcx, gcx.arenas.core.next_id(), CE::TyAbs(x, i, e1), e.span)
        }

        (SE::Lambda(i, e1), VT::Arrow(a, b)) => {
            let cid = gcx.arenas.core.lower_id(e.id);

            let e1 = check(gcx, tcx.bind_val(cid, a), e1, b, type_expectation)?;
            ast::Expr::new(gcx, cid, CE::Lam(cid, i, e1), e.span)
        }
        (SE::Let(i, Recursive::NotRecursive, None, e1, e2), _) => {
            let (e1, vt_e1) = infer(gcx, tcx.clone(), e1)?;
            let cid = gcx.arenas.core.lower_id(e.id);

            let e2 = check(
                gcx,
                tcx.clone().bind_val(cid, vt_e1),
                e2,
                it,
                type_expectation,
            )?;
            let t_e1 = quote_ty(gcx, tcx.lvl, vt_e1);

            ast::Expr::new(gcx, cid, CE::Let(cid, i, t_e1, e1, e2), e.span)
        }
        (SE::Let(i, Recursive::NotRecursive, Some(t_e1), e1, e2), _) => {
            let t_e1 = surf_ty_to_core(gcx, tcx.clone(), t_e1)?;
            let vt_e1 = eval_ty(gcx, tcx.env.clone(), t_e1);
            let cid = gcx.arenas.core.lower_id(e.id);

            let e1 = check(
                gcx,
                tcx.clone(),
                e1,
                vt_e1,
                TypeExpectation::Definition(gcx.arenas.core.ty(t_e1).span),
            )?;
            let e2 = check(
                gcx,
                tcx.clone().bind_val(cid, vt_e1),
                e2,
                it,
                type_expectation,
            )?;

            ast::Expr::new(gcx, cid, CE::Let(cid, i, t_e1, e1, e2), e.span)
        }

        (SE::TupleProj(expr, ix), _) => {
            let mvs = (0..=ix)
                .map(|i| {
                    if ix == i {
                        it
                    } else {
                        eval_ty(
                            gcx,
                            tcx.env.clone(),
                            fresh_meta(
                                gcx,
                                tcx.lvl,
                                gcx.arenas.core.next_id(),
                                Symbol::intern(&format!("?tuple_{i}")),
                                e.span,
                                Span((u32::MAX..u32::MAX).into()),
                            ),
                        )
                    }
                })
                .collect::<im::Vector<_>>();
            let vt_mvs = VTy::new(
                gcx,
                gcx.arenas.core.next_id(),
                VTyKind::TupleFlex(Rc::new(RefCell::new(FlexTuple::Flex(mvs.clone())))),
                Span((u32::MAX..u32::MAX).into()),
            );

            let (expr, vt_expr) = infer(gcx, tcx.clone(), expr)?;

            // doing it this way gives better errors than simply using
            // `check` above: working bottom-up rather than top-down
            // generally works better for tuples, to avoid giving
            // nasty `expected ((?tuple_0, Integer, ...), ...)` errors
            if let Err(err) = unify_check(gcx, tcx.clone(), vt_mvs, vt_expr) {
                unify_error(
                    gcx,
                    tcx,
                    vt_expr,
                    expr,
                    vt_mvs,
                    TypeExpectation::TupleProj(e.span, ix),
                    err,
                )?;
            }

            ast::Expr::new(
                gcx,
                gcx.arenas.core.lower_id(e.id),
                CE::TupleProj(expr, ix),
                e.span,
            )
        }
        (_, _) => {
            let (e, inferred) = infer_and_inst(gcx, tcx.clone(), ie)?;

            if let Err(err) = unify_check(gcx, tcx.clone(), it, inferred) {
                unify_error(gcx, tcx, inferred, e, it, type_expectation, err)?;
            }
            e
        }
    })
}

pub enum TypeExpectation {
    Definition(Span),
    FunctionApp(Span, Span),
    BinaryOp(Span, &'static str),
    IfCondition(Span),
    IfElse(Span),
    TupleProj(Span, u64),
}

pub fn infer(
    gcx: &GlobalCtxt,
    tcx: TypeckCtxt,
    ie: Id<surf::Expr>,
) -> Result<(Id<ast::Expr>, Id<VTy>), ElabError> {
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
            ast::Expr::new(gcx, gcx.arenas.core.lower_id(e.id), CE::Unit, e.span),
            VTy::new(gcx, gcx.arenas.core.next_id(), VT::Unit, e.span),
        ),
        SE::Name(Ident { symbol, span }) => {
            if symbol.as_str() == "_" {
                let ma = fresh_meta(
                    gcx,
                    tcx.lvl,
                    gcx.arenas.core.next_id(),
                    Symbol::intern_static("?'_"),
                    e.span,
                    Span((u32::MAX..u32::MAX).into()),
                );

                return Ok((
                    ast::Expr::new(
                        gcx,
                        gcx.arenas.core.lower_id(e.id),
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
                    let ItemKind::Enum(generics, cons, _) = gcx.arenas.ast.item(i).kind else {
                        unreachable!()
                    };

                    let dummy_span = Span((u32::MAX..u32::MAX).into());

                    let syn_ids = (0..generics.len())
                        .map(|_| gcx.arenas.core.next_id())
                        .collect::<Vec<_>>();
                    let len = syn_ids.len();
                    let vars = syn_ids
                        .iter()
                        .copied()
                        .enumerate()
                        .map(|(lvl, syn_id)| {
                            (
                                *id,
                                lvl,
                                ast::Ty::new(
                                    gcx,
                                    gcx.arenas.core.next_id(),
                                    CT::Var(syn_id, DeBruijnIdx::from(len - lvl - 1)),
                                    dummy_span,
                                ),
                            )
                        })
                        .collect::<im::Vector<_>>();

                    let (_, branch_tys) = cons.get(*branch).unwrap();
                    let branch_tys = branch_tys
                        .into_iter()
                        .map(|t| -> Result<_, _> {
                            let tcx = TypeckCtxt {
                                generic_params: vars.clone(),
                                ..TypeckCtxt::default()
                            };
                            surf_ty_to_core(gcx, tcx, *t)
                        })
                        .collect::<Result<Vec<_>, _>>()?;

                    let t = branch_tys.into_iter().rfold(
                        ast::Ty::new(
                            gcx,
                            gcx.arenas.core.next_id(),
                            CT::Enum(*id, vars.clone().into_iter().map(|(_, _, x)| x).collect()),
                            dummy_span,
                        ),
                        |acc, x| {
                            ast::Ty::new(
                                gcx,
                                gcx.arenas.core.next_id(),
                                CT::Arrow(x, acc),
                                dummy_span,
                            )
                        },
                    );

                    let t = syn_ids
                        .iter()
                        .copied()
                        .zip(generics.iter().rev())
                        .rfold(t, |acc, (x, i)| {
                            ast::Ty::new(gcx, x, CT::Forall(x, *i, acc), dummy_span)
                        });

                    let t = eval_ty(gcx, im::Vector::new(), t);
                    (
                        ast::Expr::new(
                            gcx,
                            gcx.arenas.core.next_id(),
                            CE::EnumConstructor(*id, *branch),
                            e.span,
                        ),
                        t,
                    )
                }
                Res::Defn(DefnKind::EnumRecursor, id) => {
                    let Some(Node::Item(i)) = gcx.arenas.ast.get_node_by_id(*id) else {
                        unreachable!()
                    };
                    let ItemKind::Enum(generics, cons, _) = gcx.arenas.ast.item(i).kind else {
                        unreachable!()
                    };

                    let _dummy_span = Span((u32::MAX..u32::MAX).into());

                    let id = *id;

                    let dummy_span = Span((u32::MAX..u32::MAX).into());

                    let syn_ids = generics
                        .iter()
                        .rev()
                        .map(|_| gcx.arenas.core.next_id())
                        .collect::<Vec<_>>();
                    let len = syn_ids.len() + 1;
                    let vars = syn_ids
                        .iter()
                        .copied()
                        .enumerate()
                        .map(|(lvl, syn_id)| {
                            (
                                id,
                                lvl,
                                ast::Ty::new(
                                    gcx,
                                    gcx.arenas.core.next_id(),
                                    CT::Var(syn_id, DeBruijnIdx::from(len - lvl - 1)),
                                    dummy_span,
                                ),
                            )
                        })
                        .collect::<im::Vector<_>>();

                    let this = ast::Ty::new(
                        gcx,
                        gcx.arenas.core.next_id(),
                        CT::Enum(id, vars.clone().into_iter().map(|(_, _, x)| x).collect()),
                        dummy_span,
                    );

                    let var_id = Ident {
                        symbol: Symbol::intern_static("'a"),
                        span: *dummy_span,
                    };
                    let syn_id = gcx.arenas.core.next_id();

                    let var = ast::Ty::new(
                        gcx,
                        gcx.arenas.core.next_id(),
                        CT::Var(syn_id, DeBruijnIdx::from(0usize)),
                        dummy_span,
                    );

                    let t = cons
                        .into_iter()
                        .map(|(_, t)| -> Result<_, _> {
                            Ok(t.into_iter()
                                .map(|x| {
                                    surf_ty_to_core(
                                        gcx,
                                        TypeckCtxt {
                                            generic_params: vars.clone(),
                                            ..TypeckCtxt::default()
                                        },
                                        x,
                                    )
                                })
                                .collect::<Result<Vec<_>, _>>()?
                                .into_iter()
                                .rfold(var, |acc, x| {
                                    ast::Ty::new(
                                        gcx,
                                        gcx.arenas.core.next_id(),
                                        CT::Arrow(x, acc),
                                        dummy_span,
                                    )
                                }))
                        })
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .rfold(var, |acc, x| {
                            ast::Ty::new(
                                gcx,
                                gcx.arenas.core.next_id(),
                                CT::Arrow(x, acc),
                                dummy_span,
                            )
                        });

                    let t = ast::Ty::new(
                        gcx,
                        syn_id,
                        CT::Forall(
                            syn_id,
                            var_id,
                            ast::Ty::new(
                                gcx,
                                gcx.arenas.core.next_id(),
                                CT::Arrow(this, t),
                                dummy_span,
                            ),
                        ),
                        dummy_span,
                    );

                    (
                        ast::Expr::new(
                            gcx,
                            gcx.arenas.core.lower_id(e.id),
                            CE::EnumRecursor(id),
                            e.span,
                        ),
                        eval_ty(
                            gcx,
                            im::Vector::new(),
                            syn_ids
                                .iter()
                                .copied()
                                .zip(generics.iter().rev().copied())
                                .rfold(t, |acc, (x, i)| {
                                    ast::Ty::new(gcx, x, CT::Forall(x, i, acc), dummy_span)
                                }),
                        ),
                    )
                }
                Res::Defn(DefnKind::Value, id) => {
                    let Some(Node::Item(i)) = gcx.arenas.ast.get_node_by_id(*id) else {
                        unreachable!()
                    };
                    let ItemKind::Value(t, _) = gcx.arenas.ast.item(i).kind else {
                        unreachable!()
                    };
                    (
                        ast::Expr::new(gcx, gcx.arenas.core.lower_id(e.id), CE::Free(*id), e.span),
                        eval_ty(
                            gcx,
                            im::Vector::new(),
                            surf_ty_to_core(gcx, TypeckCtxt::default(), t)?,
                        ),
                    )
                }
                Res::Local(id) => {
                    let id = gcx.arenas.core.lower_id(*id);
                    let (pos, vt) = tcx
                        .vals
                        .iter()
                        .rev()
                        .enumerate()
                        .find_map(|(i, (x, t))| if *x == id { Some((i, t)) } else { None })
                        .unwrap();
                    (
                        ast::Expr::new(
                            gcx,
                            gcx.arenas.core.lower_id(e.id),
                            CE::Var(id, DeBruijnIdx::from(pos)),
                            e.span,
                        ),
                        *vt,
                    )
                }
                _ => unreachable!("{:#?}", res),
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
                        gcx.arenas.core.next_id(),
                        Symbol::intern_static("?arg"),
                        e.span,
                        Span((u32::MAX..u32::MAX).into()),
                    );

                    let mb = fresh_meta(
                        gcx,
                        tcx.lvl,
                        gcx.arenas.core.next_id(),
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
                        VTy::new(
                            gcx,
                            gcx.arenas.core.next_id(),
                            VT::Arrow(a, b),
                            Span((u32::MAX..u32::MAX).into()),
                        ),
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
                                    .with_message(format!("found type `{inferred}`"))
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

                        return Err(ElabError);
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
                    gcx.arenas.core.lower_id(e.id),
                    CE::App(
                        mv.into_iter().fold(t, |acc, x| {
                            ast::Expr::new(
                                gcx,
                                gcx.arenas.core.next_id(),
                                CE::TyApp(acc, x),
                                e.span,
                            )
                        }),
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
                gcx.arenas.core.next_id(),
                Symbol::intern(&format!("?{}", x.as_str())),
                e.span,
                Span((u32::MAX..u32::MAX).into()),
            );
            let a = eval_ty(gcx, tcx.env.clone(), ma);

            let cid = gcx.arenas.core.lower_id(e.id);
            let (expr, b) = infer(gcx, tcx.bind_val(cid, a), body)?;
            (
                ast::Expr::new(gcx, cid, CE::Lam(cid, x, expr), e.span),
                VTy::new(
                    gcx,
                    gcx.arenas.core.next_id(),
                    VT::Arrow(a, b),
                    Span((u32::MAX..u32::MAX).into()),
                ),
            )
        }
        SE::Let(x, Recursive::NotRecursive, None, e1, e2) => {
            let (e1, vt_e1) = infer(gcx, tcx.clone(), e1)?;
            let cid = gcx.arenas.core.lower_id(e.id);
            let (e2, vt_e2) = infer(gcx, tcx.clone().bind_val(cid, vt_e1), e2)?;
            let t_e1 = quote_ty(gcx, tcx.lvl, vt_e1);

            (
                ast::Expr::new(gcx, cid, CE::Let(cid, x, t_e1, e1, e2), e.span),
                vt_e2,
            )
        }
        SE::Let(x, Recursive::NotRecursive, Some(t_e1), e1, e2) => {
            let t_e1 = surf_ty_to_core(gcx, tcx.clone(), t_e1)?;
            let vt_e1 = eval_ty(gcx, tcx.env.clone(), t_e1);
            let cid = gcx.arenas.core.lower_id(e.id);
            let e1 = check(
                gcx,
                tcx.clone(),
                e1,
                vt_e1,
                TypeExpectation::Definition(gcx.arenas.core.ty(t_e1).span),
            )?;
            let (e2, vt_e2) = infer(gcx, tcx.clone().bind_val(cid, vt_e1), e2)?;

            (
                ast::Expr::new(gcx, cid, CE::Let(cid, x, t_e1, e1, e2), e.span),
                vt_e2,
            )
        }
        SE::Number(v) => (
            ast::Expr::new(gcx, gcx.arenas.core.lower_id(e.id), CE::Number(v), e.span),
            VTy::new(
                gcx,
                gcx.arenas.core.next_id(),
                VTyKind::Primitive(PrimTy::Integer),
                e.span,
            ),
        ),
        SE::BinaryOp {
            left,
            kind:
                kind @ (BinOpKind::Add
                | BinOpKind::Subtract
                | BinOpKind::Multiply
                | BinOpKind::Divide
                | BinOpKind::BitAnd
                | BinOpKind::BitOr
                | BinOpKind::BitXor
                | BinOpKind::BitShiftLeft
                | BinOpKind::BitShiftRight
                | BinOpKind::Power
                | BinOpKind::Modulo),
            right,
        } => {
            let int = VTy::new(
                gcx,
                gcx.arenas.core.next_id(),
                VTyKind::Primitive(PrimTy::Integer),
                e.span,
            );
            // TODO: internal op's span
            let left = check(
                gcx,
                tcx.clone(),
                left,
                int,
                TypeExpectation::BinaryOp(e.span, "Integer -> Integer -> Integer"),
            )?;

            let right = check(
                gcx,
                tcx.clone(),
                right,
                int,
                TypeExpectation::BinaryOp(e.span, "Integer -> Integer -> Integer"),
            )?;

            (
                ast::Expr::new(
                    gcx,
                    gcx.arenas.core.lower_id(e.id),
                    CE::BinaryOp { left, kind, right },
                    e.span,
                ),
                int,
            )
        }
        SE::BinaryOp {
            left,
            kind: kind @ (BinOpKind::LogicalOr | BinOpKind::LogicalAnd),
            right,
        } => {
            let bool_ty = VTy::new(
                gcx,
                gcx.arenas.core.next_id(),
                VTyKind::Primitive(PrimTy::Boolean),
                e.span,
            );
            // TODO: internal op's span
            let left = check(
                gcx,
                tcx.clone(),
                left,
                bool_ty,
                TypeExpectation::BinaryOp(e.span, "Boolean -> Boolean -> Boolean"),
            )?;

            let right = check(
                gcx,
                tcx.clone(),
                right,
                bool_ty,
                TypeExpectation::BinaryOp(e.span, "Boolean -> Boolean -> Boolean"),
            )?;

            (
                ast::Expr::new(
                    gcx,
                    gcx.arenas.core.lower_id(e.id),
                    CE::BinaryOp { left, kind, right },
                    e.span,
                ),
                bool_ty,
            )
        }
        SE::BinaryOp {
            left,
            kind:
                kind @ (BinOpKind::Equal
                | BinOpKind::NotEqual
                | BinOpKind::LessThan
                | BinOpKind::LessEqual
                | BinOpKind::GreaterThan
                | BinOpKind::GreaterEqual),
            right,
        } => {
            let int = VTy::new(
                gcx,
                gcx.arenas.core.next_id(),
                VTyKind::Primitive(PrimTy::Integer),
                e.span,
            );
            // TODO: internal op's span
            let left = check(
                gcx,
                tcx.clone(),
                left,
                int,
                TypeExpectation::BinaryOp(e.span, "Integer -> Integer -> Boolean"),
            )?;

            let right = check(
                gcx,
                tcx.clone(),
                right,
                int,
                TypeExpectation::BinaryOp(e.span, "Integer -> Integer -> Boolean"),
            )?;

            (
                ast::Expr::new(
                    gcx,
                    gcx.arenas.core.lower_id(e.id),
                    CE::BinaryOp { left, kind, right },
                    e.span,
                ),
                VTy::new(
                    gcx,
                    gcx.arenas.core.next_id(),
                    VTyKind::Primitive(PrimTy::Boolean),
                    e.span,
                ),
            )
        }
        SE::Boolean(v) => (
            ast::Expr::new(gcx, gcx.arenas.core.lower_id(e.id), CE::Boolean(v), e.span),
            VTy::new(
                gcx,
                gcx.arenas.core.next_id(),
                VTyKind::Primitive(PrimTy::Boolean),
                e.span,
            ),
        ),
        // TODO: if check rule
        SE::If(cond, then, then_else) => {
            let cond = check(
                gcx,
                tcx.clone(),
                cond,
                VTy::new(
                    gcx,
                    gcx.arenas.core.next_id(),
                    VTyKind::Primitive(PrimTy::Boolean),
                    Span((u32::MAX..u32::MAX).into()),
                ),
                TypeExpectation::IfCondition(e.span),
            )?;

            let (then, vt_then) = infer(gcx, tcx.clone(), then)?;
            let then_else = check(
                gcx,
                tcx.clone(),
                then_else,
                vt_then,
                TypeExpectation::IfElse(gcx.arenas.core.expr(then).span),
            )?;

            (
                ast::Expr::new(
                    gcx,
                    gcx.arenas.core.lower_id(e.id),
                    CE::If(cond, then, then_else),
                    e.span,
                ),
                vt_then,
            )
        }
        SE::Tuple(spine) => {
            let (spine, tys) = spine
                .into_iter()
                .map(|x| infer(gcx, tcx.clone(), x))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .unzip::<_, _, im::Vector<_>, im::Vector<_>>();

            // TODO: better tuple error messages
            (
                ast::Expr::new(
                    gcx,
                    gcx.arenas.core.lower_id(e.id),
                    CE::Tuple(spine),
                    e.span,
                ),
                VTy::new(
                    gcx,
                    gcx.arenas.core.next_id(),
                    VTyKind::Tuple(tys),
                    Span((u32::MAX..u32::MAX).into()),
                ),
            )
        }
        SE::TupleProj(expr, ix) => {
            let mvs = (0..=ix)
                .map(|ix| {
                    eval_ty(
                        gcx,
                        tcx.env.clone(),
                        fresh_meta(
                            gcx,
                            tcx.lvl,
                            gcx.arenas.core.next_id(),
                            Symbol::intern(&format!("?tuple_{ix}")),
                            e.span,
                            Span((u32::MAX..u32::MAX).into()),
                        ),
                    )
                })
                .collect::<im::Vector<_>>();
            let vt_mvs = VTy::new(
                gcx,
                gcx.arenas.core.next_id(),
                VTyKind::TupleFlex(Rc::new(RefCell::new(FlexTuple::Flex(mvs.clone())))),
                Span((u32::MAX..u32::MAX).into()),
            );

            let expr = check(
                gcx,
                tcx.clone(),
                expr,
                vt_mvs,
                TypeExpectation::TupleProj(e.span, ix),
            )?;

            (
                ast::Expr::new(
                    gcx,
                    gcx.arenas.core.lower_id(e.id),
                    CE::TupleProj(expr, ix),
                    e.span,
                ),
                *mvs.get(ix as usize).unwrap(),
            )
        }
        _ => todo!("{:#?}", e),
    })
}

pub fn infer_and_inst(
    gcx: &GlobalCtxt,
    tcx: TypeckCtxt,
    ie: Id<surf::Expr>,
) -> Result<(Id<ast::Expr>, Id<VTy>), ElabError> {
    let (e, t) = infer(gcx, tcx.clone(), ie)?;
    let sp = gcx.arenas.core.expr(e).span;
    let (t, mv) = eagerly_instantiate(gcx, tcx, t, sp);

    Ok((
        mv.into_iter().fold(e, |acc, x| {
            ast::Expr::new(
                gcx,
                gcx.arenas.core.next_id(),
                ast::ExprKind::TyApp(acc, x),
                sp,
            )
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
        VTyKind::Forall(_, i, c) => {
            let mv = fresh_meta(
                gcx,
                tcx.lvl,
                gcx.arenas.core.next_id(),
                Symbol::intern(&format!("?{}", i.as_str())),
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
    cid: CoreAstId,
    name: Symbol,
    span: Span,
    ty_span: Span,
) -> Id<ast::Ty> {
    let m = MetaVar(Rc::new(RefCell::new((
        MetaEntry::Unsolved,
        MetaInfo { level, name, span },
    ))));
    ast::Ty::new(gcx, cid, ast::TyKind::InsertedMeta(m), ty_span)
}
