#![warn(clippy::undocumented_unsafe_blocks)]
use std::{collections::HashMap, path::Path};

use ariadne::Source;
use calypso_base::symbol::Symbol;
use ctxt::GlobalCtxt;
use error::TysResult;
use spinneret::{encoder::ExportKind, Function, InsnBuilderBase};

use crate::{
    ast::ItemKind,
    typeck::{
        ast::{DeBruijnLvl, Expr},
        norm::{eval_ty, nf_ty_force},
        surf_ty_to_core, TypeExpectation, TypeckCtxt,
    },
};

pub mod ast;
pub mod codegen;
pub mod ctxt;
pub mod diag;
pub mod error;
pub mod intern;
pub mod parse;
pub mod resolve;
pub mod typeck;

pub fn run(src: &str, gcx: &GlobalCtxt, suppress_output: bool) -> TysResult<()> {
    let items = parse::run(src, gcx);

    resolve::resolve_code_unit(gcx, &items)?;
    // let cu = lowering::lower_code_unit(gcx, decls)?;

    let mut cont = true;
    if !suppress_output {
        {
            let mut drcx = gcx.drcx.borrow_mut();
            for err in drcx.errors() {
                err.eprint(Source::from(&src))?;
            }

            if let Some(fatal) = drcx.fatal() {
                fatal.eprint(Source::from(&src))?;
            }
            drcx.clear();
        }

        let mut values = HashMap::new();
        let mut lifted = Vec::new();
        for &item in &items {
            let mut w = Vec::new();
            let doc = ast::pretty::pp_item(gcx, item);
            doc.render(80, &mut w).unwrap();
            println!("{}", String::from_utf8(w).unwrap());

            if let ItemKind::Value(t, e) = gcx.arenas.ast.item(item).kind {
                let t = surf_ty_to_core(gcx, TypeckCtxt::default(), t);
                {
                    let mut drcx = gcx.drcx.borrow_mut();
                    for err in drcx.errors() {
                        err.eprint(Source::from(&src))?;
                    }

                    if let Some(fatal) = drcx.fatal() {
                        fatal.eprint(Source::from(&src))?;
                        drcx.clear();
                        continue;
                    }
                    drcx.clear();
                }
                let t = t.unwrap();

                let e = typeck::check(
                    gcx,
                    TypeckCtxt::default(),
                    e,
                    eval_ty(gcx, im::Vector::new(), t),
                    TypeExpectation::Definition(gcx.arenas.core.ty(t).span),
                );

                {
                    let mut drcx = gcx.drcx.borrow_mut();
                    for err in drcx.errors() {
                        cont = false;
                        err.eprint(Source::from(&src))?;
                    }

                    if let Some(fatal) = drcx.fatal() {
                        fatal.eprint(Source::from(&src))?;
                        drcx.clear();
                        cont = false;
                        continue;
                    }
                    drcx.clear();
                }
                let e = e.unwrap();
                Expr::report_deferred(e, gcx);
                {
                    let mut drcx = gcx.drcx.borrow_mut();
                    for err in drcx.errors() {
                        cont = false;
                        err.eprint(Source::from(&src))?;
                    }

                    if let Some(fatal) = drcx.fatal() {
                        fatal.eprint(Source::from(&src))?;
                        drcx.clear();
                        cont = false;
                        continue;
                    }
                    drcx.clear();
                }
                let t = nf_ty_force(gcx, DeBruijnLvl::from(0usize), im::Vector::new(), t);

                let mut w = Vec::new();
                let doc = typeck::pretty::pp_expr(
                    0,
                    gcx,
                    DeBruijnLvl::from(0usize),
                    im::Vector::new(),
                    e,
                );
                doc.render(80, &mut w).unwrap();

                let mut w1 = Vec::new();
                let doc =
                    typeck::pretty::pp_ty(0, gcx, DeBruijnLvl::from(0usize), im::Vector::new(), t)
                        .group();
                doc.render(80, &mut w1).unwrap();

                println!(
                    "\n{}\n{}",
                    String::from_utf8(w).unwrap(),
                    String::from_utf8(w1).unwrap()
                );
                if !cont {
                    return Ok(());
                }

                let (lift, e) = codegen::closure::closure_convert(gcx, e);
                lifted.extend(lift.into_iter());
                values.insert(gcx.arenas.ast.item(item).id, (e, t));

                println!();
            }
        }

        let item = items
            .iter()
            .find(|&&x| gcx.arenas.ast.item(x).ident.as_str() == "main")
            .unwrap();
        let id = gcx.arenas.ast.item(*item).id;
        let &(main, _) = values.get(&id).unwrap();
        {
            let mut w = Vec::new();
            let doc =
                typeck::pretty::pp_expr(0, gcx, DeBruijnLvl::from(0usize), im::Vector::new(), main);
            doc.render(80, &mut w).unwrap();
            println!("{}", String::from_utf8(w).unwrap());
        }

        // println!("== Lifted ==");
        // for &val in &lift {
        //     let mut w = Vec::new();
        //     let doc =
        //         typeck::pretty::pp_expr(0, gcx, DeBruijnLvl::from(0usize), im::Vector::new(), val);
        //     doc.render(80, &mut w).unwrap();
        //     println!(
        //         "{}: {}",
        //         gcx.arenas.core.expr(val).id,
        //         String::from_utf8(w).unwrap()
        //     );
        // }
        // println!("== Main term ==");
        // {
        //     let mut w = Vec::new();
        //     let doc =
        //         typeck::pretty::pp_expr(0, gcx, DeBruijnLvl::from(0usize), im::Vector::new(), main);
        //     doc.render(80, &mut w).unwrap();
        //     println!("{}", String::from_utf8(w).unwrap());
        // }

        let mut ccx = codegen::CodegenCtxt::new(gcx, values.clone());

        let t = ccx.module.types().function([], []);
        let mut func = ccx.module.function(t);

        let mut func_counter = 1;
        let mut bodies = HashMap::new();
        let mut statics = HashMap::new();
        let mut values1 = HashMap::new();
        let mut sorted = vec![];

        for (id, (expr, _)) in values {
            let expr = codegen::ir::Expr::from_core(gcx, &mut ccx.arenas, expr);
            values1.insert(id, expr);
            if ccx.arenas.exprs[expr].ty.is_arrow(&ccx.arenas) {
                bodies.insert(expr, Function(func_counter));
            } else {
                bodies.insert(expr, Function(func_counter));
                statics.insert(expr, Function(func_counter));
                func.call(Function(func_counter));
            };
            sorted.push((
                Function(func_counter),
                expr,
                gcx.arenas
                    .ast
                    .get_node_by_id(id)
                    .unwrap()
                    .ident(gcx)
                    .unwrap()
                    .symbol,
            ));
            func_counter += 1;
        }
        for val in lifted {
            let id = gcx.arenas.core.expr(val).id;
            let val = codegen::ir::Expr::from_core(gcx, &mut ccx.arenas, val);
            bodies.insert(val, Function(func_counter));
            ccx.lifted.insert(id, val);
            sorted.push((
                Function(func_counter),
                val,
                Symbol::intern(&format!("lifted.{}", id)),
            ));
            func_counter += 1;
        }
        ccx.bodies1 = bodies;
        ccx.values = values1;

        let func = func.finish(&mut ccx.module);
        ccx.module.export("_start", ExportKind::Func, func.0);

        for (_, expr, name) in &sorted {
            ccx.declare_func(*name, *expr);
        }
        for (_, expr, name) in sorted {
            ccx.build_func(name, expr);
        }

        ccx.lmodule.verify();

        // let expr = eval::eval_expr(gcx, &mut ecx, im::Vector::new(), main);
        // let expr = eval::force_barrier(&mut ecx, expr);
        // let expr = eval::quote_expr(gcx, &mut ecx, DeBruijnLvl::from(0usize), expr);

        // let mut w = Vec::new();
        // //let doc = eval::pretty::pp_expr(0, gcx, &mut ecx, expr);
        // let doc =
        //     typeck::pretty::pp_expr(0, gcx, DeBruijnLvl::from(0usize), im::Vector::new(), expr);
        // doc.render(80, &mut w).unwrap();
        // println!("{}", String::from_utf8(w).unwrap());
        // println!("{:#?}", items);
        // println!("{:#?}", gcx.arenas.ast.res_data.borrow().to_hash_map());
        // println!("\n{:#?}", gcx);

        // let item = gcx.arenas.ast.item(*items.first().unwrap());
        // let mut tyck = TypeckCtxt::new(gcx);
        // typeck::check_item(&mut tyck, gcx, *items.first().unwrap());

        // println!("\n{:#?}", gcx);
        // println!("\n{:#?}", tyck);

        ccx.lmodule.write_to_file(Path::new("out.bc")).unwrap();

        //std::fs::write("out.wasm", ccx.finish_module()).unwrap();
    }

    Ok(())

    // let tya = Arena::new();
    // let expra = Arena::new();
    // let decla = Arena::new();
    // let mut rcx = ResCtxt {
    //     ty: &tya,
    //     expr: &expra,
    //     decl: &decla,
    //     decls: HashMap::new(),
    //     expr_names: vec![],
    //     ty_names: vec![],
    // };
    // let ast = *ast.unwrap().resolve(&mut rcx)?.get(1).unwrap();
    // let ppa = pretty::Arena::new();
    // match ast.kind {
    //     DeclKind::Defn(_, ty, expr) => {
    //         println!("{}", ty.pretty(&ppa).pretty(80));
    //         println!("{}", expr.pretty(&ppa).pretty(80));
    //     }
    // }
}
