use ariadne::Source;
use ctxt::GlobalCtxt;
use error::TysResult;
use eval::EvalCtx;

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
pub mod eval;
pub mod intern;
pub mod parse;
pub mod resolve;
pub mod typeck;

pub fn run(src: &str, gcx: &GlobalCtxt, suppress_output: bool) -> TysResult<()> {
    let items = parse::run(src, gcx);

    resolve::resolve_code_unit(gcx, &items)?;
    // let cu = lowering::lower_code_unit(gcx, decls)?;

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

        let mut ecx = EvalCtx::default();
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
                        err.eprint(Source::from(&src))?;
                    }

                    if let Some(fatal) = drcx.fatal() {
                        fatal.eprint(Source::from(&src))?;
                        drcx.clear();
                        continue;
                    }
                    drcx.clear();
                }
                let e = e.unwrap();
                Expr::report_deferred(e, gcx);
                ecx.free.insert(gcx.arenas.ast.item(item).id, e);

                let mut w = Vec::new();
                let doc = typeck::pretty::pp_expr(
                    0,
                    gcx,
                    DeBruijnLvl::from(0usize),
                    im::Vector::new(),
                    e,
                );
                doc.render(80, &mut w).unwrap();

                let t = nf_ty_force(gcx, DeBruijnLvl::from(0usize), im::Vector::new(), t);
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

                println!();
            }
        }

        let item = items
            .iter()
            .find(|&&x| gcx.arenas.ast.item(x).ident.as_str() == "main")
            .unwrap();
        let id = gcx.arenas.ast.item(*item).id;
        let main = *ecx.free.get(&id).unwrap();
        {
            let mut w = Vec::new();
            let doc =
                typeck::pretty::pp_expr(0, gcx, DeBruijnLvl::from(0usize), im::Vector::new(), main);
            doc.render(80, &mut w).unwrap();
            println!("{}", String::from_utf8(w).unwrap());
        }

        let (lift, conv) = codegen::closure::closure_convert(gcx, &mut ecx, main);

        println!("== Lifted ==");
        for val in lift {
            let mut w = Vec::new();
            let doc =
                typeck::pretty::pp_expr(0, gcx, DeBruijnLvl::from(0usize), im::Vector::new(), val);
            doc.render(80, &mut w).unwrap();
            println!(
                "{}: {}",
                gcx.arenas.core.expr(val).id,
                String::from_utf8(w).unwrap()
            );
        }
        println!("== Main term ==");
        {
            let mut w = Vec::new();
            let doc =
                typeck::pretty::pp_expr(0, gcx, DeBruijnLvl::from(0usize), im::Vector::new(), conv);
            doc.render(80, &mut w).unwrap();
            println!("{}", String::from_utf8(w).unwrap());
        }
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
