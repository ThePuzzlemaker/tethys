use std::collections::HashMap;

use calypso_base::symbol::Symbol;
use id_arena::Id;
use llvm_sys::LLVMIntPredicate;
use spinneret::Module;

use crate::{
    ast::{AstId, BinOpKind},
    codegen::llvm::Type,
    ctxt::GlobalCtxt,
    typeck::ast::{CoreAstId, Expr, Ty},
};

use self::{
    ir::{CgIrArenas, ExprKind},
    llvm::{Builder, Context},
};

pub mod closure;
pub mod ir;
pub mod llvm;

#[derive(Debug)]
pub struct CodegenCtxt<'gcx> {
    gcx: &'gcx GlobalCtxt,
    pub values: HashMap<AstId, ir::Expr>,
    pub lifted: HashMap<CoreAstId, ir::Expr>,
    pub bodies: HashMap<ir::Expr, (llvm::Function, llvm::Type)>,
    pub bodies1: HashMap<ir::Expr, spinneret::Function>,
    pub module: Module<'static>,
    pub arenas: CgIrArenas,
    n_funcs: usize,
    pub llvm: Context,
    pub lmodule: llvm::Module,
    pub builder: Builder,
}

impl<'gcx> CodegenCtxt<'gcx> {
    pub fn new(gcx: &'gcx GlobalCtxt, values: HashMap<AstId, (Id<Expr>, Id<Ty>)>) -> Self {
        let mut arenas = CgIrArenas::default();
        let values = values
            .into_iter()
            .map(|(i, (x, _))| (i, ir::Expr::from_core(gcx, &mut arenas, x)))
            .collect();
        let llvm = Context::new();
        let lmodule = llvm::Module::new(&llvm, "tethys_output");
        let builder = Builder::new(&llvm);

        Self {
            gcx,
            bodies: HashMap::new(),
            bodies1: HashMap::new(),
            lifted: HashMap::new(),
            values,
            module: Module::default(),
            arenas,
            n_funcs: 0,
            llvm,
            lmodule,
            builder,
        }
    }

    pub fn finish_module(self) -> Vec<u8> {
        self.lmodule.verify();

        self.module.finish()
    }

    pub fn declare_func(&mut self, name: Symbol, expr: ir::Expr) {
        let (v, body) = if let ExprKind::Lam(v, body) = self.arenas.exprs[expr].kind.clone() {
            (v, body)
        } else {
            (im::Vector::new(), expr)
        };

        let t = self.arenas.exprs[expr].ty;

        if !t.is_monotype(&self.arenas) {
            todo!();
        }

        let result_ty;
        let ty = if let ir::TyKind::Arrow(t, r) = self.arenas.tys[t].kind.clone() {
            result_ty = r
                .unboxed_type(&mut self.arenas, &self.llvm)
                .unwrap_or(Type::void(&self.llvm));

            Type::function(
                &self.llvm,
                result_ty,
                &t.iter()
                    .filter_map(|x| x.unboxed_type(&mut self.arenas, &self.llvm))
                    .collect::<Vec<_>>(),
            )
        } else {
            result_ty = t
                .unboxed_type(&mut self.arenas, &self.llvm)
                .unwrap_or(Type::void(&self.llvm));
            Type::function(&self.llvm, result_ty, &[])
        };

        let func = self.lmodule.add_function(name.as_str(), ty.clone());

        self.bodies.insert(expr, (func, ty));
    }

    pub fn build_func(&mut self, name: Symbol, expr: ir::Expr) {
        let (v, body) = if let ExprKind::Lam(v, body) = self.arenas.exprs[expr].kind.clone() {
            (v, body)
        } else {
            (im::Vector::new(), expr)
        };

        let t = self.arenas.exprs[expr].ty;

        if !t.is_monotype(&self.arenas) {
            todo!();
        }

        let func = self.lmodule.get_named_function(name.as_str()).unwrap();

        let mut params = HashMap::new();
        if let ir::TyKind::Arrow(t, _) = self.arenas.tys[t].kind.clone() {
            let mut ix = 0;
            for (id, ty) in v.iter().zip(t) {
                if ty.is_zero_sized(&self.arenas) {
                    params.insert(*id, None);
                } else {
                    params.insert(*id, Some(func.get_param(ix)));
                    ix += 1;
                }
            }
        }

        let entry = func.append_basic_block("entry");
        self.builder.position_at_end(&entry);

        let val = self.build_expr(&func, body, &params);
        if let Some(val) = val {
            self.builder.build_ret(val);
        } else {
            self.builder.build_ret_void();
        }
        self.lmodule.dump();
    }

    fn build_expr(
        &mut self,
        func: &llvm::Function,
        expr: ir::Expr,
        params: &HashMap<CoreAstId, Option<llvm::Value>>,
    ) -> Option<llvm::Value> {
        let ty = self.arenas.exprs[expr].ty;
        match self.arenas.exprs[expr].kind.clone() {
            ExprKind::LiftedVar(id) => params[&id].clone(),
            ExprKind::LiftedFree(id) => params[&id].clone(),
            ExprKind::Unit => None,
            ExprKind::Number(n) => Some(llvm::Value::const_int(
                &self.llvm,
                Type::i64(&self.llvm),
                n as u64,
                true,
            )),
            ExprKind::Boolean(b) => Some(llvm::Value::const_int(
                &self.llvm,
                Type::i1(&self.llvm),
                b as u64,
                false,
            )),
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::Add,
                right,
            } => {
                let left = self.build_expr(func, left, params).unwrap();
                let right = self.build_expr(func, right, params).unwrap();
                Some(self.builder.build_add(left, right, ""))
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::Subtract,
                right,
            } => {
                let left = self.build_expr(func, left, params).unwrap();
                let right = self.build_expr(func, right, params).unwrap();
                Some(self.builder.build_sub(left, right, ""))
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::Multiply,
                right,
            } => {
                let left = self.build_expr(func, left, params).unwrap();
                let right = self.build_expr(func, right, params).unwrap();
                Some(self.builder.build_mul(left, right, ""))
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::Divide,
                right,
            } => {
                let left = self.build_expr(func, left, params).unwrap();
                let right = self.build_expr(func, right, params).unwrap();
                Some(self.builder.build_sdiv(left, right, ""))
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::Equal,
                right,
            } => {
                let left = self.build_expr(func, left, params).unwrap();
                let right = self.build_expr(func, right, params).unwrap();
                Some(
                    self.builder
                        .build_icmp(LLVMIntPredicate::LLVMIntEQ, left, right, ""),
                )
            }
            ExprKind::If(cond, then, then_else) => {
                let cond = self.build_expr(func, cond, params).unwrap();
                let then_block = func.append_basic_block("if.then");
                let then_else_block = func.append_basic_block("if.else");
                let join = func.append_basic_block("if.join");

                self.builder
                    .build_cond_br(&cond, &then_block, &then_else_block);
                self.builder.position_at_end(&then_block);
                let then = self.build_expr(func, then, params);
                self.builder.build_br(&join);
                self.builder.position_at_end(&then_else_block);
                let then_else = self.build_expr(func, then_else, params);
                self.builder.build_br(&join);

                self.builder.position_at_end(&join);
                if let Some((then, then_else)) = then.zip(then_else) {
                    let phi = self.builder.build_phi(
                        ty.unboxed_type(&mut self.arenas, &self.llvm)
                            .unwrap_or(Type::void(&self.llvm)),
                        "",
                    );
                    phi.add_incoming(&[(then, then_block), (then_else, then_else_block)]);

                    Some(phi)
                } else {
                    None
                }
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::LogicalAnd,
                right,
            } => {
                let val = self.build_expr(func, left, params).unwrap();

                let bb = self.builder.get_insert_block().unwrap();
                let rhs_block = func.append_basic_block("and.rhs");
                let join_block = func.append_basic_block("and.join");

                self.builder.build_cond_br(&val, &rhs_block, &join_block);

                self.builder.position_at_end(&rhs_block);
                let rhs = self.build_expr(func, right, params).unwrap();
                self.builder.build_br(&join_block);

                self.builder.position_at_end(&join_block);
                let phi = self.builder.build_phi(Type::i1(&self.llvm), "");
                phi.add_incoming(&[(rhs, rhs_block), (val, bb)]);

                Some(phi)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::LogicalOr,
                right,
            } => {
                let val = self.build_expr(func, left, params).unwrap();

                let bb = self.builder.get_insert_block().unwrap();
                let rhs_block = func.append_basic_block("or.rhs");
                let join_block = func.append_basic_block("or.join");

                self.builder.build_cond_br(&val, &join_block, &rhs_block);

                self.builder.position_at_end(&rhs_block);
                let rhs = self.build_expr(func, right, params).unwrap();
                self.builder.build_br(&join_block);

                self.builder.position_at_end(&join_block);
                let phi = self.builder.build_phi(Type::i1(&self.llvm), "");
                phi.add_incoming(&[(rhs, rhs_block), (val, bb)]);

                Some(phi)
            }
            ExprKind::App(f, values) => {
                if let ExprKind::Lam(v, _) = self.arenas.exprs[f].kind.clone() {
                    let values = values
                        .iter()
                        .map(|x| self.build_expr(func, *x, params))
                        .collect::<Vec<_>>();
                    if v.len() != values.len() {
                        todo!()
                    } else {
                        let values = values.into_iter().flatten().collect::<Vec<_>>();
                        let (func, ty) = self.bodies.get(&f).unwrap();

                        Some(self.builder.build_call(func, ty, &values, ""))
                    }
                } else if let ExprKind::Free(id) = self.arenas.exprs[f].kind.clone() {
                    let values = values
                        .iter()
                        .map(|x| self.build_expr(func, *x, params))
                        .collect::<Vec<_>>();
                    let e = self.values[&id];
                    let ExprKind::Lam(v, _) = &self.arenas.exprs[e].kind else {
                        unreachable!() // typeck
                    };
                    if v.len() != values.len() {
                        todo!()
                    } else {
                        let values = values.into_iter().flatten().collect::<Vec<_>>();
                        let (func, ty) = self.bodies.get(&e).unwrap();

                        Some(self.builder.build_call(func, ty, &values, ""))
                    }
                } else if let ExprKind::LiftedLamRef(id) = self.arenas.exprs[f].kind.clone() {
                    let values = values
                        .iter()
                        .map(|x| self.build_expr(func, *x, params))
                        .collect::<Vec<_>>();
                    let e = self.lifted[&id];
                    let ExprKind::Lam(v, _) = &self.arenas.exprs[e].kind else {
                        unreachable!() // typeck
                    };
                    if v.len() != values.len() {
                        todo!()
                    } else {
                        let values = values.into_iter().flatten().collect::<Vec<_>>();
                        let (func, ty) = self.bodies.get(&e).unwrap();

                        Some(self.builder.build_call(func, ty, &values, ""))
                    }
                } else {
                    todo!()
                    // let f = self.build_expr(func, f, n_locals);
                    // let values = values
                    //     .iter()
                    //     .map(|x| self.build_expr(func, *x, scope))
                    //     .collect::<Vec<_>>();
                    // func.call_closure(f, &values)
                }
            }
            // ExprKind::Free(id) => {
            //     println!("{:#?}", id);
            //     todo!()
            // }
            _ => todo!("{:?}", self.arenas.exprs[expr].kind),
        }
    }

    // fn build_expr(
    //     &mut self,
    //     func: &mut FunctionCursor<'_>,
    //     expr: Id<Expr>,
    //     scope: EntityList<Value>,
    // ) -> Value {
    //     match self.gcx.arenas.core.expr(expr).kind {
    //         ExprKind::Unit => func.unit(),
    //         ExprKind::LiftedVar(ix) => scope
    //             .get(
    //                 scope.len(&func.func.dfg.value_pool) - ix.index() - 1,
    //                 &func.func.dfg.value_pool,
    //             )
    //             .unwrap(),
    //         ExprKind::LiftedFree(lvl) => scope.get(lvl.index(), &func.func.dfg.value_pool).unwrap(),
    //         ExprKind::Var(..) | ExprKind::Lam(..) | ExprKind::Let(..) | ExprKind::Err(_) => {
    //             unreachable!()
    //         }
    //         ExprKind::LiftedLam(_, _) => func.make_closure(self.gcx.arenas.core.expr(expr).id, &[]),
    //         ExprKind::LiftedApp(f, x) => {
    //             let values = x
    //                 .iter()
    //                 .map(|x| self.build_expr(func, *x, scope))
    //                 .collect::<Vec<_>>();
    //             func.make_closure(self.gcx.arenas.core.expr(f).id, &values)
    //         }
    //         ExprKind::App(mut f, x) => {
    //             let mut values = im::vector![x];
    //             loop {
    //                 if let ExprKind::App(e, x) = self.gcx.arenas.core.expr(f).kind {
    //                     values.push_front(x);
    //                     f = e;
    //                 } else if let ExprKind::LiftedApp(e, x) = self.gcx.arenas.core.expr(f).kind {
    //                     for v in x {
    //                         values.push_front(v);
    //                     }
    //                     f = e;
    //                 } else {
    //                     break;
    //                 }
    //             }
    //             if let ExprKind::LiftedLam(v, ..) = self.gcx.arenas.core.expr(f).kind {
    //                 let values = values
    //                     .iter()
    //                     .map(|x| self.build_expr(func, *x, scope))
    //                     .collect::<Vec<_>>();
    //                 if v.len() != values.len() {
    //                     func.make_closure(self.gcx.arenas.core.expr(f).id, &values)
    //                 } else {
    //                     func.call(self.gcx.arenas.core.expr(f).id, &values)
    //                 }
    //             } else if let ExprKind::Free(id) = self.gcx.arenas.core.expr(f).kind {
    //                 let values = values
    //                     .iter()
    //                     .map(|x| self.build_expr(func, *x, scope))
    //                     .collect::<Vec<_>>();
    //                 let (e, _) = self.values[&id];
    //                 let ExprKind::LiftedLam(v, ..) = self.gcx.arenas.core.expr(e).kind else {
    //                     unreachable!() // typeck
    //                 };
    //                 if v.len() != values.len() {
    //                     func.make_closure(self.gcx.arenas.core.expr(e).id, &values)
    //                 } else {
    //                     func.call(self.gcx.arenas.core.expr(e).id, &values)
    //                 }
    //             } else {
    //                 let f = self.build_expr(func, f, scope);
    //                 let values = values
    //                     .iter()
    //                     .map(|x| self.build_expr(func, *x, scope))
    //                     .collect::<Vec<_>>();
    //                 func.call_closure(f, &values)
    //             }
    //         }
    //         ExprKind::TyApp(e, _) | ExprKind::TyAbs(_, _, e) => self.build_expr(func, e, scope),
    //         ExprKind::Free(id) => {
    //             let (e, t) = self.values[&id];
    //             if Ty::is_arrow(self.gcx, t) {
    //                 func.make_closure(self.gcx.arenas.core.expr(e).id, &[])
    //             } else {
    //                 func.load_static(self.gcx.arenas.core.expr(e).id)
    //             }
    //         }
    //         ExprKind::EnumConstructor(_, _) => todo!(),
    //         ExprKind::EnumRecursor(_) => todo!(),
    //         ExprKind::Number(v) => func.iconst(v),
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::Add,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.iadd(left, right)
    //         }
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::Subtract,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.isub(left, right)
    //         }
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::Multiply,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.imult(left, right)
    //         }
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::Divide,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.idiv(left, right)
    //         }
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::Modulo,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.imod(left, right)
    //         }
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::Power,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.ipow(left, right)
    //         }
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::BitShiftLeft,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.ishl(left, right)
    //         }
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::BitShiftRight,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.ishr(left, right)
    //         }
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::BitOr,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.ior(left, right)
    //         }
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::BitXor,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.ixor(left, right)
    //         }
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::BitAnd,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.iand(left, right)
    //         }
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::Equal,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.ieq(left, right)
    //         }
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::NotEqual,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.ineq(left, right)
    //         }
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::LessThan,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.ilt(left, right)
    //         }
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::GreaterThan,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.igt(left, right)
    //         }
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::GreaterEqual,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.igte(left, right)
    //         }
    //         ExprKind::BinaryOp {
    //             left,
    //             kind: BinOpKind::LessEqual,
    //             right,
    //         } => {
    //             let left = self.build_expr(func, left, scope);
    //             let right = self.build_expr(func, right, scope);
    //             func.ilte(left, right)
    //         }
    //         ExprKind::BinaryOp { kind, .. } => todo!("{kind:?}"),
    //         ExprKind::Boolean(b) => func.bconst(b),
    //         ExprKind::If(cond, then, then_else) => {
    //             let cond_block = func.current_block().unwrap();
    //             let cond = self.build_expr(func, cond, scope);

    //             let (then_block, _) = func.begin_block(Symbol::intern("then"), 0);
    //             let then = self.build_expr(func, then, scope);

    //             let (then_else_block, _) = func.begin_block(Symbol::intern("else"), 0);
    //             let then_else = self.build_expr(func, then_else, scope);

    //             let (join_block, vals) = func.begin_block(Symbol::intern("cont"), 1);

    //             func.set_pos(CursorPosition::After(cond_block));
    //             func.br_if(cond, then_block, &[], then_else_block, &[]);
    //             func.set_pos(CursorPosition::After(then_block));
    //             func.jmp(join_block, &[then]);
    //             func.set_pos(CursorPosition::After(then_else_block));
    //             func.jmp(join_block, &[then_else]);
    //             func.set_pos(CursorPosition::After(join_block));

    //             vals.get(0, &func.func.dfg.value_pool).unwrap()
    //         }
    //         ExprKind::Tuple(_) => todo!(),
    //         ExprKind::TupleProj(_, _) => todo!(),
    //     }
    // }
}
