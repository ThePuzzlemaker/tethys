use std::{cell::RefCell, collections::HashMap, rc::Rc};

use calypso_base::symbol::Symbol;
use cranelift_entity::EntityList;
use id_arena::Id;
use itertools::Itertools;
use pretty::{DocAllocator, RcAllocator, RcDoc};

use crate::{
    ast::{AstId, BinOpKind},
    ctxt::GlobalCtxt,
    typeck::ast::{CoreAstId, Expr, ExprKind, Ty},
};

use self::ssa::{Block, CursorPosition, Function, FunctionCursor, InsnBuilder, Value};

pub mod closure;
pub mod constant_prop;
pub mod ssa;

#[derive(Debug)]
pub struct CodegenCtxt<'gcx> {
    gcx: &'gcx GlobalCtxt,
    pub values: HashMap<AstId, (Id<Expr>, Id<Ty>)>,
    pub bodies: HashMap<CoreAstId, Function>,
}

impl<'gcx> CodegenCtxt<'gcx> {
    pub fn new(gcx: &'gcx GlobalCtxt, values: HashMap<AstId, (Id<Expr>, Id<Ty>)>) -> Self {
        Self {
            gcx,
            bodies: HashMap::new(),
            values,
        }
    }

    pub fn build_func(&mut self, name: Symbol, expr: Id<Expr>) -> &mut Function {
        let mut func = Function::new(name);
        let mut cursor = FunctionCursor::new(&mut func);

        let (v, body) = if let ExprKind::LiftedLam(v, body) = self.gcx.arenas.core.expr(expr).kind {
            (v, body)
        } else {
            (im::Vector::new(), expr)
        };

        let (_block, vals) = cursor.begin_block(name, v.len() as u16);
        cursor.next_insn();
        let res = self.build_expr(&mut cursor, body, vals);
        cursor.ret(&[res]);

        func.recalculate_cfg();
        func.recalculate_dominators();
        func.assert_valid();
        let id = self.gcx.arenas.core.expr(expr).id;
        self.bodies.insert(id, func);

        self.bodies.get_mut(&id).unwrap()
    }

    fn build_expr(
        &mut self,
        func: &mut FunctionCursor<'_>,
        expr: Id<Expr>,
        scope: EntityList<Value>,
    ) -> Value {
        match self.gcx.arenas.core.expr(expr).kind {
            ExprKind::Unit => func.unit(),
            ExprKind::LiftedVar(ix) => scope
                .get(
                    scope.len(&func.func.dfg.value_pool) - ix.index() - 1,
                    &func.func.dfg.value_pool,
                )
                .unwrap(),
            ExprKind::LiftedFree(lvl) => scope.get(lvl.index(), &func.func.dfg.value_pool).unwrap(),
            ExprKind::Var(..) | ExprKind::Lam(..) | ExprKind::Let(..) | ExprKind::Err(_) => {
                unreachable!()
            }
            ExprKind::LiftedLam(_, _) => func.make_closure(self.gcx.arenas.core.expr(expr).id, &[]),
            ExprKind::LiftedApp(f, x) => {
                let values = x
                    .iter()
                    .map(|x| self.build_expr(func, *x, scope))
                    .collect::<Vec<_>>();
                func.make_closure(self.gcx.arenas.core.expr(f).id, &values)
            }
            ExprKind::App(mut f, x) => {
                let mut values = im::vector![x];
                loop {
                    if let ExprKind::App(e, x) = self.gcx.arenas.core.expr(f).kind {
                        values.push_front(x);
                        f = e;
                    } else if let ExprKind::LiftedApp(e, x) = self.gcx.arenas.core.expr(f).kind {
                        for v in x {
                            values.push_front(v);
                        }
                        f = e;
                    } else {
                        break;
                    }
                }
                if let ExprKind::LiftedLam(v, ..) = self.gcx.arenas.core.expr(f).kind {
                    let values = values
                        .iter()
                        .map(|x| self.build_expr(func, *x, scope))
                        .collect::<Vec<_>>();
                    if v.len() != values.len() {
                        func.make_closure(self.gcx.arenas.core.expr(f).id, &values)
                    } else {
                        func.call(self.gcx.arenas.core.expr(f).id, &values)
                    }
                } else if let ExprKind::Free(id) = self.gcx.arenas.core.expr(f).kind {
                    let values = values
                        .iter()
                        .map(|x| self.build_expr(func, *x, scope))
                        .collect::<Vec<_>>();
                    let (e, _) = self.values[&id];
                    let ExprKind::LiftedLam(v, ..) = self.gcx.arenas.core.expr(e).kind else {
                        unreachable!() // typeck
                    };
                    if v.len() != values.len() {
                        func.make_closure(self.gcx.arenas.core.expr(e).id, &values)
                    } else {
                        func.call(self.gcx.arenas.core.expr(e).id, &values)
                    }
                } else {
                    let f = self.build_expr(func, f, scope);
                    let values = values
                        .iter()
                        .map(|x| self.build_expr(func, *x, scope))
                        .collect::<Vec<_>>();
                    func.call_closure(f, &values)
                }
            }
            ExprKind::TyApp(e, _) | ExprKind::TyAbs(_, _, e) => self.build_expr(func, e, scope),
            ExprKind::Free(id) => {
                let (e, t) = self.values[&id];
                if Ty::is_arrow(self.gcx, t) {
                    func.make_closure(self.gcx.arenas.core.expr(e).id, &[])
                } else {
                    func.load_static(self.gcx.arenas.core.expr(e).id)
                }
            }
            ExprKind::EnumConstructor(_, _) => todo!(),
            ExprKind::EnumRecursor(_) => todo!(),
            ExprKind::Number(v) => func.iconst(v),
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::Add,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.iadd(left, right)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::Subtract,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.isub(left, right)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::Multiply,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.imult(left, right)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::Divide,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.idiv(left, right)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::Modulo,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.imod(left, right)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::Power,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.ipow(left, right)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::BitShiftLeft,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.ishl(left, right)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::BitShiftRight,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.ishr(left, right)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::BitOr,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.ior(left, right)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::BitXor,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.ixor(left, right)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::BitAnd,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.iand(left, right)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::Equal,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.ieq(left, right)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::NotEqual,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.ineq(left, right)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::LessThan,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.ilt(left, right)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::GreaterThan,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.igt(left, right)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::GreaterEqual,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.igte(left, right)
            }
            ExprKind::BinaryOp {
                left,
                kind: BinOpKind::LessEqual,
                right,
            } => {
                let left = self.build_expr(func, left, scope);
                let right = self.build_expr(func, right, scope);
                func.ilte(left, right)
            }
            ExprKind::BinaryOp { kind, .. } => todo!("{kind:?}"),
            ExprKind::Boolean(b) => func.bconst(b),
            ExprKind::If(cond, then, then_else) => {
                let cond_block = func.current_block().unwrap();
                let cond = self.build_expr(func, cond, scope);

                let (then_block, _) = func.begin_block(Symbol::intern("then"), 0);
                let then = self.build_expr(func, then, scope);

                let (then_else_block, _) = func.begin_block(Symbol::intern("else"), 0);
                let then_else = self.build_expr(func, then_else, scope);

                let (join_block, vals) = func.begin_block(Symbol::intern("cont"), 1);

                func.set_pos(CursorPosition::After(cond_block));
                func.br_if(cond, then_block, &[], then_else_block, &[]);
                func.set_pos(CursorPosition::After(then_block));
                func.jmp(join_block, &[then]);
                func.set_pos(CursorPosition::After(then_else_block));
                func.jmp(join_block, &[then_else]);
                func.set_pos(CursorPosition::After(join_block));

                vals.get(0, &func.func.dfg.value_pool).unwrap()
            }
            ExprKind::Tuple(_) => todo!(),
            ExprKind::TupleProj(_, _) => todo!(),
        }
    }
}
