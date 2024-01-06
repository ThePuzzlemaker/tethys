//! Sparse conditional constant propogation (SCCP)

use std::collections::HashSet;

use cranelift_entity::SecondaryMap;
use im::Vector;

use crate::{
    codegen::ssa::{BlockRef, Immediate, InsnBuilder, InstructionReplacer, Opcode, ValueData},
    typeck::ast::CoreAstId,
};

use super::ssa::{Block, Function, FunctionCursor, InsnData, Value};

#[derive(Debug)]
struct ConstantProp<'f> {
    pub func: FunctionCursor<'f>,
    values: SecondaryMap<Value, Constant>,
    visited: HashSet<Block>,
    block_params: SecondaryMap<Value, Constant>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Constant {
    Bconst(bool),
    Iconst(i64),
    Unit,
    NotAtCompile,
    Undefined,
}

impl Constant {
    pub fn meet(self, other: Constant) -> Constant {
        match (self, other) {
            (Constant::Bconst(a), Constant::Bconst(b)) if a == b => self,
            (Constant::Iconst(a), Constant::Iconst(b)) if a == b => self,
            (Constant::Unit, Constant::Unit) => self,
            // (Constant::Closure(id1, spine1), Constant::Closure(id2, spine2)) if id1 == id2 => {
            //     let vals = spine1
            //         .into_iter()
            //         .zip(spine2)
            //         .map(|(a, b)| a.meet(b))
            //         .collect::<Vector<_>>();
            //     if vals.iter().any(|x| *x == Constant::NotAtCompile) {
            //         Constant::NotAtCompile
            //     } else {
            //         Constant::Closure(id1, vals)
            //     }
            // }
            (Constant::Undefined, x) | (x, Constant::Undefined) => x,
            _ => Constant::NotAtCompile,
        }
    }
}

pub fn run(func: &mut Function) {
    let mut ctx = ConstantProp {
        func: FunctionCursor::new(func),
        values: SecondaryMap::with_default(Constant::Undefined),
        visited: HashSet::new(),
        block_params: SecondaryMap::with_default(Constant::Undefined),
    };

    let block = ctx
        .func
        .layout()
        .entry_block()
        .expect("Function had entry block");

    // TODO: entry block arity
    ctx.run(block, vec![]);

    let dead_blocks = ctx
        .func
        .dfg()
        .blocks
        .keys()
        .collect::<HashSet<_>>()
        .difference(&ctx.visited)
        .copied()
        .collect();
    ctx.func.dfg_mut().dead_blocks = dead_blocks;
}

impl<'f> ConstantProp<'f> {
    // TODO: worklist
    fn run(&mut self, block: Block, params: Vec<Constant>) {
        let mut worklist = vec![(block, params)];
        while let Some((block, params)) = worklist.pop() {
            use InsnData::*;
            self.func.goto_block(block);
            self.visited.insert(block);

            if self
                .visited
                .intersection(
                    &self.func.dfg().predecessors[block]
                        .iter()
                        .copied()
                        .collect(),
                )
                .count()
                == self.func.dfg().predecessors[block].len()
            {
                for (ix, (param, block_param)) in params
                    .into_iter()
                    .zip(
                        self.func.dfg().block_params[block]
                            .as_slice(&self.func.dfg().value_pool)
                            .to_vec(),
                    )
                    .enumerate()
                {
                    self.values[block_param] = param
                        .meet(self.values[block_param])
                        .meet(self.block_params[block_param]);

                    // TODO: make this less janky
                    match self.values[block_param] {
                        Constant::Bconst(b) => {
                            let dfg = self.func.dfg_mut();
                            let val = dfg.values.push(ValueData::Block(block, ix as u16));
                            *dfg.block_params[block]
                                .get_mut(ix, &mut dfg.value_pool)
                                .unwrap() = val;
                            let insn = dfg
                                .insns
                                .push(InsnData::UnaryImm(Opcode::Bconst, Immediate::Boolean(b)));
                            dfg.values[block_param] = ValueData::Result(insn, 0);
                            dfg.insn_results[insn].push(block_param, &mut dfg.value_pool);
                            self.func.next_insn();
                            self.func.insert_insn(insn);
                            self.func.prev_insn();
                        }
                        Constant::Iconst(i) => {
                            let dfg = self.func.dfg_mut();
                            let val = dfg.values.push(ValueData::Block(block, ix as u16));
                            *dfg.block_params[block]
                                .get_mut(ix, &mut dfg.value_pool)
                                .unwrap() = val;
                            let insn = dfg
                                .insns
                                .push(InsnData::UnaryImm(Opcode::Iconst, Immediate::Integer(i)));
                            dfg.values[block_param] = ValueData::Result(insn, 0);
                            dfg.insn_results[insn].push(block_param, &mut dfg.value_pool);
                            self.func.next_insn();
                            self.func.insert_insn(insn);
                            self.func.prev_insn();
                        }
                        Constant::Unit => {
                            let dfg = self.func.dfg_mut();
                            let val = dfg.values.push(ValueData::Block(block, ix as u16));
                            *dfg.block_params[block]
                                .get_mut(ix, &mut dfg.value_pool)
                                .unwrap() = val;
                            let insn = dfg.insns.push(InsnData::Nullary(Opcode::Unit));
                            dfg.values[block_param] = ValueData::Result(insn, 0);
                            dfg.insn_results[insn].push(block_param, &mut dfg.value_pool);
                            self.func.next_insn();
                            self.func.insert_insn(insn);
                            self.func.prev_insn();
                        }
                        _ => {}
                    }
                }
            } else {
                for (param, &block_param) in params
                    .into_iter()
                    .zip(self.func.dfg().block_params[block].as_slice(&self.func.dfg().value_pool))
                {
                    self.block_params[block_param] = param.meet(self.block_params[block_param]);
                }
            }

            while let Some(insn) = self.func.next_insn() {
                let results = self.func.dfg().insn_results[insn]
                    .as_slice(&self.func.dfg().value_pool)
                    .to_vec();
                match self.func.dfg().insns[insn] {
                    Nullary(Opcode::Unit) => self.values[results[0]] = Constant::Unit,
                    Unary(_, _) => todo!(),
                    UnaryImm(_, Immediate::Integer(i)) => {
                        self.values[results[0]] = Constant::Iconst(i)
                    }
                    UnaryImm(_, Immediate::Boolean(b)) => {
                        self.values[results[0]] = Constant::Bconst(b)
                    }
                    Binary(Opcode::Iadd, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a + b);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a + b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Isub, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a - b);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a - b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Imult, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a * b);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a * b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Idiv, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a / b);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a / b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Imod, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a % b);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a % b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ishl, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a << b);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a << b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ishr, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a >> b);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a >> b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Iand, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a & b);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a & b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ior, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a | b);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a | b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ixor, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a ^ b);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a ^ b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ipow, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            let val = a.pow(b.try_into().unwrap());
                            self.values[results[0]] = Constant::Iconst(val);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(val);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ieq, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Bconst(a == b);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).bconst(a == b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ineq, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Bconst(a != b);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).bconst(a != b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ilt, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Bconst(a < b);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).bconst(a < b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Igt, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Bconst(a > b);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).bconst(a > b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ilte, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Bconst(a <= b);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).bconst(a <= b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Igte, [a, b]) => match (self.values[a], self.values[b]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Bconst(a >= b);
                            InstructionReplacer::new(self.func.dfg_mut(), insn).bconst(a >= b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    BrIf(Opcode::BrIf, cond, [then, then_else]) => match self.values[cond] {
                        Constant::Bconst(true) => {
                            worklist.push((
                                then.0,
                                then.1
                                    .as_slice(&self.func.dfg().value_pool)
                                    .iter()
                                    .map(|x| self.values[*x])
                                    .collect(),
                            ));
                            let vals = then.1.as_slice(&self.func.dfg().value_pool).to_vec();
                            InstructionReplacer::new(self.func.dfg_mut(), insn).jmp(then.0, &vals);
                        }
                        Constant::Bconst(false) => {
                            worklist.push((
                                then_else.0,
                                then_else
                                    .1
                                    .as_slice(&self.func.dfg().value_pool)
                                    .iter()
                                    .map(|x| self.values[*x])
                                    .collect(),
                            ));
                            let vals = then_else.1.as_slice(&self.func.dfg().value_pool).to_vec();
                            InstructionReplacer::new(self.func.dfg_mut(), insn).jmp(then.0, &vals);
                        }
                        _ => {
                            worklist.push((
                                then.0,
                                then.1
                                    .as_slice(&self.func.dfg().value_pool)
                                    .iter()
                                    .map(|x| self.values[*x])
                                    .collect(),
                            ));

                            worklist.push((
                                then_else.0,
                                then_else
                                    .1
                                    .as_slice(&self.func.dfg().value_pool)
                                    .iter()
                                    .map(|x| self.values[*x])
                                    .collect(),
                            ));
                        }
                    },
                    Call(_, _, _) | CallClosure(..) | MakeClosure(..) => {}
                    LoadStatic(_, _) | Nary(Opcode::Ret, _) => {}
                    BlockCall(Opcode::Jmp, BlockRef(block, values)) => self.run(
                        block,
                        values
                            .as_slice(&self.func.dfg().value_pool)
                            .iter()
                            .copied()
                            .map(|x| self.values[x])
                            .collect(),
                    ),

                    _ => unreachable!("{}", self.func.dfg().insns[insn].opcode()),
                }
            }
        }
    }
}
