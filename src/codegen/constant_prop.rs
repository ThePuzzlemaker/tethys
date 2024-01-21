//! Sparse conditional constant propogation (SCCP)

use std::collections::HashSet;

use cranelift_entity::SecondaryMap;

use crate::codegen::ssa::{
    BlockRef, Immediate, InsnBuilder, InstructionReplacer, Opcode, ValueData,
};

use super::ssa::{Block, Function, FunctionCursor, InsnData, Value};

#[derive(Debug)]
struct ConstantProp<'f> {
    pub func: FunctionCursor<'f>,
    values: SecondaryMap<Value, Constant>,
    visited: HashSet<Block>,
    block_params: SecondaryMap<Value, Constant>,
    value_dependents: SecondaryMap<Value, usize>,
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
            (Constant::Undefined, x) | (x, Constant::Undefined) => x,
            _ => Constant::NotAtCompile,
        }
    }

    pub fn is_known(self) -> bool {
        matches!(
            self,
            Constant::Bconst(_) | Constant::Iconst(_) | Constant::Unit
        )
    }
}

pub fn run(func: &mut Function) {
    let mut ctx = ConstantProp {
        func: FunctionCursor::new(func),
        values: SecondaryMap::with_default(Constant::Undefined),
        visited: HashSet::new(),
        block_params: SecondaryMap::with_default(Constant::Undefined),
        value_dependents: SecondaryMap::default(),
    };

    let block = ctx
        .func
        .layout()
        .entry_block()
        .expect("Function had entry block");

    ctx.calculate_value_dependents();

    // TODO: entry block arity
    ctx.run(block, vec![]);

    ctx.remove_dead_values();

    let dead_blocks = ctx
        .func
        .layout()
        .blocks()
        .collect::<HashSet<_>>()
        .difference(&ctx.visited)
        .copied()
        .collect();
    ctx.func.dfg_mut().dead_blocks = dead_blocks;
}

impl<'f> ConstantProp<'f> {
    fn calculate_value_dependents(&mut self) {
        let dfg = self.func.dfg();
        for (_, insn) in &dfg.insns {
            match insn {
                InsnData::Nullary(_) | InsnData::UnaryImm(_, _) | InsnData::LoadStatic(_, _) => {}
                InsnData::Unary(_, val) => self.value_dependents[*val] += 1,
                InsnData::Binary(_, [val1, val2]) => {
                    self.value_dependents[*val1] += 1;
                    self.value_dependents[*val2] += 1;
                }
                InsnData::BrIf(_, cond, [then, then_else]) => {
                    self.value_dependents[*cond] += 1;
                    for val in then.1.as_slice(&dfg.value_pool) {
                        self.value_dependents[*val] += 1;
                    }
                    for val in then_else.1.as_slice(&dfg.value_pool) {
                        self.value_dependents[*val] += 1;
                    }
                }
                InsnData::Call(_, _, vals)
                | InsnData::Nary(_, vals)
                | InsnData::BlockCall(_, BlockRef(_, vals))
                | InsnData::MakeClosure(_, _, vals) => {
                    for val in vals.as_slice(&dfg.value_pool) {
                        self.value_dependents[*val] += 1;
                    }
                }
                InsnData::CallClosure(_, closure, vals) => {
                    self.value_dependents[*closure] += 1;
                    for val in vals.as_slice(&dfg.value_pool) {
                        self.value_dependents[*val] += 1;
                    }
                }
            }
        }
    }

    fn remove_dead_values(&mut self) {
        for value in self
            .value_dependents
            .iter()
            .filter_map(|(val, count)| (*count == 0).then_some(val))
        {
            if let ValueData::Result(insn, _) = self.func.dfg().values[value] {
                if let Some(block) = self.func.layout().insn_block(insn) {
                    if self.func.layout().block_contains_insn(block, insn) {
                        self.func.layout_mut().remove_insn(insn);
                    }
                }
            }
        }
    }

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
                    // TODO: remove these block params
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
                            self.value_dependents[val] = 0;
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
                            self.value_dependents[val] = 0;
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
                            self.value_dependents[val] = 0;
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
                    Binary(Opcode::Iadd, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a + b);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a + b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Isub, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a - b);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a - b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Imult, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a * b);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a * b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Idiv, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a / b);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a / b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Imod, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a % b);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a % b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ishl, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a << b);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a << b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ishr, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a >> b);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a >> b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Iand, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a & b);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a & b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ior, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a | b);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a | b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ixor, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Iconst(a ^ b);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(a ^ b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ipow, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            let val = a.pow(b.try_into().unwrap());
                            self.values[results[0]] = Constant::Iconst(val);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
                            InstructionReplacer::new(self.func.dfg_mut(), insn).iconst(val);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ieq, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Bconst(a == b);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
                            InstructionReplacer::new(self.func.dfg_mut(), insn).bconst(a == b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ineq, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Bconst(a != b);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
                            InstructionReplacer::new(self.func.dfg_mut(), insn).bconst(a != b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ilt, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Bconst(a < b);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
                            InstructionReplacer::new(self.func.dfg_mut(), insn).bconst(a < b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Igt, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Bconst(a > b);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
                            InstructionReplacer::new(self.func.dfg_mut(), insn).bconst(a > b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Ilte, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Bconst(a <= b);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
                            InstructionReplacer::new(self.func.dfg_mut(), insn).bconst(a <= b);
                        }
                        _ => self.values[results[0]] = Constant::NotAtCompile,
                    },
                    Binary(Opcode::Igte, [av, bv]) => match (self.values[av], self.values[bv]) {
                        (Constant::Iconst(a), Constant::Iconst(b)) => {
                            self.values[results[0]] = Constant::Bconst(a >= b);
                            self.value_dependents[av] -= 1;
                            self.value_dependents[bv] -= 1;
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
                            self.value_dependents[cond] -= 1;
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
                            self.value_dependents[cond] -= 1;
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
