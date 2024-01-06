use std::{
    cell::RefCell,
    fmt,
    rc::{Rc, Weak},
};

use calypso_base::symbol::Symbol;
use cranelift_entity::{
    entity_impl, packed_option::PackedOption, EntityList, EntitySet, ListPool, PrimaryMap,
    SecondaryMap,
};
use id_arena::{Arena, Id};
use im::HashSet;
use pretty::{DocAllocator, RcAllocator, RcDoc};

use crate::{ctxt::GlobalCtxt, typeck::ast::CoreAstId};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum InsnData {
    Nullary(Opcode),
    Unary(Opcode, Value),
    UnaryImm(Opcode, Immediate),
    Binary(Opcode, [Value; 2]),
    BrIf(Opcode, Value, [BlockRef; 2]),
    Call(Opcode, CoreAstId, EntityList<Value>),
    CallClosure(Opcode, Value, EntityList<Value>),
    MakeClosure(Opcode, CoreAstId, EntityList<Value>),
    LoadStatic(Opcode, CoreAstId),
    Nary(Opcode, EntityList<Value>),
    BlockCall(Opcode, BlockRef),
}

impl InsnData {
    pub fn opcode(self) -> Opcode {
        match self {
            InsnData::Nullary(op)
            | InsnData::Unary(op, ..)
            | InsnData::UnaryImm(op, ..)
            | InsnData::Binary(op, ..)
            | InsnData::BrIf(op, ..)
            | InsnData::Call(op, ..)
            | InsnData::CallClosure(op, ..)
            | InsnData::MakeClosure(op, ..)
            | InsnData::LoadStatic(op, ..)
            | InsnData::Nary(op, ..)
            | InsnData::BlockCall(op, ..) => op,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct BlockRef(pub Block, pub EntityList<Value>);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Immediate {
    Integer(i64),
    Boolean(bool),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Opcode {
    Iconst,
    Iadd,
    Isub,
    Imult,
    Idiv,
    Imod,
    Ishl,
    Ishr,
    Ior,
    Ixor,
    Iand,
    Ipow,
    Ieq,
    Ineq,
    Ilt,
    Igt,
    Ilte,
    Igte,
    Bconst,
    BrIf,
    Jmp,
    Ret,
    MakeClosure,
    CallClosure,
    Call,
    LoadStatic,
    Unit,
}

impl fmt::Display for Opcode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Opcode::Iconst => "iconst",
                Opcode::Iadd => "iadd",
                Opcode::Isub => "isub",
                Opcode::Imult => "imult",
                Opcode::Idiv => "idiv",
                Opcode::Imod => "imod",
                Opcode::Ishl => "ishl",
                Opcode::Ishr => "ishr",
                Opcode::Ior => "ior",
                Opcode::Ixor => "ixor",
                Opcode::Iand => "iand",
                Opcode::Ipow => "ipow",
                Opcode::Ieq => "ieq",
                Opcode::Ineq => "ineq",
                Opcode::Ilt => "ilt",
                Opcode::Igt => "igt",
                Opcode::Ilte => "ilte",
                Opcode::Igte => "igte",
                Opcode::Bconst => "bconst",
                Opcode::BrIf => "br_if",
                Opcode::Jmp => "jmp",
                Opcode::Ret => "ret",
                Opcode::MakeClosure => "make_closure",
                Opcode::CallClosure => "call_closure",
                Opcode::Call => "call",
                Opcode::LoadStatic => "load_static",
                Opcode::Unit => "unit",
            }
        )
    }
}

impl Opcode {
    pub fn result_arity(self) -> u16 {
        match self {
            Opcode::Iconst
            | Opcode::Iadd
            | Opcode::Isub
            | Opcode::Imult
            | Opcode::Idiv
            | Opcode::Imod
            | Opcode::Ishl
            | Opcode::Ishr
            | Opcode::Ior
            | Opcode::Ixor
            | Opcode::Iand
            | Opcode::Ipow
            | Opcode::Ieq
            | Opcode::Ineq
            | Opcode::Ilt
            | Opcode::Igt
            | Opcode::Ilte
            | Opcode::Igte
            | Opcode::Bconst
            | Opcode::MakeClosure
            | Opcode::LoadStatic
            | Opcode::Unit => 1,
            Opcode::BrIf | Opcode::Jmp | Opcode::Ret => 0,
            // TODO: n-ary function returns
            Opcode::CallClosure | Opcode::Call => 1,
        }
    }
}

pub trait InsnBuilder<'a>
where
    Self: Sized + 'a,
{
    fn dfg(&self) -> &DataFlowGraph;
    fn dfg_mut(&mut self) -> &mut DataFlowGraph;
    fn build(self, insn: InsnData) -> (Insn, &'a mut DataFlowGraph);

    // TODO: assert opcodes valid
    fn binary_(self, opcode: Opcode, arg0: Value, arg1: Value) -> (Insn, &'a mut DataFlowGraph) {
        self.build(InsnData::Binary(opcode, [arg0, arg1]))
    }
    fn nullary_(self, opcode: Opcode) -> (Insn, &'a mut DataFlowGraph) {
        self.build(InsnData::Nullary(opcode))
    }
    fn unary_imm_(self, opcode: Opcode, imm: Immediate) -> (Insn, &'a mut DataFlowGraph) {
        self.build(InsnData::UnaryImm(opcode, imm))
    }
    fn nary_(self, opcode: Opcode, vals: EntityList<Value>) -> (Insn, &'a mut DataFlowGraph) {
        self.build(InsnData::Nary(opcode, vals))
    }
    fn block_call_(
        self,
        opcode: Opcode,
        block: Block,
        vals: EntityList<Value>,
    ) -> (Insn, &'a mut DataFlowGraph) {
        self.build(InsnData::BlockCall(opcode, BlockRef(block, vals)))
    }

    fn iconst(self, i: i64) -> Value {
        let (insn, dfg) = self.unary_imm_(Opcode::Iconst, Immediate::Integer(i));
        dfg.first_result(insn)
    }

    fn bconst(self, b: bool) -> Value {
        let (insn, dfg) = self.unary_imm_(Opcode::Bconst, Immediate::Boolean(b));
        dfg.first_result(insn)
    }

    fn unit(self) -> Value {
        let (insn, dfg) = self.nullary_(Opcode::Unit);
        dfg.first_result(insn)
    }

    fn iadd(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Iadd, lhs, rhs);
        dfg.first_result(insn)
    }

    fn isub(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Isub, lhs, rhs);
        dfg.first_result(insn)
    }

    fn imult(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Imult, lhs, rhs);
        dfg.first_result(insn)
    }

    fn idiv(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Idiv, lhs, rhs);
        dfg.first_result(insn)
    }

    fn imod(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Imod, lhs, rhs);
        dfg.first_result(insn)
    }

    fn ipow(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Ipow, lhs, rhs);
        dfg.first_result(insn)
    }

    fn ishl(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Ishl, lhs, rhs);
        dfg.first_result(insn)
    }

    fn ishr(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Ishr, lhs, rhs);
        dfg.first_result(insn)
    }

    fn iand(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Iand, lhs, rhs);
        dfg.first_result(insn)
    }

    fn ior(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Ior, lhs, rhs);
        dfg.first_result(insn)
    }

    fn ixor(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Ixor, lhs, rhs);
        dfg.first_result(insn)
    }

    fn ieq(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Ieq, lhs, rhs);
        dfg.first_result(insn)
    }

    fn ineq(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Ineq, lhs, rhs);
        dfg.first_result(insn)
    }

    fn igt(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Igt, lhs, rhs);
        dfg.first_result(insn)
    }

    fn ilt(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Ilt, lhs, rhs);
        dfg.first_result(insn)
    }

    fn igte(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Igte, lhs, rhs);
        dfg.first_result(insn)
    }

    fn ilte(self, lhs: Value, rhs: Value) -> Value {
        let (insn, dfg) = self.binary_(Opcode::Ilte, lhs, rhs);
        dfg.first_result(insn)
    }

    fn make_closure(mut self, func: CoreAstId, values: &[Value]) -> Value {
        let value_list = EntityList::from_slice(values, &mut self.dfg_mut().value_pool);
        let (insn, dfg) = self.build(InsnData::MakeClosure(Opcode::MakeClosure, func, value_list));
        dfg.first_result(insn)
    }

    // TODO: return arity
    fn call_closure(mut self, closure: Value, values: &[Value]) -> Value {
        let value_list = EntityList::from_slice(values, &mut self.dfg_mut().value_pool);
        let (insn, dfg) = self.build(InsnData::CallClosure(
            Opcode::CallClosure,
            closure,
            value_list,
        ));
        dfg.first_result(insn)
    }

    fn call(mut self, func: CoreAstId, values: &[Value]) -> Value {
        let value_list = EntityList::from_slice(values, &mut self.dfg_mut().value_pool);
        let (insn, dfg) = self.build(InsnData::Call(Opcode::Call, func, value_list));
        dfg.first_result(insn)
    }

    fn load_static(self, val: CoreAstId) -> Value {
        let (insn, dfg) = self.build(InsnData::LoadStatic(Opcode::LoadStatic, val));
        dfg.first_result(insn)
    }

    fn br_if(
        mut self,
        cond: Value,
        then: Block,
        then_values: &[Value],
        then_else: Block,
        then_else_values: &[Value],
    ) -> Insn {
        let mut then_val_list = EntityList::new();
        then_val_list.extend(then_values.iter().copied(), &mut self.dfg_mut().value_pool);
        let mut then_else_val_list = EntityList::new();
        then_else_val_list.extend(
            then_else_values.iter().copied(),
            &mut self.dfg_mut().value_pool,
        );

        let (insn, _dfg) = self.build(InsnData::BrIf(
            Opcode::BrIf,
            cond,
            [
                BlockRef(then, then_val_list),
                BlockRef(then_else, then_else_val_list),
            ],
        ));

        insn
    }

    fn jmp(mut self, goto: Block, values: &[Value]) -> Insn {
        let mut val_list = EntityList::new();
        val_list.extend(values.iter().copied(), &mut self.dfg_mut().value_pool);

        let (insn, _dfg) = self.block_call_(Opcode::Jmp, goto, val_list);
        insn
    }

    fn ret(mut self, values: &[Value]) -> Insn {
        let mut val_list = EntityList::new();
        val_list.extend(values.iter().copied(), &mut self.dfg_mut().value_pool);

        let (insn, _dfg) = self.nary_(Opcode::Ret, val_list);
        insn
    }
}

impl<'a, 'f> InsnBuilder<'a> for &'a mut FunctionCursor<'f> {
    fn dfg(&self) -> &DataFlowGraph {
        &self.func.dfg
    }

    fn dfg_mut(&mut self) -> &mut DataFlowGraph {
        &mut self.func.dfg
    }

    fn build(self, insn: InsnData) -> (Insn, &'a mut DataFlowGraph) {
        let arity = insn.opcode().result_arity();
        let insn = self.func.dfg.insns.push(insn);
        // TODO
        let results = (0..arity)
            .map(|x| self.func.dfg.values.push(ValueData::Result(insn, x)))
            .collect::<Vec<_>>();
        self.func.dfg.insn_results[insn].extend(results, &mut self.func.dfg.value_pool);
        match self.pos {
            CursorPosition::Nowhere | CursorPosition::Before(_) => panic!("invalid position"),
            CursorPosition::At(before) => self.func.layout.insert_insn_before(insn, before),
            CursorPosition::After(block) => self.func.layout.append_insn(block, insn),
        }
        (insn, &mut self.func.dfg)
    }
}

impl<'f> FunctionCursor<'f> {
    pub fn insert_insn(&mut self, insn: Insn) {
        match self.pos {
            CursorPosition::Nowhere | CursorPosition::Before(_) => panic!("invalid position"),
            CursorPosition::At(before) => self.func.layout.insert_insn_before(insn, before),
            CursorPosition::After(block) => self.func.layout.append_insn(block, insn),
        }
    }
}

pub struct InstructionReplacer<'f> {
    dfg: &'f mut DataFlowGraph,
    insn: Insn,
}

impl<'f> InstructionReplacer<'f> {
    pub fn new(dfg: &'f mut DataFlowGraph, insn: Insn) -> Self {
        Self { dfg, insn }
    }
}

impl<'f> InsnBuilder<'f> for InstructionReplacer<'f> {
    fn dfg(&self) -> &DataFlowGraph {
        self.dfg
    }

    fn dfg_mut(&mut self) -> &mut DataFlowGraph {
        self.dfg
    }

    fn build(self, insn: InsnData) -> (Insn, &'f mut DataFlowGraph) {
        {
            // TODO: assert result arity
            self.dfg.insns[self.insn] = insn;
        }
        (self.insn, self.dfg)
    }
}

// impl<'a> FunctionCursor<'a> {
//     pub fn remove_insn(&mut self) {
//         match self.pos {
//             CursorPosition::Nowhere | CursorPosition::Before(_) => panic!("invalid position"),
//             CursorPosition::At(insn) => {
//                 if let Some(insn_after) = self.layout().next_insn(insn) {
//                     self.set_pos(CursorPosition::At(insn_after));
//                 } else {
//                     let block = self.layout().insn_block(insn).unwrap();
//                     self.set_pos(CursorPosition::After(block));
//                 }
//                 self.func.layout.remove_insn(insn)
//             }
//             CursorPosition::After(block) => self
//                 .func
//                 .layout
//                 .remove_insn(self.func.layout.last_insn(block).unwrap()),
//         }
//     }
// }

#[derive(Debug)]
pub struct BlockData {
    pub name: Symbol,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Block(u32);
entity_impl!(Block);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Value(u32);
entity_impl!(Value);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Insn(u32);
entity_impl!(Insn);

#[derive(Debug, Default)]
pub struct DataFlowGraph {
    pub blocks: PrimaryMap<Block, BlockData>,
    pub block_params: SecondaryMap<Block, EntityList<Value>>,
    pub predecessors: SecondaryMap<Block, Vec<Block>>,
    pub successors: SecondaryMap<Block, Vec<Block>>,
    /// N.B. We can't use EntitySet since it doesn't have helpful ops
    /// for union, intersect, etc., or even a remove, which is needed
    /// for dominator calculation.
    pub dominators: SecondaryMap<Block, HashSet<Block>>,
    pub postdominators: SecondaryMap<Block, HashSet<Block>>,

    pub dead_blocks: HashSet<Block>,

    pub value_pool: ListPool<Value>,
    pub values: PrimaryMap<Value, ValueData>,

    pub insns: PrimaryMap<Insn, InsnData>,
    pub insn_results: SecondaryMap<Insn, EntityList<Value>>,
}

impl Function {
    pub fn recalculate_cfg(&mut self) {
        self.dfg
            .predecessors
            .iter_mut()
            .for_each(|(_, x)| x.clear());
        self.dfg.successors.iter_mut().for_each(|(_, x)| x.clear());
        for (block, _) in &self.dfg.blocks {
            for insn in self.layout.insns(block) {
                match self.dfg.insns[insn] {
                    InsnData::Nullary(_)
                    | InsnData::Unary(..)
                    | InsnData::UnaryImm(..)
                    | InsnData::Binary(_, _)
                    | InsnData::Call(..)
                    | InsnData::CallClosure(..)
                    | InsnData::MakeClosure(..)
                    | InsnData::LoadStatic(..) => {}
                    InsnData::BrIf(_, _, [then, then_else]) => {
                        self.dfg.successors[block].push(then.0);
                        self.dfg.successors[block].push(then_else.0);
                        self.dfg.predecessors[then.0].push(block);
                        self.dfg.predecessors[then_else.0].push(block);
                    }
                    InsnData::Nary(Opcode::Ret, _) => {}
                    InsnData::BlockCall(Opcode::Jmp, goto) => {
                        self.dfg.successors[block].push(goto.0);
                        self.dfg.predecessors[goto.0].push(block);
                    }
                    _ => unimplemented!(),
                }
            }
        }
    }

    /// N.B. [`Self::recalculate_cfg`] must be called before this
    /// function, if the CFG has not been calculated yet or has been
    /// invalidated.
    pub fn recalculate_dominators(&mut self) {
        let entry = self.layout.entry_block().unwrap();

        for (block, _) in &self.dfg.blocks {
            //if !self.dfg.predecessors[block].is_empty() {
            self.dfg.dominators[block] = self
                .dfg
                .blocks
                .keys()
                //.filter(|x| !self.dfg.predecessors[*x].is_empty())
                .collect();
            self.dfg.postdominators[block] = self
                .dfg
                .blocks
                .keys()
                //.filter(|x| !self.dfg.predecessors[*x].is_empty())
                .collect();
            //} else {
            //    self.dfg.dominators[block] = [block].into_iter().collect();
            //    self.dfg.postdominators[block] = [block].into_iter().collect();
            //}
        }

        let mut worklist = vec![entry];
        while let Some(block) = worklist.pop() {
            let new = im::hashset![block].union(
                self.dfg.predecessors[block]
                    .iter()
                    .map(|x| self.dfg.dominators[*x].clone())
                    .reduce(|acc, x| acc.intersection(x))
                    .unwrap_or_default(),
            );
            if new != self.dfg.dominators[block] {
                self.dfg.dominators[block] = new;
                for block in &self.dfg.successors[block] {
                    worklist.push(*block);
                }
            }
        }

        let last = self.layout.last_block().unwrap();

        let mut worklist = vec![last];
        while let Some(block) = worklist.pop() {
            let new = im::hashset![block].union(
                self.dfg.successors[block]
                    .iter()
                    .map(|x| self.dfg.postdominators[*x].clone())
                    .reduce(|acc, x| acc.intersection(x))
                    .unwrap_or_default(),
            );
            if new != self.dfg.postdominators[block] {
                self.dfg.postdominators[block] = new;
                for block in &self.dfg.predecessors[block] {
                    worklist.push(*block);
                }
            }
        }
    }
}

#[derive(Default)]
pub struct Layout {
    pub block_layout: SecondaryMap<Block, BlockNode>,
    pub insn_layout: SecondaryMap<Insn, InsnNode>,

    first_block: Option<Block>,
    last_block: Option<Block>,
}

impl fmt::Debug for Layout {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Layout")
            .field("blocks", &DebugAdapterBlocks(self))
            .field("insn_layout", &self.insn_layout)
            .field("first_block", &self.first_block)
            .field("last_block", &self.last_block)
            .finish()
    }
}

struct DebugAdapterBlocks<'f>(&'f Layout);

impl<'f> fmt::Debug for DebugAdapterBlocks<'f> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.0.blocks()).finish()
    }
}

impl Layout {
    pub fn contains_block(&self, block: Block) -> bool {
        self.first_block == Some(block) || self.block_layout[block].prev.is_some()
    }

    pub fn block_contains_insn(&self, block: Block, insn: Insn) -> bool {
        self.insn_layout[insn].block == Some(block).into()
    }

    pub fn append_block(&mut self, block: Block) {
        debug_assert!(!self.contains_block(block));
        {
            let node = &mut self.block_layout[block];
            node.prev = self.last_block.into();
            node.next = None.into();
        }
        if let Some(last) = self.last_block {
            self.block_layout[last].next = block.into();
        } else {
            self.first_block = Some(block);
        }
        self.last_block = Some(block);
    }

    pub fn append_insn(&mut self, block: Block, insn: Insn) {
        debug_assert!(self.contains_block(block));
        debug_assert!(!self.block_contains_insn(block, insn));
        {
            let node = &mut self.insn_layout[insn];
            node.block = block.into();
            node.prev = self.block_layout[block].last_insn;
            node.next = None.into();
        }
        if let Some(last) = self.block_layout[block].last_insn.expand() {
            self.insn_layout[last].next = insn.into();
        } else {
            self.block_layout[block].first_insn = Some(insn).into();
        }
        self.block_layout[block].last_insn = Some(insn).into();
    }

    pub fn insert_block_before(&mut self, block: Block, before: Block) {
        debug_assert!(!self.contains_block(block));
        debug_assert!(self.contains_block(before));

        let prev = self.block_layout[before].prev;
        {
            let node = &mut self.block_layout[block];
            node.next = before.into();
            node.prev = prev;
        }
        self.block_layout[before].prev = block.into();
        match prev.expand() {
            None => self.first_block = Some(block),
            Some(prev) => self.block_layout[prev].next = block.into(),
        }
    }

    pub fn insert_insn_before(&mut self, insn: Insn, before: Insn) {
        let block = self.insn_block(before).unwrap();
        debug_assert!(self.block_contains_insn(block, before));
        debug_assert!(!self.block_contains_insn(block, insn));

        let prev = self.insn_layout[before].prev;
        {
            let node = &mut self.insn_layout[insn];
            node.block = block.into();
            node.next = before.into();
            node.prev = prev;
        }
        self.insn_layout[before].prev = insn.into();
        match prev.expand() {
            None => self.block_layout[block].first_insn = insn.into(),
            Some(prev) => self.insn_layout[prev].next = insn.into(),
        }
    }

    pub fn insert_block_after(&mut self, block: Block, after: Block) {
        debug_assert!(!self.contains_block(block));
        debug_assert!(self.contains_block(after));

        let next = self.block_layout[after].next;
        {
            let node = &mut self.block_layout[block];
            node.next = next;
            node.prev = after.into();
        }
        self.block_layout[after].next = block.into();
        match next.expand() {
            None => self.last_block = Some(block),
            Some(next) => self.block_layout[next].prev = block.into(),
        }
    }

    pub fn insert_insn_after(&mut self, insn: Insn, after: Insn) {
        let block = self.insn_block(after).unwrap();
        debug_assert!(self.block_contains_insn(block, after));
        debug_assert!(!self.block_contains_insn(block, insn));

        let next = self.insn_layout[after].next;
        {
            let node = &mut self.insn_layout[insn];
            node.block = block.into();
            node.prev = after.into();
            node.next = next;
        }
        self.insn_layout[after].next = insn.into();
        match next.expand() {
            None => self.block_layout[block].last_insn = insn.into(),
            Some(next) => self.insn_layout[next].next = insn.into(),
        }
    }

    pub fn remove_insn(&mut self, insn: Insn) {
        let block = self.insn_block(insn).unwrap();
        let next = self.insn_layout[insn].next;
        let prev = self.insn_layout[insn].prev;
        {
            let node = &mut self.insn_layout[insn];
            node.block = None.into();
            node.next = None.into();
            node.prev = None.into();
        }
        match next.expand() {
            None => self.block_layout[block].last_insn = prev,
            Some(next) => self.insn_layout[next].prev = prev,
        }
        match prev.expand() {
            None => self.block_layout[block].first_insn = next,
            Some(prev) => self.insn_layout[prev].next = next,
        }
    }

    pub fn entry_block(&self) -> Option<Block> {
        self.first_block
    }

    pub fn last_block(&self) -> Option<Block> {
        self.last_block
    }

    pub fn prev_block(&self, block: Block) -> Option<Block> {
        self.block_layout[block].prev.expand()
    }

    pub fn next_block(&self, block: Block) -> Option<Block> {
        self.block_layout[block].next.expand()
    }

    pub fn insn_block(&self, insn: Insn) -> Option<Block> {
        self.insn_layout[insn].block.expand()
    }

    pub fn next_insn(&self, insn: Insn) -> Option<Insn> {
        self.insn_layout[insn].next.expand()
    }

    pub fn prev_insn(&self, insn: Insn) -> Option<Insn> {
        self.insn_layout[insn].prev.expand()
    }

    pub fn first_insn(&self, block: Block) -> Option<Insn> {
        self.block_layout[block].first_insn.expand()
    }

    pub fn last_insn(&self, block: Block) -> Option<Insn> {
        self.block_layout[block].last_insn.expand()
    }

    pub fn blocks(&'_ self) -> Blocks<'_> {
        Blocks {
            layout: self,
            next: self.first_block,
        }
    }

    pub fn insns(&'_ self, block: Block) -> Insns<'_> {
        Insns {
            layout: self,
            next: self.block_layout[block].first_insn.expand(),
        }
    }
}

pub struct Blocks<'b> {
    layout: &'b Layout,
    next: Option<Block>,
}

impl<'b> Iterator for Blocks<'b> {
    type Item = Block;

    fn next(&mut self) -> Option<Block> {
        if let Some(block) = self.next.map(|x| self.layout.next_block(x)) {
            let next = self.next;
            self.next = block;
            next
        } else {
            self.next
        }
    }
}

pub struct Insns<'b> {
    layout: &'b Layout,
    next: Option<Insn>,
}

impl<'b> Iterator for Insns<'b> {
    type Item = Insn;

    fn next(&mut self) -> Option<Insn> {
        if let Some(insn) = self.next.map(|x| self.layout.next_insn(x)) {
            let next = self.next;
            self.next = insn;
            next
        } else {
            self.next
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct BlockNode {
    prev: PackedOption<Block>,
    next: PackedOption<Block>,
    first_insn: PackedOption<Insn>,
    last_insn: PackedOption<Insn>,
}

#[derive(Clone, Debug, Default)]
pub struct InsnNode {
    block: PackedOption<Block>,
    prev: PackedOption<Insn>,
    next: PackedOption<Insn>,
}

#[derive(Debug)]
pub enum ValueData {
    Result(Insn, u16),
    Block(Block, u16),
}

impl DataFlowGraph {
    pub fn clear(&mut self) {
        self.blocks.clear();
        self.block_params.clear();

        self.value_pool.clear();
        self.values.clear();

        self.insns.clear();
        self.insn_results.clear();
    }

    pub fn first_result(&self, insn: Insn) -> Value {
        self.insn_results[insn]
            .get(0, &self.value_pool)
            .expect("Insn result")
    }
}

#[derive(Debug)]
pub struct Function {
    pub dfg: DataFlowGraph,
    pub layout: Layout,
    pub name: Symbol,
}

impl Function {
    pub fn new(name: Symbol) -> Self {
        Self {
            name,
            dfg: DataFlowGraph::default(),
            layout: Layout::default(),
        }
    }

    pub fn arity(&self) -> usize {
        self.dfg.block_params[self.layout.entry_block().expect("Function had entry block")]
            .len(&self.dfg.value_pool)
    }

    fn assert_value_valid(&self, block: Block, value: Value) {
        match self.dfg.values[value] {
            ValueData::Result(insn, _) => {
                let insn_block = self.layout.insn_block(insn).expect("Instruction had block");
                assert!(
                    self.dfg.dominators[block].contains(&insn_block),
                    "Instruction result {} was not valid in block {}",
                    value.pretty(self).pretty(80),
                    block.pretty(self).pretty(80)
                );
                let insn_results = self.dfg.insn_results[insn].as_slice(&self.dfg.value_pool);
                assert!(
                    insn_results.contains(&value),
                    "Instruction results contain resultant value"
                );
            }
            ValueData::Block(value_block, _) => {
                assert!(
                    self.dfg.dominators[block].contains(&value_block),
                    "Block parameter {} was not valid in block {}",
                    value.pretty(self).pretty(80),
                    block.pretty(self).pretty(80)
                );

                let block_params =
                    self.dfg.block_params[value_block].as_slice(&self.dfg.value_pool);
                assert!(
                    block_params.contains(&value),
                    "Block params did not contain resultant value"
                );
            }
        }
    }

    pub fn assert_valid(&self) {
        let _entry = self.layout.entry_block().expect("Function had entry block");
        for (block, _) in &self.dfg.blocks {
            let mut found_branch = 0;
            for insn in self.layout.insns(block) {
                match self.dfg.insns[insn] {
                    InsnData::Unary(_, val) => self.assert_value_valid(block, val),
                    InsnData::Binary(_, [a, b]) => {
                        self.assert_value_valid(block, a);
                        self.assert_value_valid(block, b);
                    }
                    InsnData::BlockCall(_, BlockRef(_, vals))
                    | InsnData::Nary(Opcode::Ret, vals) => {
                        found_branch += 1;
                        for val in vals.as_slice(&self.dfg.value_pool) {
                            self.assert_value_valid(block, *val);
                        }
                    }
                    InsnData::Nary(_, vs)
                    | InsnData::MakeClosure(_, _, vs)
                    | InsnData::Call(_, _, vs) => {
                        for v in vs.as_slice(&self.dfg.value_pool) {
                            self.assert_value_valid(block, *v);
                        }
                    }
                    InsnData::CallClosure(_, v, vs) => {
                        self.assert_value_valid(block, v);
                        for v in vs.as_slice(&self.dfg.value_pool) {
                            self.assert_value_valid(block, *v);
                        }
                    }
                    InsnData::BrIf(_, cond, [BlockRef(_, then_vs), BlockRef(_, else_vs)]) => {
                        found_branch += 1;

                        self.assert_value_valid(block, cond);
                        for v in then_vs.as_slice(&self.dfg.value_pool) {
                            self.assert_value_valid(block, *v);
                        }
                        for v in else_vs.as_slice(&self.dfg.value_pool) {
                            self.assert_value_valid(block, *v);
                        }
                    }
                    InsnData::UnaryImm(..) | InsnData::Nullary(..) | InsnData::LoadStatic(..) => {}
                }
            }
            assert!(
                found_branch == 1,
                "Block {} did not have an exit point, or was not basic",
                block.pretty(self).pretty(80)
            );
        }
    }
}

impl Block {
    pub fn pretty_name(self, func: &Function) -> RcDoc<'_> {
        RcDoc::text(".")
            .append(func.dfg.blocks[self].name.as_str())
            .append(".")
            .append(self.as_u32().to_string())
    }

    pub fn params(self, func: &Function) -> &[Value] {
        func.dfg.block_params[self].as_slice(&func.dfg.value_pool)
    }

    fn pretty_params<'f>(self, func: &'f Function, params: &[Value]) -> RcDoc<'f> {
        if params.is_empty() {
            RcDoc::nil()
        } else {
            RcAllocator
                .intersperse(
                    params.iter().map(|x| x.pretty(func)),
                    RcDoc::text(",").append(RcDoc::space()),
                )
                .parens()
                .into_doc()
        }
    }

    pub fn pretty(self, func: &Function) -> RcDoc<'_> {
        self.pretty_name(func)
            .append(self.pretty_params(func, self.params(func)))
    }
}

impl Value {
    // TODO: value names
    pub fn pretty(self, _func: &Function) -> RcDoc<'_> {
        RcDoc::text("%").append(self.as_u32().to_string())
    }
}

impl Function {
    pub fn pretty(&self) {
        println!("fn {}:", self.name);
        for block in self.layout.blocks() {
            println!("  {}", block.pretty(self).pretty(80));
            for insn in self.layout.insns(block) {
                let data = &self.dfg.insns[insn];
                let results = self.dfg.insn_results[insn].as_slice(&self.dfg.value_pool);
                if !results.is_empty() {
                    print!(
                        "    {} = ",
                        RcAllocator
                            .intersperse(results.iter().map(|x| x.pretty(self)), RcDoc::text(", "))
                            .pretty(80)
                    );
                } else {
                    print!("    ");
                }
                match data {
                    InsnData::Nullary(op) => println!("{}", op),
                    InsnData::Unary(op, val) => println!("{} {}", op, val.pretty(self).pretty(80)),
                    InsnData::UnaryImm(op, Immediate::Boolean(b)) => println!("{op} {b}"),
                    InsnData::UnaryImm(op, Immediate::Integer(i)) => println!("{op} {i}"),
                    InsnData::Binary(op, [a, b]) => println!(
                        "{} {}, {}",
                        op,
                        a.pretty(self).pretty(80),
                        b.pretty(self).pretty(80)
                    ),
                    InsnData::BrIf(op, cond, [then, then_else]) => println!(
                        "{op} {}, {}{}, {}{}",
                        cond.pretty(self).pretty(80),
                        then.0.pretty_name(self).pretty(80),
                        then.0
                            .pretty_params(self, then.1.as_slice(&self.dfg.value_pool))
                            .pretty(80),
                        then_else.0.pretty_name(self).pretty(80),
                        then_else
                            .0
                            .pretty_params(self, then_else.1.as_slice(&self.dfg.value_pool))
                            .pretty(80),
                    ),
                    InsnData::Call(op, id, vals) | InsnData::MakeClosure(op, id, vals) => println!(
                        "{op} <id>({})",
                        RcAllocator
                            .intersperse(
                                vals.as_slice(&self.dfg.value_pool)
                                    .iter()
                                    .map(|x| x.pretty(self)),
                                RcDoc::text(", ")
                            )
                            .pretty(80)
                    ),
                    InsnData::CallClosure(op, closure, vals) => println!(
                        "{op} {}({})",
                        closure.pretty(self).pretty(80),
                        RcAllocator
                            .intersperse(
                                vals.as_slice(&self.dfg.value_pool)
                                    .iter()
                                    .map(|x| x.pretty(self)),
                                RcDoc::text(", ")
                            )
                            .pretty(80)
                    ),
                    InsnData::LoadStatic(op, id) => println!("{op} <id>"),
                    InsnData::Nary(op, vals) => {
                        println!(
                            "{op} {}",
                            RcAllocator
                                .intersperse(
                                    vals.as_slice(&self.dfg.value_pool)
                                        .iter()
                                        .map(|x| x.pretty(self)),
                                    RcDoc::text(", ")
                                )
                                .pretty(80)
                        )
                    }
                    InsnData::BlockCall(op, block) => println!(
                        "{op} {}{}",
                        block.0.pretty_name(self).pretty(80),
                        block
                            .0
                            .pretty_params(self, block.1.as_slice(&self.dfg.value_pool))
                            .pretty(80)
                    ),
                    // InsnData::Jmp(b, vals) => {
                    //     println!(
                    //         "jmp {}{}",
                    //         b.pretty_name(self).pretty(80),
                    //         b.pretty_params(self, vals.as_slice(&self.dfg.value_pool))
                    //             .pretty(80),
                    //     )
                    // }
                    // InsnData::Return(vals) => {
                    //     println!(
                    //         "return {}",
                    //         RcAllocator
                    //             .intersperse(
                    //                 vals.as_slice(&self.dfg.value_pool)
                    //                     .iter()
                    //                     .map(|x| x.pretty(self)),
                    //                 RcDoc::text(", ")
                    //             )
                    //             .pretty(80)
                    //     );
                    // }
                    // InsnData::MakeClosure(f, vals) => println!(
                    //     "make_closure <{f}>({})",
                    //     RcAllocator
                    //         .intersperse(
                    //             vals.as_slice(&self.dfg.value_pool)
                    //                 .iter()
                    //                 .map(|x| x.pretty(self)),
                    //             RcDoc::text(", ")
                    //         )
                    //         .pretty(80)
                    // ),
                    // InsnData::CallClosure(f, vals) => println!(
                    //     "call_closure {}({})",
                    //     f.pretty(self).pretty(80),
                    //     RcAllocator
                    //         .intersperse(
                    //             vals.as_slice(&self.dfg.value_pool)
                    //                 .iter()
                    //                 .map(|x| x.pretty(self)),
                    //             RcDoc::text(", ")
                    //         )
                    //         .pretty(80)
                    // ),
                    // InsnData::Call(f, vals) => println!(
                    //     "call <{f}>({})",
                    //     RcAllocator
                    //         .intersperse(
                    //             vals.as_slice(&self.dfg.value_pool)
                    //                 .iter()
                    //                 .map(|x| x.pretty(self)),
                    //             RcDoc::text(", ")
                    //         )
                    //         .pretty(80)
                    // ),
                    // InsnData::LoadStatic(f) => println!("load_static <{f}>"),
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct FunctionCursor<'a> {
    pub func: &'a mut Function,
    pos: CursorPosition,
}

impl<'a> FunctionCursor<'a> {
    pub fn new(func: &'a mut Function) -> Self {
        Self {
            func,
            pos: CursorPosition::Nowhere,
        }
    }

    pub fn layout(&self) -> &Layout {
        &self.func.layout
    }

    pub fn layout_mut(&mut self) -> &mut Layout {
        &mut self.func.layout
    }

    pub fn dfg(&self) -> &DataFlowGraph {
        &self.func.dfg
    }

    pub fn dfg_mut(&mut self) -> &mut DataFlowGraph {
        &mut self.func.dfg
    }

    pub fn pos(&self) -> CursorPosition {
        self.pos
    }

    pub fn set_pos(&mut self, pos: CursorPosition) {
        self.pos = pos
    }

    pub fn at(mut self, pos: CursorPosition) -> Self {
        self.set_pos(pos);
        self
    }

    pub fn at_insn(mut self, insn: Insn) -> Self {
        self.set_pos(CursorPosition::At(insn));
        self
    }

    // pub fn after_insn(mut self, insn: Insn) -> Self {
    //     self.goto_after_insn(insn);
    //     self
    // }

    // pub fn goto_after_insn(&mut self, insn: Insn) {
    //     let block = self.func.dfg.insn_block[insn].unwrap();
    //     let insns = &self.func.dfg.block_insns[block];
    //     if let Some(pos) = insns
    //         .iter()
    //         .enumerate()
    //         .find_map(|(i, x)| (*x == insn).then_some(i))
    //     {
    //         self.set_pos(CursorPosition::At(insns[pos]))
    //     } else {
    //         self.set_pos(CursorPosition::After(block));
    //     }
    // }

    pub fn goto_insn(&mut self, insn: Insn) {
        self.set_pos(CursorPosition::At(insn));
    }

    pub fn goto_block(&mut self, block: Block) {
        self.set_pos(CursorPosition::Before(block));
    }

    pub fn next_block(&mut self) -> Option<Block> {
        let next = if let Some(block) = self.current_block() {
            self.func.layout.next_block(block)
        } else {
            self.func.layout.entry_block()
        };
        self.set_pos(match next {
            Some(next) => CursorPosition::Before(next),
            None => CursorPosition::Nowhere,
        });
        next
    }

    pub fn prev_block(&mut self) -> Option<Block> {
        let prev = if let Some(block) = self.current_block() {
            self.func.layout.next_block(block)
        } else {
            self.func.layout.last_block()
        };
        self.set_pos(match prev {
            Some(prev) => CursorPosition::After(prev),
            None => CursorPosition::Nowhere,
        });
        prev
    }

    pub fn current_block(&self) -> Option<Block> {
        match self.pos() {
            CursorPosition::Nowhere => self.func.layout.first_block,
            CursorPosition::At(insn) => self.func.layout.insn_block(insn),
            CursorPosition::Before(block) | CursorPosition::After(block) => Some(block),
        }
    }

    pub fn current_insn(&self) -> Option<Insn> {
        match self.pos() {
            CursorPosition::At(insn) => Some(insn),
            _ => None,
        }
    }

    pub fn next_insn(&mut self) -> Option<Insn> {
        match self.pos() {
            CursorPosition::Nowhere | CursorPosition::After(..) => None,
            CursorPosition::At(insn) => {
                if let Some(next) = self.func.layout.next_insn(insn) {
                    self.set_pos(CursorPosition::At(next));
                    Some(next)
                } else {
                    self.set_pos(CursorPosition::After(
                        self.func.layout.insn_block(insn).unwrap(),
                    ));
                    None
                }
            }
            CursorPosition::Before(block) => {
                if let Some(next) = self.func.layout.first_insn(block) {
                    self.set_pos(CursorPosition::At(next));
                    Some(next)
                } else {
                    self.set_pos(CursorPosition::After(block));
                    None
                }
            }
        }
    }

    pub fn prev_insn(&mut self) -> Option<Insn> {
        match self.pos() {
            CursorPosition::Nowhere | CursorPosition::Before(..) => None,
            CursorPosition::At(insn) => {
                if let Some(prev) = self.func.layout.prev_insn(insn) {
                    self.set_pos(CursorPosition::At(prev));
                    Some(prev)
                } else {
                    self.set_pos(CursorPosition::Before(
                        self.func.layout.insn_block(insn).unwrap(),
                    ));
                    None
                }
            }
            CursorPosition::After(block) => {
                if let Some(last) = self.func.layout.last_insn(block) {
                    self.set_pos(CursorPosition::At(last));
                    Some(last)
                } else {
                    self.set_pos(CursorPosition::After(block));
                    None
                }
            }
        }
    }

    pub fn begin_block(&mut self, name: Symbol, arity: u16) -> (Block, EntityList<Value>) {
        let block = self.func.dfg.blocks.push(BlockData { name });
        for i in 0..arity {
            let value = self.func.dfg.values.push(ValueData::Block(block, i));
            self.func.dfg.block_params[block].push(value, &mut self.func.dfg.value_pool);
        }

        match self.pos() {
            CursorPosition::Nowhere => {
                self.func.layout.append_block(block);
                self.set_pos(CursorPosition::Before(block));
            }
            CursorPosition::Before(before) => {
                self.func.layout.insert_block_before(block, before);
                self.set_pos(CursorPosition::Before(block));
            }
            CursorPosition::After(after) => {
                self.func.layout.insert_block_after(block, after);
                self.set_pos(CursorPosition::After(block));
            }
            // split block? or just error
            _ => todo!(),
        }
        (block, self.func.dfg.block_params[block])
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum CursorPosition {
    Nowhere,
    /// Instructions are prepended *before* this insn
    At(Insn),
    /// Instructions cannot be inserted until next_insn is called.
    Before(Block),
    /// Instructions will be appended to the end of the block
    After(Block),
}
