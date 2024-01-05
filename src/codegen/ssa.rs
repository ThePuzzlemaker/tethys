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
    IntegerConst(i64),
    IntegerAdd(Value, Value),
    IntegerSub(Value, Value),
    IntegerMult(Value, Value),
    IntegerDiv(Value, Value),
    IntegerMod(Value, Value),
    IntegerShl(Value, Value),
    IntegerShr(Value, Value),
    IntegerOr(Value, Value),
    IntegerXor(Value, Value),
    IntegerAnd(Value, Value),
    IntegerPow(Value, Value),
    IntegerEq(Value, Value),
    IntegerNeq(Value, Value),
    IntegerGt(Value, Value),
    IntegerLt(Value, Value),
    IntegerGte(Value, Value),
    IntegerLte(Value, Value),
    BooleanConst(bool),
    BrIf(Value, Block, EntityList<Value>, Block, EntityList<Value>),
    Jmp(Block, EntityList<Value>),
    Return(EntityList<Value>),
    MakeClosure(CoreAstId, EntityList<Value>),
    CallClosure(Value, EntityList<Value>),
    Call(CoreAstId, EntityList<Value>),
    LoadStatic(CoreAstId),
    Unit,
}

impl<'a> FunctionCursor<'a> {
    pub fn iconst(&mut self, i: i64) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerConst(i));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn bconst(&mut self, b: bool) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::BooleanConst(b));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn unit(&mut self) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::Unit);
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn iadd(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerAdd(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn isub(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerSub(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn imult(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerMult(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn idiv(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerDiv(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn imod(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerMod(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn ipow(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerPow(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn ishl(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerShl(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn ishr(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerShr(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn iand(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerAnd(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn ior(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerOr(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn ixor(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerXor(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn ieq(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerEq(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn ineq(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerNeq(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn igt(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerGt(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn ilt(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerLt(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn igte(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerGte(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn ilte(&mut self, lhs: Value, rhs: Value) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::IntegerLte(lhs, rhs));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn make_closure(&mut self, func: CoreAstId, values: &[Value]) -> Value {
        let mut value_list = EntityList::new();
        value_list.extend(values.iter().copied(), &mut self.func.dfg.value_pool);
        let insn = self
            .func
            .dfg
            .insns
            .push(InsnData::MakeClosure(func, value_list));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn call_closure(&mut self, closure: Value, values: &[Value]) -> Value {
        let mut value_list = EntityList::new();
        value_list.extend(values.iter().copied(), &mut self.func.dfg.value_pool);
        let insn = self
            .func
            .dfg
            .insns
            .push(InsnData::CallClosure(closure, value_list));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn call(&mut self, func: CoreAstId, values: &[Value]) -> Value {
        let mut value_list = EntityList::new();
        value_list.extend(values.iter().copied(), &mut self.func.dfg.value_pool);
        let insn = self.func.dfg.insns.push(InsnData::Call(func, value_list));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn load_static(&mut self, val: CoreAstId) -> Value {
        let insn = self.func.dfg.insns.push(InsnData::LoadStatic(val));
        let value = self.func.dfg.values.push(ValueData::Result(insn, 0));
        self.func.dfg.insn_results[insn].push(value, &mut self.func.dfg.value_pool);
        self.build_insn(insn);
        value
    }

    pub fn br_if(
        &mut self,
        cond: Value,
        then: Block,
        then_values: &[Value],
        then_else: Block,
        then_else_values: &[Value],
    ) -> Insn {
        let mut then_val_list = EntityList::new();
        then_val_list.extend(then_values.iter().copied(), &mut self.func.dfg.value_pool);
        let mut then_else_val_list = EntityList::new();
        then_else_val_list.extend(
            then_else_values.iter().copied(),
            &mut self.func.dfg.value_pool,
        );

        let insn = self.func.dfg.insns.push(InsnData::BrIf(
            cond,
            then,
            then_val_list,
            then_else,
            then_else_val_list,
        ));
        let block = self.current_block().unwrap();
        self.func.dfg.successors[block].extend([then, then_else]);
        self.func.dfg.predecessors[then].push(block);
        self.func.dfg.predecessors[then_else].push(block);
        self.build_insn(insn);
        insn
    }

    pub fn jmp(&mut self, goto: Block, values: &[Value]) -> Insn {
        let block = self.current_block().unwrap();
        let mut val_list = EntityList::new();
        val_list.extend(values.iter().copied(), &mut self.func.dfg.value_pool);

        let insn = self.func.dfg.insns.push(InsnData::Jmp(goto, val_list));
        self.func.dfg.predecessors[goto].push(block);
        self.func.dfg.successors[block].push(goto);
        self.build_insn(insn);
        insn
    }

    pub fn ret(&mut self, values: &[Value]) -> Insn {
        let mut val_list = EntityList::new();
        val_list.extend(values.iter().copied(), &mut self.func.dfg.value_pool);

        let insn = self.func.dfg.insns.push(InsnData::Return(val_list));
        self.build_insn(insn);
        insn
    }

    fn build_insn(&mut self, insn: Insn) {
        match self.pos {
            CursorPosition::Nowhere | CursorPosition::Before(_) => panic!("invalid position"),
            CursorPosition::At(before) => self.func.layout.insert_insn_before(insn, before),
            CursorPosition::After(block) => self.func.layout.append_insn(block, insn),
        }
    }
}

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

    pub value_pool: ListPool<Value>,
    pub values: PrimaryMap<Value, ValueData>,

    pub insns: PrimaryMap<Insn, InsnData>,
    pub insn_results: SecondaryMap<Insn, EntityList<Value>>,
}

impl Function {
    pub fn calculate_dominators(&mut self) {
        let entry = self.layout.entry_block().unwrap();

        for (block, _) in &self.dfg.blocks {
            self.dfg.dominators[block] = self.dfg.blocks.keys().collect();
            self.dfg.postdominators[block] = self.dfg.blocks.keys().collect();
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
                    InsnData::IntegerConst(_)
                    | InsnData::BooleanConst(_)
                    | InsnData::Unit
                    | InsnData::LoadStatic(..) => {}
                    InsnData::IntegerAdd(a, b)
                    | InsnData::IntegerMult(a, b)
                    | InsnData::IntegerSub(a, b)
                    | InsnData::IntegerDiv(a, b)
                    | InsnData::IntegerMod(a, b)
                    | InsnData::IntegerPow(a, b)
                    | InsnData::IntegerShl(a, b)
                    | InsnData::IntegerShr(a, b)
                    | InsnData::IntegerAnd(a, b)
                    | InsnData::IntegerOr(a, b)
                    | InsnData::IntegerXor(a, b)
                    | InsnData::IntegerEq(a, b)
                    | InsnData::IntegerNeq(a, b)
                    | InsnData::IntegerGt(a, b)
                    | InsnData::IntegerLt(a, b)
                    | InsnData::IntegerLte(a, b)
                    | InsnData::IntegerGte(a, b) => {
                        self.assert_value_valid(block, a);
                        self.assert_value_valid(block, b);
                    }
                    InsnData::MakeClosure(_, vs) | InsnData::Call(_, vs) => {
                        for v in vs.as_slice(&self.dfg.value_pool) {
                            self.assert_value_valid(block, *v);
                        }
                    }
                    InsnData::CallClosure(v, vs) => {
                        self.assert_value_valid(block, v);
                        for v in vs.as_slice(&self.dfg.value_pool) {
                            self.assert_value_valid(block, *v);
                        }
                    }
                    InsnData::BrIf(cond, _, then_vs, _, else_vs) => {
                        found_branch += 1;

                        self.assert_value_valid(block, cond);
                        for v in then_vs.as_slice(&self.dfg.value_pool) {
                            self.assert_value_valid(block, *v);
                        }
                        for v in else_vs.as_slice(&self.dfg.value_pool) {
                            self.assert_value_valid(block, *v);
                        }
                    }
                    InsnData::Jmp(_, vs) | InsnData::Return(vs) => {
                        found_branch += 1;

                        for v in vs.as_slice(&self.dfg.value_pool) {
                            self.assert_value_valid(block, *v);
                        }
                    }
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
                    InsnData::Unit => println!("unit"),
                    InsnData::IntegerConst(v) => println!("iconst {v}"),
                    InsnData::IntegerAdd(a, b) => println!("iadd %{}, %{}", a.as_u32(), b.as_u32()),
                    InsnData::IntegerMult(a, b) => {
                        println!("imult %{}, %{}", a.as_u32(), b.as_u32())
                    }
                    InsnData::IntegerSub(a, b) => {
                        println!("isub %{}, %{}", a.as_u32(), b.as_u32())
                    }
                    InsnData::IntegerDiv(a, b) => {
                        println!("idiv %{}, %{}", a.as_u32(), b.as_u32())
                    }
                    InsnData::IntegerMod(a, b) => {
                        println!("imod %{}, %{}", a.as_u32(), b.as_u32())
                    }
                    InsnData::IntegerPow(a, b) => {
                        println!("ipow %{}, %{}", a.as_u32(), b.as_u32())
                    }
                    InsnData::IntegerShl(a, b) => {
                        println!("ishl %{}, %{}", a.as_u32(), b.as_u32())
                    }
                    InsnData::IntegerShr(a, b) => {
                        println!("ishr %{}, %{}", a.as_u32(), b.as_u32())
                    }
                    InsnData::IntegerAnd(a, b) => {
                        println!("iand %{}, %{}", a.as_u32(), b.as_u32())
                    }
                    InsnData::IntegerOr(a, b) => {
                        println!("ior %{}, %{}", a.as_u32(), b.as_u32())
                    }
                    InsnData::IntegerXor(a, b) => {
                        println!("ixor %{}, %{}", a.as_u32(), b.as_u32())
                    }
                    InsnData::IntegerEq(a, b) => {
                        println!("ieq %{}, %{}", a.as_u32(), b.as_u32())
                    }
                    InsnData::IntegerNeq(a, b) => {
                        println!("ineq %{}, %{}", a.as_u32(), b.as_u32())
                    }
                    InsnData::IntegerGt(a, b) => {
                        println!("igt %{}, %{}", a.as_u32(), b.as_u32())
                    }
                    InsnData::IntegerLt(a, b) => {
                        println!("ilt %{}, %{}", a.as_u32(), b.as_u32())
                    }
                    InsnData::IntegerLte(a, b) => {
                        println!("ilte %{}, %{}", a.as_u32(), b.as_u32())
                    }
                    InsnData::IntegerGte(a, b) => {
                        println!("igte %{}, %{}", a.as_u32(), b.as_u32())
                    }
                    InsnData::BooleanConst(b) => println!("bconst {b}"),
                    InsnData::BrIf(c, b1, b1_vals, b2, b2_vals) => println!(
                        "br_if %{}, {}{}, {}{}",
                        c.as_u32(),
                        b1.pretty_name(self).pretty(80),
                        b1.pretty_params(self, b1_vals.as_slice(&self.dfg.value_pool))
                            .pretty(80),
                        b2.pretty_name(self).pretty(80),
                        b2.pretty_params(self, b2_vals.as_slice(&self.dfg.value_pool))
                            .pretty(80),
                    ),
                    InsnData::Jmp(b, vals) => {
                        println!(
                            "jmp {}{}",
                            b.pretty_name(self).pretty(80),
                            b.pretty_params(self, vals.as_slice(&self.dfg.value_pool))
                                .pretty(80),
                        )
                    }
                    InsnData::Return(vals) => {
                        println!(
                            "return {}",
                            RcAllocator
                                .intersperse(
                                    vals.as_slice(&self.dfg.value_pool)
                                        .iter()
                                        .map(|x| x.pretty(self)),
                                    RcDoc::text(", ")
                                )
                                .pretty(80)
                        );
                    }
                    InsnData::MakeClosure(f, vals) => println!(
                        "make_closure <{f}>({})",
                        RcAllocator
                            .intersperse(
                                vals.as_slice(&self.dfg.value_pool)
                                    .iter()
                                    .map(|x| x.pretty(self)),
                                RcDoc::text(", ")
                            )
                            .pretty(80)
                    ),
                    InsnData::CallClosure(f, vals) => println!(
                        "call_closure {}({})",
                        f.pretty(self).pretty(80),
                        RcAllocator
                            .intersperse(
                                vals.as_slice(&self.dfg.value_pool)
                                    .iter()
                                    .map(|x| x.pretty(self)),
                                RcDoc::text(", ")
                            )
                            .pretty(80)
                    ),
                    InsnData::Call(f, vals) => println!(
                        "call <{f}>({})",
                        RcAllocator
                            .intersperse(
                                vals.as_slice(&self.dfg.value_pool)
                                    .iter()
                                    .map(|x| x.pretty(self)),
                                RcDoc::text(", ")
                            )
                            .pretty(80)
                    ),
                    InsnData::LoadStatic(f) => println!("load_static <{f}>"),
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
