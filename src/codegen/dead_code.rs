use super::ssa::{Function, FunctionCursor};

/// Dead code elimination and block inlining

#[derive(Debug)]
struct DeadCode<'f> {
    pub func: FunctionCursor<'f>,
}

pub fn run(func: &mut Function) {
    let mut ctx = DeadCode {
        func: FunctionCursor::new(func),
    };

    ctx.run();
}

impl<'f> DeadCode<'f> {
    fn run(&mut self) {
        self.dead_blocks();
    }

    fn dead_blocks(&mut self) {
        let dfg = &mut self.func.func.dfg;
        let layout = &mut self.func.func.layout;
        for block in layout.blocks().collect::<Vec<_>>() {
            if dfg.predecessors[block].is_empty() && Some(block) != layout.entry_block() {
                layout.remove_block(block);
                dfg.predecessors[block] = Vec::new();
                dfg.successors[block] = Vec::new();
            }
        }
    }
}
