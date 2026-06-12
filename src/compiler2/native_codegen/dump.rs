//! Cranelift body telemetry helpers.

use cranelift_codegen::ir::{self};

pub(crate) fn cranelift_body_stats(func: &ir::Function) -> (usize, usize) {
    let block_count = func.layout.blocks().count();
    let instruction_count = func
        .layout
        .blocks()
        .map(|block| func.layout.block_insts(block).count())
        .sum();
    (block_count, instruction_count)
}
