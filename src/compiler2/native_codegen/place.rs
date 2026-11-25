//! Where an inline allocation gets its room.
//!
//! Compiled code places an object by bumping the heap's tip: load `bump_top`
//! and `block_end`, add the size, compare, store the new top. A tip with no
//! room sends the code to one cold block, which calls the runtime's
//! `fz_heap_room` and gets back an address; both paths join at one `placed`
//! block, so each kind writes its object once, after the join. The runtime
//! only finds room and writes nothing into the object.
//!
//! The process register is read afresh in each block that uses it, as the
//! pinned register is a copy that costs one move. A value held across the
//! cold call would have to live in a register the call's argument and result
//! also claim; read per block, the address is in the call's result register
//! on both paths and the join needs no move.
//!
//! `emit_place` is the one emitter of that bump. Every inline allocation site
//! places through it, and it counts the site after the join, so a placement
//! the runtime made room for is counted by the same site as one the tip took.

use super::*;
use cranelift_codegen::ir::{self, InstBuilder, MemFlagsData, condcodes::IntCC, types};
use fz_runtime::alloc_site::AllocSite;
use fz_runtime::heap::{HeapAllocKind, INLINE_ALLOC_LAYOUT};
use fz_runtime::ir_runtime::fz_heap_room;
use fz_runtime::process_abi::PROCESS_HEAP_OFFSET;

/// Place `size` bytes (a multiple of 16) on the heap and answer the address
/// the object starts at. The caller writes every word of the object.
pub(super) fn emit_place<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    kind: HeapAllocKind,
    size: usize,
) -> ir::Value {
    let layout = INLINE_ALLOC_LAYOUT;
    let flags = MemFlagsData::trusted();
    let field = |offset: usize| PROCESS_HEAP_OFFSET + offset as i32;
    let process = body.process_arg();
    let top = body.b.ins().load(types::I64, flags, process, field(layout.bump_top));
    let end = body.b.ins().load(types::I64, flags, process, field(layout.block_end));
    let new_top = body.b.ins().iadd_imm_s(top, size as i64);
    let fits = body.b.ins().icmp(IntCC::UnsignedLessThanOrEqual, new_top, end);
    let inline = body.b.create_block();
    let room = body.b.create_block();
    let placed = body.b.create_block();
    body.b.append_block_param(placed, types::I64);
    body.b.ins().brif(fits, inline, &[], room, &[]);

    body.b.switch_to_block(room);
    body.b.seal_block(room);
    body.b.set_cold_block(room);
    let process = body.process_arg();
    let bytes = body.b.ins().iconst(types::I64, size as i64);
    let from_runtime = runtime_call1!(body, fz_heap_room, [process, bytes]);
    body.b.ins().jump(placed, &[from_runtime.into()]);

    body.b.switch_to_block(inline);
    body.b.seal_block(inline);
    let process = body.process_arg();
    body.b.ins().store(flags, new_top, process, field(layout.bump_top));
    body.b.ins().jump(placed, &[top.into()]);

    body.b.switch_to_block(placed);
    body.b.seal_block(placed);
    let scope = body.scope;
    scope.sites.borrow_mut().count(
        body,
        AllocSite {
            kind,
            bytes: size as u32,
            function: scope.function.to_owned(),
        },
    );
    body.b.block_params(placed)[0]
}

#[cfg(test)]
#[path = "place_test.rs"]
mod place_test;
