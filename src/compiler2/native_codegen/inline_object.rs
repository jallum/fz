//! A struct, tuple or closure whose header compiled code writes itself.
//!
//! Compiled code places the object with `emit_place` and stores the words the
//! runtime used to store: a struct's schema id, or a closure's header and
//! code address. The captures and fields that follow are stored by the code
//! that builds the object, before any other code can read it.
//!
//! The runtime stores nothing into the object. The slots and kind bytes after
//! the header are written in full by the code that knows the values. The
//! bytes after the last kind byte only pad the object to whole 16-byte
//! slots; nothing reads them, and a struct's were never zeroed.
//!
//! A continuation frame is a closure, so it is placed here too, under its own
//! statistics kind.

use super::place::emit_place;
use super::*;
use cranelift_codegen::ir::{self, InstBuilder, MemFlagsData, types};
use fz_runtime::any_value::{CLOSURE_CODE_OFFSET, ValueKind, closure_size_for_count, struct_header_word};
use fz_runtime::heap::HeapAllocKind;

/// An object placed on the heap: where it starts, and the ref word that names
/// it.
#[derive(Clone, Copy)]
pub(crate) struct Placed {
    pub(crate) address: ir::Value,
    pub(crate) reference: ir::Value,
}

/// Place a struct of `size` bytes whose schema is `schema_id`, and write its
/// header word.
pub(super) fn emit_struct<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    schema_id: u32,
    size: usize,
) -> Placed {
    let address = emit_place(body, HeapAllocKind::Struct, size);
    let header = body.b.ins().iconst(types::I64, struct_header_word(schema_id) as i64);
    body.b.ins().store(MemFlagsData::trusted(), header, address, 0);
    Placed {
        address,
        reference: body.heap_ref_word_from_addr(address, ValueKind::STRUCT),
    }
}

/// Place a closure of `captured_count` captures, counted under `kind`
/// (`Closure`, or `Continuation` for a frame), and write its `header` word and
/// its `code_addr`.
pub(super) fn emit_closure<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    kind: HeapAllocKind,
    header: u64,
    captured_count: usize,
    code_addr: ir::Value,
) -> Placed {
    let size = closure_size_for_count(captured_count);
    let address = emit_place(body, kind, size);
    let flags = MemFlagsData::trusted();
    let header = body.b.ins().iconst(types::I64, header as i64);
    body.b.ins().store(flags, header, address, 0);
    body.b.ins().store(flags, code_addr, address, CLOSURE_CODE_OFFSET);
    Placed {
        address,
        reference: body.heap_ref_word_from_addr(address, ValueKind::CLOSURE),
    }
}
