//! A body frame's slots, read and written where they are.
//!
//! A body frame is one continuation descriptor that a chain of continuations
//! runs in. It starts as a lazy descriptor in a stack slot and moves to the
//! heap when something keeps it past the stack it lives on, so each access
//! reads the frame's tag and picks the layout. Both layouts keep one raw word
//! per slot followed by one kind byte per slot; only where the slots start
//! and how kinds are spelled differ.

use super::closure::{
    LAZY_CONT_HEADER_BYTES, LAZY_CONT_KIND_ATOM, LAZY_CONT_KIND_F64, LAZY_CONT_KIND_I64, LAZY_CONT_KIND_REF,
};
use super::*;
use crate::fz_ir::FrameLane;
use cranelift_codegen::ir::{self, InstBuilder, MemFlags, condcodes::IntCC, types};
use cranelift_module::Module;
use fz_runtime::any_value::{
    AnyValueRefPacking, CLOSURE_CAPTURES_OFFSET, CLOSURE_CODE_OFFSET, NIL_ATOM_ID, TAG_LAZY_CONT, ValueKind,
};
use fz_runtime::ir_runtime::{fz_heap_frame_clear, fz_heap_frame_store_ref};

/// Where a frame's slots are, read once per access from the frame's word.
#[derive(Clone, Copy)]
struct FrameRow {
    on_stack: ir::Value,
    address: ir::Value,
    captures: ir::Value,
}

/// A scalar lane, which both layouts hold as the value's raw bits.
#[derive(Clone, Copy)]
enum RawLane {
    Int,
    Float,
    Atom,
}

impl RawLane {
    /// The kind byte the stack layout and the heap layout write for the lane.
    fn kind_bytes(self) -> (i64, i64) {
        match self {
            Self::Int => (LAZY_CONT_KIND_I64, i64::from(ValueKind::INT.tag())),
            Self::Float => (LAZY_CONT_KIND_F64, i64::from(ValueKind::FLOAT.tag())),
            Self::Atom => (LAZY_CONT_KIND_ATOM, i64::from(ValueKind::ATOM.tag())),
        }
    }
}

fn raw_offset(slot: u32) -> i32 {
    slot as i32 * SLOT_BYTES
}

fn kind_offset(width: u32, slot: u32) -> i32 {
    width as i32 * SLOT_BYTES + slot as i32
}

impl<M: Module> CodegenFn<'_, '_, M> {
    fn frame_row(&mut self, frame: ir::Value) -> FrameRow {
        let packing = AnyValueRefPacking::current();
        let tag = self.b.ins().ushr_imm(frame, i64::from(packing.tag_shift()));
        let on_stack = self.b.ins().icmp_imm(IntCC::Equal, tag, TAG_LAZY_CONT as i64);
        let address = self.b.ins().band_imm(frame, packing.address_mask() as i64);
        let stack_captures = self.b.ins().iadd_imm(address, LAZY_CONT_HEADER_BYTES as i64);
        let heap_captures = self.b.ins().iadd_imm(address, CLOSURE_CAPTURES_OFFSET as i64);
        let captures = self.b.ins().select(on_stack, stack_captures, heap_captures);
        FrameRow {
            on_stack,
            address,
            captures,
        }
    }

    /// Points the frame at `code`, the continuation that next runs in it.
    pub(super) fn frame_resume_at(&mut self, frame: ir::Value, code: ir::Value) {
        let row = self.frame_row(frame);
        let stack_code = self.b.ins().iconst(types::I64, 0);
        let heap_code = self.b.ins().iconst(types::I64, CLOSURE_CODE_OFFSET as i64);
        let offset = self.b.ins().select(row.on_stack, stack_code, heap_code);
        let at = self.b.ins().iadd(row.address, offset);
        self.b.ins().store(MemFlags::trusted(), code, at, 0);
    }

    /// The value in `slot` of the frame.
    pub(super) fn frame_load(&mut self, frame: ir::Value, slot: u32, lane: FrameLane) -> CodegenValue {
        let row = self.frame_row(frame);
        let flags = MemFlags::trusted();
        match lane {
            FrameLane::Int => {
                CodegenValue::RawInt(self.b.ins().load(types::I64, flags, row.captures, raw_offset(slot)))
            }
            FrameLane::Float => {
                CodegenValue::RawF64(self.b.ins().load(types::F64, flags, row.captures, raw_offset(slot)))
            }
            FrameLane::Atom => {
                CodegenValue::RawAtom(self.b.ins().load(types::I64, flags, row.captures, raw_offset(slot)))
            }
            FrameLane::Ref => CodegenValue::any_ref(self.frame_load_ref(frame, row, slot)),
        }
    }

    /// A boxed slot of a stack frame holds the value's word itself; one of a
    /// heap frame holds the value in the closure capture layout, which only
    /// the runtime turns back into a word.
    fn frame_load_ref(&mut self, frame: ir::Value, row: FrameRow, slot: u32) -> ir::Value {
        let stack = self.b.create_block();
        let heap = self.b.create_block();
        let done = self.b.create_block();
        let word = self.b.append_block_param(done, types::I64);
        self.b.ins().brif(row.on_stack, stack, &[], heap, &[]);

        self.b.switch_to_block(stack);
        self.b.seal_block(stack);
        let on_stack = self
            .b
            .ins()
            .load(types::I64, MemFlags::trusted(), row.captures, raw_offset(slot));
        self.b.ins().jump(done, &[on_stack.into()]);

        self.b.switch_to_block(heap);
        self.b.seal_block(heap);
        let on_heap = self.closure_capture_ref_at(frame, slot as usize);
        self.b.ins().jump(done, &[on_heap.into()]);

        self.b.switch_to_block(done);
        self.b.seal_block(done);
        word
    }

    /// Writes `capture` into the empty `slot` of a frame `width` slots wide.
    pub(super) fn frame_store(&mut self, frame: ir::Value, width: u32, slot: u32, capture: ClosureCapture) {
        let row = self.frame_row(frame);
        match capture {
            ClosureCapture::RawInt(raw) => self.frame_store_raw(row, width, slot, raw, RawLane::Int),
            ClosureCapture::RawAtom(raw) => self.frame_store_raw(row, width, slot, raw, RawLane::Atom),
            ClosureCapture::RawF64(float) => {
                let raw = self.b.ins().bitcast(types::I64, MemFlags::new(), float);
                self.frame_store_raw(row, width, slot, raw, RawLane::Float)
            }
            ClosureCapture::RefWord(word) => self.frame_store_ref(frame, row, width, slot, word),
        }
    }

    fn frame_store_raw(&mut self, row: FrameRow, width: u32, slot: u32, raw: ir::Value, lane: RawLane) {
        let (stack_kind, heap_kind) = lane.kind_bytes();
        let stack_kind = self.b.ins().iconst(types::I8, stack_kind);
        let heap_kind = self.b.ins().iconst(types::I8, heap_kind);
        let kind = self.b.ins().select(row.on_stack, stack_kind, heap_kind);
        self.store_slot(row, width, slot, raw, kind);
    }

    fn store_slot(&mut self, row: FrameRow, width: u32, slot: u32, raw: ir::Value, kind: ir::Value) {
        let flags = MemFlags::trusted();
        self.b.ins().store(flags, raw, row.captures, raw_offset(slot));
        self.b.ins().store(flags, kind, row.captures, kind_offset(width, slot));
    }

    /// A stack frame takes the word as it is. A heap frame outlives the stack,
    /// so the runtime moves a stack continuation the value names to the heap
    /// and marks the value shared before the frame holds it.
    fn frame_store_ref(&mut self, frame: ir::Value, row: FrameRow, width: u32, slot: u32, word: ir::Value) {
        let stack = self.b.create_block();
        let heap = self.b.create_block();
        let done = self.b.create_block();
        self.b.ins().brif(row.on_stack, stack, &[], heap, &[]);

        self.b.switch_to_block(stack);
        self.b.seal_block(stack);
        let kind = self.b.ins().iconst(types::I8, LAZY_CONT_KIND_REF);
        self.store_slot(row, width, slot, word, kind);
        self.b.ins().jump(done, &[]);

        self.b.switch_to_block(heap);
        self.b.seal_block(heap);
        let process = self.process_arg();
        let slot_index = self.b.ins().iconst(types::I64, i64::from(slot));
        runtime_call!(self, fz_heap_frame_store_ref, [process, frame, slot_index, word]);
        self.b.ins().jump(done, &[]);

        self.b.switch_to_block(done);
        self.b.seal_block(done);
    }

    /// Empties a boxed `slot` whose value died, so the frame no longer keeps
    /// it alive.
    pub(super) fn frame_clear(&mut self, frame: ir::Value, width: u32, slot: u32) {
        let row = self.frame_row(frame);
        let stack = self.b.create_block();
        let heap = self.b.create_block();
        let done = self.b.create_block();
        self.b.ins().brif(row.on_stack, stack, &[], heap, &[]);

        self.b.switch_to_block(stack);
        self.b.seal_block(stack);
        let nil = self.b.ins().iconst(types::I64, i64::from(NIL_ATOM_ID));
        let kind = self.b.ins().iconst(types::I8, LAZY_CONT_KIND_ATOM);
        self.store_slot(row, width, slot, nil, kind);
        self.b.ins().jump(done, &[]);

        self.b.switch_to_block(heap);
        self.b.seal_block(heap);
        let process = self.process_arg();
        let slot_index = self.b.ins().iconst(types::I64, i64::from(slot));
        runtime_call!(self, fz_heap_frame_clear, [process, frame, slot_index]);
        self.b.ins().jump(done, &[]);

        self.b.switch_to_block(done);
        self.b.seal_block(done);
    }
}
