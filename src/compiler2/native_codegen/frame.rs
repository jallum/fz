//! A body frame's slots, read and written where they are.
//!
//! A body frame is a heap continuation closure that a chain of continuations
//! runs in. Slot `i` is capture `i`; slot 0 is the outer continuation.
//!
//! A frame a collection kept lives in an old block, and a write into it that
//! names a younger object would be invisible to the next minor collection. So
//! every write first asks whether the frame is a heap object in a young block,
//! by the age table; a literal frame is read-only program data and is not asked.
//! A frame that is literal or old is copied by the runtime to the tip, and the
//! write goes to the copy. A write answers the frame to use from then on.

use super::closure::{CaptureStores, StoredRefKind};
use super::*;
use crate::fz_ir::FrameLane;
use cranelift_codegen::ir::{self, InstBuilder, MemFlagsData, types};
use cranelift_module::Module;
use fz_runtime::any_value::{AnyValueRefPacking, CLOSURE_CAPTURES_OFFSET, CLOSURE_CODE_OFFSET, NIL_ATOM_ID, ValueKind};
use fz_runtime::ir_runtime::fz_frame_for_write;

fn lane_to_repr(lane: FrameLane) -> ArgRepr {
    match lane {
        FrameLane::Ref => ArgRepr::ValueRef,
        FrameLane::Int => ArgRepr::RawInt,
        FrameLane::Float => ArgRepr::RawF64,
        FrameLane::Atom => ArgRepr::RawAtom,
        FrameLane::Stored => ArgRepr::Stored,
    }
}

impl<M: Module> CodegenFn<'_, '_, M> {
    /// Points the frame at `code`, the continuation that next runs in it. The
    /// code address is no heap reference, so the write is safe in an old frame.
    pub(super) fn frame_resume_at(&mut self, frame: ir::Value, code: ir::Value) {
        let address = address_field(self.b, frame);
        self.b
            .ins()
            .store(MemFlagsData::trusted(), code, address, CLOSURE_CODE_OFFSET);
    }

    /// The value in `slot` of the frame.
    pub(super) fn frame_load(&mut self, frame: ir::Value, slot: u32, lane: FrameLane) -> CodegenValue {
        self.closure_capture_as_binding(frame, slot as usize, lane_to_repr(lane), CaptureCount::InHeader)
    }

    /// Writes `capture` into the empty `slot` of a frame `width` slots wide and
    /// answers the frame to use from here on.
    pub(super) fn frame_store(
        &mut self,
        frame: ir::Value,
        width: u32,
        slot: u32,
        capture: ClosureCapture,
    ) -> ir::Value {
        let frame = self.frame_young_or_copy(frame);
        let address = address_field(self.b, frame);
        let stores = CaptureStores::new(address, width as usize);
        let idx = slot as usize;
        match capture {
            ClosureCapture::RefWord(word) => stores.store_ref_word(self, idx, word, StoredRefKind::Open),
            ClosureCapture::RawInt(raw) => stores.store_raw(self, idx, raw, ValueKind::INT),
            ClosureCapture::RawAtom(raw) => stores.store_raw(self, idx, raw, ValueKind::ATOM),
            ClosureCapture::Stored { word, kind } => stores.store_stored(self, idx, word, kind),
            ClosureCapture::RawF64(float) => {
                let bits = self.b.ins().bitcast(types::I64, MemFlagsData::new(), float);
                stores.store_raw(self, idx, bits, ValueKind::FLOAT);
            }
        }
        frame
    }

    /// Overwrites a dead boxed slot with the nil atom, so the object it held is
    /// no longer reachable through the frame, and answers the frame to use from
    /// here on. A slot holding a scalar-kinded value is left whole: a live ref
    /// to a scalar names its own slot and is read through it.
    pub(super) fn frame_clear(&mut self, frame: ir::Value, width: u32, slot: u32) -> ir::Value {
        let frame = self.frame_young_or_copy(frame);
        let address = address_field(self.b, frame);
        let stores = CaptureStores::new(address, width as usize);
        let kind_offset = CLOSURE_CAPTURES_OFFSET + (width as usize * 8 + slot as usize) as i32;
        let kind = self
            .b
            .ins()
            .uload8(types::I64, MemFlagsData::trusted(), address, kind_offset);
        let named = self.kind_names_its_slot(kind);
        let clear = self.b.create_block();
        let done = self.b.create_block();
        self.b.ins().brif(named, done, &[], clear, &[]);
        self.b.switch_to_block(clear);
        self.b.seal_block(clear);
        let nil = self.b.ins().iconst(types::I64, i64::from(NIL_ATOM_ID));
        stores.store_raw(self, slot as usize, nil, ValueKind::ATOM);
        self.b.ins().jump(done, &[]);
        self.b.switch_to_block(done);
        self.b.seal_block(done);
        frame
    }

    /// `frame` when it is a heap object a collection has not kept, else the
    /// copy `fz_frame_for_write` answers. A literal frame is read-only program
    /// data, outside the age table, so it is asked about first.
    fn frame_young_or_copy(&mut self, frame: ir::Value) -> ir::Value {
        let process = self.process_arg();
        let age = self.b.create_block();
        let keep = self.b.create_block();
        let copy = self.b.create_block();
        let done = self.b.create_block();
        let result = self.b.append_block_param(done, types::I64);
        let literal = self
            .b
            .ins()
            .band_imm_u(frame, AnyValueRefPacking::current().literal_bit() as i64);
        self.b.ins().brif(literal, copy, &[], age, &[]);

        self.b.switch_to_block(age);
        self.b.seal_block(age);
        let address = address_field(self.b, frame);
        let young = self.emit_is_young(address);
        self.b.ins().brif(young, keep, &[], copy, &[]);

        self.b.switch_to_block(copy);
        self.b.seal_block(copy);
        self.b.set_cold_block(copy);
        let copied = runtime_call1!(self, fz_frame_for_write, [process, frame]);
        self.b.ins().jump(done, &[copied.into()]);

        self.b.switch_to_block(keep);
        self.b.seal_block(keep);
        self.b.ins().jump(done, &[frame.into()]);

        self.b.switch_to_block(done);
        self.b.seal_block(done);
        result
    }
}
