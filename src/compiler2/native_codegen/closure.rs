use super::*;
use cranelift_codegen::ir::{self, InstBuilder, MemFlags, condcodes::IntCC, types};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::FuncId;
use fz_runtime::any_value::{
    AnyValueRefPacking, CLOSURE_CAPTURES_OFFSET, CLOSURE_CODE_OFFSET, CLOSURE_FLAGS_CAPTURED_MASK,
    CLOSURE_LAYOUT_FLAGS_SHIFT, ClosureDenotationId, NIL_ATOM_ID, TAG_CLOSURE, TaggedRefArch, ValueKind,
    closure_header_word, closure_size_for_count,
};
use fz_runtime::heap::INLINE_ALLOC_LAYOUT;
use fz_runtime::process_abi::PROCESS_HEAP_OFFSET;

/// Build a cont closure and answer its ref word: placed at the heap tip by
/// inline code, with its header, code address, and every capture stored in
/// place. Only a full tip block calls the runtime, which places the object
/// and leaves the stores to the same inline code.
///
/// `cap_bindings` is a slice of user captures. Typed captures stay in raw
/// payload slots; `ValueRef` captures are already one-word any value refs.
/// Capture 0 is the synthetic outer cont; user captures follow.
pub(crate) fn build_cont_closure<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    outer_cont: ir::Value,
    cont_fid: FuncId,
    cap_bindings: &[ClosureCapture],
    empty_slots: usize,
) -> ir::Value {
    let count = cap_bindings.len() + empty_slots + 1;
    let code_addr = fn_addr(body.jmod, cont_fid, body.b);
    let closure_ref = place_cont_closure(body, count, code_addr);
    let address = body
        .b
        .ins()
        .band_imm(closure_ref, AnyValueRefPacking::current().address_mask() as i64);
    let stores = CaptureStores::new(address, count);
    stores.store_ref_word(body, 0, outer_cont);
    store_user_captures(cap_bindings, |idx, capture| match capture {
        ClosureCapture::RefWord(word) => stores.store_ref_word(body, idx, word),
        ClosureCapture::RawInt(raw) => stores.store_raw(body, idx, raw, ValueKind::INT),
        ClosureCapture::RawF64(raw) => {
            let bits = body.b.ins().bitcast(types::I64, MemFlags::new(), raw);
            stores.store_raw(body, idx, bits, ValueKind::FLOAT);
        }
        ClosureCapture::RawAtom(raw) => stores.store_raw(body, idx, raw, ValueKind::ATOM),
    });
    let nil = body.b.ins().iconst(types::I64, i64::from(NIL_ATOM_ID));
    for idx in count - empty_slots..count {
        stores.store_raw(body, idx, nil, ValueKind::ATOM);
    }
    closure_ref
}

/// Place an unfilled continuation closure of `count` captures: the header and
/// code address are written, the captures are not. The tip block takes it
/// inline when it has room, and the statistics a runtime allocation records
/// are counted here; a full block asks the runtime.
fn place_cont_closure<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    count: usize,
    code_addr: ir::Value,
) -> ir::Value {
    let size = closure_size_for_count(count) as i64;
    let layout = INLINE_ALLOC_LAYOUT;
    let heap = PROCESS_HEAP_OFFSET;
    let field = |offset: usize| heap + offset as i32;
    let flags = MemFlags::trusted();
    let process = body.process_arg();
    let top = body.b.ins().load(types::I64, flags, process, field(layout.bump_top));
    let end = body.b.ins().load(types::I64, flags, process, field(layout.block_end));
    let new_top = body.b.ins().iadd_imm(top, size);
    let fits = body.b.ins().icmp(IntCC::UnsignedLessThanOrEqual, new_top, end);
    let inline = body.b.create_block();
    let runtime = body.b.create_block();
    let placed = body.b.create_block();
    body.b.append_block_param(placed, types::I64);
    body.b.ins().brif(fits, inline, &[], runtime, &[]);

    body.b.switch_to_block(runtime);
    body.b.seal_block(runtime);
    let arity = body.b.ins().iconst(types::I32, CONT_ARITY);
    let captured = body.b.ins().iconst(types::I32, count as i64);
    let from_runtime = body.alloc_continuation(arity, captured, code_addr);
    body.b.ins().jump(placed, &[from_runtime.into()]);

    body.b.switch_to_block(inline);
    body.b.seal_block(inline);
    let process = body.process_arg();
    body.b.ins().store(flags, new_top, process, field(layout.bump_top));
    for (counter, add) in [
        (layout.alloc_count, 1),
        (layout.total_allocs, 1),
        (layout.continuation_allocs, 1),
        (layout.total_bytes, size),
        (layout.continuation_bytes, size),
    ] {
        let old = body.b.ins().load(types::I64, flags, process, field(counter));
        let new = body.b.ins().iadd_imm(old, add);
        body.b.ins().store(flags, new, process, field(counter));
    }
    let header = closure_header_word(ClosureDenotationId::INTERNAL, count as u16, 0, CONT_ARITY as u16);
    let header = body.b.ins().iconst(types::I64, header as i64);
    body.b.ins().store(flags, header, top, 0);
    body.b.ins().store(flags, code_addr, top, CLOSURE_CODE_OFFSET);
    let from_tip = emit_tagged_pointer_ref_word(body.b, top, TAG_CLOSURE);
    body.b.ins().jump(placed, &[from_tip.into()]);

    body.b.switch_to_block(placed);
    body.b.seal_block(placed);
    body.b.block_params(placed)[0]
}

/// Stores into the capture slots and kind bytes of one closure being built.
pub(super) struct CaptureStores {
    address: ir::Value,
    count: usize,
}

impl CaptureStores {
    pub(super) fn new(address: ir::Value, count: usize) -> Self {
        Self { address, count }
    }

    fn slot_offset(&self, idx: usize) -> i32 {
        CLOSURE_CAPTURES_OFFSET + (idx * 8) as i32
    }

    fn kind_offset(&self, idx: usize) -> i32 {
        CLOSURE_CAPTURES_OFFSET + (self.count * 8 + idx) as i32
    }

    pub(super) fn store_raw<M: cranelift_module::Module>(
        &self,
        body: &mut CodegenFn<'_, '_, M>,
        idx: usize,
        raw: ir::Value,
        kind: ValueKind,
    ) {
        let flags = MemFlags::trusted();
        body.b.ins().store(flags, raw, self.address, self.slot_offset(idx));
        let kind = body.b.ins().iconst(types::I8, i64::from(kind.tag()));
        body.b.ins().store(flags, kind, self.address, self.kind_offset(idx));
    }

    /// Store the value a ref word names: its kind byte, and the raw word the
    /// slot holds. An int, float, pid or reference ref names a slot that holds
    /// the raw word, which is read through it; an atom's raw word is its id,
    /// and every other kind's is its payload. The slot read is branch-free: a
    /// ref that names no slot reads the closure's own header, and that word
    /// goes unused.
    pub(super) fn store_ref_word<M: cranelift_module::Module>(
        &self,
        body: &mut CodegenFn<'_, '_, M>,
        idx: usize,
        word: ir::Value,
    ) {
        let packing = AnyValueRefPacking::current();
        let flags = MemFlags::trusted();
        let shifted = body.b.ins().ushr_imm(word, i64::from(packing.tag_shift()));
        let tag = body.b.ins().band_imm(shifted, 0xF);
        let named_address = body.b.ins().band_imm(word, packing.address_mask() as i64);
        let payload = body.b.ins().band_imm(word, packing.payload_mask() as i64);
        let names_slot = body.kind_names_its_slot(tag);
        let source = body.b.ins().select(names_slot, named_address, self.address);
        let loaded = body.b.ins().load(types::I64, MemFlags::new(), source, 0);
        let is_atom = body
            .b
            .ins()
            .icmp_imm(IntCC::Equal, tag, i64::from(ValueKind::ATOM.tag()));
        let unboxed = body.b.ins().select(is_atom, named_address, payload);
        let raw = body.b.ins().select(names_slot, loaded, unboxed);
        body.b.ins().store(flags, raw, self.address, self.slot_offset(idx));
        let kind = body.b.ins().ireduce(types::I8, tag);
        body.b.ins().store(flags, kind, self.address, self.kind_offset(idx));
    }
}

/// Iterate user captures (typed `cap_bindings` followed by `extra_ref_captures`)
/// and invoke `store` for each one at its target slot index. Slot 0 is reserved
/// for the synthetic outer cont and must be written by the caller before
/// invoking this helper; user captures begin at index 1.
fn store_user_captures<F>(cap_bindings: &[ClosureCapture], mut store: F)
where
    F: FnMut(usize, ClosureCapture),
{
    for (i, &capture) in cap_bindings.iter().enumerate() {
        store(i + 1, capture);
    }
}

/// A continuation is applied to exactly the one value it receives.
pub(crate) const CONT_ARITY: i64 = 1;

fn emit_tagged_pointer_ref_word(b: &mut FunctionBuilder<'_>, ptr: ir::Value, tag: u64) -> ir::Value {
    emit_tagged_pointer_ref_word_for_arch(b, ptr, tag, TaggedRefArch::current())
}

fn emit_tagged_pointer_ref_word_for_arch(
    b: &mut FunctionBuilder<'_>,
    ptr: ir::Value,
    tag: u64,
    arch: TaggedRefArch,
) -> ir::Value {
    let ptr_payload = emit_tagged_pointer_payload_for_arch(b, ptr, arch);
    let tag_word = (tag << AnyValueRefPacking::for_arch(arch).tag_shift()) as i64;
    b.ins().bor_imm(ptr_payload, tag_word)
}

fn emit_tagged_pointer_payload_for_arch(b: &mut FunctionBuilder<'_>, ptr: ir::Value, arch: TaggedRefArch) -> ir::Value {
    match arch {
        TaggedRefArch::Arm64Tbi => ptr,
        TaggedRefArch::X86_64Canonical57 => {
            let clear_shift = i64::from(64 - AnyValueRefPacking::for_arch(arch).tag_shift());
            let shifted = b.ins().ishl_imm(ptr, clear_shift);
            b.ins().ushr_imm(shifted, clear_shift)
        }
    }
}

/// Which captures a resumed frame hands back and what happens to its bytes.
///
/// A continuation is resumed at most once, so a frame that has been read is
/// dead. Collections run only at quantum end, so no collection sees the dead
/// frame between its reads and the release; a runnable process and a park
/// record take their continuation out of their own storage when they resume
/// it; and a try handler captures the outer continuation and is popped before
/// that continuation resumes.
///
/// The dead frame is given back to the heap when it is the newest object,
/// unless one of its `ValueRef` captures is scalar-kinded: such a ref names
/// the frame's own capture slot, so the frame stays while that ref lives.
/// The heap's object count falls with the frame; the allocation statistics
/// count allocations and keep it. Every capture and the outer continuation are
/// read into registers before this runs.
pub(crate) fn release_resumed_frame<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    frame: ir::Value,
    ref_slots: &[usize],
    slot_count: usize,
) {
    let packing = AnyValueRefPacking::current();
    let flags = MemFlags::trusted();
    let tag = body.b.ins().ushr_imm(frame, i64::from(packing.tag_shift()));
    let tag = body.b.ins().band_imm(tag, 0xF);
    let is_closure = body
        .b
        .ins()
        .icmp_imm(IntCC::Equal, tag, i64::from(ValueKind::CLOSURE.tag()));
    let examine = body.b.create_block();
    let done = body.b.create_block();
    body.b.ins().brif(is_closure, examine, &[], done, &[]);

    body.b.switch_to_block(examine);
    body.b.seal_block(examine);
    let address = body.b.ins().band_imm(frame, packing.address_mask() as i64);
    let layout = body.b.ins().uload32(flags, address, 0);
    let count = body.b.ins().ushr_imm(layout, CLOSURE_LAYOUT_FLAGS_SHIFT as i64);
    let count = body.b.ins().band_imm(count, i64::from(CLOSURE_FLAGS_CAPTURED_MASK));
    let kinds_offset = body.b.ins().ishl_imm(count, 3);
    let kinds = body.b.ins().iadd(address, kinds_offset);
    let mut pinned = body.b.ins().iconst(types::I8, 0);
    for &slot in ref_slots {
        let kind = body
            .b
            .ins()
            .uload8(types::I64, flags, kinds, CLOSURE_CAPTURES_OFFSET + slot as i32);
        let names_slot = body.kind_names_its_slot(kind);
        pinned = body.b.ins().bor(pinned, names_slot);
    }
    let size = frame_size(body, count);
    let end = body.b.ins().iadd(address, size);
    let heap = PROCESS_HEAP_OFFSET + INLINE_ALLOC_LAYOUT.bump_top as i32;
    let process = body.process_arg();
    let top = body.b.ins().load(types::I64, flags, process, heap);
    let at_tip = body.b.ins().icmp(IntCC::Equal, end, top);
    let released = body.b.ins().icmp_imm(IntCC::Equal, pinned, 0);
    if POISON_DEAD_FRAMES {
        poison_dead_frame(body, address, kinds, released, slot_count);
    } else {
        let pop = body.b.ins().band(at_tip, released);
        let new_top = body.b.ins().select(pop, address, top);
        body.b.ins().store(flags, new_top, process, heap);
        let objects_at = PROCESS_HEAP_OFFSET + INLINE_ALLOC_LAYOUT.alloc_count as i32;
        let objects = body.b.ins().load(types::I64, flags, process, objects_at);
        let given_back = body.b.ins().uextend(types::I64, pop);
        let objects = body.b.ins().isub(objects, given_back);
        body.b.ins().store(flags, objects, process, objects_at);
    }
    body.b.ins().jump(done, &[]);

    body.b.switch_to_block(done);
    body.b.seal_block(done);
}

/// `closure_size_for_count` over a runtime count.
fn frame_size<M: cranelift_module::Module>(body: &mut CodegenFn<'_, '_, M>, count: ir::Value) -> ir::Value {
    let raw_words = body.b.ins().iadd_imm(count, 1);
    let raw_bytes = body.b.ins().ishl_imm(raw_words, 3);
    let kind_bytes = body.b.ins().iadd_imm(count, 7);
    let kind_bytes = body.b.ins().band_imm(kind_bytes, !7);
    let size = body.b.ins().iadd(raw_bytes, kind_bytes);
    let size = body.b.ins().iadd_imm(size, 8 + 15);
    body.b.ins().band_imm(size, !15)
}

/// The `poison_dead_frames` test feature builds a compiler whose released
/// frames are poisoned instead of given back; production builds pop.
const POISON_DEAD_FRAMES: bool = cfg!(feature = "poison_dead_frames");

/// The positive control of the poison test: a poisoned build that is asked to
/// read the outer continuation after the release, which must fail.
pub(crate) fn outer_cont_read_after_release() -> bool {
    POISON_DEAD_FRAMES && std::env::var_os("FZ_POISON_LATE_OUTER_READ").is_some()
}

/// Marks a released frame dead instead of giving it back, so that a read after
/// the resume fails loudly: a null code pointer, an unused kind byte, and a
/// raw word no address can mean. A frame the release would keep is left whole.
fn poison_dead_frame<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    address: ir::Value,
    kinds: ir::Value,
    released: ir::Value,
    slot_count: usize,
) {
    let flags = MemFlags::trusted();
    let poison = body.b.create_block();
    let done = body.b.create_block();
    body.b.ins().brif(released, poison, &[], done, &[]);
    body.b.switch_to_block(poison);
    body.b.seal_block(poison);
    let null = body.b.ins().iconst(types::I64, 0);
    body.b.ins().store(flags, null, address, CLOSURE_CODE_OFFSET);
    let dead_word = body.b.ins().iconst(types::I64, DEAD_FRAME_WORD as i64);
    let dead_kind = body.b.ins().iconst(types::I8, i64::from(DEAD_FRAME_KIND));
    for slot in 0..slot_count {
        body.b
            .ins()
            .store(flags, dead_word, address, CLOSURE_CAPTURES_OFFSET + (slot * 8) as i32);
        body.b
            .ins()
            .store(flags, dead_kind, kinds, CLOSURE_CAPTURES_OFFSET + slot as i32);
    }
    body.b.ins().jump(done, &[]);
    body.b.switch_to_block(done);
    body.b.seal_block(done);
}

const DEAD_FRAME_WORD: u64 = 0xDEAD_0000_0000_0008;
const DEAD_FRAME_KIND: u8 = 0xB;
