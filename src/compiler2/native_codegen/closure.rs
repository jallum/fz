use super::place::emit_place;
use super::*;
use cranelift_codegen::ir::{self, InstBuilder, MemFlagsData, condcodes::IntCC, types};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::FuncId;
use fz_runtime::any_value::{
    AnyValueRefPacking, CLOSURE_CAPTURES_OFFSET, CLOSURE_CODE_OFFSET, CLOSURE_FLAGS_CAPTURED_MASK,
    CLOSURE_LAYOUT_FLAGS_SHIFT, ClosureDenotationId, NIL_ATOM_ID, TAG_CLOSURE, TaggedRefArch, ValueKind,
    closure_header_word, closure_size_for_count,
};
use fz_runtime::heap::{HeapAllocKind, INLINE_ALLOC_LAYOUT};
use fz_runtime::ir_runtime::fz_handler_reserve;
use fz_runtime::process_abi::{PROCESS_HANDLER_END_OFFSET, PROCESS_HANDLER_TOP_OFFSET, PROCESS_HEAP_OFFSET};

/// Build a cont closure and answer its ref word: placed by `emit_place`, with
/// its header, code address, and every capture stored in place by inline code.
///
/// `cap_bindings` is a slice of user captures. Typed captures stay in raw
/// payload slots; `ValueRef` captures are already one-word any value refs.
/// Capture 0 is the synthetic outer cont; user captures follow.
pub(crate) fn build_cont_closure<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    outer_cont: ir::Value,
    cont_fid: FuncId,
    cap_bindings: &[ClosureCapture],
    empty_slots: usize,
) -> ir::Value {
    let count = cap_bindings.len() + empty_slots + 1;
    let code_addr = fn_addr(body.jmod, cont_fid, body.b);
    let closure_ref = place_cont_closure(body, env, count, code_addr);
    let address = address_field(body.b, closure_ref);
    fill_cont_captures(body, address, outer_cont, cap_bindings, empty_slots);
    closure_ref
}

/// Push a `try`'s handler record onto the process's handler stack: the image
/// of the continuation `build_cont_closure` would build for the handler, in
/// place on the stack, followed by the trailer naming the record's size. The
/// stack's own room takes it inline; only a full stack calls the runtime, which
/// grows it. Nothing is built on the heap: a raise materializes the handler
/// from the record.
pub(crate) fn push_handler_record<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    outer_cont: ir::Value,
    cont_fid: FuncId,
    cap_bindings: &[ClosureCapture],
    empty_slots: usize,
) {
    let count = cap_bindings.len() + empty_slots + 1;
    let image_bytes = closure_size_for_count(count) as i64;
    let record_bytes = image_bytes + 8;
    let address = reserve_handler_record(body, record_bytes);
    let flags = MemFlagsData::trusted();
    let header = closure_header_word(ClosureDenotationId::INTERNAL, count as u16, 0, CONT_ARITY as u16);
    let header = body.b.ins().iconst(types::I64, header as i64);
    body.b.ins().store(flags, header, address, 0);
    let code_addr = fn_addr(body.jmod, cont_fid, body.b);
    body.b.ins().store(flags, code_addr, address, CLOSURE_CODE_OFFSET);
    fill_cont_captures(body, address, outer_cont, cap_bindings, empty_slots);
    let trailer = body.b.ins().iconst(types::I64, record_bytes);
    body.b.ins().store(flags, trailer, address, image_bytes as i32);
}

/// Pop the innermost handler record: the trailer under the stack's top names
/// how far the top falls.
pub(crate) fn pop_handler_record<M: cranelift_module::Module>(body: &mut CodegenFn<'_, '_, M>) {
    let flags = MemFlagsData::trusted();
    let process = body.process_arg();
    let top = body
        .b
        .ins()
        .load(types::I64, flags, process, PROCESS_HANDLER_TOP_OFFSET);
    let record_bytes = body.b.ins().load(types::I64, flags, top, -8);
    let below = body.b.ins().isub(top, record_bytes);
    body.b.ins().store(flags, below, process, PROCESS_HANDLER_TOP_OFFSET);
}

/// Reserve `record_bytes` on top of the handler stack and answer where they
/// start: inline while the stack has room, through `fz_handler_reserve` when
/// it is full.
fn reserve_handler_record<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    record_bytes: i64,
) -> ir::Value {
    let flags = MemFlagsData::trusted();
    let process = body.process_arg();
    let top = body
        .b
        .ins()
        .load(types::I64, flags, process, PROCESS_HANDLER_TOP_OFFSET);
    let end = body
        .b
        .ins()
        .load(types::I64, flags, process, PROCESS_HANDLER_END_OFFSET);
    let new_top = body.b.ins().iadd_imm_u(top, record_bytes);
    let fits = body.b.ins().icmp(IntCC::UnsignedLessThanOrEqual, new_top, end);
    let inline = body.b.create_block();
    let runtime = body.b.create_block();
    let reserved = body.b.create_block();
    body.b.append_block_param(reserved, types::I64);
    body.b.ins().brif(fits, inline, &[], runtime, &[]);

    body.b.switch_to_block(runtime);
    body.b.seal_block(runtime);
    let bytes = body.b.ins().iconst(types::I64, record_bytes);
    let from_runtime = runtime_call1!(body, fz_handler_reserve, [process, bytes]);
    body.b.ins().jump(reserved, &[from_runtime.into()]);

    body.b.switch_to_block(inline);
    body.b.seal_block(inline);
    body.b.ins().store(flags, new_top, process, PROCESS_HANDLER_TOP_OFFSET);
    body.b.ins().jump(reserved, &[top.into()]);

    body.b.switch_to_block(reserved);
    body.b.seal_block(reserved);
    body.b.block_params(reserved)[0]
}

/// Store a continuation's captures at `address`: the outer continuation as
/// capture 0, the user captures after it, and `nil` in the empty slots a body
/// frame fills later.
fn fill_cont_captures<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    address: ir::Value,
    outer_cont: ir::Value,
    cap_bindings: &[ClosureCapture],
    empty_slots: usize,
) {
    let count = cap_bindings.len() + empty_slots + 1;
    let stores = CaptureStores::new(address, count);
    stores.store_ref_word(body, 0, outer_cont, StoredRefKind::Heap(ValueKind::CLOSURE));
    store_user_captures(cap_bindings, |idx, capture| match capture {
        ClosureCapture::RefWord(word) => stores.store_ref_word(body, idx, word, StoredRefKind::Open),
        ClosureCapture::RawInt(raw) => stores.store_raw(body, idx, raw, ValueKind::INT),
        ClosureCapture::RawF64(raw) => {
            let bits = body.b.ins().bitcast(types::I64, MemFlagsData::new(), raw);
            stores.store_raw(body, idx, bits, ValueKind::FLOAT);
        }
        ClosureCapture::RawAtom(raw) => stores.store_raw(body, idx, raw, ValueKind::ATOM),
    });
    let nil = body.b.ins().iconst(types::I64, i64::from(NIL_ATOM_ID));
    for idx in count - empty_slots..count {
        stores.store_raw(body, idx, nil, ValueKind::ATOM);
    }
}

/// Place an unfilled continuation closure of `count` captures: the header and
/// code address are written, the captures are not.
pub(super) fn place_cont_closure<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    count: usize,
    code_addr: ir::Value,
) -> ir::Value {
    let size = closure_size_for_count(count);
    let address = emit_place(body, env.site_scope(), HeapAllocKind::Continuation, size);
    let flags = MemFlagsData::trusted();
    let header = closure_header_word(ClosureDenotationId::INTERNAL, count as u16, 0, CONT_ARITY as u16);
    let header = body.b.ins().iconst(types::I64, header as i64);
    body.b.ins().store(flags, header, address, 0);
    body.b.ins().store(flags, code_addr, address, CLOSURE_CODE_OFFSET);
    emit_tagged_pointer_ref_word(body.b, address, TAG_CLOSURE)
}

/// What codegen knows, where a ref word is stored, of the kind it names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum StoredRefKind {
    /// Any kind: the store reads the kind off the word.
    Open,
    /// One heap kind: the slot holds the word's payload under a constant kind
    /// byte, as the open store would write for a word of that kind.
    Heap(ValueKind),
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
        let flags = MemFlagsData::trusted();
        body.b.ins().store(flags, raw, self.address, self.slot_offset(idx));
        let kind = body.b.ins().iconst(types::I8, i64::from(kind.tag()));
        body.b.ins().store(flags, kind, self.address, self.kind_offset(idx));
    }

    /// Store the value a ref word names: its kind byte, and the raw word the
    /// slot holds. A heap kind's raw word is the word's payload.
    pub(super) fn store_ref_word<M: cranelift_module::Module>(
        &self,
        body: &mut CodegenFn<'_, '_, M>,
        idx: usize,
        word: ir::Value,
        kind: StoredRefKind,
    ) {
        match kind {
            StoredRefKind::Open => self.store_open_ref_word(body, idx, word),
            StoredRefKind::Heap(kind) => {
                debug_assert!(kind.is_heap(), "a known stored kind is a heap kind");
                let payload = payload_field(body.b, word);
                self.store_raw(body, idx, payload, kind);
            }
        }
    }

    /// Store a ref word of any kind. An int, float, pid or reference ref names
    /// a slot that holds the raw word, which is read through it; an atom's raw
    /// word is its id, and every other kind's is its payload. The slot read is
    /// branch-free: a ref that names no slot reads the closure's own header,
    /// and that word goes unused.
    fn store_open_ref_word<M: cranelift_module::Module>(
        &self,
        body: &mut CodegenFn<'_, '_, M>,
        idx: usize,
        word: ir::Value,
    ) {
        let flags = MemFlagsData::trusted();
        let tag = kind_field(body.b, word);
        let named_address = address_field(body.b, word);
        let payload = payload_field(body.b, word);
        let names_slot = body.kind_names_its_slot(tag);
        let source = body.b.ins().select(names_slot, named_address, self.address);
        let loaded = body.b.ins().load(types::I64, MemFlagsData::new(), source, 0);
        let is_atom = body
            .b
            .ins()
            .icmp_imm_s(IntCC::Equal, tag, i64::from(ValueKind::ATOM.tag()));
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
    b.ins().bor_imm_u(ptr_payload, tag_word)
}

fn emit_tagged_pointer_payload_for_arch(b: &mut FunctionBuilder<'_>, ptr: ir::Value, arch: TaggedRefArch) -> ir::Value {
    match arch {
        TaggedRefArch::Arm64Tbi => ptr,
        TaggedRefArch::X86_64Canonical57 => {
            let clear_shift = i64::from(64 - AnyValueRefPacking::for_arch(arch).tag_shift());
            let shifted = b.ins().ishl_imm_u(ptr, clear_shift);
            b.ins().ushr_imm_u(shifted, clear_shift)
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
    let flags = MemFlagsData::trusted();
    let tag = kind_field(body.b, frame);
    let is_closure = body
        .b
        .ins()
        .icmp_imm_s(IntCC::Equal, tag, i64::from(ValueKind::CLOSURE.tag()));
    let examine = body.b.create_block();
    let done = body.b.create_block();
    body.b.ins().brif(is_closure, examine, &[], done, &[]);

    body.b.switch_to_block(examine);
    body.b.seal_block(examine);
    let address = address_field(body.b, frame);
    let layout = body.b.ins().uload32(flags, address, 0);
    let count = body.b.ins().ushr_imm_u(layout, CLOSURE_LAYOUT_FLAGS_SHIFT as i64);
    let count = body.b.ins().band_imm_u(count, i64::from(CLOSURE_FLAGS_CAPTURED_MASK));
    let kinds_offset = body.b.ins().ishl_imm_u(count, 3);
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
    let released = body.b.ins().icmp_imm_s(IntCC::Equal, pinned, 0);
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
    let raw_words = body.b.ins().iadd_imm_s(count, 1);
    let raw_bytes = body.b.ins().ishl_imm_u(raw_words, 3);
    let kind_bytes = body.b.ins().iadd_imm_s(count, 7);
    let kind_bytes = body.b.ins().band_imm_u(kind_bytes, !7);
    let size = body.b.ins().iadd(raw_bytes, kind_bytes);
    let size = body.b.ins().iadd_imm_s(size, 8 + 15);
    body.b.ins().band_imm_u(size, !15)
}

/// The `poison_dead_frames` test feature builds a compiler whose released
/// frames are poisoned instead of given back; production builds pop.
pub(crate) const POISON_DEAD_FRAMES: bool = cfg!(feature = "poison_dead_frames");

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
    let flags = MemFlagsData::trusted();
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
