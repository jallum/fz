use super::*;
use cranelift_codegen::ir::{self, InstBuilder, MemFlags, StackSlotData, StackSlotKind, types};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::FuncId;
use fz_runtime::any_value::{AnyValueRefPacking, TAG_LAZY_CONT, TaggedRefArch};

/// The outer-cont ref to forward into a new cont closure. A cont fn's
/// `cont_param` is its own closure, so the outer cont is loaded from the
/// closure env; any other fn's `cont_param` already is the outer cont.
pub(crate) fn resolve_outer_cont<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    is_cont_fn: bool,
    cont_param: ir::Value,
) -> ir::Value {
    if is_cont_fn {
        body.outer_cont_ref(cont_param)
    } else {
        cont_param
    }
}

/// Allocate a cont closure, populate its code-addr, outer-cont, and user
/// captures. Returns the heap pointer to the new closure object.
///
/// `cap_bindings` is a slice of user captures. Typed captures stay in raw
/// payload slots; `ValueRef` captures are already one-word any value refs.
pub(crate) fn build_cont_closure<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    is_cont_fn: bool,
    cont_param: ir::Value,
    cont_fid: FuncId,
    cap_bindings: &[ClosureCapture],
    extra_ref_captures: &[ir::Value],
) -> ir::Value {
    let my_outer_cont = resolve_outer_cont(body, is_cont_fn, cont_param);
    let cont_arity = body.b.ins().iconst(types::I32, CONT_ARITY);
    // +1 reserves env field 0 for the synthetic outer_cont; user captures follow.
    let n_caps_v = body
        .b
        .ins()
        .iconst(types::I32, (cap_bindings.len() + extra_ref_captures.len() + 1) as i64);
    let zero_hk = body.b.ins().iconst(types::I32, 0);
    let cont_code_addr = fn_addr(body.jmod, cont_fid, body.b);
    let cl_ptr = body.alloc_closure(
        fz_runtime::any_value::ClosureDenotationId::INTERNAL,
        cont_arity,
        n_caps_v,
        zero_hk,
        cont_code_addr,
    );
    let heap_safe_outer_cont = body.materialize_cont(my_outer_cont);
    body.store_closure_capture_ref_word(cl_ptr, 0, heap_safe_outer_cont);
    store_user_captures(cap_bindings, extra_ref_captures, |idx, capture| match capture {
        ClosureCapture::RefWord(ref_word) => {
            let heap_safe_ref = body.materialize_cont(ref_word);
            body.store_closure_capture_ref_word(cl_ptr, idx, heap_safe_ref);
        }
        ClosureCapture::RawInt(raw) => {
            body.store_closure_capture_i64(cl_ptr, idx, raw);
        }
        ClosureCapture::RawF64(raw) => {
            body.store_closure_capture_f64(cl_ptr, idx, raw);
        }
        ClosureCapture::RawAtom(raw) => {
            body.store_closure_capture_atom(cl_ptr, idx, raw);
        }
    });
    cl_ptr
}

/// Iterate user captures (typed `cap_bindings` followed by `extra_ref_captures`)
/// and invoke `store` for each one at its target slot index. Slot 0 is reserved
/// for the synthetic outer_cont and must be written by the caller before
/// invoking this helper; user captures begin at index 1.
fn store_user_captures<F>(cap_bindings: &[ClosureCapture], extra_ref_captures: &[ir::Value], mut store: F)
where
    F: FnMut(usize, ClosureCapture),
{
    for (i, &capture) in cap_bindings.iter().enumerate() {
        store(i + 1, capture);
    }
    for (i, &extra) in extra_ref_captures.iter().enumerate() {
        store(cap_bindings.len() + 1 + i, ClosureCapture::RefWord(extra));
    }
}

/// A continuation is applied to exactly the one value it receives.
pub(crate) const CONT_ARITY: i64 = 1;

const LAZY_CONT_HEADER_BYTES: usize = 32;
const LAZY_CONT_KIND_REF: i64 = 0;
const LAZY_CONT_KIND_I64: i64 = 1;
const LAZY_CONT_KIND_F64: i64 = 2;
const LAZY_CONT_KIND_ATOM: i64 = 3;

pub(crate) fn build_lazy_cont_descriptor<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    is_cont_fn: bool,
    cont_param: ir::Value,
    cont_fid: FuncId,
    cap_bindings: &[ClosureCapture],
    extra_ref_captures: &[ir::Value],
) -> ir::Value {
    let my_outer_cont = resolve_outer_cont(body, is_cont_fn, cont_param);
    let captured_count = cap_bindings.len() + extra_ref_captures.len() + 1;
    let raw_base = LAZY_CONT_HEADER_BYTES;
    let kind_base = raw_base + captured_count * SLOT_BYTES as usize;
    let slot_size = kind_base + captured_count;
    let slot = body
        .b
        .create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, slot_size as u32, 3));
    let code_addr = fn_addr(body.jmod, cont_fid, body.b);
    body.b.ins().stack_store(code_addr, slot, 0);
    // +8 is a reserved hole: nothing reads it (fz-gk4).
    let captured_count_v = body.b.ins().iconst(types::I64, captured_count as i64);
    body.b.ins().stack_store(captured_count_v, slot, 16);

    store_lazy_capture(body.b, slot, raw_base, kind_base, 0, my_outer_cont, LAZY_CONT_KIND_REF);
    store_user_captures(cap_bindings, extra_ref_captures, |idx, capture| match capture {
        ClosureCapture::RefWord(value) => {
            store_lazy_capture(body.b, slot, raw_base, kind_base, idx, value, LAZY_CONT_KIND_REF);
        }
        ClosureCapture::RawInt(value) => {
            store_lazy_capture(body.b, slot, raw_base, kind_base, idx, value, LAZY_CONT_KIND_I64);
        }
        ClosureCapture::RawF64(value) => {
            let raw = body.b.ins().bitcast(types::I64, MemFlags::new(), value);
            store_lazy_capture(body.b, slot, raw_base, kind_base, idx, raw, LAZY_CONT_KIND_F64);
        }
        ClosureCapture::RawAtom(value) => {
            store_lazy_capture(body.b, slot, raw_base, kind_base, idx, value, LAZY_CONT_KIND_ATOM);
        }
    });
    let ptr = body.b.ins().stack_addr(types::I64, slot, 0);
    emit_tagged_pointer_ref_word(body.b, ptr, TAG_LAZY_CONT)
}

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

fn store_lazy_capture(
    b: &mut FunctionBuilder<'_>,
    slot: ir::StackSlot,
    raw_base: usize,
    kind_base: usize,
    idx: usize,
    raw: ir::Value,
    kind: i64,
) {
    b.ins()
        .stack_store(raw, slot, (raw_base + idx * SLOT_BYTES as usize) as i32);
    let kind_v = b.ins().iconst(types::I8, kind);
    b.ins().stack_store(kind_v, slot, (kind_base + idx) as i32);
}
