use super::*;
use crate::fz_ir::{BinOp, Const, FnId, Module, Prim, Stmt, Term, UnOp};
use cranelift_codegen::Context;
use cranelift_codegen::ir::{
    self, AbiParam, BlockArg, InstBuilder, MemFlags, Signature, StackSlotData, StackSlotKind,
    condcodes::{FloatCC, IntCC},
    types,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module as ClModule};
use fz_runtime::any_value::{AnyValueRefPacking, TAG_FWD, TaggedRefArch};
use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema};
use std::collections::HashMap;
use std::sync::Arc;

/// Allocate and return a halt-cont singleton for `repr` via `fz_get_halt_cont`.
/// Used when the caller has no cont_param and needs a halt-cont to pass to the
/// callee — the callee's Term::Return chains through it to record halt_value.
pub(crate) fn synthesize_halt_cont<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    runtime: &RuntimeRefs,
    repr: ArgRepr,
) -> ir::Value {
    let hcb_addr = fn_addr(body.jmod, halt_cont_body_id_for(runtime, repr), body.b);
    let kind_v = body.b.ins().iconst(types::I32, repr.halt_kind() as i64);
    body.get_halt_cont(hcb_addr, kind_v)
}

/// Pick the halt_cont_body FuncId matching `repr`.
pub(crate) fn halt_cont_body_id_for(runtime: &RuntimeRefs, repr: ArgRepr) -> FuncId {
    match repr {
        ArgRepr::ValueRef => runtime.halt_cont_body_strict_id,
        ArgRepr::RawInt => runtime.halt_cont_body_i64_id,
        ArgRepr::RawF64 => runtime.halt_cont_body_f64_id,
        ArgRepr::RawAtom => runtime.halt_cont_body_atom_id,
        ArgRepr::Condition => unreachable!("Condition vars never reach halt-cont"),
    }
}

/// Resolve the outer-cont ref to forward into a new cont closure.
/// For cont fns: loaded from closure env field 0. For non-cont native:
/// `cont_param` already is the outer cont.
/// For uniform fns without cont_param: load frame_ptr+16, brif on null to
/// allocate a halt-cont fallback closure.
///
/// Uniform cont fns (cont fns whose enclosing chain forced a uniform frame
/// ABI) have no `self` closure ptr; their outer_cont lives in frame slot 0
/// — fall through to the uniform branch when cont_param is None.
pub(crate) fn resolve_outer_cont<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    runtime: &RuntimeRefs,
    return_reprs: &[ArgRepr],
    is_cont_fn: bool,
    cont_param: Option<ir::Value>,
    frame_ptr: Option<ir::Value>,
    cont_sid: u32,
) -> ir::Value {
    if is_cont_fn && let Some(self_val) = cont_param {
        return body.outer_cont_ref(self_val);
    }
    // No `self` closure ptr: caller dispatched through the uniform
    // path; outer_cont lives in frame slot 0. Fall through.
    {
        let _ = is_cont_fn;
        match cont_param {
            Some(c) => c,
            None => {
                let from_slot = body.b.ins().load(
                    types::I64,
                    MemFlags::trusted(),
                    frame_ptr.expect("uniform caller building cont closure must have frame_ptr"),
                    HEADER_SIZE,
                );
                let zero = body.b.ins().iconst(types::I64, 0);
                let is_null = body.b.ins().icmp(IntCC::Equal, from_slot, zero);
                let alloc_blk = body.b.create_block();
                let join_blk = body.b.create_block();
                body.b.append_block_param(join_blk, types::I64);
                body.b
                    .ins()
                    .brif(is_null, alloc_blk, &[][..], join_blk, &[BlockArg::Value(from_slot)]);
                body.b.switch_to_block(alloc_blk);
                body.b.seal_block(alloc_blk);
                let dummy_fid = body.b.ins().iconst(types::I32, 0);
                let n_caps0 = body.b.ins().iconst(types::I32, 0);
                let hc_repr = return_reprs[cont_sid as usize];
                let hcb_addr = fn_addr(body.jmod, halt_cont_body_id_for(runtime, hc_repr), body.b);
                let zero_hk = body.b.ins().iconst(types::I32, 0);
                let halt_cl = body.alloc_closure(dummy_fid, n_caps0, zero_hk, hcb_addr);
                body.b.ins().jump(join_blk, &[BlockArg::Value(halt_cl)]);
                body.b.switch_to_block(join_blk);
                body.b.seal_block(join_blk);
                body.b.block_params(join_blk)[0]
            }
        }
    }
}

/// Allocate a cont closure, populate its code-addr, outer-cont, and user
/// captures. Returns the heap pointer to the new closure object.
///
/// `cap_bindings` is a slice of user captures. Typed captures stay in raw
/// payload slots; `ValueRef` captures are already one-word any value refs.
#[allow(clippy::too_many_arguments)]
pub(crate) fn build_cont_closure<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    runtime: &RuntimeRefs,
    return_reprs: &[ArgRepr],
    is_cont_fn: bool,
    cont_param: Option<ir::Value>,
    frame_ptr: Option<ir::Value>,
    cont_sid: u32,
    cont_fid: FuncId,
    cap_bindings: &[ClosureCapture],
    extra_ref_captures: &[ir::Value],
) -> ir::Value {
    let my_outer_cont = resolve_outer_cont(body, runtime, return_reprs, is_cont_fn, cont_param, frame_ptr, cont_sid);
    let cl_fid_v = body.b.ins().iconst(types::I32, cont_sid as i64);
    // +1 reserves env field 0 for the synthetic outer_cont; user captures follow.
    let n_caps_v = body
        .b
        .ins()
        .iconst(types::I32, (cap_bindings.len() + extra_ref_captures.len() + 1) as i64);
    let zero_hk = body.b.ins().iconst(types::I32, 0);
    let cont_code_addr = fn_addr(body.jmod, cont_fid, body.b);
    let cl_ptr = body.alloc_closure(cl_fid_v, n_caps_v, zero_hk, cont_code_addr);
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

const LAZY_CONT_HEADER_BYTES: usize = 32;
const LAZY_CONT_KIND_REF: i64 = 0;
const LAZY_CONT_KIND_I64: i64 = 1;
const LAZY_CONT_KIND_F64: i64 = 2;
const LAZY_CONT_KIND_ATOM: i64 = 3;

pub(crate) fn build_lazy_cont_descriptor<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    runtime: &RuntimeRefs,
    return_reprs: &[ArgRepr],
    is_cont_fn: bool,
    cont_param: Option<ir::Value>,
    frame_ptr: Option<ir::Value>,
    cont_sid: u32,
    cont_fid: FuncId,
    cap_bindings: &[ClosureCapture],
    extra_ref_captures: &[ir::Value],
) -> ir::Value {
    let my_outer_cont = resolve_outer_cont(body, runtime, return_reprs, is_cont_fn, cont_param, frame_ptr, cont_sid);
    let captured_count = cap_bindings.len() + extra_ref_captures.len() + 1;
    let raw_base = LAZY_CONT_HEADER_BYTES;
    let kind_base = raw_base + captured_count * SLOT_BYTES as usize;
    let slot_size = kind_base + captured_count;
    let slot = body
        .b
        .create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, slot_size as u32, 3));
    let code_addr = fn_addr(body.jmod, cont_fid, body.b);
    body.b.ins().stack_store(code_addr, slot, 0);
    let sid_v = body.b.ins().iconst(types::I64, cont_sid as i64);
    body.b.ins().stack_store(sid_v, slot, 8);
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
    emit_tagged_pointer_ref_word(body.b, ptr, TAG_FWD)
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

#[cfg(test)]
mod tests {
    use super::*;
    use cranelift_codegen::Context;
    use cranelift_codegen::ir::{AbiParam, Signature};
    use cranelift_codegen::isa::CallConv;

    fn render_pointer_ref_pack_for_arch(arch: TaggedRefArch) -> String {
        let mut ctx = Context::new();
        ctx.func.signature = Signature::new(CallConv::SystemV);
        ctx.func.signature.params.push(AbiParam::new(types::I64));
        ctx.func.signature.returns.push(AbiParam::new(types::I64));
        let mut fbctx = FunctionBuilderContext::new();
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let ptr = b.block_params(entry)[0];
            let value = emit_tagged_pointer_ref_word_for_arch(&mut b, ptr, TAG_FWD, arch);
            b.ins().return_(&[value]);
            b.finalize();
        }
        ctx.func.display().to_string()
    }

    #[test]
    fn arm64_tbi_pointer_ref_pack_omits_clear_step() {
        let clif = render_pointer_ref_pack_for_arch(TaggedRefArch::Arm64Tbi);

        assert!(
            !clif.contains("band_imm"),
            "arm64/TBI must not mask fresh pointers:\n{clif}"
        );
        assert!(
            !clif.contains("ishl_imm") && !clif.contains("ushr_imm"),
            "arm64/TBI must not shift-clear fresh pointers:\n{clif}"
        );
        assert!(
            clif.contains("bor_imm v0, 0x0800_0000_0000_0000"),
            "arm64/TBI should OR the top-byte tag directly into the pointer:\n{clif}"
        );
    }

    #[test]
    fn x86_64_pointer_ref_pack_shift_clears_before_tagging() {
        let clif = render_pointer_ref_pack_for_arch(TaggedRefArch::X86_64Canonical57);

        assert!(
            clif.contains("ishl_imm v0, 7") && clif.contains("ushr_imm"),
            "x86_64 canonical refs must shift-clear high bits before tagging:\n{clif}"
        );
        assert!(
            !clif.contains("band_imm"),
            "x86_64 must not use mask immediates for this clear:\n{clif}"
        );
        assert!(
            clif.contains("bor_imm") && clif.contains("0x1000_0000_0000_0000"),
            "x86_64 canonical refs should OR the shifted tag word after clearing:\n{clif}"
        );
    }
}
