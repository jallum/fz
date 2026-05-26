//! Split from src/ir_codegen.rs (fz-ame.7). Mechanical move only.

#![allow(unused_imports)]

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
use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema};
use std::collections::HashMap;
use std::sync::Arc;

/// Allocate and return a halt-cont singleton for `repr` via `fz_get_halt_cont`.
/// Used when the caller has no cont_param and needs a halt-cont to pass to the
/// callee — the callee's Term::Return chains through it to record halt_value.
pub(crate) fn synthesize_halt_cont<M: cranelift_module::Module>(
    jmod: &mut M,
    b: &mut FunctionBuilder<'_>,
    runtime: &RuntimeRefs,
    repr: ArgRepr,
) -> ir::Value {
    let fref = jmod.declare_func_in_func(runtime.get_halt_cont_id, b.func);
    let hcb_addr = fn_addr(jmod, halt_cont_body_id_for(runtime, repr), b);
    let kind_v = b.ins().iconst(types::I32, repr.halt_kind() as i64);
    let inst = b.ins().call(fref, &[hcb_addr, kind_v]);
    b.inst_results(inst)[0]
}

/// fz-ul4.27.22.3 — pick the halt_cont_body FuncId matching `repr`.
pub(crate) fn halt_cont_body_id_for(runtime: &RuntimeRefs, repr: ArgRepr) -> FuncId {
    match repr {
        ArgRepr::ValueRef => runtime.halt_cont_body_strict_id,
        ArgRepr::RawInt => runtime.halt_cont_body_i64_id,
        ArgRepr::RawF64 => runtime.halt_cont_body_f64_id,
        ArgRepr::Condition => unreachable!("Condition vars never reach halt-cont"),
    }
}

pub(crate) fn load_closure_capture_as_binding(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut impl cranelift_module::Module,
    runtime: &RuntimeRefs,
    closure_ref: ir::Value,
    _captured_count: usize,
    idx: usize,
    repr: ArgRepr,
) -> CodegenValue {
    let index = b.ins().iconst(types::I64, idx as i64);
    match repr {
        ArgRepr::RawInt => {
            let fref = jmod.declare_func_in_func(runtime.closure_get_capture_i64_id, b.func);
            let inst = b.ins().call(fref, &[closure_ref, index]);
            CodegenValue::from_abi_value(b.inst_results(inst)[0], ArgRepr::RawInt)
        }
        ArgRepr::RawF64 => {
            let fref = jmod.declare_func_in_func(runtime.closure_get_capture_f64_id, b.func);
            let inst = b.ins().call(fref, &[closure_ref, index]);
            CodegenValue::from_abi_value(b.inst_results(inst)[0], ArgRepr::RawF64)
        }
        ArgRepr::ValueRef => {
            let fref = jmod.declare_func_in_func(runtime.closure_get_capture_ref_id, b.func);
            let inst = b.ins().call(fref, &[closure_ref, index]);
            CodegenValue::any_ref(b.inst_results(inst)[0])
        }
        ArgRepr::Condition => unreachable!("closure captures are never condition-only"),
    }
}

pub(crate) fn load_outer_cont_ref<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    closure_ref: ir::Value,
) -> ir::Value {
    let fref = jmod.declare_func_in_func(runtime.closure_get_capture_ref_id, b.func);
    let index = b.ins().iconst(types::I64, 0);
    let inst = b.ins().call(fref, &[closure_ref, index]);
    b.inst_results(inst)[0]
}

pub(crate) fn load_closure_code_ref<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    closure_ref: ir::Value,
) -> ir::Value {
    let fref = jmod.declare_func_in_func(runtime.closure_code_ref_id, b.func);
    let inst = b.ins().call(fref, &[closure_ref]);
    b.inst_results(inst)[0]
}

pub(crate) fn load_closure_halt_kind_ref<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    closure_ref: ir::Value,
) -> ir::Value {
    let fref = jmod.declare_func_in_func(runtime.closure_halt_kind_ref_id, b.func);
    let inst = b.ins().call(fref, &[closure_ref]);
    b.inst_results(inst)[0]
}

pub(crate) fn store_closure_capture_ref_word<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    closure_ref: ir::Value,
    _captured_count: usize,
    idx: usize,
    value: ir::Value,
) {
    let fref = jmod.declare_func_in_func(runtime.closure_set_capture_ref_id, b.func);
    let index = b.ins().iconst(types::I64, idx as i64);
    b.ins().call(fref, &[closure_ref, index, value]);
}

fn materialize_cont_word<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    value: ir::Value,
) -> ir::Value {
    let fref = jmod.declare_func_in_func(runtime.materialize_cont_id, b.func);
    let inst = b.ins().call(fref, &[value]);
    b.inst_results(inst)[0]
}

pub(crate) fn store_closure_capture_i64<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    closure_ref: ir::Value,
    idx: usize,
    value: ir::Value,
) {
    let fref = jmod.declare_func_in_func(runtime.closure_set_capture_i64_id, b.func);
    let index = b.ins().iconst(types::I64, idx as i64);
    b.ins().call(fref, &[closure_ref, index, value]);
}

pub(crate) fn store_closure_capture_f64<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    closure_ref: ir::Value,
    idx: usize,
    value: ir::Value,
) {
    let fref = jmod.declare_func_in_func(runtime.closure_set_capture_f64_id, b.func);
    let index = b.ins().iconst(types::I64, idx as i64);
    b.ins().call(fref, &[closure_ref, index, value]);
}

pub(crate) fn store_outer_cont_capture(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut impl cranelift_module::Module,
    runtime: &RuntimeRefs,
    closure_ref: ir::Value,
    captured_count: usize,
    outer_cont: ir::Value,
) {
    store_closure_capture_ref_word(b, jmod, runtime, closure_ref, captured_count, 0, outer_cont);
}

pub(crate) fn emit_struct_set_field_value<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    cache: &mut CodegenCache,
    struct_bits: ir::Value,
    field_idx: usize,
    value: CodegenValue,
) {
    let offset = b
        .ins()
        .iconst(types::I32, (field_idx as i64) * SLOT_BYTES as i64);
    match value {
        CodegenValue::RawInt(raw)
        | CodegenValue::Known {
            payload: raw,
            kind: fz_runtime::any_value::ValueKind::INT,
        } => {
            let fref = jmod.declare_func_in_func(runtime.struct_set_field_int_id, b.func);
            b.ins().call(fref, &[struct_bits, offset, raw]);
        }
        CodegenValue::RawF64(raw) => {
            let fref = jmod.declare_func_in_func(runtime.struct_set_field_float_id, b.func);
            b.ins().call(fref, &[struct_bits, offset, raw]);
        }
        CodegenValue::Known {
            payload,
            kind: fz_runtime::any_value::ValueKind::FLOAT,
        } => {
            let fref = jmod.declare_func_in_func(runtime.struct_set_field_float_id, b.func);
            let raw = b.ins().bitcast(types::F64, MemFlags::new(), payload);
            b.ins().call(fref, &[struct_bits, offset, raw]);
        }
        CodegenValue::Known {
            payload,
            kind: fz_runtime::any_value::ValueKind::ATOM,
        } => {
            let fref = jmod.declare_func_in_func(runtime.struct_set_field_atom_id, b.func);
            b.ins().call(fref, &[struct_bits, offset, payload]);
        }
        other => {
            let value_ref = codegen_value_as_any_ref(b, jmod, runtime, cache, other);
            let fref = jmod.declare_func_in_func(runtime.struct_set_field_ref_id, b.func);
            b.ins().call(fref, &[struct_bits, offset, value_ref]);
        }
    }
}

/// Resolve the outer-cont ref to forward into a new cont closure.
/// For cont fns: loaded from closure env field 0. For non-cont native:
/// `cont_param` already is the outer cont.
/// For uniform fns without cont_param: load frame_ptr+16, brif on null to
/// allocate a halt-cont fallback closure.
pub(crate) fn resolve_outer_cont<M: cranelift_module::Module>(
    jmod: &mut M,
    b: &mut FunctionBuilder<'_>,
    runtime: &RuntimeRefs,
    return_reprs: &[ArgRepr],
    is_cont_fn: bool,
    cont_param: Option<ir::Value>,
    frame_ptr: Option<ir::Value>,
    cont_sid: u32,
) -> ir::Value {
    if is_cont_fn {
        // fz-70q.5.5 — uniform cont fn (cont fn whose enclosing chain
        // forced a uniform frame ABI): there is no `self` closure ptr
        // — the caller dispatched through the older trampoline using a
        // heap frame. The outer_cont in that case lives in frame slot 0
        // (frame+16), same layout the entry harness already uses for
        // the uniform path. Fall through to the older frame-slot load
        // below so the same site can build cont closures whether it
        // got entered via the scheduler resume seam or via a uniform call.
        if let Some(self_val) = cont_param {
            return load_outer_cont_ref(b, jmod, runtime, self_val);
        }
        // else fall through to the uniform frame-slot branch below.
    }
    {
        let _ = is_cont_fn; // consumed above when cont_param was Some
        match cont_param {
            Some(c) => c,
            None => {
                let from_slot = b.ins().load(
                    types::I64,
                    MemFlags::trusted(),
                    frame_ptr.expect("uniform caller building cont closure must have frame_ptr"),
                    HEADER_SIZE,
                );
                let zero = b.ins().iconst(types::I64, 0);
                let is_null = b.ins().icmp(IntCC::Equal, from_slot, zero);
                let alloc_blk = b.create_block();
                let join_blk = b.create_block();
                b.append_block_param(join_blk, types::I64);
                b.ins().brif(
                    is_null,
                    alloc_blk,
                    &[][..],
                    join_blk,
                    &[BlockArg::Value(from_slot)],
                );
                b.switch_to_block(alloc_blk);
                b.seal_block(alloc_blk);
                let acl = jmod.declare_func_in_func(runtime.alloc_closure_id, b.func);
                let dummy_fid = b.ins().iconst(types::I32, 0);
                let n_caps0 = b.ins().iconst(types::I32, 0);
                let hc_repr = return_reprs[cont_sid as usize];
                let hcb_addr = fn_addr(jmod, halt_cont_body_id_for(runtime, hc_repr), b);
                let zero_hk = b.ins().iconst(types::I32, 0);
                let halt_alloc = b.ins().call(acl, &[dummy_fid, n_caps0, zero_hk, hcb_addr]);
                let halt_cl = b.inst_results(halt_alloc)[0];
                b.ins().jump(join_blk, &[BlockArg::Value(halt_cl)]);
                b.switch_to_block(join_blk);
                b.seal_block(join_blk);
                b.block_params(join_blk)[0]
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
    jmod: &mut M,
    b: &mut FunctionBuilder<'_>,
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
    let my_outer_cont = resolve_outer_cont(
        jmod,
        b,
        runtime,
        return_reprs,
        is_cont_fn,
        cont_param,
        frame_ptr,
        cont_sid,
    );
    let acl_fref = jmod.declare_func_in_func(runtime.alloc_closure_id, b.func);
    let cl_fid_v = b.ins().iconst(types::I32, cont_sid as i64);
    // +1: closure env field 0 is synthetic outer_cont; user captures follow.
    let n_caps_v = b.ins().iconst(
        types::I32,
        (cap_bindings.len() + extra_ref_captures.len() + 1) as i64,
    );
    let zero_hk = b.ins().iconst(types::I32, 0);
    let cont_code_addr = fn_addr(jmod, cont_fid, b);
    let cl_inst = b
        .ins()
        .call(acl_fref, &[cl_fid_v, n_caps_v, zero_hk, cont_code_addr]);
    let cl_ptr = b.inst_results(cl_inst)[0];
    let captured_count = cap_bindings.len() + extra_ref_captures.len() + 1;
    let heap_safe_outer_cont = materialize_cont_word(b, jmod, runtime, my_outer_cont);
    store_outer_cont_capture(
        b,
        jmod,
        runtime,
        cl_ptr,
        captured_count,
        heap_safe_outer_cont,
    );
    for (i, &capture) in cap_bindings.iter().enumerate() {
        match capture {
            ClosureCapture::RefWord(ref_word) => {
                let heap_safe_ref = materialize_cont_word(b, jmod, runtime, ref_word);
                store_closure_capture_ref_word(
                    b,
                    jmod,
                    runtime,
                    cl_ptr,
                    captured_count,
                    i + 1,
                    heap_safe_ref,
                );
            }
            ClosureCapture::RawInt(raw) => {
                store_closure_capture_i64(b, jmod, runtime, cl_ptr, i + 1, raw);
            }
            ClosureCapture::RawF64(raw) => {
                store_closure_capture_f64(b, jmod, runtime, cl_ptr, i + 1, raw);
            }
        }
    }
    for (i, extra) in extra_ref_captures.iter().enumerate() {
        let heap_safe_ref = materialize_cont_word(b, jmod, runtime, *extra);
        store_closure_capture_ref_word(
            b,
            jmod,
            runtime,
            cl_ptr,
            captured_count,
            cap_bindings.len() + 1 + i,
            heap_safe_ref,
        );
    }
    cl_ptr
}

const LAZY_CONT_HEADER_BYTES: usize = 32;
const LAZY_CONT_KIND_REF: i64 = 0;
const LAZY_CONT_KIND_I64: i64 = 1;
const LAZY_CONT_KIND_F64: i64 = 2;

pub(crate) fn build_lazy_cont_descriptor<M: cranelift_module::Module>(
    jmod: &mut M,
    b: &mut FunctionBuilder<'_>,
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
    let my_outer_cont = resolve_outer_cont(
        jmod,
        b,
        runtime,
        return_reprs,
        is_cont_fn,
        cont_param,
        frame_ptr,
        cont_sid,
    );
    let captured_count = cap_bindings.len() + extra_ref_captures.len() + 1;
    let raw_base = LAZY_CONT_HEADER_BYTES;
    let kind_base = raw_base + captured_count * SLOT_BYTES as usize;
    let slot_size = kind_base + captured_count;
    let slot = b.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        slot_size as u32,
        3,
    ));
    let code_addr = fn_addr(jmod, cont_fid, b);
    b.ins().stack_store(code_addr, slot, 0);
    let sid_v = b.ins().iconst(types::I64, cont_sid as i64);
    b.ins().stack_store(sid_v, slot, 8);
    let captured_count_v = b.ins().iconst(types::I64, captured_count as i64);
    b.ins().stack_store(captured_count_v, slot, 16);

    store_lazy_capture(
        b,
        slot,
        raw_base,
        kind_base,
        0,
        my_outer_cont,
        LAZY_CONT_KIND_REF,
    );
    for (i, &capture) in cap_bindings.iter().enumerate() {
        match capture {
            ClosureCapture::RefWord(value) => {
                store_lazy_capture(
                    b,
                    slot,
                    raw_base,
                    kind_base,
                    i + 1,
                    value,
                    LAZY_CONT_KIND_REF,
                );
            }
            ClosureCapture::RawInt(value) => {
                store_lazy_capture(
                    b,
                    slot,
                    raw_base,
                    kind_base,
                    i + 1,
                    value,
                    LAZY_CONT_KIND_I64,
                );
            }
            ClosureCapture::RawF64(value) => {
                let raw = b.ins().bitcast(types::I64, MemFlags::new(), value);
                store_lazy_capture(b, slot, raw_base, kind_base, i + 1, raw, LAZY_CONT_KIND_F64);
            }
        }
    }
    for (i, &extra) in extra_ref_captures.iter().enumerate() {
        store_lazy_capture(
            b,
            slot,
            raw_base,
            kind_base,
            cap_bindings.len() + 1 + i,
            extra,
            LAZY_CONT_KIND_REF,
        );
    }
    let ptr = b.ins().stack_addr(types::I64, slot, 0);
    let address_mask = fz_runtime::any_value::AnyValueRefPacking::current().address_mask() as i64;
    let ptr_payload = b.ins().band_imm(ptr, address_mask);
    let tag_word = (fz_runtime::any_value::TAG_FWD
        << fz_runtime::any_value::AnyValueRefPacking::current().tag_shift())
        as i64;
    b.ins().bor_imm(ptr_payload, tag_word)
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
