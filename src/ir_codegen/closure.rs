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
    cx: &mut CodegenFn<'_>,
    jmod: &mut M,
    b: &mut FunctionBuilder<'_>,
    runtime: &RuntimeRefs,
    repr: ArgRepr,
) -> ir::Value {
    let hcb_addr = fn_addr(jmod, halt_cont_body_id_for(runtime, repr), b);
    let kind_v = b.ins().iconst(types::I32, repr.halt_kind() as i64);
    cx.get_halt_cont(b, jmod, hcb_addr, kind_v)
}

/// Pick the halt_cont_body FuncId matching `repr`.
pub(crate) fn halt_cont_body_id_for(runtime: &RuntimeRefs, repr: ArgRepr) -> FuncId {
    match repr {
        ArgRepr::ValueRef => runtime.halt_cont_body_strict_id,
        ArgRepr::RawInt => runtime.halt_cont_body_i64_id,
        ArgRepr::RawF64 => runtime.halt_cont_body_f64_id,
        ArgRepr::Condition => unreachable!("Condition vars never reach halt-cont"),
    }
}

pub(crate) fn load_closure_capture_as_binding(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut impl cranelift_module::Module,
    closure_ref: ir::Value,
    _captured_count: usize,
    idx: usize,
    repr: ArgRepr,
) -> CodegenValue {
    let index = b.ins().iconst(types::I64, idx as i64);
    match repr {
        ArgRepr::RawInt => CodegenValue::from_abi_value(
            cx.closure_capture_i64(b, jmod, closure_ref, index),
            ArgRepr::RawInt,
        ),
        ArgRepr::RawF64 => CodegenValue::from_abi_value(
            cx.closure_capture_f64(b, jmod, closure_ref, index),
            ArgRepr::RawF64,
        ),
        ArgRepr::ValueRef => {
            CodegenValue::any_ref(cx.closure_capture_ref(b, jmod, closure_ref, index))
        }
        ArgRepr::Condition => unreachable!("closure captures are never condition-only"),
    }
}

pub(crate) fn load_outer_cont_ref<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    closure_ref: ir::Value,
) -> ir::Value {
    let index = b.ins().iconst(types::I64, 0);
    cx.closure_capture_ref(b, jmod, closure_ref, index)
}

pub(crate) fn load_closure_code_ref<M: cranelift_module::Module, K>(
    cx: &mut CodegenFn<'_, K>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    closure_ref: ir::Value,
) -> ir::Value {
    cx.closure_code_ref(b, jmod, closure_ref)
}

pub(crate) fn load_closure_halt_kind_ref<M: cranelift_module::Module, K>(
    cx: &mut CodegenFn<'_, K>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    closure_ref: ir::Value,
) -> ir::Value {
    cx.closure_halt_kind_ref(b, jmod, closure_ref)
}

pub(crate) fn store_closure_capture_ref_word<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    closure_ref: ir::Value,
    _captured_count: usize,
    idx: usize,
    value: ir::Value,
) {
    let value = cx.mark_published_ref_aliased(b, jmod, value);
    let index = b.ins().iconst(types::I64, idx as i64);
    cx.set_closure_capture_ref(b, jmod, closure_ref, index, value);
}

fn materialize_cont_word<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    value: ir::Value,
) -> ir::Value {
    cx.materialize_cont(b, jmod, value)
}

pub(crate) fn store_closure_capture_i64<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    closure_ref: ir::Value,
    idx: usize,
    value: ir::Value,
) {
    let index = b.ins().iconst(types::I64, idx as i64);
    cx.set_closure_capture_i64(b, jmod, closure_ref, index, value);
}

pub(crate) fn store_closure_capture_f64<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    closure_ref: ir::Value,
    idx: usize,
    value: ir::Value,
) {
    let index = b.ins().iconst(types::I64, idx as i64);
    cx.set_closure_capture_f64(b, jmod, closure_ref, index, value);
}

pub(crate) fn store_outer_cont_capture(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut impl cranelift_module::Module,
    closure_ref: ir::Value,
    captured_count: usize,
    outer_cont: ir::Value,
) {
    store_closure_capture_ref_word(cx, b, jmod, closure_ref, captured_count, 0, outer_cont);
}

pub(crate) fn emit_struct_set_field_value<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
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
            cx.struct_set_field_int(b, jmod, struct_bits, offset, raw);
        }
        CodegenValue::RawF64(raw) => {
            cx.struct_set_field_float(b, jmod, struct_bits, offset, raw);
        }
        CodegenValue::Known {
            payload,
            kind: fz_runtime::any_value::ValueKind::FLOAT,
        } => {
            let raw = b.ins().bitcast(types::F64, MemFlags::new(), payload);
            cx.struct_set_field_float(b, jmod, struct_bits, offset, raw);
        }
        CodegenValue::Known {
            payload,
            kind: fz_runtime::any_value::ValueKind::ATOM,
        } => {
            cx.struct_set_field_atom(b, jmod, struct_bits, offset, payload);
        }
        other => {
            let value_ref = cx.body(b, jmod, cache).value_as_any_ref(other);
            let value_ref = cx.mark_published_ref_aliased(b, jmod, value_ref);
            cx.struct_set_field_ref(b, jmod, struct_bits, offset, value_ref);
        }
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
    cx: &mut CodegenFn<'_>,
    jmod: &mut M,
    b: &mut FunctionBuilder<'_>,
    runtime: &RuntimeRefs,
    return_reprs: &[ArgRepr],
    is_cont_fn: bool,
    cont_param: Option<ir::Value>,
    frame_ptr: Option<ir::Value>,
    cont_sid: u32,
) -> ir::Value {
    if is_cont_fn && let Some(self_val) = cont_param {
        return load_outer_cont_ref(cx, b, jmod, self_val);
    }
    // No `self` closure ptr: caller dispatched through the uniform
    // path; outer_cont lives in frame slot 0. Fall through.
    {
        let _ = is_cont_fn;
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
                let dummy_fid = b.ins().iconst(types::I32, 0);
                let n_caps0 = b.ins().iconst(types::I32, 0);
                let hc_repr = return_reprs[cont_sid as usize];
                let hcb_addr = fn_addr(jmod, halt_cont_body_id_for(runtime, hc_repr), b);
                let zero_hk = b.ins().iconst(types::I32, 0);
                let halt_cl = cx.alloc_closure(b, jmod, dummy_fid, n_caps0, zero_hk, hcb_addr);
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
    cx: &mut CodegenFn<'_>,
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
        cx,
        jmod,
        b,
        runtime,
        return_reprs,
        is_cont_fn,
        cont_param,
        frame_ptr,
        cont_sid,
    );
    let cl_fid_v = b.ins().iconst(types::I32, cont_sid as i64);
    // +1 reserves env field 0 for the synthetic outer_cont; user captures follow.
    let n_caps_v = b.ins().iconst(
        types::I32,
        (cap_bindings.len() + extra_ref_captures.len() + 1) as i64,
    );
    let zero_hk = b.ins().iconst(types::I32, 0);
    let cont_code_addr = fn_addr(jmod, cont_fid, b);
    let cl_ptr = cx.alloc_closure(b, jmod, cl_fid_v, n_caps_v, zero_hk, cont_code_addr);
    let captured_count = cap_bindings.len() + extra_ref_captures.len() + 1;
    let heap_safe_outer_cont = materialize_cont_word(cx, b, jmod, my_outer_cont);
    store_outer_cont_capture(cx, b, jmod, cl_ptr, captured_count, heap_safe_outer_cont);
    store_user_captures(
        cap_bindings,
        extra_ref_captures,
        |idx, capture| match capture {
            ClosureCapture::RefWord(ref_word) => {
                let heap_safe_ref = materialize_cont_word(cx, b, jmod, ref_word);
                store_closure_capture_ref_word(
                    cx,
                    b,
                    jmod,
                    cl_ptr,
                    captured_count,
                    idx,
                    heap_safe_ref,
                );
            }
            ClosureCapture::RawInt(raw) => {
                store_closure_capture_i64(cx, b, jmod, cl_ptr, idx, raw);
            }
            ClosureCapture::RawF64(raw) => {
                store_closure_capture_f64(cx, b, jmod, cl_ptr, idx, raw);
            }
        },
    );
    cl_ptr
}

/// Iterate user captures (typed `cap_bindings` followed by `extra_ref_captures`)
/// and invoke `store` for each one at its target slot index. Slot 0 is reserved
/// for the synthetic outer_cont and must be written by the caller before
/// invoking this helper; user captures begin at index 1.
fn store_user_captures<F>(
    cap_bindings: &[ClosureCapture],
    extra_ref_captures: &[ir::Value],
    mut store: F,
) where
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

pub(crate) fn build_lazy_cont_descriptor<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
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
        cx,
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
    store_user_captures(
        cap_bindings,
        extra_ref_captures,
        |idx, capture| match capture {
            ClosureCapture::RefWord(value) => {
                store_lazy_capture(b, slot, raw_base, kind_base, idx, value, LAZY_CONT_KIND_REF);
            }
            ClosureCapture::RawInt(value) => {
                store_lazy_capture(b, slot, raw_base, kind_base, idx, value, LAZY_CONT_KIND_I64);
            }
            ClosureCapture::RawF64(value) => {
                let raw = b.ins().bitcast(types::I64, MemFlags::new(), value);
                store_lazy_capture(b, slot, raw_base, kind_base, idx, raw, LAZY_CONT_KIND_F64);
            }
        },
    );
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
