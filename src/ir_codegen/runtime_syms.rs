//! Split from src/ir_codegen.rs (fz-ame.7). Mechanical move only.

#![allow(unused_imports)]

use super::*;
use crate::fz_ir::{BinOp, Const, FnId, Module, Prim, Stmt, Term, UnOp};
use cranelift_codegen::Context;
use cranelift_codegen::ir::{
    self, AbiParam, BlockArg, InstBuilder, MemFlags, Signature,
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

pub(crate) fn sig1(params: &[ir::Type], rets: &[ir::Type]) -> Signature {
    let mut s = Signature::new(CallConv::SystemV);
    for p in params {
        s.params.push(AbiParam::new(*p));
    }
    for r in rets {
        s.returns.push(AbiParam::new(*r));
    }
    s
}

/// Declare every fz runtime FFI fn as an Import in the given Cranelift
/// Module and return the resulting FuncIds packed into a RuntimeRefs.
///
/// Generic on `M: cranelift_module::Module` so the JIT (JITModule) and a
/// future AOT driver (ObjectModule, fz-ul4.23.6) call the same fn — the
/// declarations don't care whether the underlying symbol resolves via
/// JIT-installed Rust fn pointers or via a linker-resolved staticlib.
///
/// This is the only place that knows the wire ABI of each runtime fn;
/// changing one signature requires updating both the FFI body in
/// ir_runtime.rs AND the matching entry here.
pub(crate) fn declare_runtime_symbols<M: cranelift_module::Module>(
    jmod: &mut M,
) -> Result<RuntimeRefs, CodegenError> {
    // fz-02r.5 — import FZ_SHOULD_YIELD as a 1-byte external data object.
    // Must be declared before the `decl` closure borrows `jmod`.
    let should_yield_data_id = jmod
        .declare_data("FZ_SHOULD_YIELD", Linkage::Import, false, false)
        .map_err(|e| CodegenError::new(format!("declare FZ_SHOULD_YIELD: {}", e)))?;
    let mut decl = |name: &str, params: &[ir::Type], rets: &[ir::Type]| {
        let sig = sig1(params, rets);
        jmod.declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))
    };

    let halt_implicit_ref_id = decl("fz_halt_implicit_ref", &[types::I64], &[])?;
    // fz-ul4.27.22.3 — typed halt-implicit variants.
    let halt_implicit_i64_id = decl("fz_halt_implicit_i64", &[types::I64], &[])?;
    let halt_implicit_f64_id = decl("fz_halt_implicit_f64", &[types::F64], &[])?;
    let alloc_id = decl("fz_alloc_frame", &[types::I32, types::I32], &[types::I64])?;
    let list_cons_any_id = decl("fz_list_cons_any", &[types::I64, types::I64], &[types::I64])?;
    let list_cons_int_id = decl("fz_list_cons_int", &[types::I64, types::I64], &[types::I64])?;
    let list_cons_float_id = decl(
        "fz_list_cons_float",
        &[types::F64, types::I64],
        &[types::I64],
    )?;
    let list_cons_atom_id = decl(
        "fz_list_cons_atom",
        &[types::I64, types::I64],
        &[types::I64],
    )?;
    let list_is_cons_id = decl("fz_list_is_cons", &[types::I64], &[types::I8])?;
    let list_head_fallback_id = decl("fz_list_head_ref", &[types::I64], &[types::I64])?;
    let list_head_int_ref_id = decl("fz_list_head_int_ref", &[types::I64], &[types::I64])?;
    let list_head_float_ref_id = decl("fz_list_head_float_ref", &[types::I64], &[types::F64])?;
    let list_tail_fallback_id = decl("fz_list_tail_ref", &[types::I64], &[types::I64])?;
    let alloc_struct_id = decl("fz_alloc_struct", &[types::I32], &[types::I64])?;
    let struct_get_field_id = decl(
        "fz_struct_get_field_ref",
        &[types::I64, types::I32],
        &[types::I64],
    )?;
    let struct_set_field_ref_id = decl(
        "fz_struct_set_field_ref",
        &[types::I64, types::I32, types::I64],
        &[],
    )?;
    let struct_set_field_int_id = decl(
        "fz_struct_set_field_int",
        &[types::I64, types::I32, types::I64],
        &[],
    )?;
    let struct_set_field_float_id = decl(
        "fz_struct_set_field_float",
        &[types::I64, types::I32, types::F64],
        &[],
    )?;
    let struct_set_field_atom_id = decl(
        "fz_struct_set_field_atom",
        &[types::I64, types::I32, types::I64],
        &[],
    )?;
    let bs_begin_id = decl("fz_bs_begin", &[], &[])?;
    let bs_write_ref_id = decl(
        "fz_bs_write_field_ref",
        &[
            types::I64, // value ref
            types::I32, // ty tag
            types::I32, // size_present
            types::I32, // size_value
            types::I32, // unit
            types::I32, // endian
            types::I32, // signed
        ],
        &[],
    )?;
    let bs_finalize_id = decl("fz_bs_finalize", &[], &[types::I64])?;
    // fz-cty.8 — `(payload_ptr: i64, byte_len: i64, bit_len: i64) -> i64`.
    let alloc_bitstring_const_id = decl(
        "fz_alloc_bitstring_const",
        &[types::I64, types::I64, types::I64],
        &[types::I64],
    )?;
    // fz-q8d.2 — `(static_sharedbin: i64) -> i64`. Retains the anchor on
    // the supplied static SharedBin and allocates a ProcBin on the
    // current process heap that owns the new refcount edge.
    let alloc_procbin_from_static_id =
        decl("fz_alloc_procbin_from_static", &[types::I64], &[types::I64])?;
    // fz-q8d.2 — noop destructor symbol. Imported so its address can be
    // baked into each static SharedBin's `destructor` slot via a
    // function-address relocation. Matches the runtime's `extern "C" fn
    // (*mut SharedBin)` signature exactly.
    let shared_bin_destructor_noop_id = decl("shared_bin_destructor_noop", &[types::I64], &[])?;
    // fz-9ss — extern binary marshal helpers.
    let binary_as_ptr_id = decl("fz_binary_as_ptr", &[types::I64], &[types::I64])?;
    let binary_as_cstring_id = decl("fz_binary_as_cstring", &[types::I64], &[types::I64])?;
    let bs_reader_init_ref_id = decl("fz_bs_reader_init_ref", &[types::I64], &[types::I64])?;
    let bs_read_field_ref_id = decl(
        "fz_bs_read_field_ref",
        &[
            types::I64, // reader ref
            types::I64, // packed field spec
            types::I32, // size_value
        ],
        &[types::I64],
    )?;
    let bs_reader_done_ref_id = decl("fz_bs_reader_done_ref", &[types::I64], &[types::I8])?;
    let map_empty_id = decl("fz_map_empty", &[], &[types::I64])?;
    let map_builder_begin_id = decl("fz_map_builder_begin", &[types::I32], &[types::I64])?;
    let map_builder_begin_update_id = decl(
        "fz_map_builder_begin_update",
        &[types::I64, types::I32],
        &[types::I64],
    )?;
    let map_builder_put_parts_id = decl(
        "fz_map_builder_put_parts",
        &[types::I64, types::I64, types::I64, types::I64, types::I64],
        &[],
    )?;
    let map_builder_put_ref_id = decl(
        "fz_map_builder_put_ref",
        &[types::I64, types::I64, types::I64],
        &[],
    )?;
    let map_builder_freeze_id = decl("fz_map_builder_freeze", &[types::I64], &[types::I64])?;
    let map_put_ref_id = decl(
        "fz_map_put_ref",
        &[types::I64, types::I64, types::I64],
        &[types::I64],
    )?;
    let map_put_int_id = decl(
        "fz_map_put_int",
        &[types::I64, types::I64, types::I64],
        &[types::I64],
    )?;
    let map_put_float_id = decl(
        "fz_map_put_float",
        &[types::I64, types::I64, types::F64],
        &[types::I64],
    )?;
    let map_put_atom_id = decl(
        "fz_map_put_atom",
        &[types::I64, types::I64, types::I64],
        &[types::I64],
    )?;
    let map_put_atom_key_int_id = decl(
        "fz_map_put_atom_key_int",
        &[types::I64, types::I64, types::I64],
        &[types::I64],
    )?;
    let map_put_atom_key_float_id = decl(
        "fz_map_put_atom_key_float",
        &[types::I64, types::I64, types::F64],
        &[types::I64],
    )?;
    let map_put_atom_key_atom_id = decl(
        "fz_map_put_atom_key_atom",
        &[types::I64, types::I64, types::I64],
        &[types::I64],
    )?;
    let map_put_int_key_int_id = decl(
        "fz_map_put_int_key_int",
        &[types::I64, types::I64, types::I64],
        &[types::I64],
    )?;
    let map_put_int_key_float_id = decl(
        "fz_map_put_int_key_float",
        &[types::I64, types::I64, types::F64],
        &[types::I64],
    )?;
    let map_put_int_key_atom_id = decl(
        "fz_map_put_int_key_atom",
        &[types::I64, types::I64, types::I64],
        &[types::I64],
    )?;
    let map_put_float_key_int_id = decl(
        "fz_map_put_float_key_int",
        &[types::I64, types::F64, types::I64],
        &[types::I64],
    )?;
    let map_put_float_key_float_id = decl(
        "fz_map_put_float_key_float",
        &[types::I64, types::F64, types::F64],
        &[types::I64],
    )?;
    let map_put_float_key_atom_id = decl(
        "fz_map_put_float_key_atom",
        &[types::I64, types::F64, types::I64],
        &[types::I64],
    )?;
    let map_get_ref_id = decl("fz_map_get_ref", &[types::I64, types::I64], &[types::I64])?;
    let map_get_atom_key_ref_id = decl(
        "fz_map_get_atom_key_ref",
        &[types::I64, types::I64],
        &[types::I64],
    )?;
    let map_get_int_key_ref_id = decl(
        "fz_map_get_int_key_ref",
        &[types::I64, types::I64],
        &[types::I64],
    )?;
    let map_get_float_key_ref_id = decl(
        "fz_map_get_float_key_ref",
        &[types::I64, types::F64],
        &[types::I64],
    )?;
    let ref_load_int_id = decl("fz_ref_load_int", &[types::I64], &[types::I64])?;
    let ref_load_float_id = decl("fz_ref_load_float", &[types::I64], &[types::F64])?;
    let ref_load_atom_id = decl("fz_ref_load_atom", &[types::I64], &[types::I64])?;
    let type_of_id = decl("fz_type_of", &[types::I64], &[types::I8])?;
    let unbox_int_id = decl("fz_unbox_int", &[types::I64], &[types::I64])?;
    let unbox_float_id = decl("fz_unbox_float", &[types::I64], &[types::F64])?;
    let unbox_atom_id = decl("fz_unbox_atom", &[types::I64], &[types::I64])?;
    let struct_schema_id_ref_id = decl("fz_struct_schema_id_ref", &[types::I64], &[types::I32])?;
    let truthy_ref_id = decl("fz_truthy_ref", &[types::I64], &[types::I8])?;
    let box_int_for_any_id = decl("fz_box_int_for_any", &[types::I64], &[types::I64])?;
    let box_float_for_any_id = decl("fz_box_float_for_any", &[types::F64], &[types::I64])?;
    let box_atom_for_any_id = decl("fz_box_atom_for_any", &[types::I64], &[types::I64])?;
    let map_is_map_id = decl("fz_map_is_map", &[types::I64], &[types::I8])?;
    let arith_ret: &[ir::Type] = &[types::I64];
    // fz-ul4.27.9: mixed-type arith/cmp slow paths are now inlined in JIT.
    // `fz_promote_f64` does the tag-aware Int|Float→f64 conversion (with the
    // same panic-on-non-numeric semantics the old fz_arith_* helpers had);
    let promote_f64_id = decl("fz_promote_f64", &[types::I64], &[types::F64])?;
    let dynamic_float_arith_unsupported_id =
        decl("fz_dynamic_float_arith_unsupported", &[], &[types::I64])?;
    let value_eq_ref_id = decl("fz_value_eq_ref", &[types::I64, types::I64], arith_ret)?;
    // fz-puj.45 (X4) — receive matcher binary-literal comparison.
    // `(val_bits: i64, bytes_ptr: i64, byte_len: i64) -> i32`.
    let matcher_eq_bytes_id = decl(
        "fz_matcher_eq_bytes",
        &[types::I64, types::I64, types::I64],
        &[types::I32],
    )?;
    // fz-puj.47 (X6) — receive matcher map-key lookup.
    // `(map_bits: i64, key_bits: i64) -> i64` (returns matcher miss sentinel on miss).
    let matcher_map_get_id = decl(
        "fz_matcher_map_get",
        &[types::I64, types::I64],
        &[types::I64],
    )?;
    let matcher_map_get_ref_id = decl(
        "fz_matcher_map_get_ref",
        &[types::I64, types::I64],
        &[types::I64],
    )?;

    let alloc_closure_id = decl(
        "fz_alloc_closure",
        &[types::I32, types::I32, types::I32, types::I64],
        &[types::I64],
    )?;
    let closure_code_ref_id = decl("fz_closure_code_ref", &[types::I64], &[types::I64])?;
    let closure_halt_kind_ref_id = decl("fz_closure_halt_kind_ref", &[types::I64], &[types::I32])?;
    let closure_get_capture_ref_id = decl(
        "fz_closure_get_capture_ref",
        &[types::I64, types::I64],
        &[types::I64],
    )?;
    let closure_get_capture_i64_id = decl(
        "fz_closure_get_capture_i64",
        &[types::I64, types::I64],
        &[types::I64],
    )?;
    let closure_get_capture_f64_id = decl(
        "fz_closure_get_capture_f64",
        &[types::I64, types::I64],
        &[types::F64],
    )?;
    let closure_set_capture_ref_id = decl(
        "fz_closure_set_capture_ref",
        &[types::I64, types::I64, types::I64],
        &[],
    )?;
    let closure_set_capture_i64_id = decl(
        "fz_closure_set_capture_i64",
        &[types::I64, types::I64, types::I64],
        &[],
    )?;
    let closure_set_capture_f64_id = decl(
        "fz_closure_set_capture_f64",
        &[types::I64, types::I64, types::F64],
        &[],
    )?;
    // fz-cps.1.2 — receive cutover. Takes a cont closure ptr (i64),
    // parks an accept-any matcher record, returns YIELD sentinel.
    let receive_park_id = decl("fz_receive_park", &[types::I64], &[types::I64])?;
    // fz-yxs/fz-st5/fz-70q.3 — selective-receive park entry. Args:
    //   matcher_fn_bits (i64), pinned_ptr (i64), n_pinned (i64),
    //   clause_bodies_ptr (i64), n_clauses (i64),
    //   clause_bound_counts_ptr (i64), bound_arity (i32),
    //   after_deadline_or_neg1 (i64), after_cont_bits (i64).
    // Returns YIELD sentinel (i64).
    let receive_park_matched_id = decl(
        "fz_receive_park_matched",
        &[
            types::I64,
            types::I64,
            types::I64,
            types::I64,
            types::I64,
            types::I64,
            types::I32,
            types::I64,
            types::I64,
        ],
        &[types::I64],
    )?;
    let yield_mid_flight_id = decl("fz_yield_mid_flight", &[types::I64], &[types::I64])?;
    // fz-cps.1.7 — static zero-capture closure singleton lookup.
    // Returns the per-Process singleton pointer for the given cl_sid.
    let get_static_closure_id = decl("fz_get_static_closure", &[types::I32], &[types::I64])?;
    // fz-cps.1.11 — halt-cont singleton lookup. Returns the per-Process
    // halt-cont closure ptr; lazily initialized using the supplied
    // halt_cont_body addr (JIT pre-populates at make_process time;
    // AOT path relies on lazy init at first call).
    // fz-ul4.27.22.3 — `(addr, kind)` sig: kind selects among 3 Process
    // singletons (0=ValueRef, 1=RawInt, 2=RawF64).
    let get_halt_cont_id = decl("fz_get_halt_cont", &[types::I64, types::I32], &[types::I64])?;
    // fz-ul4.27.22.3 — three fz_halt_cont_body variants, declared LOCAL
    // (bodies emitted below). Strict: `(raw i64, kind i8, self i64) -> i64 tail`;
    // RawInt: `(i64, self i64) -> i64 tail`; RawF64: `(f64, self i64) -> i64 tail`.
    let halt_cont_body_strict_id = {
        let mut sig = Signature::new(CallConv::Tail);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I8));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        jmod.declare_function("fz_halt_cont_body_strict", Linkage::Local, &sig)
            .map_err(|e| CodegenError::new(format!("declare fz_halt_cont_body_strict: {}", e)))?
    };
    let mut declare_narrow_hcb = |name: &str, val_ty: ir::Type| -> Result<FuncId, CodegenError> {
        let mut sig = Signature::new(CallConv::Tail);
        sig.params.push(AbiParam::new(val_ty));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        jmod.declare_function(name, Linkage::Local, &sig)
            .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))
    };
    let halt_cont_body_i64_id = declare_narrow_hcb("fz_halt_cont_body_i64", types::I64)?;
    let halt_cont_body_f64_id = declare_narrow_hcb("fz_halt_cont_body_f64", types::F64)?;
    // fz-cps.1.11 — fz_spawn_entry: SystemV entry the scheduler calls to
    // launch a new task's zero-arg closure. Sig: `(closure:i64) -> i64`.
    let mut se_sig = Signature::new(CallConv::SystemV);
    se_sig.params.push(AbiParam::new(types::I64));
    se_sig.returns.push(AbiParam::new(types::I64));
    let spawn_entry_id = jmod
        .declare_function("fz_spawn_entry", Linkage::Local, &se_sig)
        .map_err(|e| CodegenError::new(format!("declare fz_spawn_entry: {}", e)))?;
    // fz-ul4.27.22.3 — fz_main_entry: SystemV entry the scheduler calls
    // to launch at a known main fn. Sig: `(main_fp:i64, halt_cl:i64)
    // -> i64`. Rust caller picks halt_cl from process.halt_cont_singletons
    // by the entry fn's return_repr kind.
    let mut me_sig = Signature::new(CallConv::SystemV);
    me_sig.params.push(AbiParam::new(types::I64));
    me_sig.params.push(AbiParam::new(types::I64));
    me_sig.returns.push(AbiParam::new(types::I64));
    let main_entry_id = jmod
        .declare_function("fz_main_entry", Linkage::Local, &me_sig)
        .map_err(|e| CodegenError::new(format!("declare fz_main_entry: {}", e)))?;
    // fz-4mk.3a — fz_drain_dtor_entry: SystemV entry the scheduler calls
    // per pending dtor at task-exit. Sig: `(closure:i64, payload_ref:i64)
    // -> i64 system_v`. Body reads the closure body addr through the runtime
    // ABI, allocates a
    // Strict halt-cont via fz_get_halt_cont, and Tail-CC indirect-calls
    // the closure body with `(self, payload, halt_cl)`.
    let mut dd_sig = Signature::new(CallConv::SystemV);
    dd_sig.params.push(AbiParam::new(types::I64));
    dd_sig.params.push(AbiParam::new(types::I64));
    dd_sig.returns.push(AbiParam::new(types::I64));
    let drain_dtor_entry_id = jmod
        .declare_function("fz_drain_dtor_entry", Linkage::Local, &dd_sig)
        .map_err(|e| CodegenError::new(format!("declare fz_drain_dtor_entry: {}", e)))?;

    Ok(RuntimeRefs {
        halt_implicit_ref_id,
        halt_implicit_i64_id,
        halt_implicit_f64_id,
        halt_cont_body_strict_id,
        halt_cont_body_i64_id,
        halt_cont_body_f64_id,
        alloc_id,
        list_cons_any_id,
        list_cons_int_id,
        list_cons_float_id,
        list_cons_atom_id,
        list_is_cons_id,
        list_head_fallback_id,
        list_head_int_ref_id,
        list_head_float_ref_id,
        list_tail_fallback_id,
        alloc_struct_id,
        struct_get_field_id,
        struct_set_field_ref_id,
        struct_set_field_int_id,
        struct_set_field_float_id,
        struct_set_field_atom_id,
        bs_begin_id,
        bs_write_ref_id,
        bs_finalize_id,
        alloc_bitstring_const_id,
        alloc_procbin_from_static_id,
        shared_bin_destructor_noop_id,
        binary_as_ptr_id,
        binary_as_cstring_id,
        bs_reader_init_ref_id,
        bs_read_field_ref_id,
        bs_reader_done_ref_id,
        map_empty_id,
        map_builder_begin_id,
        map_builder_begin_update_id,
        map_builder_put_parts_id,
        map_builder_put_ref_id,
        map_builder_freeze_id,
        map_put_ref_id,
        map_put_int_id,
        map_put_float_id,
        map_put_atom_id,
        map_put_atom_key_int_id,
        map_put_atom_key_float_id,
        map_put_atom_key_atom_id,
        map_put_int_key_int_id,
        map_put_int_key_float_id,
        map_put_int_key_atom_id,
        map_put_float_key_int_id,
        map_put_float_key_float_id,
        map_put_float_key_atom_id,
        map_get_ref_id,
        map_get_atom_key_ref_id,
        map_get_int_key_ref_id,
        map_get_float_key_ref_id,
        ref_load_int_id,
        ref_load_float_id,
        ref_load_atom_id,
        type_of_id,
        unbox_int_id,
        unbox_float_id,
        unbox_atom_id,
        struct_schema_id_ref_id,
        truthy_ref_id,
        box_int_for_any_id,
        box_float_for_any_id,
        box_atom_for_any_id,
        map_is_map_id,
        promote_f64_id,
        dynamic_float_arith_unsupported_id,
        value_eq_ref_id,
        matcher_eq_bytes_id,
        matcher_map_get_id,
        matcher_map_get_ref_id,
        alloc_closure_id,
        closure_code_ref_id,
        closure_halt_kind_ref_id,
        closure_get_capture_ref_id,
        closure_get_capture_i64_id,
        closure_get_capture_f64_id,
        closure_set_capture_ref_id,
        closure_set_capture_i64_id,
        closure_set_capture_f64_id,
        receive_park_id,
        receive_park_matched_id,
        get_static_closure_id,
        get_halt_cont_id,
        spawn_entry_id,
        main_entry_id,
        drain_dtor_entry_id,
        yield_mid_flight_id,
        should_yield_data_id,
    })
}

#[derive(Clone, Copy)]
pub(crate) struct RuntimeRefs {
    pub(super) halt_implicit_ref_id: FuncId,
    pub(super) halt_implicit_i64_id: FuncId,
    pub(super) halt_implicit_f64_id: FuncId,
    pub(super) halt_cont_body_strict_id: FuncId,
    pub(super) halt_cont_body_i64_id: FuncId,
    pub(super) halt_cont_body_f64_id: FuncId,
    pub(super) alloc_id: FuncId,
    pub(super) list_cons_any_id: FuncId,
    pub(super) list_cons_int_id: FuncId,
    pub(super) list_cons_float_id: FuncId,
    pub(super) list_cons_atom_id: FuncId,
    pub(super) list_is_cons_id: FuncId,
    pub(super) list_head_fallback_id: FuncId,
    pub(super) list_head_int_ref_id: FuncId,
    pub(super) list_head_float_ref_id: FuncId,
    pub(super) list_tail_fallback_id: FuncId,
    pub(super) alloc_struct_id: FuncId,
    pub(super) struct_get_field_id: FuncId,
    pub(super) struct_set_field_ref_id: FuncId,
    pub(super) struct_set_field_int_id: FuncId,
    pub(super) struct_set_field_float_id: FuncId,
    pub(super) struct_set_field_atom_id: FuncId,
    pub(super) bs_begin_id: FuncId,
    pub(super) bs_write_ref_id: FuncId,
    pub(super) bs_finalize_id: FuncId,
    // fz-cty.8 — single-shot allocation from a module-baked byte payload.
    pub(super) alloc_bitstring_const_id: FuncId,
    // fz-q8d.2 — alloc a ProcBin referencing a static SharedBin in .data.
    pub(super) alloc_procbin_from_static_id: FuncId,
    // fz-q8d.2 — noop destructor address relocated into static SharedBins.
    pub(super) shared_bin_destructor_noop_id: FuncId,
    // fz-9ss — binary/cstring extern marshal helpers. Both have signature
    // `(i64 tagged_heap_bits) -> i64 *const u8` from Cranelift's perspective.
    pub(super) binary_as_ptr_id: FuncId,
    pub(super) binary_as_cstring_id: FuncId,
    pub(super) bs_reader_init_ref_id: FuncId,
    pub(super) bs_read_field_ref_id: FuncId,
    pub(super) bs_reader_done_ref_id: FuncId,
    pub(super) map_empty_id: FuncId,
    pub(super) map_builder_begin_id: FuncId,
    pub(super) map_builder_begin_update_id: FuncId,
    pub(super) map_builder_put_parts_id: FuncId,
    pub(super) map_builder_put_ref_id: FuncId,
    pub(super) map_builder_freeze_id: FuncId,
    pub(super) map_put_ref_id: FuncId,
    pub(super) map_put_int_id: FuncId,
    pub(super) map_put_float_id: FuncId,
    pub(super) map_put_atom_id: FuncId,
    pub(super) map_put_atom_key_int_id: FuncId,
    pub(super) map_put_atom_key_float_id: FuncId,
    pub(super) map_put_atom_key_atom_id: FuncId,
    pub(super) map_put_int_key_int_id: FuncId,
    pub(super) map_put_int_key_float_id: FuncId,
    pub(super) map_put_int_key_atom_id: FuncId,
    pub(super) map_put_float_key_int_id: FuncId,
    pub(super) map_put_float_key_float_id: FuncId,
    pub(super) map_put_float_key_atom_id: FuncId,
    pub(super) map_get_ref_id: FuncId,
    pub(super) map_get_atom_key_ref_id: FuncId,
    pub(super) map_get_int_key_ref_id: FuncId,
    pub(super) map_get_float_key_ref_id: FuncId,
    pub(super) ref_load_int_id: FuncId,
    pub(super) ref_load_float_id: FuncId,
    pub(super) ref_load_atom_id: FuncId,
    pub(super) type_of_id: FuncId,
    pub(super) unbox_int_id: FuncId,
    pub(super) unbox_float_id: FuncId,
    pub(super) unbox_atom_id: FuncId,
    pub(super) struct_schema_id_ref_id: FuncId,
    pub(super) truthy_ref_id: FuncId,
    pub(super) box_int_for_any_id: FuncId,
    pub(super) box_float_for_any_id: FuncId,
    pub(super) box_atom_for_any_id: FuncId,
    pub(super) map_is_map_id: FuncId,
    pub(super) promote_f64_id: FuncId,
    pub(super) dynamic_float_arith_unsupported_id: FuncId,
    pub(super) value_eq_ref_id: FuncId,
    // fz-puj.45 (X4) — selective-receive matcher binary-literal helper.
    pub matcher_eq_bytes_id: FuncId,
    // fz-puj.47 (X6) — selective-receive matcher map-key lookup helper.
    pub matcher_map_get_id: FuncId,
    pub matcher_map_get_ref_id: FuncId,
    pub(super) alloc_closure_id: FuncId,
    pub(super) closure_code_ref_id: FuncId,
    pub(super) closure_halt_kind_ref_id: FuncId,
    pub(super) closure_get_capture_ref_id: FuncId,
    pub(super) closure_get_capture_i64_id: FuncId,
    pub(super) closure_get_capture_f64_id: FuncId,
    pub(super) closure_set_capture_ref_id: FuncId,
    pub(super) closure_set_capture_i64_id: FuncId,
    pub(super) closure_set_capture_f64_id: FuncId,
    pub(super) receive_park_id: FuncId,
    /// fz-70q.3 — fz_receive_park_matched FFI entry. Called from the
    /// Term::ReceiveMatched arm in compile_block_terminator.
    pub(super) receive_park_matched_id: FuncId,
    pub(super) get_static_closure_id: FuncId,
    pub(super) get_halt_cont_id: FuncId,
    pub(super) spawn_entry_id: FuncId,
    pub(super) main_entry_id: FuncId,
    /// fz-4mk.3a — fz_drain_dtor_entry: SystemV→Tail-CC shim for invoking
    /// a resource dtor closure with its payload. Sig: `(closure:i64,
    /// payload_ref:i64) -> i64 system_v`. Reads body addr through the
    /// closure ABI and indirect-calls (closure, payload, halt_cl) via Tail-CC; result
    /// discarded. Scheduler drains `pending_dtors` through this shim at
    /// task-exit, replacing the older `resolve_dtor_from_closure` C
    /// extraction path.
    pub(super) drain_dtor_entry_id: FuncId,
    pub(super) yield_mid_flight_id: FuncId,
    pub(super) should_yield_data_id: DataId,
}
