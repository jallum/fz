//! Runtime FFI symbol declarations shared by JIT and AOT backends.
//!
//! Sole owner of each runtime fn's wire ABI; changing one signature
//! requires updating the FFI body in ir_runtime.rs AND the matching
//! entry here.

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

/// Declare a SystemV runtime FFI fn as an Import in `jmod`.
fn decl_import<M: cranelift_module::Module>(
    jmod: &mut M,
    name: &str,
    params: &[ir::Type],
    rets: &[ir::Type],
) -> Result<FuncId, CodegenError> {
    let sig = sig1(params, rets);
    jmod.declare_function(name, Linkage::Import, &sig)
        .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))
}

/// Declare every fz runtime FFI fn as an Import in the given Cranelift
/// Module and return the resulting FuncIds packed into a RuntimeRefs.
///
/// Generic on `M: cranelift_module::Module` so JIT and AOT share one
/// declaration site — the declarations don't care whether the underlying
/// symbol resolves via JIT-installed Rust fn pointers or via a linker.
pub(crate) fn declare_runtime_symbols<M: cranelift_module::Module>(
    jmod: &mut M,
) -> Result<RuntimeRefs, CodegenError> {
    // FZ_SHOULD_YIELD is a 1-byte external data object.
    let should_yield_data_id = jmod
        .declare_data("FZ_SHOULD_YIELD", Linkage::Import, false, false)
        .map_err(|e| CodegenError::new(format!("declare FZ_SHOULD_YIELD: {}", e)))?;

    let halt = declare_halt_runtime(jmod)?;
    let list = declare_list_runtime(jmod)?;
    let strct = declare_struct_runtime(jmod)?;
    let bs = declare_bitstring_runtime(jmod)?;
    let map = declare_map_runtime(jmod)?;
    let val = declare_value_runtime(jmod)?;
    let arith = declare_arith_runtime(jmod)?;
    let matcher = declare_matcher_runtime(jmod)?;
    let closure = declare_closure_runtime(jmod)?;
    let receive = declare_receive_runtime(jmod)?;
    let halt_cont = declare_halt_cont_runtime(jmod)?;
    let scheduler = declare_scheduler_runtime(jmod)?;
    let alloc_id = decl_import(jmod, "fz_alloc_frame", &[types::I32, types::I32], &[types::I64])?;

    Ok(RuntimeRefs {
        halt_implicit_ref_id: halt.halt_implicit_ref_id,
        halt_implicit_i64_id: halt.halt_implicit_i64_id,
        halt_implicit_f64_id: halt.halt_implicit_f64_id,
        halt_cont_body_strict_id: halt_cont.halt_cont_body_strict_id,
        halt_cont_body_i64_id: halt_cont.halt_cont_body_i64_id,
        halt_cont_body_f64_id: halt_cont.halt_cont_body_f64_id,
        alloc_id,
        list_cons_any_id: list.list_cons_any_id,
        list_cons_int_id: list.list_cons_int_id,
        list_cons_float_id: list.list_cons_float_id,
        list_cons_atom_id: list.list_cons_atom_id,
        list_is_cons_id: list.list_is_cons_id,
        list_head_fallback_id: list.list_head_fallback_id,
        list_head_int_ref_id: list.list_head_int_ref_id,
        list_head_float_ref_id: list.list_head_float_ref_id,
        list_tail_fallback_id: list.list_tail_fallback_id,
        alloc_struct_id: strct.alloc_struct_id,
        struct_get_field_id: strct.struct_get_field_id,
        struct_set_field_ref_id: strct.struct_set_field_ref_id,
        struct_set_field_int_id: strct.struct_set_field_int_id,
        struct_set_field_float_id: strct.struct_set_field_float_id,
        struct_set_field_atom_id: strct.struct_set_field_atom_id,
        bs_begin_id: bs.bs_begin_id,
        bs_write_ref_id: bs.bs_write_ref_id,
        bs_finalize_id: bs.bs_finalize_id,
        alloc_bitstring_const_id: bs.alloc_bitstring_const_id,
        alloc_procbin_from_static_id: bs.alloc_procbin_from_static_id,
        shared_bin_destructor_noop_id: bs.shared_bin_destructor_noop_id,
        binary_as_ptr_id: bs.binary_as_ptr_id,
        binary_as_cstring_id: bs.binary_as_cstring_id,
        bs_reader_init_ref_id: bs.bs_reader_init_ref_id,
        bs_read_field_ref_id: bs.bs_read_field_ref_id,
        bs_reader_done_ref_id: bs.bs_reader_done_ref_id,
        map_empty_id: map.map_empty_id,
        map_dest_begin_id: map.map_dest_begin_id,
        map_dest_begin_update_id: map.map_dest_begin_update_id,
        map_dest_put_parts_id: map.map_dest_put_parts_id,
        map_dest_put_ref_id: map.map_dest_put_ref_id,
        map_dest_freeze_id: map.map_dest_freeze_id,
        map_put_ref_id: map.map_put_ref_id,
        map_put_int_id: map.map_put_int_id,
        map_put_float_id: map.map_put_float_id,
        map_put_atom_id: map.map_put_atom_id,
        map_put_atom_key_int_id: map.map_put_atom_key_int_id,
        map_put_atom_key_float_id: map.map_put_atom_key_float_id,
        map_put_atom_key_atom_id: map.map_put_atom_key_atom_id,
        map_put_int_key_int_id: map.map_put_int_key_int_id,
        map_put_int_key_float_id: map.map_put_int_key_float_id,
        map_put_int_key_atom_id: map.map_put_int_key_atom_id,
        map_put_float_key_int_id: map.map_put_float_key_int_id,
        map_put_float_key_float_id: map.map_put_float_key_float_id,
        map_put_float_key_atom_id: map.map_put_float_key_atom_id,
        map_get_ref_id: map.map_get_ref_id,
        map_get_atom_key_ref_id: map.map_get_atom_key_ref_id,
        map_get_int_key_ref_id: map.map_get_int_key_ref_id,
        map_get_float_key_ref_id: map.map_get_float_key_ref_id,
        ref_load_int_id: val.ref_load_int_id,
        ref_load_float_id: val.ref_load_float_id,
        ref_load_atom_id: val.ref_load_atom_id,
        type_of_id: val.type_of_id,
        unbox_int_id: val.unbox_int_id,
        unbox_float_id: val.unbox_float_id,
        unbox_atom_id: val.unbox_atom_id,
        struct_schema_id_ref_id: val.struct_schema_id_ref_id,
        truthy_ref_id: val.truthy_ref_id,
        box_int_for_any_id: val.box_int_for_any_id,
        box_float_for_any_id: val.box_float_for_any_id,
        box_atom_for_any_id: val.box_atom_for_any_id,
        map_is_map_id: val.map_is_map_id,
        promote_f64_id: arith.promote_f64_id,
        dynamic_float_arith_unsupported_id: arith.dynamic_float_arith_unsupported_id,
        value_eq_ref_id: arith.value_eq_ref_id,
        matcher_eq_bytes_id: matcher.matcher_eq_bytes_id,
        matcher_map_get_id: matcher.matcher_map_get_id,
        matcher_map_get_ref_id: matcher.matcher_map_get_ref_id,
        alloc_closure_id: closure.alloc_closure_id,
        closure_code_ref_id: closure.closure_code_ref_id,
        closure_halt_kind_ref_id: closure.closure_halt_kind_ref_id,
        materialize_cont_id: closure.materialize_cont_id,
        closure_get_capture_ref_id: closure.closure_get_capture_ref_id,
        closure_get_capture_i64_id: closure.closure_get_capture_i64_id,
        closure_get_capture_f64_id: closure.closure_get_capture_f64_id,
        closure_set_capture_ref_id: closure.closure_set_capture_ref_id,
        closure_set_capture_i64_id: closure.closure_set_capture_i64_id,
        closure_set_capture_f64_id: closure.closure_set_capture_f64_id,
        receive_park_id: receive.receive_park_id,
        receive_park_matched_id: receive.receive_park_matched_id,
        get_static_closure_id: closure.get_static_closure_id,
        get_halt_cont_id: halt_cont.get_halt_cont_id,
        spawn_entry_id: scheduler.spawn_entry_id,
        main_entry_id: scheduler.main_entry_id,
        drain_dtor_entry_id: scheduler.drain_dtor_entry_id,
        yield_mid_flight_id: scheduler.yield_mid_flight_id,
        should_yield_data_id,
    })
}

struct HaltRefs {
    halt_implicit_ref_id: FuncId,
    halt_implicit_i64_id: FuncId,
    halt_implicit_f64_id: FuncId,
}

/// Implicit-halt FFI entries (one per return repr).
fn declare_halt_runtime<M: cranelift_module::Module>(
    jmod: &mut M,
) -> Result<HaltRefs, CodegenError> {
    Ok(HaltRefs {
        halt_implicit_ref_id: decl_import(jmod, "fz_halt_implicit_ref", &[types::I64], &[])?,
        halt_implicit_i64_id: decl_import(jmod, "fz_halt_implicit_i64", &[types::I64], &[])?,
        halt_implicit_f64_id: decl_import(jmod, "fz_halt_implicit_f64", &[types::F64], &[])?,
    })
}

struct ListRefs {
    list_cons_any_id: FuncId,
    list_cons_int_id: FuncId,
    list_cons_float_id: FuncId,
    list_cons_atom_id: FuncId,
    list_is_cons_id: FuncId,
    list_head_fallback_id: FuncId,
    list_head_int_ref_id: FuncId,
    list_head_float_ref_id: FuncId,
    list_tail_fallback_id: FuncId,
}

/// Cons-cell list FFI entries.
fn declare_list_runtime<M: cranelift_module::Module>(
    jmod: &mut M,
) -> Result<ListRefs, CodegenError> {
    Ok(ListRefs {
        list_cons_any_id: decl_import(
            jmod,
            "fz_list_cons_any",
            &[types::I64, types::I64],
            &[types::I64],
        )?,
        list_cons_int_id: decl_import(
            jmod,
            "fz_list_cons_int",
            &[types::I64, types::I64],
            &[types::I64],
        )?,
        list_cons_float_id: decl_import(
            jmod,
            "fz_list_cons_float",
            &[types::F64, types::I64],
            &[types::I64],
        )?,
        list_cons_atom_id: decl_import(
            jmod,
            "fz_list_cons_atom",
            &[types::I64, types::I64],
            &[types::I64],
        )?,
        list_is_cons_id: decl_import(jmod, "fz_list_is_cons", &[types::I64], &[types::I8])?,
        list_head_fallback_id: decl_import(jmod, "fz_list_head_ref", &[types::I64], &[types::I64])?,
        list_head_int_ref_id: decl_import(
            jmod,
            "fz_list_head_int_ref",
            &[types::I64],
            &[types::I64],
        )?,
        list_head_float_ref_id: decl_import(
            jmod,
            "fz_list_head_float_ref",
            &[types::I64],
            &[types::F64],
        )?,
        list_tail_fallback_id: decl_import(jmod, "fz_list_tail_ref", &[types::I64], &[types::I64])?,
    })
}

struct StructRefs {
    alloc_struct_id: FuncId,
    struct_get_field_id: FuncId,
    struct_set_field_ref_id: FuncId,
    struct_set_field_int_id: FuncId,
    struct_set_field_float_id: FuncId,
    struct_set_field_atom_id: FuncId,
}

/// Struct allocation and field accessor FFI entries.
fn declare_struct_runtime<M: cranelift_module::Module>(
    jmod: &mut M,
) -> Result<StructRefs, CodegenError> {
    Ok(StructRefs {
        alloc_struct_id: decl_import(jmod, "fz_alloc_struct", &[types::I32], &[types::I64])?,
        struct_get_field_id: decl_import(
            jmod,
            "fz_struct_get_field_ref",
            &[types::I64, types::I32],
            &[types::I64],
        )?,
        struct_set_field_ref_id: decl_import(
            jmod,
            "fz_struct_set_field_ref",
            &[types::I64, types::I32, types::I64],
            &[],
        )?,
        struct_set_field_int_id: decl_import(
            jmod,
            "fz_struct_set_field_int",
            &[types::I64, types::I32, types::I64],
            &[],
        )?,
        struct_set_field_float_id: decl_import(
            jmod,
            "fz_struct_set_field_float",
            &[types::I64, types::I32, types::F64],
            &[],
        )?,
        struct_set_field_atom_id: decl_import(
            jmod,
            "fz_struct_set_field_atom",
            &[types::I64, types::I32, types::I64],
            &[],
        )?,
    })
}

struct BitstringRefs {
    bs_begin_id: FuncId,
    bs_write_ref_id: FuncId,
    bs_finalize_id: FuncId,
    alloc_bitstring_const_id: FuncId,
    alloc_procbin_from_static_id: FuncId,
    shared_bin_destructor_noop_id: FuncId,
    binary_as_ptr_id: FuncId,
    binary_as_cstring_id: FuncId,
    bs_reader_init_ref_id: FuncId,
    bs_read_field_ref_id: FuncId,
    bs_reader_done_ref_id: FuncId,
}

/// Bitstring/binary builder + reader FFI entries.
fn declare_bitstring_runtime<M: cranelift_module::Module>(
    jmod: &mut M,
) -> Result<BitstringRefs, CodegenError> {
    let bs_begin_id = decl_import(jmod, "fz_bs_begin", &[], &[])?;
    let bs_write_ref_id = decl_import(
        jmod,
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
    let bs_finalize_id = decl_import(jmod, "fz_bs_finalize", &[], &[types::I64])?;
    let alloc_bitstring_const_id = decl_import(
        jmod,
        "fz_alloc_bitstring_const",
        &[types::I64, types::I64, types::I64],
        &[types::I64],
    )?;
    // Retains the anchor on a static SharedBin and allocates a ProcBin on
    // the current process heap that owns the new refcount edge.
    let alloc_procbin_from_static_id = decl_import(
        jmod,
        "fz_alloc_procbin_from_static",
        &[types::I64],
        &[types::I64],
    )?;
    // Noop destructor symbol. Imported so its address can be baked into
    // each static SharedBin's `destructor` slot via a function-address
    // relocation. Matches the runtime's `extern "C" fn (*mut SharedBin)`
    // signature exactly.
    let shared_bin_destructor_noop_id =
        decl_import(jmod, "shared_bin_destructor_noop", &[types::I64], &[])?;
    let binary_as_ptr_id = decl_import(jmod, "fz_binary_as_ptr", &[types::I64], &[types::I64])?;
    let binary_as_cstring_id =
        decl_import(jmod, "fz_binary_as_cstring", &[types::I64], &[types::I64])?;
    let bs_reader_init_ref_id =
        decl_import(jmod, "fz_bs_reader_init_ref", &[types::I64], &[types::I64])?;
    let bs_read_field_ref_id = decl_import(
        jmod,
        "fz_bs_read_field_ref",
        &[
            types::I64, // reader ref
            types::I64, // packed field spec
            types::I32, // size_value
        ],
        &[types::I64],
    )?;
    let bs_reader_done_ref_id =
        decl_import(jmod, "fz_bs_reader_done_ref", &[types::I64], &[types::I8])?;
    Ok(BitstringRefs {
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
    })
}

struct MapRefs {
    map_empty_id: FuncId,
    map_dest_begin_id: FuncId,
    map_dest_begin_update_id: FuncId,
    map_dest_put_parts_id: FuncId,
    map_dest_put_ref_id: FuncId,
    map_dest_freeze_id: FuncId,
    map_put_ref_id: FuncId,
    map_put_int_id: FuncId,
    map_put_float_id: FuncId,
    map_put_atom_id: FuncId,
    map_put_atom_key_int_id: FuncId,
    map_put_atom_key_float_id: FuncId,
    map_put_atom_key_atom_id: FuncId,
    map_put_int_key_int_id: FuncId,
    map_put_int_key_float_id: FuncId,
    map_put_int_key_atom_id: FuncId,
    map_put_float_key_int_id: FuncId,
    map_put_float_key_float_id: FuncId,
    map_put_float_key_atom_id: FuncId,
    map_get_ref_id: FuncId,
    map_get_atom_key_ref_id: FuncId,
    map_get_int_key_ref_id: FuncId,
    map_get_float_key_ref_id: FuncId,
}

/// Map construction, mutation and lookup FFI entries.
fn declare_map_runtime<M: cranelift_module::Module>(
    jmod: &mut M,
) -> Result<MapRefs, CodegenError> {
    Ok(MapRefs {
        map_empty_id: decl_import(jmod, "fz_map_empty", &[], &[types::I64])?,
        map_dest_begin_id: decl_import(
            jmod,
            "fz_map_dest_begin",
            &[types::I32],
            &[types::I64],
        )?,
        map_dest_begin_update_id: decl_import(
            jmod,
            "fz_map_dest_begin_update",
            &[types::I64, types::I32],
            &[types::I64],
        )?,
        map_dest_put_parts_id: decl_import(
            jmod,
            "fz_map_dest_put_parts",
            &[types::I64, types::I64, types::I64, types::I64, types::I64],
            &[],
        )?,
        map_dest_put_ref_id: decl_import(
            jmod,
            "fz_map_dest_put_ref",
            &[types::I64, types::I64, types::I64],
            &[],
        )?,
        map_dest_freeze_id: decl_import(jmod, "fz_map_dest_freeze", &[types::I64], &[types::I64])?,
        map_put_ref_id: decl_import(
            jmod,
            "fz_map_put_ref",
            &[types::I64, types::I64, types::I64],
            &[types::I64],
        )?,
        map_put_int_id: decl_import(
            jmod,
            "fz_map_put_int",
            &[types::I64, types::I64, types::I64],
            &[types::I64],
        )?,
        map_put_float_id: decl_import(
            jmod,
            "fz_map_put_float",
            &[types::I64, types::I64, types::F64],
            &[types::I64],
        )?,
        map_put_atom_id: decl_import(
            jmod,
            "fz_map_put_atom",
            &[types::I64, types::I64, types::I64],
            &[types::I64],
        )?,
        map_put_atom_key_int_id: decl_import(
            jmod,
            "fz_map_put_atom_key_int",
            &[types::I64, types::I64, types::I64],
            &[types::I64],
        )?,
        map_put_atom_key_float_id: decl_import(
            jmod,
            "fz_map_put_atom_key_float",
            &[types::I64, types::I64, types::F64],
            &[types::I64],
        )?,
        map_put_atom_key_atom_id: decl_import(
            jmod,
            "fz_map_put_atom_key_atom",
            &[types::I64, types::I64, types::I64],
            &[types::I64],
        )?,
        map_put_int_key_int_id: decl_import(
            jmod,
            "fz_map_put_int_key_int",
            &[types::I64, types::I64, types::I64],
            &[types::I64],
        )?,
        map_put_int_key_float_id: decl_import(
            jmod,
            "fz_map_put_int_key_float",
            &[types::I64, types::I64, types::F64],
            &[types::I64],
        )?,
        map_put_int_key_atom_id: decl_import(
            jmod,
            "fz_map_put_int_key_atom",
            &[types::I64, types::I64, types::I64],
            &[types::I64],
        )?,
        map_put_float_key_int_id: decl_import(
            jmod,
            "fz_map_put_float_key_int",
            &[types::I64, types::F64, types::I64],
            &[types::I64],
        )?,
        map_put_float_key_float_id: decl_import(
            jmod,
            "fz_map_put_float_key_float",
            &[types::I64, types::F64, types::F64],
            &[types::I64],
        )?,
        map_put_float_key_atom_id: decl_import(
            jmod,
            "fz_map_put_float_key_atom",
            &[types::I64, types::F64, types::I64],
            &[types::I64],
        )?,
        map_get_ref_id: decl_import(
            jmod,
            "fz_map_get_ref",
            &[types::I64, types::I64],
            &[types::I64],
        )?,
        map_get_atom_key_ref_id: decl_import(
            jmod,
            "fz_map_get_atom_key_ref",
            &[types::I64, types::I64],
            &[types::I64],
        )?,
        map_get_int_key_ref_id: decl_import(
            jmod,
            "fz_map_get_int_key_ref",
            &[types::I64, types::I64],
            &[types::I64],
        )?,
        map_get_float_key_ref_id: decl_import(
            jmod,
            "fz_map_get_float_key_ref",
            &[types::I64, types::F64],
            &[types::I64],
        )?,
    })
}

struct ValueRefs {
    ref_load_int_id: FuncId,
    ref_load_float_id: FuncId,
    ref_load_atom_id: FuncId,
    type_of_id: FuncId,
    unbox_int_id: FuncId,
    unbox_float_id: FuncId,
    unbox_atom_id: FuncId,
    struct_schema_id_ref_id: FuncId,
    truthy_ref_id: FuncId,
    box_int_for_any_id: FuncId,
    box_float_for_any_id: FuncId,
    box_atom_for_any_id: FuncId,
    map_is_map_id: FuncId,
}

/// Tagged-value introspection: ref-load, type-of, unbox, box-for-Any, truthy.
fn declare_value_runtime<M: cranelift_module::Module>(
    jmod: &mut M,
) -> Result<ValueRefs, CodegenError> {
    Ok(ValueRefs {
        ref_load_int_id: decl_import(jmod, "fz_ref_load_int", &[types::I64], &[types::I64])?,
        ref_load_float_id: decl_import(jmod, "fz_ref_load_float", &[types::I64], &[types::F64])?,
        ref_load_atom_id: decl_import(jmod, "fz_ref_load_atom", &[types::I64], &[types::I64])?,
        type_of_id: decl_import(jmod, "fz_type_of", &[types::I64], &[types::I8])?,
        unbox_int_id: decl_import(jmod, "fz_unbox_int", &[types::I64], &[types::I64])?,
        unbox_float_id: decl_import(jmod, "fz_unbox_float", &[types::I64], &[types::F64])?,
        unbox_atom_id: decl_import(jmod, "fz_unbox_atom", &[types::I64], &[types::I64])?,
        struct_schema_id_ref_id: decl_import(
            jmod,
            "fz_struct_schema_id_ref",
            &[types::I64],
            &[types::I32],
        )?,
        truthy_ref_id: decl_import(jmod, "fz_truthy_ref", &[types::I64], &[types::I8])?,
        box_int_for_any_id: decl_import(jmod, "fz_box_int_for_any", &[types::I64], &[types::I64])?,
        box_float_for_any_id: decl_import(
            jmod,
            "fz_box_float_for_any",
            &[types::F64],
            &[types::I64],
        )?,
        box_atom_for_any_id: decl_import(
            jmod,
            "fz_box_atom_for_any",
            &[types::I64],
            &[types::I64],
        )?,
        map_is_map_id: decl_import(jmod, "fz_map_is_map", &[types::I64], &[types::I8])?,
    })
}

struct ArithRefs {
    promote_f64_id: FuncId,
    dynamic_float_arith_unsupported_id: FuncId,
    value_eq_ref_id: FuncId,
}

/// Mixed-type arithmetic and value-equality slow-path helpers. Mixed-type
/// arith/cmp slow paths are inlined in JIT. `fz_promote_f64` does the
/// tag-aware Int|Float -> f64 conversion (panics on non-numeric).
fn declare_arith_runtime<M: cranelift_module::Module>(
    jmod: &mut M,
) -> Result<ArithRefs, CodegenError> {
    let arith_ret: &[ir::Type] = &[types::I64];
    Ok(ArithRefs {
        promote_f64_id: decl_import(jmod, "fz_promote_f64", &[types::I64], &[types::F64])?,
        dynamic_float_arith_unsupported_id: decl_import(
            jmod,
            "fz_dynamic_float_arith_unsupported",
            &[],
            &[types::I64],
        )?,
        value_eq_ref_id: decl_import(
            jmod,
            "fz_value_eq_ref",
            &[types::I64, types::I64],
            arith_ret,
        )?,
    })
}

struct MatcherRefs {
    matcher_eq_bytes_id: FuncId,
    matcher_map_get_id: FuncId,
    matcher_map_get_ref_id: FuncId,
}

/// Selective-receive matcher helpers (binary-literal compare + map-key lookup).
fn declare_matcher_runtime<M: cranelift_module::Module>(
    jmod: &mut M,
) -> Result<MatcherRefs, CodegenError> {
    // Receive matcher binary-literal comparison.
    let matcher_eq_bytes_id = decl_import(
        jmod,
        "fz_matcher_eq_bytes",
        &[types::I64, types::I64, types::I64],
        &[types::I32],
    )?;
    // Receive matcher map-key lookup. Returns matcher miss sentinel on miss.
    let matcher_map_get_id = decl_import(
        jmod,
        "fz_matcher_map_get",
        &[types::I64, types::I64],
        &[types::I64],
    )?;
    let matcher_map_get_ref_id = decl_import(
        jmod,
        "fz_matcher_map_get_ref",
        &[types::I64, types::I64],
        &[types::I64],
    )?;
    Ok(MatcherRefs {
        matcher_eq_bytes_id,
        matcher_map_get_id,
        matcher_map_get_ref_id,
    })
}

struct ClosureRefs {
    alloc_closure_id: FuncId,
    closure_code_ref_id: FuncId,
    closure_halt_kind_ref_id: FuncId,
    materialize_cont_id: FuncId,
    closure_get_capture_ref_id: FuncId,
    closure_get_capture_i64_id: FuncId,
    closure_get_capture_f64_id: FuncId,
    closure_set_capture_ref_id: FuncId,
    closure_set_capture_i64_id: FuncId,
    closure_set_capture_f64_id: FuncId,
    get_static_closure_id: FuncId,
}

/// Closure allocation, capture access, and static-singleton lookup.
fn declare_closure_runtime<M: cranelift_module::Module>(
    jmod: &mut M,
) -> Result<ClosureRefs, CodegenError> {
    let alloc_closure_id = decl_import(
        jmod,
        "fz_alloc_closure",
        &[types::I32, types::I32, types::I32, types::I64],
        &[types::I64],
    )?;
    let closure_code_ref_id =
        decl_import(jmod, "fz_closure_code_ref", &[types::I64], &[types::I64])?;
    let closure_halt_kind_ref_id = decl_import(
        jmod,
        "fz_closure_halt_kind_ref",
        &[types::I64],
        &[types::I32],
    )?;
    let materialize_cont_id =
        decl_import(jmod, "fz_materialize_cont", &[types::I64], &[types::I64])?;
    let closure_get_capture_ref_id = decl_import(
        jmod,
        "fz_closure_get_capture_ref",
        &[types::I64, types::I64],
        &[types::I64],
    )?;
    let closure_get_capture_i64_id = decl_import(
        jmod,
        "fz_closure_get_capture_i64",
        &[types::I64, types::I64],
        &[types::I64],
    )?;
    let closure_get_capture_f64_id = decl_import(
        jmod,
        "fz_closure_get_capture_f64",
        &[types::I64, types::I64],
        &[types::F64],
    )?;
    let closure_set_capture_ref_id = decl_import(
        jmod,
        "fz_closure_set_capture_ref",
        &[types::I64, types::I64, types::I64],
        &[],
    )?;
    let closure_set_capture_i64_id = decl_import(
        jmod,
        "fz_closure_set_capture_i64",
        &[types::I64, types::I64, types::I64],
        &[],
    )?;
    let closure_set_capture_f64_id = decl_import(
        jmod,
        "fz_closure_set_capture_f64",
        &[types::I64, types::I64, types::F64],
        &[],
    )?;
    // Static zero-capture closure singleton lookup. Returns the per-Process
    // singleton pointer for the given cl_sid.
    let get_static_closure_id =
        decl_import(jmod, "fz_get_static_closure", &[types::I32], &[types::I64])?;
    Ok(ClosureRefs {
        alloc_closure_id,
        closure_code_ref_id,
        closure_halt_kind_ref_id,
        materialize_cont_id,
        closure_get_capture_ref_id,
        closure_get_capture_i64_id,
        closure_get_capture_f64_id,
        closure_set_capture_ref_id,
        closure_set_capture_i64_id,
        closure_set_capture_f64_id,
        get_static_closure_id,
    })
}

struct ReceiveRefs {
    receive_park_id: FuncId,
    receive_park_matched_id: FuncId,
}

/// Selective-receive park FFI entries (accept-any and matched variants).
fn declare_receive_runtime<M: cranelift_module::Module>(
    jmod: &mut M,
) -> Result<ReceiveRefs, CodegenError> {
    // Receive: parks an accept-any matcher record on the cont closure;
    // returns YIELD sentinel.
    let receive_park_id = decl_import(jmod, "fz_receive_park", &[types::I64], &[types::I64])?;
    // Selective-receive park entry. Args:
    //   matcher_fn_bits (i64), pinned_ptr (i64), n_pinned (i64),
    //   clause_bodies_ptr (i64), n_clauses (i64),
    //   clause_bound_counts_ptr (i64), bound_arity (i32),
    //   after_deadline_or_neg1 (i64), after_cont_bits (i64).
    // Returns YIELD sentinel (i64).
    let receive_park_matched_id = decl_import(
        jmod,
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
    Ok(ReceiveRefs {
        receive_park_id,
        receive_park_matched_id,
    })
}

struct HaltContRefs {
    get_halt_cont_id: FuncId,
    halt_cont_body_strict_id: FuncId,
    halt_cont_body_i64_id: FuncId,
    halt_cont_body_f64_id: FuncId,
}

/// Halt-cont singleton lookup plus the three LOCAL Tail-CC body declarations.
fn declare_halt_cont_runtime<M: cranelift_module::Module>(
    jmod: &mut M,
) -> Result<HaltContRefs, CodegenError> {
    // Halt-cont singleton lookup. `(addr, kind)`: kind selects among 3
    // Process singletons (0=ValueRef, 1=RawInt, 2=RawF64). Lazily
    // initialized using the supplied halt_cont_body addr (JIT pre-populates
    // at make_process time; AOT relies on lazy init at first call).
    let get_halt_cont_id = decl_import(
        jmod,
        "fz_get_halt_cont",
        &[types::I64, types::I32],
        &[types::I64],
    )?;
    // Three fz_halt_cont_body variants, declared LOCAL (bodies emitted
    // elsewhere). Strict: `(raw i64, kind i8, self i64) -> i64 tail`;
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
    Ok(HaltContRefs {
        get_halt_cont_id,
        halt_cont_body_strict_id,
        halt_cont_body_i64_id,
        halt_cont_body_f64_id,
    })
}

struct SchedulerRefs {
    spawn_entry_id: FuncId,
    main_entry_id: FuncId,
    drain_dtor_entry_id: FuncId,
    yield_mid_flight_id: FuncId,
}

/// Scheduler-facing LOCAL entry shims and the mid-flight yield helper.
fn declare_scheduler_runtime<M: cranelift_module::Module>(
    jmod: &mut M,
) -> Result<SchedulerRefs, CodegenError> {
    let yield_mid_flight_id =
        decl_import(jmod, "fz_yield_mid_flight", &[types::I64], &[types::I64])?;
    // fz_spawn_entry: SystemV entry the scheduler calls to launch a new
    // task's zero-arg closure. Sig: `(closure:i64) -> i64`.
    let mut se_sig = Signature::new(CallConv::SystemV);
    se_sig.params.push(AbiParam::new(types::I64));
    se_sig.returns.push(AbiParam::new(types::I64));
    let spawn_entry_id = jmod
        .declare_function("fz_spawn_entry", Linkage::Local, &se_sig)
        .map_err(|e| CodegenError::new(format!("declare fz_spawn_entry: {}", e)))?;
    // fz_main_entry: SystemV entry the scheduler calls to launch at a
    // known main fn. Sig: `(main_fp:i64, halt_cl:i64) -> i64`. Rust caller
    // picks halt_cl from process.halt_cont_singletons by the entry fn's
    // return_repr kind.
    let mut me_sig = Signature::new(CallConv::SystemV);
    me_sig.params.push(AbiParam::new(types::I64));
    me_sig.params.push(AbiParam::new(types::I64));
    me_sig.returns.push(AbiParam::new(types::I64));
    let main_entry_id = jmod
        .declare_function("fz_main_entry", Linkage::Local, &me_sig)
        .map_err(|e| CodegenError::new(format!("declare fz_main_entry: {}", e)))?;
    // fz_drain_dtor_entry: SystemV entry the scheduler calls per pending
    // dtor at task-exit. Sig: `(closure:i64, payload_ref:i64) -> i64`.
    // Body reads the closure body addr through the runtime ABI, allocates
    // a Strict halt-cont via fz_get_halt_cont, and Tail-CC indirect-calls
    // the closure body with `(self, payload, halt_cl)`.
    let mut dd_sig = Signature::new(CallConv::SystemV);
    dd_sig.params.push(AbiParam::new(types::I64));
    dd_sig.params.push(AbiParam::new(types::I64));
    dd_sig.returns.push(AbiParam::new(types::I64));
    let drain_dtor_entry_id = jmod
        .declare_function("fz_drain_dtor_entry", Linkage::Local, &dd_sig)
        .map_err(|e| CodegenError::new(format!("declare fz_drain_dtor_entry: {}", e)))?;
    Ok(SchedulerRefs {
        spawn_entry_id,
        main_entry_id,
        drain_dtor_entry_id,
        yield_mid_flight_id,
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
    /// Single-shot allocation from a module-baked byte payload.
    pub(super) alloc_bitstring_const_id: FuncId,
    /// Alloc a ProcBin referencing a static SharedBin in .data.
    pub(super) alloc_procbin_from_static_id: FuncId,
    /// Noop destructor address relocated into static SharedBins.
    pub(super) shared_bin_destructor_noop_id: FuncId,
    // Binary/cstring extern marshal helpers. Both have signature
    // `(i64 tagged_heap_bits) -> i64 *const u8` from Cranelift's perspective.
    pub(super) binary_as_ptr_id: FuncId,
    pub(super) binary_as_cstring_id: FuncId,
    pub(super) bs_reader_init_ref_id: FuncId,
    pub(super) bs_read_field_ref_id: FuncId,
    pub(super) bs_reader_done_ref_id: FuncId,
    pub(super) map_empty_id: FuncId,
    pub(super) map_dest_begin_id: FuncId,
    pub(super) map_dest_begin_update_id: FuncId,
    pub(super) map_dest_put_parts_id: FuncId,
    pub(super) map_dest_put_ref_id: FuncId,
    pub(super) map_dest_freeze_id: FuncId,
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
    /// Selective-receive matcher binary-literal helper.
    pub matcher_eq_bytes_id: FuncId,
    /// Selective-receive matcher map-key lookup helper.
    pub matcher_map_get_id: FuncId,
    pub matcher_map_get_ref_id: FuncId,
    pub(super) alloc_closure_id: FuncId,
    pub(super) closure_code_ref_id: FuncId,
    pub(super) closure_halt_kind_ref_id: FuncId,
    pub(super) materialize_cont_id: FuncId,
    pub(super) closure_get_capture_ref_id: FuncId,
    pub(super) closure_get_capture_i64_id: FuncId,
    pub(super) closure_get_capture_f64_id: FuncId,
    pub(super) closure_set_capture_ref_id: FuncId,
    pub(super) closure_set_capture_i64_id: FuncId,
    pub(super) closure_set_capture_f64_id: FuncId,
    pub(super) receive_park_id: FuncId,
    /// fz_receive_park_matched FFI entry. Called from the
    /// Term::ReceiveMatched arm in compile_block_terminator.
    pub(super) receive_park_matched_id: FuncId,
    pub(super) get_static_closure_id: FuncId,
    pub(super) get_halt_cont_id: FuncId,
    pub(super) spawn_entry_id: FuncId,
    pub(super) main_entry_id: FuncId,
    /// fz_drain_dtor_entry: SystemV->Tail-CC shim for invoking a resource
    /// dtor closure with its payload. Sig: `(closure:i64, payload_ref:i64)
    /// -> i64`. Reads body addr through the closure ABI and indirect-calls
    /// (closure, payload, halt_cl) via Tail-CC; result discarded. Scheduler
    /// drains `pending_dtors` through this shim at task-exit.
    pub(super) drain_dtor_entry_id: FuncId,
    pub(super) yield_mid_flight_id: FuncId,
    pub(super) should_yield_data_id: DataId,
}
