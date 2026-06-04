#![allow(unused_imports)]

use super::*;
use crate::diag::Diagnostics;
use crate::fz_ir::{BinOp, Const, FnId, Module, Prim, Stmt, Term, UnOp, Var};
use crate::ir_planner::SpecPlan;
use crate::ir_planner::fn_types::{CallableCapability, SpecKey};
use crate::types::{ClosureLitInfo, ClosureTypes, Ty, Types, key_slots_from_tys};
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
use cranelift_object::{ObjectBuilder, ObjectModule};
use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema};
use fz_runtime::process::Node;
use fz_runtime::{extern_binary, extern_variadic, fz_panic, ir_runtime, procbin, resource};
use object::macho::PLATFORM_MACOS;
use object::write::MachOBuildVersion;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

/// Abstracts the JIT/AOT split. The codegen pipeline is shared; the trait
/// owns every legitimate point of variation — fn linkage, per-program
/// metadata emission, and the finalize step that materializes Output.
pub trait Backend {
    type Module: cranelift_module::Module;
    /// Whatever the backend hands the user after compilation finishes.
    /// JIT returns a `CompiledModule` (in-memory, runnable); AOT returns
    /// an `AotArtifact` (object bytes + linker metadata).
    type Output;

    fn module_mut(&mut self) -> &mut Self::Module;

    /// Linkage applied to user `fz_fn_<id>` declarations. JIT keeps them
    /// `Local` (only resolved in-process). AOT exports them so the linker
    /// can see them when assembling the final binary.
    fn fn_linkage(&self) -> Linkage;

    /// Emit per-program metadata carriers (dispatch fn, frame-size fn,
    /// atom-name blob, C `main` shim). The JIT impl is a no-op — the same
    /// data lives in `CompiledModule`'s Rust HashMaps and the runtime
    /// reads them directly. AOT emits Cranelift data + fns so the linker
    /// + `fz_aot_run_main` can resolve them at runtime.
    fn emit_metadata_carriers(
        &mut self,
        fbctx: &mut FunctionBuilderContext,
        meta: &CompiledMetadata,
    ) -> Result<(), CodegenError>;

    /// Finalize the backend into its Output. JIT finalizes the JITModule
    /// and resolves fn pointers. AOT emits the object-file bytes.
    fn finalize(self, meta: CompiledMetadata) -> Result<Self::Output, CodegenError>;
}

/// JIT backend: wraps a JITModule pre-finalize. compile() constructs one,
/// drives codegen through the Backend trait, then unpacks to call the
/// JIT-specific finalize_definitions / get_finalized_function pair.
pub struct JitBackend {
    jmod: JITModule,
}

impl JitBackend {
    pub(crate) fn new() -> Self {
        let isa = host_isa();
        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        // Bind every fz runtime FFI fn pointer. JIT-specific: the linker
        // is in-process and resolves symbols by name → Rust fn pointer.
        // AOT will skip this entire block (linker resolves against the
        // fz_runtime staticlib instead).
        register_runtime_symbols(&mut builder);
        Self {
            jmod: JITModule::new(builder),
        }
    }
}

/// Bind every fz runtime FFI fn pointer into the JIT linker. Split out
/// of `JitBackend::new` purely for readability — the list is long and
/// flat. Grouped by subsystem (debug print/panic, list, struct, bitstring,
/// map, closure, scheduler, receive, etc.).
pub(crate) fn register_runtime_symbols(builder: &mut JITBuilder) {
    builder.symbol("fz_dbg_value_ref", ir_runtime::fz_dbg_value_ref as *const u8);
    builder.symbol("fz_dbg_value", ir_runtime::fz_dbg_value as *const u8);
    builder.symbol(
        "fz_process_heap_alloc_stats",
        ir_runtime::fz_process_heap_alloc_stats as *const u8,
    );
    builder.symbol("fz_map_count", ir_runtime::fz_map_count as *const u8);
    builder.symbol("fz_map_entry_key", ir_runtime::fz_map_entry_key as *const u8);
    builder.symbol("fz_map_entry_value", ir_runtime::fz_map_entry_value as *const u8);
    builder.symbol("fz_panic", fz_panic as *const u8);
    builder.symbol(
        "fz_dynamic_float_arith_unsupported",
        ir_runtime::fz_dynamic_float_arith_unsupported as *const u8,
    );
    builder.symbol("fz_halt_implicit_ref", ir_runtime::fz_halt_implicit_ref as *const u8);
    builder.symbol("fz_halt_implicit_i64", ir_runtime::fz_halt_implicit_i64 as *const u8);
    builder.symbol("fz_halt_implicit_f64", ir_runtime::fz_halt_implicit_f64 as *const u8);
    builder.symbol("fz_halt_implicit_atom", ir_runtime::fz_halt_implicit_atom as *const u8);
    builder.symbol("fz_alloc_frame", ir_runtime::fz_alloc_frame as *const u8);
    builder.symbol("fz_list_cons_ref", ir_runtime::fz_list_cons_ref as *const u8);
    builder.symbol("fz_list_cons_any", ir_runtime::fz_list_cons_any as *const u8);
    builder.symbol("fz_list_cons_int", ir_runtime::fz_list_cons_int as *const u8);
    builder.symbol("fz_list_cons_float", ir_runtime::fz_list_cons_float as *const u8);
    builder.symbol("fz_list_cons_atom", ir_runtime::fz_list_cons_atom as *const u8);
    builder.symbol("fz_list_is_cons", ir_runtime::fz_list_is_cons as *const u8);
    builder.symbol("fz_list_head_ref", ir_runtime::fz_list_head_ref as *const u8);
    builder.symbol("fz_list_head_int_ref", ir_runtime::fz_list_head_int_ref as *const u8);
    builder.symbol(
        "fz_list_head_float_ref",
        ir_runtime::fz_list_head_float_ref as *const u8,
    );
    builder.symbol("fz_list_tail_ref", ir_runtime::fz_list_tail_ref as *const u8);
    builder.symbol(
        "fz_list_reuse_or_cons_tail_ref",
        ir_runtime::fz_list_reuse_or_cons_tail_ref as *const u8,
    );
    builder.symbol(
        "fz_mark_published_ref_aliased",
        ir_runtime::fz_mark_published_ref_aliased as *const u8,
    );
    builder.symbol("fz_alloc_struct", ir_runtime::fz_alloc_struct as *const u8);
    builder.symbol(
        "fz_struct_get_field_ref",
        ir_runtime::fz_struct_get_field_ref as *const u8,
    );
    builder.symbol(
        "fz_struct_get_named_field_ref",
        ir_runtime::fz_struct_get_named_field_ref as *const u8,
    );
    builder.symbol(
        "fz_struct_set_field_ref",
        ir_runtime::fz_struct_set_field_ref as *const u8,
    );
    builder.symbol(
        "fz_struct_set_field_int",
        ir_runtime::fz_struct_set_field_int as *const u8,
    );
    builder.symbol(
        "fz_struct_set_field_float",
        ir_runtime::fz_struct_set_field_float as *const u8,
    );
    builder.symbol(
        "fz_struct_set_field_atom",
        ir_runtime::fz_struct_set_field_atom as *const u8,
    );
    builder.symbol("fz_bs_begin", ir_runtime::fz_bs_begin as *const u8);
    builder.symbol("fz_bs_write_field_ref", ir_runtime::fz_bs_write_field_ref as *const u8);
    builder.symbol("fz_bs_finalize", ir_runtime::fz_bs_finalize as *const u8);
    builder.symbol(
        "fz_alloc_bitstring_const",
        ir_runtime::fz_alloc_bitstring_const as *const u8,
    );
    builder.symbol("fz_binary_concat", ir_runtime::fz_binary_concat as *const u8);
    builder.symbol("fz_bs_reader_init_ref", ir_runtime::fz_bs_reader_init_ref as *const u8);
    builder.symbol("fz_bs_read_field_ref", ir_runtime::fz_bs_read_field_ref as *const u8);
    builder.symbol("fz_bs_reader_done_ref", ir_runtime::fz_bs_reader_done_ref as *const u8);
    // Static SharedBin path: codegen emits a 40-byte data symbol in
    // `.data`, then calls this helper to wrap it in a per-process
    // ProcBin / MSO entry.
    builder.symbol(
        "fz_alloc_procbin_from_static",
        ir_runtime::fz_alloc_procbin_from_static as *const u8,
    );
    // Noop destructor address baked into each static SharedBin's
    // `destructor` field via a function-address relocation. Never
    // invoked in practice (anchor refcount stays >= 1) but must
    // resolve at link time.
    builder.symbol(
        "shared_bin_destructor_noop",
        procbin::shared_bin_destructor_noop as *const u8,
    );
    builder.symbol("fz_binary_as_ptr", extern_binary::fz_binary_as_ptr as *const u8);
    builder.symbol("fz_binary_as_cstring", extern_binary::fz_binary_as_cstring as *const u8);
    builder.symbol(
        "fz_extern_symbol_addr",
        extern_variadic::fz_extern_symbol_addr as *const u8,
    );
    builder.symbol(
        "fz_call_var_i64_cstring_i64_i64_to_i64",
        extern_variadic::fz_call_var_i64_cstring_i64_i64_to_i64 as *const u8,
    );
    builder.symbol(
        "fz_call_var_i64_cstring_i64_to_i64",
        extern_variadic::fz_call_var_i64_cstring_i64_to_i64 as *const u8,
    );
    builder.symbol("fz_map_dest_begin", ir_runtime::fz_map_dest_begin as *const u8);
    builder.symbol(
        "fz_map_dest_begin_update",
        ir_runtime::fz_map_dest_begin_update as *const u8,
    );
    builder.symbol("fz_map_dest_put_parts", ir_runtime::fz_map_dest_put_parts as *const u8);
    builder.symbol("fz_map_dest_put_ref", ir_runtime::fz_map_dest_put_ref as *const u8);
    builder.symbol("fz_map_dest_freeze", ir_runtime::fz_map_dest_freeze as *const u8);
    builder.symbol("fz_map_get_ref", ir_runtime::fz_map_get_ref as *const u8);
    builder.symbol(
        "fz_map_get_atom_key_ref",
        ir_runtime::fz_map_get_atom_key_ref as *const u8,
    );
    builder.symbol(
        "fz_map_get_int_key_ref",
        ir_runtime::fz_map_get_int_key_ref as *const u8,
    );
    builder.symbol(
        "fz_map_get_float_key_ref",
        ir_runtime::fz_map_get_float_key_ref as *const u8,
    );
    builder.symbol("fz_ref_load_float", ir_runtime::fz_ref_load_float as *const u8);
    builder.symbol("fz_ref_load_int", ir_runtime::fz_ref_load_int as *const u8);
    builder.symbol("fz_type_of", ir_runtime::fz_type_of as *const u8);
    builder.symbol("fz_unbox_int", ir_runtime::fz_unbox_int as *const u8);
    builder.symbol("fz_unbox_float", ir_runtime::fz_unbox_float as *const u8);
    builder.symbol("fz_unbox_atom", ir_runtime::fz_unbox_atom as *const u8);
    builder.symbol(
        "fz_struct_schema_id_ref",
        ir_runtime::fz_struct_schema_id_ref as *const u8,
    );
    builder.symbol("fz_truthy_ref", ir_runtime::fz_truthy_ref as *const u8);
    builder.symbol("fz_box_int_for_any", ir_runtime::fz_box_int_for_any as *const u8);
    builder.symbol("fz_box_float_for_any", ir_runtime::fz_box_float_for_any as *const u8);
    builder.symbol("fz_box_atom_for_any", ir_runtime::fz_box_atom_for_any as *const u8);
    builder.symbol("fz_map_is_map", ir_runtime::fz_map_is_map as *const u8);
    builder.symbol("fz_promote_f64", ir_runtime::fz_promote_f64 as *const u8);
    builder.symbol("fz_value_eq_ref", ir_runtime::fz_value_eq_ref as *const u8);
    // Receive matcher's binary-literal helper.
    builder.symbol("fz_matcher_eq_bytes", ir_runtime::fz_matcher_eq_bytes as *const u8);
    // Receive matcher's map-key lookup helper.
    builder.symbol(
        "fz_matcher_map_get_ref",
        ir_runtime::fz_matcher_map_get_ref as *const u8,
    );
    builder.symbol("fz_alloc_closure", ir_runtime::fz_alloc_closure as *const u8);
    builder.symbol("fz_closure_code_ref", ir_runtime::fz_closure_code_ref as *const u8);
    builder.symbol("fz_materialize_cont", ir_runtime::fz_materialize_cont as *const u8);
    builder.symbol(
        "fz_closure_halt_kind_ref",
        ir_runtime::fz_closure_halt_kind_ref as *const u8,
    );
    builder.symbol(
        "fz_closure_get_capture_ref",
        ir_runtime::fz_closure_get_capture_ref as *const u8,
    );
    builder.symbol(
        "fz_closure_get_capture_i64",
        ir_runtime::fz_closure_get_capture_i64 as *const u8,
    );
    builder.symbol(
        "fz_closure_get_capture_f64",
        ir_runtime::fz_closure_get_capture_f64 as *const u8,
    );
    builder.symbol(
        "fz_closure_get_capture_atom",
        ir_runtime::fz_closure_get_capture_atom as *const u8,
    );
    builder.symbol(
        "fz_closure_set_capture_ref",
        ir_runtime::fz_closure_set_capture_ref as *const u8,
    );
    builder.symbol(
        "fz_closure_set_capture_i64",
        ir_runtime::fz_closure_set_capture_i64 as *const u8,
    );
    builder.symbol(
        "fz_closure_set_capture_f64",
        ir_runtime::fz_closure_set_capture_f64 as *const u8,
    );
    builder.symbol(
        "fz_closure_set_capture_atom",
        ir_runtime::fz_closure_set_capture_atom as *const u8,
    );
    builder.symbol("fz_spawn_ref", ir_runtime::fz_spawn_ref as *const u8);
    builder.symbol("fz_spawn_opt_ref", ir_runtime::fz_spawn_opt_ref as *const u8);
    builder.symbol("fz_self_raw", ir_runtime::fz_self_raw as *const u8);
    builder.symbol("fz_make_ref_raw", ir_runtime::fz_make_ref_raw as *const u8);
    builder.symbol("fz_make_resource_ref", ir_runtime::fz_make_resource_ref as *const u8);
    builder.symbol("fz_send_ref", ir_runtime::fz_send_ref as *const u8);
    // utf8 brand support.
    builder.symbol(
        "fz_bitstring_valid_utf8",
        ir_runtime::fz_bitstring_valid_utf8 as *const u8,
    );
    builder.symbol(
        "fz_brand_bitstring_as_utf8",
        ir_runtime::fz_brand_bitstring_as_utf8 as *const u8,
    );
    // Runtime-exported fixture/test dtor. Bound unconditionally (not
    // cfg(test)-gated) so any `fz dump --emit clif` or `fz run` over
    // a fixture using it resolves cleanly — the golden-CLIF harness
    // compiles every non-deferred fixture.
    builder.symbol(
        "fz_resource_test_print_dtor",
        resource::fz_resource_test_print_dtor as *const u8,
    );
    // Selective-receive park entry. Used by JIT codegen at the
    // Term::ReceiveMatched seam.
    builder.symbol(
        "fz_receive_park_matched",
        ir_runtime::fz_receive_park_matched as *const u8,
    );
    builder.symbol(
        "fz_yield_mid_flight_report",
        ir_runtime::fz_yield_mid_flight_report as *const u8,
    );
    builder.symbol(
        "fz_yield_slow_path_begin",
        ir_runtime::fz_yield_slow_path_begin as *const u8,
    );
    builder.symbol("fz_get_static_closure", ir_runtime::fz_get_static_closure as *const u8);
    builder.symbol("fz_get_halt_cont", ir_runtime::fz_get_halt_cont as *const u8);
    // Test externs (e.g. the `_resource_test_dtor` counter used by
    // JIT-leg resource lifecycle tests). Production paths see no
    // extra symbols.
    #[cfg(test)]
    builder.symbol("_resource_test_dtor", crate::ir_interp::tests_support_test_dtor_addr());
}

impl Backend for JitBackend {
    type Module = JITModule;
    type Output = CompiledModule;

    fn module_mut(&mut self) -> &mut JITModule {
        &mut self.jmod
    }

    fn fn_linkage(&self) -> Linkage {
        Linkage::Local
    }

    fn emit_metadata_carriers(
        &mut self,
        _fbctx: &mut FunctionBuilderContext,
        _meta: &CompiledMetadata,
    ) -> Result<(), CodegenError> {
        // No-op: JIT carries per-program metadata (fn_ptrs, frame_sizes,
        // atom_names) in the returned CompiledModule's Rust HashMaps.
        // The runtime reads them directly. No Cranelift carriers needed.
        Ok(())
    }

    fn finalize(self, meta: CompiledMetadata) -> Result<CompiledModule, CodegenError> {
        let JitBackend { mut jmod } = self;
        jmod.finalize_definitions()
            .map_err(|e| CodegenError::new(format!("finalize: {}", e)))?;
        let mut fn_ptrs: HashMap<u32, *const u8> = HashMap::new();
        for (fz_fn_id, func_id) in &meta.fn_ids {
            fn_ptrs.insert(*fz_fn_id, jmod.get_finalized_function(*func_id));
        }
        // Resolve each zero-cap closure-target stub_func_id to its
        // finalized code address. `make_process` writes these into the
        // off-heap singleton's `code_ptr` slot at +8.
        let static_closure_targets: Vec<(u32, u32, *const u8, u32)> = meta
            .static_closure_targets
            .iter()
            .map(|(cl_sid, fn_id, stub_fid, halt_kind)| {
                let ptr = jmod.get_finalized_function(*stub_fid);
                (*cl_sid, *fn_id, ptr, *halt_kind)
            })
            .collect();
        let entry_thunk_addr = jmod.get_finalized_function(meta.entry_thunk_id);
        let main_trampoline_addr = jmod.get_finalized_function(meta.main_trampoline_id);
        let drain_dtor_entry_addr = jmod.get_finalized_function(meta.drain_dtor_entry_id);
        let halt_cont_body_addrs = [
            jmod.get_finalized_function(meta.halt_cont_body_ids[0]),
            jmod.get_finalized_function(meta.halt_cont_body_ids[1]),
            jmod.get_finalized_function(meta.halt_cont_body_ids[2]),
            jmod.get_finalized_function(meta.halt_cont_body_ids[3]),
        ];
        let resume_addr = jmod.get_finalized_function(meta.resume_id);
        // Build the module's shared node once; every Process clones the Rc.
        let node = Rc::new(Node::new(meta.atom_names.clone(), meta.frame_sizes.clone()));
        Ok(CompiledModule {
            _module: jmod,
            fn_ptrs,
            user_schemas: meta.user_schemas,
            frame_sizes: meta.frame_sizes,
            atom_names: meta.atom_names,
            node,
            bs_tuple_arity1_schema: meta.bs_tuple_arity1_schema,
            bs_tuple_arity3_schema: meta.bs_tuple_arity3_schema,
            diagnostics: meta.diagnostics,
            static_closure_targets,
            entry_thunk_addr,
            main_trampoline_addr,
            drain_dtor_entry_addr,
            halt_cont_body_addrs,
            fn_halt_kinds: meta.fn_halt_kinds,
            resume_addr,
        })
    }
}

/// AOT backend: wraps a cranelift_object ObjectModule. Drives the same
/// codegen as the JIT (through the Backend trait + declare_runtime_symbols)
/// but finalizes by emitting object-file bytes for a linker rather than
/// resolving fn pointers in memory.
pub struct AotBackend {
    omod: ObjectModule,
}

impl AotBackend {
    pub fn new(name: &str) -> Self {
        // PIC is required on macOS (linker rejects text relocations in
        // regular executables) and conventional for Linux distributables.
        let isa = host_isa_with(true);
        let builder = ObjectBuilder::new(isa, name.to_string(), cranelift_module::default_libcall_names())
            .expect("ObjectBuilder::new");
        Self {
            omod: ObjectModule::new(builder),
        }
    }
}

impl Backend for AotBackend {
    type Module = ObjectModule;
    type Output = AotArtifact;

    fn module_mut(&mut self) -> &mut ObjectModule {
        &mut self.omod
    }

    fn fn_linkage(&self) -> Linkage {
        Linkage::Export
    }

    fn emit_metadata_carriers(
        &mut self,
        fbctx: &mut FunctionBuilderContext,
        meta: &CompiledMetadata,
    ) -> Result<(), CodegenError> {
        // No `main`/0 in the source → nothing to drive at startup. `fz build`
        // errors gracefully on this artifact via its main_symbol check.
        let Some(main_fn_id) = meta.main_fn_id else {
            return Ok(());
        };

        // AOT C-main is a thin driver around the Tail-CC entry bodies
        // (fz_entry_thunk / fz_main_trampoline / fz_halt_cont_body) emitted by
        // planned codegen. Three fz-runtime FFI fns handle Process
        // setup, static-closure registration, and run-main+teardown.
        // Setup takes the four halt_cont_body addrs (ValueRef, RawInt,
        // RawF64, RawAtom) in slots 2-5.
        let setup_sig = sig1(
            &[
                types::I64,
                types::I32,
                types::I64,
                types::I64,
                types::I64,
                types::I64,
                types::I64,
            ],
            &[types::I64],
        );
        let setup_id = self
            .omod
            .declare_function("fz_aot_setup", Linkage::Import, &setup_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_setup: {}", e)))?;

        // Trailing i32 carries halt_kind.
        let reg_sig = sig1(&[types::I64, types::I32, types::I32, types::I64, types::I32], &[]);
        let reg_id = self
            .omod
            .declare_function("fz_aot_register_static_closure", Linkage::Import, &reg_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_register_static_closure: {}", e)))?;

        let run_sig = sig1(&[types::I64, types::I64, types::I64, types::I32], &[types::I32]);
        let run_id = self
            .omod
            .declare_function("fz_aot_run_main", Linkage::Import, &run_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_run_main: {}", e)))?;

        // Registers the SystemV→Tail-CC `fz_drain_dtor_entry` shim so
        // the AOT run-queue loop can dispatch pending dtor closures at
        // task-exit. `(proc, addr)` — proc carries the scheduler handle.
        let set_drain_sig = sig1(&[types::I64, types::I64], &[]);
        let set_drain_id = self
            .omod
            .declare_function("fz_aot_set_drain_dtor_entry", Linkage::Import, &set_drain_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_set_drain_dtor_entry: {}", e)))?;

        // Registers the SystemV `fz_resume(cont)` shim so the AOT run-queue
        // loop can resume `runnable` (entry thunk or selective-receive/
        // mid-flight continuation) on parity with the JIT.
        // `(proc, addr)` — proc carries the scheduler handle.
        let set_resume_sig = sig1(&[types::I64, types::I64], &[]);
        let set_resume_id = self
            .omod
            .declare_function("fz_aot_set_resume_addr", Linkage::Import, &set_resume_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_set_resume_addr: {}", e)))?;

        // `fz_aot_register_tuple_schemas(proc, arities_ptr, len)` populates
        // the AOT process's SchemaRegistry with one Tuple{N} entry per
        // arity in array order. That order matches the planned codegen
        // schema iteration, so the schema ids baked into the CLIF
        // (via tuple_schema_ids) resolve correctly.
        let reg_tuples_sig = sig1(&[types::I64, types::I64, types::I32], &[]);
        let reg_tuples_id = self
            .omod
            .declare_function("fz_aot_register_tuple_schemas", Linkage::Import, &reg_tuples_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_register_tuple_schemas: {}", e)))?;
        let reg_named_schemas_sig = sig1(&[types::I64, types::I64, types::I32], &[]);
        let reg_named_schemas_id = self
            .omod
            .declare_function("fz_aot_register_named_schemas", Linkage::Import, &reg_named_schemas_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_register_named_schemas: {}", e)))?;

        let (tuple_arities_data, tuple_arities_len): (Option<DataId>, u32) = if meta.tuple_arities.is_empty() {
            (None, 0)
        } else {
            let mut bytes: Vec<u8> = Vec::with_capacity(meta.tuple_arities.len() * 4);
            for &a in &meta.tuple_arities {
                bytes.extend_from_slice(&a.to_ne_bytes());
            }
            let len = meta.tuple_arities.len() as u32;
            let id = self
                .omod
                .declare_data("fz_aot_tuple_arities", Linkage::Local, false, false)
                .map_err(|e| CodegenError::new(format!("declare tuple arities: {}", e)))?;
            let mut desc = DataDescription::new();
            desc.define(bytes.into_boxed_slice());
            self.omod
                .define_data(id, &desc)
                .map_err(|e| CodegenError::new(format!("define tuple arities: {}", e)))?;
            (Some(id), len)
        };

        let (atom_blob_data, atom_blob_len): (Option<DataId>, u32) = if meta.atom_names.is_empty() {
            (None, 0)
        } else {
            let mut blob: Vec<u8> = Vec::new();
            for name in &meta.atom_names {
                blob.extend_from_slice(name.as_bytes());
                blob.push(0);
            }
            blob.push(0);
            let len = blob.len() as u32;
            let id = self
                .omod
                .declare_data("fz_aot_atom_blob", Linkage::Local, false, false)
                .map_err(|e| CodegenError::new(format!("declare atom blob: {}", e)))?;
            let mut desc = DataDescription::new();
            desc.define(blob.into_boxed_slice());
            self.omod
                .define_data(id, &desc)
                .map_err(|e| CodegenError::new(format!("define atom blob: {}", e)))?;
            (Some(id), len)
        };
        let (named_schemas_data, named_schemas_len): (Option<DataId>, u32) = if meta.named_schemas.is_empty() {
            (None, 0)
        } else {
            let mut bytes: Vec<u8> = Vec::new();
            bytes.extend_from_slice(&(meta.named_schemas.len() as u32).to_ne_bytes());
            for (name, fields) in &meta.named_schemas {
                bytes.extend_from_slice(&(name.len() as u32).to_ne_bytes());
                bytes.extend_from_slice(name.as_bytes());
                bytes.extend_from_slice(&(fields.len() as u32).to_ne_bytes());
                for field in fields {
                    bytes.extend_from_slice(&(field.len() as u32).to_ne_bytes());
                    bytes.extend_from_slice(field.as_bytes());
                }
            }
            let len = bytes.len() as u32;
            let id = self
                .omod
                .declare_data("fz_aot_named_schemas", Linkage::Local, false, false)
                .map_err(|e| CodegenError::new(format!("declare named schemas: {}", e)))?;
            let mut desc = DataDescription::new();
            desc.define(bytes.into_boxed_slice());
            self.omod
                .define_data(id, &desc)
                .map_err(|e| CodegenError::new(format!("define named schemas: {}", e)))?;
            (Some(id), len)
        };

        let mut c_main_sig = Signature::new(CallConv::SystemV);
        c_main_sig.params.push(AbiParam::new(types::I32));
        c_main_sig.params.push(AbiParam::new(types::I64));
        c_main_sig.returns.push(AbiParam::new(types::I32));
        let c_main_id = self
            .omod
            .declare_function("main", Linkage::Export, &c_main_sig)
            .map_err(|e| CodegenError::new(format!("declare C main: {}", e)))?;
        emit_aot_c_main(
            &mut self.omod,
            fbctx,
            c_main_id,
            &c_main_sig,
            meta.fn_ids[&main_fn_id.0],
            meta.fn_halt_kinds.get(&main_fn_id.0).copied().unwrap_or(0),
            meta.main_trampoline_id,
            meta.halt_cont_body_ids,
            meta.entry_thunk_id,
            &meta.static_closure_targets,
            atom_blob_data,
            atom_blob_len,
            setup_id,
            reg_id,
            run_id,
            reg_tuples_id,
            tuple_arities_data,
            tuple_arities_len,
            reg_named_schemas_id,
            named_schemas_data,
            named_schemas_len,
            set_drain_id,
            meta.drain_dtor_entry_id,
            set_resume_id,
            meta.resume_id,
        )?;
        Ok(())
    }

    fn finalize(self, meta: CompiledMetadata) -> Result<AotArtifact, CodegenError> {
        let AotBackend { omod } = self;
        // Emit the macOS platform load command (LC_BUILD_VERSION) so ld
        // doesn't warn "no platform load command found". Cranelift's
        // ObjectBuilder doesn't inject this automatically.
        #[cfg(target_os = "macos")]
        let product = {
            let mut p = omod.finish();
            let mut ver = MachOBuildVersion::default();
            ver.platform = PLATFORM_MACOS;
            ver.minos = 11 << 16; // 11.0.0 — first macOS on Apple Silicon
            ver.sdk = 11 << 16;
            p.object.set_macho_build_version(ver);
            p
        };
        #[cfg(not(target_os = "macos"))]
        let product = omod.finish();
        let object = product
            .emit()
            .map_err(|e| CodegenError::new(format!("object emit: {}", e)))?;
        // For programs with a fz `main`, the C-callable `main` shim is the
        // linker's entry point. Without a fz main, no shim was emitted and
        // we surface the underlying fz_fn_<id> name so `fz build` can
        // error cleanly.
        let main_symbol = if meta.main_fn_id.is_some() {
            Some("main".to_string())
        } else {
            None
        };
        Ok(AotArtifact {
            object,
            main_symbol,
            diagnostics: meta.diagnostics,
        })
    }
}

/// AOT artifact: per-module emitted object bytes plus enough metadata to
/// drive linking. Consumed by `fz build`.
pub struct AotArtifact {
    /// Object-file bytes (ELF on Linux, Mach-O on macOS, COFF on Windows)
    /// suitable for `cc` to link against fz_runtime + libc.
    pub object: Vec<u8>,
    /// `main` fn's symbol name as emitted in the object, or None if the
    /// source had no `main/0`. The AOT driver uses this when generating
    /// the startup shim's call site.
    pub main_symbol: Option<String>,
    pub diagnostics: Diagnostics,
}

/// Resolve a TailCallClosure edge to its body's (FnId, SpecId raw u32).
/// Returns None when the closure var isn't typed as a singleton closure_lit
/// or when no covering spec is registered for the resolved key.
/// Shared by tagged-return seeding, halt_kind analysis, and TailCallClosure
/// codegen.
pub(crate) fn resolve_tcc_body<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    closure: &Var,
    args: &[Var],
    ft: &SpecPlan,
    module: &Module,
    spec_registry: &SpecRegistry,
) -> Option<(FnId, u32)> {
    let (fn_id, captures) = if let Some(ClosureLitInfo { target, captures, .. }) =
        ft.vars.get(closure).and_then(|ty| t.closure_lit_parts(ty))
    {
        (FnId::from(target), captures)
    } else {
        match ft.callable_capabilities.get(closure)? {
            CallableCapability::KnownFn(fn_id) => (*fn_id, Vec::new()),
            CallableCapability::KnownClosure { fn_id, captures, .. } => (*fn_id, captures.clone()),
            CallableCapability::OpaqueCallable => return None,
        }
    };
    let body_fn = module.fn_by_id(fn_id);
    let np = body_fn.block(body_fn.entry).params.len();
    let any = t.any();
    let mut key: Vec<Ty> = captures;
    for av in args {
        key.push(ft.vars.get(av).cloned().unwrap_or_else(|| any.clone()));
    }
    while key.len() < np {
        key.push(any.clone());
    }
    key.truncate(np);
    let key = SpecKey::value(fn_id, key_slots_from_tys(key));
    Some((fn_id, spec_registry.resolve_spec_key(t, &key)?.0))
}
