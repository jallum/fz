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

/// shared and the trait owns every legitimate point of variation —
/// fn linkage, per-program metadata emission, and the finalize step
/// that materializes the backend's Output.
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

/// fz-ul4.29.2 — Two-way mapping between (FnId, input-type-tuple) and
/// SpecId. Each compiled body has one entry; SpecIds are dense from 0.
///
/// In .29.2 every FnIr has exactly one SpecId (its any-key spec), so
/// `SpecId.0 == FnId.0` is an invariant — preserves bit-identical CLIF
/// vs. the pre-atom baseline. fz-ul4.29.2.1 admits multiple SpecIds per
/// FnId for narrow specs, at which point the invariant relaxes.
use crate::spec_registry::SpecRegistry;

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
        builder.symbol(
            "fz_print_value_ref",
            fz_runtime::ir_runtime::fz_print_value_ref as *const u8,
        );
        builder.symbol(
            "fz_process_heap_alloc_stats",
            fz_runtime::ir_runtime::fz_process_heap_alloc_stats as *const u8,
        );
        // fz-ul4.27.7 (VR.5b): typed print helpers — JIT routes here when
        // the arg type is monomorphic, passing the raw payload directly.
        builder.symbol("fz_print_i64", fz_runtime::fz_print_i64 as *const u8);
        // Linux JIT needs explicit symbol bindings; macOS happens to
        // resolve runtime crate exports via dlsym on the executable
        // image, but Linux's stricter visibility under cargo llvm-cov
        // drops them. Bind the assert family here so JIT-emitted code
        // can call them on every platform.
        builder.symbol("fz_assert", fz_runtime::fz_assert as *const u8);
        builder.symbol("fz_assert_eq", fz_runtime::fz_assert_eq as *const u8);
        builder.symbol("fz_assert_neq", fz_runtime::fz_assert_neq as *const u8);
        builder.symbol("fz_print_f64", fz_runtime::fz_print_f64 as *const u8);
        builder.symbol(
            "fz_dynamic_float_arith_unsupported",
            fz_runtime::ir_runtime::fz_dynamic_float_arith_unsupported as *const u8,
        );
        builder.symbol(
            "fz_halt_implicit_ref",
            fz_runtime::ir_runtime::fz_halt_implicit_ref as *const u8,
        );
        builder.symbol(
            "fz_halt_implicit_i64",
            fz_runtime::ir_runtime::fz_halt_implicit_i64 as *const u8,
        );
        builder.symbol(
            "fz_halt_implicit_f64",
            fz_runtime::ir_runtime::fz_halt_implicit_f64 as *const u8,
        );
        builder.symbol(
            "fz_alloc_frame",
            fz_runtime::ir_runtime::fz_alloc_frame as *const u8,
        );
        builder.symbol(
            "fz_list_cons_ref",
            fz_runtime::ir_runtime::fz_list_cons_ref as *const u8,
        );
        builder.symbol(
            "fz_list_cons_any",
            fz_runtime::ir_runtime::fz_list_cons_any as *const u8,
        );
        builder.symbol(
            "fz_list_cons_int",
            fz_runtime::ir_runtime::fz_list_cons_int as *const u8,
        );
        builder.symbol(
            "fz_list_cons_float",
            fz_runtime::ir_runtime::fz_list_cons_float as *const u8,
        );
        builder.symbol(
            "fz_list_cons_atom",
            fz_runtime::ir_runtime::fz_list_cons_atom as *const u8,
        );
        builder.symbol(
            "fz_list_is_cons",
            fz_runtime::ir_runtime::fz_list_is_cons as *const u8,
        );
        builder.symbol(
            "fz_list_head_ref",
            fz_runtime::ir_runtime::fz_list_head_ref as *const u8,
        );
        builder.symbol(
            "fz_list_head_int_ref",
            fz_runtime::ir_runtime::fz_list_head_int_ref as *const u8,
        );
        builder.symbol(
            "fz_list_head_float_ref",
            fz_runtime::ir_runtime::fz_list_head_float_ref as *const u8,
        );
        builder.symbol(
            "fz_list_tail",
            fz_runtime::ir_runtime::fz_list_tail as *const u8,
        );
        builder.symbol(
            "fz_list_tail_ref",
            fz_runtime::ir_runtime::fz_list_tail_ref as *const u8,
        );
        builder.symbol(
            "fz_alloc_struct",
            fz_runtime::ir_runtime::fz_alloc_struct as *const u8,
        );
        builder.symbol(
            "fz_struct_get_field_ref",
            fz_runtime::ir_runtime::fz_struct_get_field_ref as *const u8,
        );
        builder.symbol(
            "fz_struct_set_field_ref",
            fz_runtime::ir_runtime::fz_struct_set_field_ref as *const u8,
        );
        builder.symbol(
            "fz_struct_set_field_int",
            fz_runtime::ir_runtime::fz_struct_set_field_int as *const u8,
        );
        builder.symbol(
            "fz_struct_set_field_float",
            fz_runtime::ir_runtime::fz_struct_set_field_float as *const u8,
        );
        builder.symbol(
            "fz_struct_set_field_atom",
            fz_runtime::ir_runtime::fz_struct_set_field_atom as *const u8,
        );
        builder.symbol(
            "fz_bs_begin",
            fz_runtime::ir_runtime::fz_bs_begin as *const u8,
        );
        builder.symbol(
            "fz_bs_write_field_ref",
            fz_runtime::ir_runtime::fz_bs_write_field_ref as *const u8,
        );
        builder.symbol(
            "fz_bs_finalize",
            fz_runtime::ir_runtime::fz_bs_finalize as *const u8,
        );
        builder.symbol(
            "fz_alloc_bitstring_const",
            fz_runtime::ir_runtime::fz_alloc_bitstring_const as *const u8,
        );
        builder.symbol(
            "fz_bs_reader_init_ref",
            fz_runtime::ir_runtime::fz_bs_reader_init_ref as *const u8,
        );
        builder.symbol(
            "fz_bs_read_field_ref",
            fz_runtime::ir_runtime::fz_bs_read_field_ref as *const u8,
        );
        builder.symbol(
            "fz_bs_reader_done_ref",
            fz_runtime::ir_runtime::fz_bs_reader_done_ref as *const u8,
        );
        // fz-q8d.2 — static SharedBin path: codegen emits a 40-byte data
        // symbol in `.data`, then a call to this helper to wrap it in a
        // per-process ProcBin / MSO entry.
        builder.symbol(
            "fz_alloc_procbin_from_static",
            fz_runtime::ir_runtime::fz_alloc_procbin_from_static as *const u8,
        );
        // fz-q8d.2 — noop destructor address baked into each static
        // SharedBin's `destructor` field via a function-address
        // relocation. Never invoked in practice (anchor refcount stays
        // ≥ 1) but must resolve at link time.
        builder.symbol(
            "shared_bin_destructor_noop",
            fz_runtime::procbin::shared_bin_destructor_noop as *const u8,
        );
        // fz-9ss — extern binary marshal helpers.
        builder.symbol(
            "fz_binary_as_ptr",
            fz_runtime::extern_binary::fz_binary_as_ptr as *const u8,
        );
        builder.symbol(
            "fz_binary_as_cstring",
            fz_runtime::extern_binary::fz_binary_as_cstring as *const u8,
        );
        builder.symbol(
            "fz_map_empty",
            fz_runtime::ir_runtime::fz_map_empty as *const u8,
        );
        builder.symbol(
            "fz_map_dest_begin",
            fz_runtime::ir_runtime::fz_map_dest_begin as *const u8,
        );
        builder.symbol(
            "fz_map_dest_begin_update",
            fz_runtime::ir_runtime::fz_map_dest_begin_update as *const u8,
        );
        builder.symbol(
            "fz_map_dest_put_parts",
            fz_runtime::ir_runtime::fz_map_dest_put_parts as *const u8,
        );
        builder.symbol(
            "fz_map_dest_put_ref",
            fz_runtime::ir_runtime::fz_map_dest_put_ref as *const u8,
        );
        builder.symbol(
            "fz_map_dest_freeze",
            fz_runtime::ir_runtime::fz_map_dest_freeze as *const u8,
        );
        builder.symbol(
            "fz_map_put_ref",
            fz_runtime::ir_runtime::fz_map_put_ref as *const u8,
        );
        builder.symbol(
            "fz_map_put_int",
            fz_runtime::ir_runtime::fz_map_put_int as *const u8,
        );
        builder.symbol(
            "fz_map_put_float",
            fz_runtime::ir_runtime::fz_map_put_float as *const u8,
        );
        builder.symbol(
            "fz_map_put_atom",
            fz_runtime::ir_runtime::fz_map_put_atom as *const u8,
        );
        builder.symbol(
            "fz_map_put_atom_key_int",
            fz_runtime::ir_runtime::fz_map_put_atom_key_int as *const u8,
        );
        builder.symbol(
            "fz_map_put_atom_key_float",
            fz_runtime::ir_runtime::fz_map_put_atom_key_float as *const u8,
        );
        builder.symbol(
            "fz_map_put_atom_key_atom",
            fz_runtime::ir_runtime::fz_map_put_atom_key_atom as *const u8,
        );
        builder.symbol(
            "fz_map_put_int_key_int",
            fz_runtime::ir_runtime::fz_map_put_int_key_int as *const u8,
        );
        builder.symbol(
            "fz_map_put_int_key_float",
            fz_runtime::ir_runtime::fz_map_put_int_key_float as *const u8,
        );
        builder.symbol(
            "fz_map_put_int_key_atom",
            fz_runtime::ir_runtime::fz_map_put_int_key_atom as *const u8,
        );
        builder.symbol(
            "fz_map_put_float_key_int",
            fz_runtime::ir_runtime::fz_map_put_float_key_int as *const u8,
        );
        builder.symbol(
            "fz_map_put_float_key_float",
            fz_runtime::ir_runtime::fz_map_put_float_key_float as *const u8,
        );
        builder.symbol(
            "fz_map_put_float_key_atom",
            fz_runtime::ir_runtime::fz_map_put_float_key_atom as *const u8,
        );
        builder.symbol(
            "fz_map_get_ref",
            fz_runtime::ir_runtime::fz_map_get_ref as *const u8,
        );
        builder.symbol(
            "fz_map_get_atom_key_ref",
            fz_runtime::ir_runtime::fz_map_get_atom_key_ref as *const u8,
        );
        builder.symbol(
            "fz_map_get_int_key_ref",
            fz_runtime::ir_runtime::fz_map_get_int_key_ref as *const u8,
        );
        builder.symbol(
            "fz_map_get_float_key_ref",
            fz_runtime::ir_runtime::fz_map_get_float_key_ref as *const u8,
        );
        builder.symbol(
            "fz_ref_load_float",
            fz_runtime::ir_runtime::fz_ref_load_float as *const u8,
        );
        builder.symbol(
            "fz_ref_load_int",
            fz_runtime::ir_runtime::fz_ref_load_int as *const u8,
        );
        builder.symbol(
            "fz_type_of",
            fz_runtime::ir_runtime::fz_type_of as *const u8,
        );
        builder.symbol(
            "fz_unbox_int",
            fz_runtime::ir_runtime::fz_unbox_int as *const u8,
        );
        builder.symbol(
            "fz_unbox_float",
            fz_runtime::ir_runtime::fz_unbox_float as *const u8,
        );
        builder.symbol(
            "fz_unbox_atom",
            fz_runtime::ir_runtime::fz_unbox_atom as *const u8,
        );
        builder.symbol(
            "fz_struct_schema_id_ref",
            fz_runtime::ir_runtime::fz_struct_schema_id_ref as *const u8,
        );
        builder.symbol(
            "fz_truthy_ref",
            fz_runtime::ir_runtime::fz_truthy_ref as *const u8,
        );
        builder.symbol(
            "fz_box_int_for_any",
            fz_runtime::ir_runtime::fz_box_int_for_any as *const u8,
        );
        builder.symbol(
            "fz_box_float_for_any",
            fz_runtime::ir_runtime::fz_box_float_for_any as *const u8,
        );
        builder.symbol(
            "fz_box_atom_for_any",
            fz_runtime::ir_runtime::fz_box_atom_for_any as *const u8,
        );
        builder.symbol(
            "fz_map_is_map",
            fz_runtime::ir_runtime::fz_map_is_map as *const u8,
        );
        builder.symbol(
            "fz_promote_f64",
            fz_runtime::ir_runtime::fz_promote_f64 as *const u8,
        );
        builder.symbol(
            "fz_value_eq_ref",
            fz_runtime::ir_runtime::fz_value_eq_ref as *const u8,
        );
        // fz-puj.45 (X4) — receive matcher's binary-literal helper.
        builder.symbol(
            "fz_matcher_eq_bytes",
            fz_runtime::ir_runtime::fz_matcher_eq_bytes as *const u8,
        );
        // fz-puj.47 (X6) — receive matcher's map-key lookup helper.
        builder.symbol(
            "fz_matcher_map_get_ref",
            fz_runtime::ir_runtime::fz_matcher_map_get_ref as *const u8,
        );
        builder.symbol(
            "fz_alloc_closure",
            fz_runtime::ir_runtime::fz_alloc_closure as *const u8,
        );
        builder.symbol(
            "fz_closure_code_ref",
            fz_runtime::ir_runtime::fz_closure_code_ref as *const u8,
        );
        builder.symbol(
            "fz_closure_halt_kind_ref",
            fz_runtime::ir_runtime::fz_closure_halt_kind_ref as *const u8,
        );
        builder.symbol(
            "fz_closure_get_capture_ref",
            fz_runtime::ir_runtime::fz_closure_get_capture_ref as *const u8,
        );
        builder.symbol(
            "fz_closure_get_capture_i64",
            fz_runtime::ir_runtime::fz_closure_get_capture_i64 as *const u8,
        );
        builder.symbol(
            "fz_closure_get_capture_f64",
            fz_runtime::ir_runtime::fz_closure_get_capture_f64 as *const u8,
        );
        builder.symbol(
            "fz_closure_set_capture_ref",
            fz_runtime::ir_runtime::fz_closure_set_capture_ref as *const u8,
        );
        builder.symbol(
            "fz_closure_set_capture_i64",
            fz_runtime::ir_runtime::fz_closure_set_capture_i64 as *const u8,
        );
        builder.symbol(
            "fz_closure_set_capture_f64",
            fz_runtime::ir_runtime::fz_closure_set_capture_f64 as *const u8,
        );
        builder.symbol(
            "fz_spawn_ref",
            fz_runtime::ir_runtime::fz_spawn_ref as *const u8,
        );
        builder.symbol(
            "fz_spawn_opt_ref",
            fz_runtime::ir_runtime::fz_spawn_opt_ref as *const u8,
        );
        builder.symbol(
            "fz_self_raw",
            fz_runtime::ir_runtime::fz_self_raw as *const u8,
        );
        builder.symbol(
            "fz_make_ref_raw",
            fz_runtime::ir_runtime::fz_make_ref_raw as *const u8,
        );
        builder.symbol(
            "fz_make_resource_ref",
            fz_runtime::ir_runtime::fz_make_resource_ref as *const u8,
        );
        builder.symbol(
            "fz_send_ref",
            fz_runtime::ir_runtime::fz_send_ref as *const u8,
        );
        // fz-axu.14 (R1) / .13 (S2) — utf8 brand support.
        builder.symbol(
            "fz_bitstring_valid_utf8",
            fz_runtime::ir_runtime::fz_bitstring_valid_utf8 as *const u8,
        );
        builder.symbol(
            "fz_brand_bitstring_as_utf8",
            fz_runtime::ir_runtime::fz_brand_bitstring_as_utf8 as *const u8,
        );
        // fz-swt.11 — runtime-exported fixture/test dtor. Always bound to
        // the JIT (not gated on cfg(test)) so any `fz dump --emit clif`
        // or `fz run` over a fixture that uses it resolves cleanly — the
        // golden-CLIF harness compiles every non-deferred fixture.
        builder.symbol(
            "fz_resource_test_print_dtor",
            fz_runtime::resource::fz_resource_test_print_dtor as *const u8,
        );
        builder.symbol(
            "fz_receive_attempt",
            fz_runtime::ir_runtime::fz_receive_attempt as *const u8,
        );
        builder.symbol(
            "fz_receive_park",
            fz_runtime::ir_runtime::fz_receive_park as *const u8,
        );
        // fz-yxs/fz-st5 — selective receive park entry. Used by B3's
        // JIT codegen at the Term::ReceiveMatched seam.
        builder.symbol(
            "fz_receive_park_matched",
            fz_runtime::ir_runtime::fz_receive_park_matched as *const u8,
        );
        builder.symbol(
            "fz_yield_mid_flight",
            fz_runtime::ir_runtime::fz_yield_mid_flight as *const u8,
        );
        builder.symbol(
            "fz_get_static_closure",
            fz_runtime::ir_runtime::fz_get_static_closure as *const u8,
        );
        builder.symbol(
            "fz_get_halt_cont",
            fz_runtime::ir_runtime::fz_get_halt_cont as *const u8,
        );
        // fz-02r.5 — bind the cooperative yield helpers and the yield-flag data.
        builder.symbol("FZ_SHOULD_YIELD", fz_runtime::yield_flag::jit_flag_ptr());
        // fz-swt.10 (test only) — register test externs (e.g. the
        // `_resource_test_dtor` counter used by the JIT-leg resource
        // lifecycle tests). Production paths see no extra symbols.
        #[cfg(test)]
        builder.symbol(
            "_resource_test_dtor",
            crate::ir_interp::tests_support_test_dtor_addr(),
        );
        Self {
            jmod: JITModule::new(builder),
        }
    }
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
        // fz-cps.1.7 — resolve each zero-cap closure-target stub_func_id
        // to its finalized code address. `make_process` writes these into
        // the off-heap singleton's `code_ptr` slot at +8.
        let static_closure_targets: Vec<(u32, u32, *const u8, u32)> = meta
            .static_closure_targets
            .iter()
            .map(|(cl_sid, fn_id, stub_fid, halt_kind)| {
                let ptr = jmod.get_finalized_function(*stub_fid);
                (*cl_sid, *fn_id, ptr, *halt_kind)
            })
            .collect();
        let spawn_entry_addr = jmod.get_finalized_function(meta.spawn_entry_id);
        let main_entry_addr = jmod.get_finalized_function(meta.main_entry_id);
        let drain_dtor_entry_addr = jmod.get_finalized_function(meta.drain_dtor_entry_id);
        let halt_cont_body_addrs = [
            jmod.get_finalized_function(meta.halt_cont_body_ids[0]),
            jmod.get_finalized_function(meta.halt_cont_body_ids[1]),
            jmod.get_finalized_function(meta.halt_cont_body_ids[2]),
        ];
        let resume_addr = jmod.get_finalized_function(meta.resume_id);
        Ok(CompiledModule {
            _module: jmod,
            fn_ptrs,
            user_schemas: meta.user_schemas,
            frame_sizes: meta.frame_sizes,
            atom_names: meta.atom_names,
            bs_tuple_arity1_schema: meta.bs_tuple_arity1_schema,
            bs_tuple_arity3_schema: meta.bs_tuple_arity3_schema,
            diagnostics: meta.diagnostics,
            static_closure_targets,
            spawn_entry_addr,
            main_entry_addr,
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
/// resolving fn pointers in memory. fz-ul4.23.6.1.
pub struct AotBackend {
    omod: cranelift_object::ObjectModule,
}

impl AotBackend {
    pub fn new(name: &str) -> Self {
        // AOT needs PIC for macOS — the linker rejects text relocations
        // in regular executables. PIC on x86_64-linux / aarch64-linux is
        // also conventional for distributable binaries.
        let isa = host_isa_with(true);
        let builder = cranelift_object::ObjectBuilder::new(
            isa,
            name.to_string(),
            cranelift_module::default_libcall_names(),
        )
        .expect("ObjectBuilder::new");
        Self {
            omod: cranelift_object::ObjectModule::new(builder),
        }
    }
}

impl Backend for AotBackend {
    type Module = cranelift_object::ObjectModule;
    type Output = AotArtifact;

    fn module_mut(&mut self) -> &mut cranelift_object::ObjectModule {
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

        // fz-siu.6.1: AOT C-main is a thin driver around the cps-in-clif
        // SystemV→Tail-CC shims (fz_main_entry / fz_halt_cont_body) emitted
        // in compile_with_backend. Three FFI fns from fz-runtime do the
        // Process setup, static-closure registration, and run-main+teardown.
        // fz-ul4.27.22.3 — setup takes 3 halt_cont_body addrs (ValueRef,
        // RawInt, RawF64) in slots 2-4.
        let setup_sig = sig1(
            &[
                types::I64,
                types::I32,
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

        // fz-ul4.27.22.6: trailing i32 carries halt_kind.
        let reg_sig = sig1(
            &[types::I64, types::I32, types::I32, types::I64, types::I32],
            &[],
        );
        let reg_id = self
            .omod
            .declare_function("fz_aot_register_static_closure", Linkage::Import, &reg_sig)
            .map_err(|e| {
                CodegenError::new(format!("declare fz_aot_register_static_closure: {}", e))
            })?;

        let run_sig = sig1(&[types::I64, types::I64, types::I64], &[types::I32]);
        let run_id = self
            .omod
            .declare_function("fz_aot_run_main", Linkage::Import, &run_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_run_main: {}", e)))?;

        // fz-4mk.3b — fz_aot_set_drain_dtor_entry(addr). Registers the
        // SystemV→Tail-CC `fz_drain_dtor_entry` shim so the AOT run-queue
        // loop can dispatch pending dtor closures at task-exit.
        let set_drain_sig = sig1(&[types::I64], &[]);
        let set_drain_id = self
            .omod
            .declare_function(
                "fz_aot_set_drain_dtor_entry",
                Linkage::Import,
                &set_drain_sig,
            )
            .map_err(|e| {
                CodegenError::new(format!("declare fz_aot_set_drain_dtor_entry: {}", e))
            })?;

        // fz-xx8.1 — fz_aot_set_resume_addr(addr). Registers the SystemV
        // `fz_resume(cont)` shim so the AOT run-queue loop can dispatch
        // `runnable_closure` (selective-receive wakeup) on parity
        // with the JIT path (src/ir_codegen.rs:335).
        let set_resume_sig = sig1(&[types::I64], &[]);
        let set_resume_id = self
            .omod
            .declare_function("fz_aot_set_resume_addr", Linkage::Import, &set_resume_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_set_resume_addr: {}", e)))?;

        // fz-ul4.38 — fz_aot_register_tuple_schemas(proc, arities_ptr, len)
        // populates the AOT process's SchemaRegistry with one Tuple{N} entry
        // per arity, in the order the array was emitted. That order matches
        // the sorted iteration in compile_with_backend, so the schema ids
        // baked into the CLIF (via tuple_schema_ids) resolve correctly.
        let reg_tuples_sig = sig1(&[types::I64, types::I64, types::I32], &[]);
        let reg_tuples_id = self
            .omod
            .declare_function(
                "fz_aot_register_tuple_schemas",
                Linkage::Import,
                &reg_tuples_sig,
            )
            .map_err(|e| {
                CodegenError::new(format!("declare fz_aot_register_tuple_schemas: {}", e))
            })?;

        let (tuple_arities_data, tuple_arities_len): (Option<DataId>, u32) =
            if meta.tuple_arities.is_empty() {
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
            meta.main_entry_id,
            meta.halt_cont_body_ids,
            meta.spawn_entry_id,
            &meta.static_closure_targets,
            atom_blob_data,
            atom_blob_len,
            setup_id,
            reg_id,
            run_id,
            reg_tuples_id,
            tuple_arities_data,
            tuple_arities_len,
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
        // ObjectBuilder doesn't inject this automatically (fz-ul4.33).
        #[cfg(target_os = "macos")]
        let product = {
            let mut p = omod.finish();
            let mut ver = object::write::MachOBuildVersion::default();
            ver.platform = object::macho::PLATFORM_MACOS;
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
/// drive linking. fz-ul4.23.6.3 (`fz build`) consumes this.
pub struct AotArtifact {
    /// Object-file bytes (ELF on Linux, Mach-O on macOS, COFF on Windows)
    /// suitable for `cc` to link against fz_runtime + libc.
    pub object: Vec<u8>,
    /// `main` fn's symbol name as emitted in the object, or None if the
    /// source had no `main/0`. The AOT driver uses this when generating
    /// the startup shim's call site.
    pub main_symbol: Option<String>,
    pub diagnostics: crate::diag::Diagnostics,
}

/// Resolve a TailCallClosure edge to its body's (FnId, SpecId raw u32).
/// Returns None when the closure var isn't typed as a singleton closure_lit
/// or when no covering spec is registered for the resolved key.
/// Shared by the return-type fixpoint, tagged-return seeding, halt_kind
/// analysis, and TailCallClosure codegen — all four had identical inline copies.
pub(crate) fn resolve_tcc_body<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    closure: &crate::fz_ir::Var,
    args: &[crate::fz_ir::Var],
    ft: &crate::ir_typer::FnTypes,
    module: &crate::fz_ir::Module,
    spec_registry: &SpecRegistry,
) -> Option<(crate::fz_ir::FnId, u32)> {
    let crate::types::ClosureLitInfo { target, captures } =
        t.closure_lit_parts(ft.vars.get(closure)?)?;
    let fn_id = target.into();
    let body_fn = module.fn_by_id(fn_id);
    let np = body_fn.block(body_fn.entry).params.len();
    let any = t.any();
    let mut key: Vec<crate::types::Ty> = captures;
    for av in args {
        key.push(ft.vars.get(av).cloned().unwrap_or_else(|| any.clone()));
    }
    while key.len() < np {
        key.push(any.clone());
    }
    key.truncate(np);
    Some((fn_id, spec_registry.resolve(t, fn_id, &key)?.0))
}
