use super::*;
use crate::diag::Diagnostics;
use cranelift_codegen::ir::{AbiParam, types};
use cranelift_codegen::isa::TargetIsa;
use cranelift_codegen::settings::{Configurable, Flags};
use cranelift_frontend::FunctionBuilderContext;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, DataId, Linkage, Module as ClModule};
use cranelift_object::{ObjectBuilder, ObjectModule};
use fz_runtime::process::Node;
#[cfg(target_os = "macos")]
use object::macho::PLATFORM_MACOS;
#[cfg(target_os = "macos")]
use object::write::MachOBuildVersion;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

fn host_isa() -> Arc<dyn TargetIsa> {
    host_isa_with(false)
}

fn host_isa_with(pic: bool) -> Arc<dyn TargetIsa> {
    let mut flag_builder = cranelift_codegen::settings::builder();
    flag_builder.set("opt_level", "speed").unwrap();
    flag_builder.set("is_pic", if pic { "true" } else { "false" }).unwrap();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    flag_builder.set("preserve_frame_pointers", "true").unwrap();
    flag_builder.set("enable_pinned_reg", "true").unwrap();
    let isa_builder = cranelift_native::builder().expect("host ISA");
    isa_builder.finish(Flags::new(flag_builder)).expect("isa finish")
}

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
        #[cfg(test)]
        register_test_symbols(&mut builder);
        // Every symbol the JIT cannot resolve itself -- fz's own runtime
        // helpers and foreign C functions alike -- goes through the resolver
        // the interpreter uses, rather than cranelift's own `dlsym`. It asks
        // the loaded image, then the standard C libraries. Cranelift's
        // `dlsym` searched only what the process had
        // already loaded, so there were two answers to "where does `libc::sqrt`
        // live" and the JIT door failed on Linux, where libm is a separate
        // library, while the interp door did not.
        builder.symbol_lookup_fn(Box::new(|name| {
            let name = std::ffi::CString::new(name).ok()?;
            let addr = unsafe { fz_runtime::symbol_lookup::fz_extern_symbol_addr(name.as_ptr()) };
            (addr != 0).then_some(addr as *const u8)
        }));
        Self {
            jmod: JITModule::new(builder),
        }
    }
}

/// Test externs (e.g. the `_resource_test_dtor` counter used by JIT-leg
/// resource lifecycle tests). They live in this crate's test support, not in
/// the runtime, so they are the only symbols the JIT is handed by hand.
#[cfg(test)]
fn register_test_symbols(builder: &mut JITBuilder) {
    builder.symbol("_resource_test_dtor", crate::ir_interp::tests_support_test_dtor_addr());
    builder.symbol(
        "_test_integer_boolean_pair",
        crate::ir_interp::tests_support_integer_boolean_pair_addr(),
    );
    for (name, address) in crate::ir_interp::tests_support_scalar_pair_symbols() {
        builder.symbol(name, address);
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
        // Resolve each zero-cap closure-target stub_func_id to its
        // finalized code address. `make_process` writes these into the
        // off-heap singleton's `code_ptr` slot at +8.
        let static_closure_targets: Vec<(u32, u32, *const u8, u32, fz_runtime::any_value::ClosureDenotationId)> = meta
            .static_closure_targets
            .iter()
            .map(|(cl_sid, fn_id, stub_fid, halt_kind, denotation)| {
                let ptr = jmod.get_finalized_function(*stub_fid);
                (*cl_sid, *fn_id, ptr, *halt_kind, *denotation)
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
        for (id, denotation) in &meta.closure_denotations {
            node.register_closure_denotation(*id, Arc::clone(denotation));
        }
        Ok(CompiledModule {
            _module: jmod,
            fn_ptrs,
            user_schemas: meta.user_schemas,
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
/// codegen as the JIT (through the Backend trait) but finalizes by emitting
/// object-file bytes for a linker rather than resolving fn pointers in
/// memory.
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
        // No `main`/0 in the source → nothing to drive at startup. `fz2 build`
        // errors gracefully on this artifact via its main_symbol check.
        let Some(main_fn_id) = meta.main_fn_id else {
            return Ok(());
        };

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
        let (closure_denotations_data, closure_denotations_len) = if meta.closure_denotations.is_empty() {
            (None, 0)
        } else {
            let bytes = fz_runtime::function_denotation::encode_closure_denotations(&meta.closure_denotations)
                .map_err(CodegenError::new)?;
            let len =
                u32::try_from(bytes.len()).map_err(|_| CodegenError::new("closure denotation metadata exceeds u32"))?;
            let id = self
                .omod
                .declare_data("fz_aot_closure_denotations", Linkage::Local, false, false)
                .map_err(|e| CodegenError::new(format!("declare closure denotations: {e}")))?;
            let mut desc = DataDescription::new();
            desc.define(bytes.into_boxed_slice());
            self.omod
                .define_data(id, &desc)
                .map_err(|e| CodegenError::new(format!("define closure denotations: {e}")))?;
            (Some(id), len)
        };
        let (named_schemas_data, named_schemas_len): (Option<DataId>, u32) = if meta.named_schemas.is_empty() {
            (None, 0)
        } else {
            let mut bytes: Vec<u8> = Vec::new();
            bytes.extend_from_slice(&(meta.named_schemas.len() as u32).to_ne_bytes());
            for (name, fields) in &meta.named_schemas {
                bytes.extend_from_slice(&(name.segments().len() as u32).to_ne_bytes());
                for segment in name.segments() {
                    bytes.extend_from_slice(&(segment.len() as u32).to_ne_bytes());
                    bytes.extend_from_slice(segment.as_bytes());
                }
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

        // C `main(argc, argv) -> int`: not a runtime item, so its signature
        // is written out here.
        let mut c_main_sig = self.omod.make_signature();
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
            closure_denotations_data,
            closure_denotations_len,
            tuple_arities_data,
            tuple_arities_len,
            named_schemas_data,
            named_schemas_len,
            meta.drain_dtor_entry_id,
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
        // we surface the underlying fz_fn_<id> name so `fz2 build` can
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
/// drive linking. Consumed by `fz2 build`.
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
