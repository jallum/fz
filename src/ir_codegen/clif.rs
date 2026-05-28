//! Low-level Cranelift helpers shared by codegen modules.

use super::*;
use cranelift_codegen::ir::{self, InstBuilder, Signature, types};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::FuncId;
use std::sync::Arc;

pub(crate) fn host_isa() -> Arc<dyn cranelift_codegen::isa::TargetIsa> {
    host_isa_with(false)
}

/// Build a host ISA. `pic = false` is right for the JIT (no relocations
/// needed inside in-memory code). `pic = true` is required for AOT on
/// macOS, where the linker rejects text relocations in regular
/// executables.
pub(crate) fn host_isa_with(pic: bool) -> Arc<dyn cranelift_codegen::isa::TargetIsa> {
    let mut flag_builder = settings::builder();
    flag_builder.set("opt_level", "speed").unwrap();
    flag_builder
        .set("is_pic", if pic { "true" } else { "false" })
        .unwrap();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    // Cranelift's Tail CC implementation asserts frame pointers are present.
    // macOS preserves them by default; Linux does not.
    flag_builder.set("preserve_frame_pointers", "true").unwrap();
    flag_builder.set("enable_pinned_reg", "true").unwrap();
    let isa_builder = cranelift_native::builder().expect("host ISA");
    isa_builder
        .finish(settings::Flags::new(flag_builder))
        .expect("isa finish")
}

/// Declare `id` in the current function and return its address as an i64.
/// Collapses the ubiquitous `declare_func_in_func` + `func_addr` pair.
pub(crate) fn fn_addr<M: cranelift_module::Module>(
    jmod: &mut M,
    id: FuncId,
    b: &mut FunctionBuilder<'_>,
) -> ir::Value {
    let fref = jmod.declare_func_in_func(id, b.func);
    b.ins().func_addr(types::I64, fref)
}

/// Emit a single Cranelift function: make_context → set sig → build body →
/// finalize → define_function → clear_context. Eliminates the boilerplate
/// repeated for every runtime shim (fz_main_entry, fz_spawn_entry, etc.).
pub(crate) fn emit_fn_body<M: cranelift_module::Module>(
    module: &mut M,
    fbctx: &mut FunctionBuilderContext,
    sig: Signature,
    func_id: FuncId,
    body: impl FnOnce(&mut M, &mut FunctionBuilder<'_>),
) -> Result<(), Box<cranelift_module::ModuleError>> {
    emit_fn_body_stats(module, fbctx, sig, func_id, body).map(|_| ())
}

pub(crate) fn emit_fn_body_stats<M: cranelift_module::Module>(
    module: &mut M,
    fbctx: &mut FunctionBuilderContext,
    sig: Signature,
    func_id: FuncId,
    body: impl FnOnce(&mut M, &mut FunctionBuilder<'_>),
) -> Result<(usize, usize), Box<cranelift_module::ModuleError>> {
    let mut ctx = module.make_context();
    ctx.func.signature = sig;
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);
        body(module, &mut b);
        b.finalize();
    }
    let stats = cranelift_body_stats(&ctx.func);
    module
        .define_function(func_id, &mut ctx)
        .map_err(Box::new)?;
    module.clear_context(&mut ctx);
    Ok(stats)
}

/// Pack a Span into a Cranelift SourceLoc (u32): 8 bits file_id + 24
/// bits start offset. Dummy spans become SourceLoc::default() so they
/// don't generate noise in the dump.
pub(crate) fn span_to_srcloc(s: crate::diag::Span) -> cranelift_codegen::ir::SourceLoc {
    if s.is_dummy() {
        return cranelift_codegen::ir::SourceLoc::default();
    }
    let file = (s.file.0 & 0xFF) << 24;
    let offset = s.start & 0x00FF_FFFF;
    cranelift_codegen::ir::SourceLoc::new(file | offset)
}

pub(crate) fn cached_iconst(
    b: &mut FunctionBuilder<'_>,
    cache: &mut CodegenCache,
    val: i64,
) -> ir::Value {
    if let Some(blk) = b.current_block() {
        if let Some(&v) = cache.const_cache.get(&(blk, val)) {
            return v;
        }
        let v = b.ins().iconst(types::I64, val);
        cache.const_cache.insert((blk, val), v);
        return v;
    }
    b.ins().iconst(types::I64, val)
}

/// Convert an i8 Cranelift bool to the reserved true/false atom bit patterns.
pub(crate) fn bool_to_fz(
    b: &mut FunctionBuilder<'_>,
    cache: &mut CodegenCache,
    v: ir::Value,
) -> ir::Value {
    let true_v = cached_iconst(b, cache, TRUE_BITS);
    let false_v = cached_iconst(b, cache, FALSE_BITS);
    b.ins().select(v, true_v, false_v)
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelift_codegen::Context;
    use cranelift_codegen::ir::AbiParam;
    use cranelift_jit::{JITBuilder, JITModule};
    use cranelift_module::{Linkage, Module};
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn pinned_register_instructions_verify_for_jit_and_aot_isa() {
        for pic in [false, true] {
            let isa = host_isa_with(pic);
            assert!(isa.flags().enable_pinned_reg());

            let mut sig = Signature::new(isa.default_call_conv());
            sig.params.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));

            let mut ctx = Context::new();
            ctx.func.signature = sig;
            let mut fbctx = FunctionBuilderContext::new();
            {
                let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                b.seal_block(entry);
                let process = b.block_params(entry)[0];
                b.ins().set_pinned_reg(process);
                let observed = b.ins().get_pinned_reg(types::I64);
                b.ins().return_(&[observed]);
                b.finalize();
            }

            cranelift_codegen::verifier::verify_function(&ctx.func, isa.as_ref())
                .expect("pinned-register CLIF should verify");
            let clif = ctx.func.display().to_string();
            assert!(clif.contains("set_pinned_reg"));
            assert!(clif.contains("get_pinned_reg"));
        }
    }

    #[test]
    fn pinned_register_survives_runtime_helper_call() {
        let isa = host_isa();
        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        builder.symbol(
            "fz_yield_slow_path_begin",
            fz_runtime::ir_runtime::fz_yield_slow_path_begin as *const u8,
        );
        let mut module = JITModule::new(builder);

        let yield_slow_path_begin_id = module
            .declare_function("fz_yield_slow_path_begin", Linkage::Import, &sig1(&[], &[]))
            .expect("declare yield slow path helper");
        let probe_id = module
            .declare_function(
                "fz_pinned_runtime_call_probe",
                Linkage::Local,
                &sig1(&[types::I64], &[types::I64]),
            )
            .expect("declare probe");

        let mut fbctx = FunctionBuilderContext::new();
        emit_fn_body(
            &mut module,
            &mut fbctx,
            sig1(&[types::I64], &[types::I64]),
            probe_id,
            |module, b| {
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                b.seal_block(entry);

                let slow_path = module.declare_func_in_func(yield_slow_path_begin_id, b.func);
                b.ins().call(slow_path, &[]);

                let observed = b.ins().get_pinned_reg(types::I64);
                b.ins().return_(&[observed]);
            },
        )
        .expect("define probe");
        module.finalize_definitions().expect("finalize probe");
        let probe_addr = module.get_finalized_function(probe_id);

        let schemas = Rc::new(RefCell::new(fz_runtime::heap::SchemaRegistry::new()));
        let mut process = fz_runtime::process::Process::new(schemas);
        let expected = (&mut process as *mut fz_runtime::process::Process) as u64;
        let _guard = fz_runtime::process::CurrentProcessGuard::install(&mut process);

        let observed = unsafe { fz_runtime::pinned_abi::call1(probe_addr, &mut process, 0) } as u64;
        assert_eq!(observed, expected);
    }
}
