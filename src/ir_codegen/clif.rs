//! Low-level Cranelift helpers shared by codegen modules.

use super::*;
use crate::compiler::source::Span;
use cranelift_codegen::ir::{self, InstBuilder, Signature, SourceLoc, types};
use cranelift_codegen::isa::TargetIsa;
use cranelift_codegen::settings::{self, Configurable, Flags};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{FuncId, Module, ModuleError};
use cranelift_native::builder;
use std::sync::Arc;

pub(crate) fn host_isa() -> Arc<dyn TargetIsa> {
    host_isa_with(false)
}

/// Build a host ISA. `pic = false` is right for the JIT (no relocations
/// needed inside in-memory code). `pic = true` is required for AOT on
/// macOS, where the linker rejects text relocations in regular
/// executables.
pub(crate) fn host_isa_with(pic: bool) -> Arc<dyn TargetIsa> {
    let mut flag_builder = settings::builder();
    flag_builder.set("opt_level", "speed").unwrap();
    flag_builder.set("is_pic", if pic { "true" } else { "false" }).unwrap();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    // Cranelift's Tail CC implementation asserts frame pointers are present.
    // macOS preserves them by default; Linux does not.
    flag_builder.set("preserve_frame_pointers", "true").unwrap();
    flag_builder.set("enable_pinned_reg", "true").unwrap();
    let isa_builder = builder().expect("host ISA");
    isa_builder.finish(Flags::new(flag_builder)).expect("isa finish")
}

/// Declare `id` in the current function and return its address as an i64.
/// Collapses the ubiquitous `declare_func_in_func` + `func_addr` pair.
pub(crate) fn fn_addr<M: Module>(jmod: &mut M, id: FuncId, b: &mut FunctionBuilder<'_>) -> ir::Value {
    let fref = jmod.declare_func_in_func(id, b.func);
    b.ins().func_addr(types::I64, fref)
}

/// Emit a single Cranelift function: make_context → set sig → build body →
/// finalize → define_function → clear_context. Eliminates the boilerplate
/// repeated for every runtime shim (fz_main_entry, fz_spawn_entry, etc.).
pub(crate) fn emit_fn_body<M: Module>(
    module: &mut M,
    fbctx: &mut FunctionBuilderContext,
    sig: Signature,
    func_id: FuncId,
    body: impl FnOnce(&mut M, &mut FunctionBuilder<'_>),
) -> Result<(), Box<ModuleError>> {
    emit_fn_body_stats(module, fbctx, sig, func_id, body).map(|_| ())
}

pub(crate) fn emit_fn_body_stats<M: Module>(
    module: &mut M,
    fbctx: &mut FunctionBuilderContext,
    sig: Signature,
    func_id: FuncId,
    body: impl FnOnce(&mut M, &mut FunctionBuilder<'_>),
) -> Result<(usize, usize), Box<ModuleError>> {
    let mut ctx = module.make_context();
    ctx.func.signature = sig;
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);
        body(module, &mut b);
        b.finalize();
    }
    let stats = cranelift_body_stats(&ctx.func);
    module.define_function(func_id, &mut ctx).map_err(Box::new)?;
    module.clear_context(&mut ctx);
    Ok(stats)
}

/// Pack a Span into a Cranelift SourceLoc (u32): 8 bits file_id + 24
/// bits start offset. Dummy spans become SourceLoc::default() so they
/// don't generate noise in the dump.
pub(crate) fn span_to_srcloc(s: Span) -> SourceLoc {
    if s.is_dummy() {
        return SourceLoc::default();
    }
    let file = (s.file.0 & 0xFF) << 24;
    let offset = s.start & 0x00FF_FFFF;
    SourceLoc::new(file | offset)
}

pub(crate) fn cached_iconst(b: &mut FunctionBuilder<'_>, cache: &mut CodegenCache, val: i64) -> ir::Value {
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
pub(crate) fn bool_to_fz(b: &mut FunctionBuilder<'_>, cache: &mut CodegenCache, v: ir::Value) -> ir::Value {
    let true_v = cached_iconst(b, cache, TRUE_BITS);
    let false_v = cached_iconst(b, cache, FALSE_BITS);
    b.ins().select(v, true_v, false_v)
}

#[cfg(test)]
#[path = "clif_test.rs"]
mod clif_test;
