//! Cranelift codegen for fz-IR (CPS form).
//!
//! Per-fz-IR-fn ABI: `extern "C" fn(frame_ptr: *mut u8, host_ctx: *mut u8) -> *mut u8`
//!   * `frame_ptr` points to a heap-allocated frame with 16 bytes of
//!     object-local metadata followed by slots.
//!     Slot 0 = continuation pointer. Slots 1..N+1 = entry params for this fn.
//!   * `host_ctx` is an opaque pointer the host (trampoline) supplies. Halt
//!     writes the final value through it.
//!   * Return value: the next frame pointer to invoke (the trampoline calls
//!     it next), or null to halt.
//!
//! Frame schema is regenerated here as the source of truth for codegen + the
//! GC tracer: [cont_ptr, ...entry_params], all StoredValue slots. (Replaces the
//! placeholder schema computed in .11.6.)
//!
//! .11.8 scope additions over .11.7: Term::Call (allocates continuation frame
//!   + callee frame), Term::TailCall (frame reuse when callee shares schema,
//!     else fresh alloc), Term::Return (writes result into continuation frame's
//!     result slot or halts on null), real trampoline. Out of scope:
//!     Term::CallClosure / TailCallClosure (closure invocation needs heap-typed
//!     closures — lands later), and heap-typed prims (.11.10+).

// fz-ame.7 — split into focused submodules. Public surface is preserved
// by re-export below.

#![allow(unused_imports)]

use crate::fz_ir::Module;
pub(crate) use crate::spec_registry::SpecRegistry;

pub(crate) mod aot_main;
pub(crate) mod backend;
mod call;
mod clif;
pub(crate) mod closure;
pub(crate) mod compiled;
pub(crate) mod driver;
pub(crate) mod dump;
pub(crate) mod entry;
pub(crate) mod env;
pub(crate) mod error;
#[cfg(debug_assertions)]
mod invariants;
mod prim;
mod receive;
pub(crate) mod repr;
pub(crate) mod runtime_syms;
pub(crate) mod schema;
mod type_pred;
mod value;

// Glob re-exports keep cross-module references resolvable through
// `use super::*;` in each submodule. This is the mechanical split's seam;
// fz-ame.8 may tighten individual symbol visibility post-integration.
pub(crate) use aot_main::*;
pub(crate) use backend::*;
pub(crate) use call::*;
pub(crate) use clif::*;
pub(crate) use closure::*;
pub(crate) use compiled::*;
pub(crate) use driver::*;
pub(crate) use dump::*;
pub(crate) use entry::*;
pub(crate) use env::*;
pub(crate) use error::*;
pub(crate) use prim::*;
pub(crate) use repr::*;
pub(crate) use runtime_syms::*;
pub(crate) use schema::*;
pub(crate) use type_pred::*;
pub(crate) use value::*;

// Public surface preserved for `crate::ir_codegen::*` callers.
pub use compiled::{CompiledMetadata, CompiledModule};
pub use driver::{asm_record_enable, asm_record_take, ir_text_record_enable, ir_text_record_take};
#[cfg(test)]
pub use driver::{heap_reset_for_test, test_capture_take};
pub use error::CodegenError;

pub use fz_runtime::process::{CURRENT_PROCESS, PidId, Process, ProcessState};
#[cfg(test)]
pub(crate) use fz_runtime::process::{DEFAULT_PROCESS, current_process};

// Runtime FFI fns called from JIT'd code now live in src/ir_runtime.rs.
// Value rendering lives in fz_runtime::fz_value::debug (fz-ul4.23.4.3).

/// Drive the shared compile pipeline through any Backend impl. JIT and
/// AOT both route through here; the backend's hooks pick the legit
/// variation points (linkage, per-program metadata carriers, finalize).
///
/// fz-ul4.23.12. Before this, `compile()` and `compile_aot()` duplicated
/// ~90% of the pipeline side by side. Now they're each ~5-line wrappers
/// constructing a backend and calling here.
#[cfg(test)]
pub fn compile_with_backend<
    B: Backend,
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::LiteralTypes
        + crate::types::RenderTypes
        + crate::types::VisibilityTypes,
>(
    t: &mut T,
    module: &Module,
    backend: B,
    tel: &dyn crate::telemetry::Telemetry,
) -> Result<B::Output, CodegenError> {
    compile_with_backend_impl(t, module, backend, None, tel)
}

pub fn compile_with_backend_pretyped<
    B: Backend,
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::LiteralTypes
        + crate::types::RenderTypes
        + crate::types::VisibilityTypes,
>(
    t: &mut T,
    module: &Module,
    backend: B,
    pre_types: &crate::ir_typer::ModuleTypes,
    tel: &dyn crate::telemetry::Telemetry,
) -> Result<B::Output, CodegenError> {
    compile_with_backend_impl(t, module, backend, Some(pre_types), tel)
}

#[cfg(test)]
pub fn compile<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::LiteralTypes
        + crate::types::RenderTypes
        + crate::types::VisibilityTypes,
>(
    t: &mut T,
    module: &Module,
    tel: &dyn crate::telemetry::Telemetry,
) -> Result<CompiledModule, CodegenError> {
    compile_with_backend(t, module, JitBackend::new(), tel)
}

pub fn compile_pretyped<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::LiteralTypes
        + crate::types::RenderTypes
        + crate::types::VisibilityTypes,
>(
    t: &mut T,
    module: &Module,
    pre_types: &crate::ir_typer::ModuleTypes,
    tel: &dyn crate::telemetry::Telemetry,
) -> Result<CompiledModule, CodegenError> {
    compile_with_backend_pretyped(t, module, JitBackend::new(), pre_types, tel)
}

#[cfg(test)]
pub fn compile_aot<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::LiteralTypes
        + crate::types::RenderTypes
        + crate::types::VisibilityTypes,
>(
    t: &mut T,
    module: &Module,
    obj_name: &str,
    tel: &dyn crate::telemetry::Telemetry,
) -> Result<AotArtifact, CodegenError> {
    compile_with_backend(t, module, AotBackend::new(obj_name), tel)
}

pub fn compile_aot_pretyped<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::LiteralTypes
        + crate::types::RenderTypes
        + crate::types::VisibilityTypes,
>(
    t: &mut T,
    module: &Module,
    pre_types: &crate::ir_typer::ModuleTypes,
    obj_name: &str,
    tel: &dyn crate::telemetry::Telemetry,
) -> Result<AotArtifact, CodegenError> {
    compile_with_backend_pretyped(t, module, AotBackend::new(obj_name), pre_types, tel)
}

#[cfg(test)]
mod tests;
