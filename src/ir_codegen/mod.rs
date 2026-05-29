//! Cranelift codegen for fz-IR (CPS form).
//!
//! Uniform-tier per-fn ABI:
//!   `extern "C" fn(frame_ptr: *mut u8, host_ctx: *mut u8) -> *mut u8`
//!   * `frame_ptr` points to a heap-allocated frame with 16 bytes of
//!     object-local metadata followed by slots. Slot 0 = continuation
//!     pointer. Slots 1..N+1 = entry params for this fn.
//!   * `host_ctx` is an opaque pointer the host (trampoline) supplies.
//!     Halt writes the final value through it.
//!   * Return value: the next frame pointer to invoke (the trampoline
//!     calls it next), or null to halt.
//!
//! Frame schema is the source of truth for codegen + the GC tracer:
//! [cont_ptr, ...entry_params], all StoredValue slots.
//!
//! Native-tier fns bypass the trampoline; their ABI is built per-spec
//! from ArgRepr (see `repr.rs`).

#![allow(unused_imports)]

use crate::fz_ir::Module;
pub(crate) use crate::spec_registry::SpecRegistry;

pub(crate) mod aot_main;
pub(crate) mod backend;
mod call;
mod clif;
pub(crate) mod closure;
pub(crate) mod compiled;
mod demand;
pub(crate) mod driver;
pub(crate) mod dump;
pub(crate) mod entry;
pub(crate) mod env;
pub(crate) mod error;
mod fn_ctx;
mod function;
#[cfg(debug_assertions)]
mod invariants;
mod prim;
mod receive;
pub(crate) mod repr;
pub(crate) mod runtime_syms;
pub(crate) mod schema;
mod support;
mod terminator;
mod type_pred;
mod value;

// Glob re-exports keep cross-module references resolvable through
// `use super::*;` in each submodule.
pub(crate) use aot_main::*;
pub(crate) use backend::*;
pub(crate) use call::*;
pub(crate) use clif::*;
pub(crate) use closure::*;
pub(crate) use compiled::*;
pub(crate) use demand::*;
pub(crate) use driver::*;
pub(crate) use dump::*;
pub(crate) use entry::*;
pub(crate) use env::*;
pub(crate) use error::*;
pub(crate) use fn_ctx::*;
pub(crate) use function::*;
pub(crate) use prim::*;
pub(crate) use repr::*;
pub(crate) use runtime_syms::*;
pub(crate) use schema::*;
pub(crate) use support::*;
pub(crate) use terminator::*;
pub(crate) use type_pred::*;
pub(crate) use value::*;

// Public surface preserved for `crate::ir_codegen::*` callers.
pub use compiled::{
    CompiledImage, CompiledMetadata, CompiledModule, CompiledProgram, CompiledUnit, ImageLinkError,
    RuntimeEntrypoints, RuntimeImageMetadata, RuntimeMetadataLinkError, RuntimeStaticClosure,
    RuntimeUnitMetadata, RuntimeUnitRelocations,
};
pub use error::CodegenError;
pub use support::{asm_record_enable, asm_record_take, ir_text_record_enable, ir_text_record_take};

pub use fz_runtime::process::{PidId, Process, ProcessState};

/// Drive the shared compile pipeline through any Backend impl. JIT and
/// AOT both route through here; the backend's hooks pick the legit
/// variation points (linkage, per-program metadata carriers, finalize).
///
/// The pipeline re-plans the linked working module internally (see
/// `compile_with_backend_impl`), so there is no caller-supplied pre-types
/// plan to thread — a frontend plan cannot see linked provider bodies.
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
    compile_with_backend_impl(t, module, backend, tel)
}

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

#[cfg(test)]
mod tests;
