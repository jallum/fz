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

pub(crate) use crate::compiler2::Ty;
use crate::telemetry::Telemetry;
pub(crate) use crate::types::{ClosureTypes, LiteralTypes, RenderTypes, Types, VisibilityTypes};

mod call;
mod clif;
pub(crate) mod closure;
mod demand;
pub(crate) mod driver;
pub(crate) mod dump;
pub(crate) mod entry;
pub(crate) mod env;
mod fn_ctx;
mod function;
mod prim;
mod receive;
pub(crate) mod repr;
mod support;
pub(crate) mod surface;
mod terminator;
mod type_pred;
mod value;

// Glob re-exports keep cross-module references resolvable through
// `use super::*;` in each submodule.
pub(crate) use call::*;
pub(crate) use clif::*;
pub(crate) use closure::*;
pub(crate) use demand::*;
pub(crate) use dump::*;
pub(crate) use entry::*;
pub(crate) use env::*;
pub(crate) use fn_ctx::*;
pub(crate) use function::*;
pub(crate) use prim::*;
pub(crate) use repr::*;
pub(crate) use support::*;
pub(crate) use surface::*;
pub(crate) use terminator::*;
pub(crate) use type_pred::*;
pub(crate) use value::*;

pub(crate) use crate::ir_codegen::{
    AotBackend, Backend, BsConstSyms, CodegenError, CompiledMetadata, JitBackend, RuntimeRefs, build_frame_schema,
    declare_runtime_symbols, define_static_sharedbin, runtime_import_sig, sig1,
};

pub(crate) fn compile_with_backend_native_program<
    B: Backend,
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes + VisibilityTypes,
>(
    t: &mut T,
    program: &crate::compiler2::NativeProgram,
    backend: B,
    tel: &dyn Telemetry,
) -> Result<B::Output, CodegenError> {
    driver::compile_with_backend_native_program(t, program, backend, tel)
}
