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

pub(crate) use crate::frontend::spec_registry::SpecRegistry;
use crate::fz_ir::Module;
use crate::ir_planner::ModulePlan;
use crate::ir_planner::planned::PlannedProgram;
use crate::telemetry::Telemetry;
use crate::types::{ClosureTypes, LiteralTypes, RenderTypes, Ty, Types, VisibilityTypes};

pub(crate) mod abi_facts;
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
pub(crate) use abi_facts::AbiFacts;
pub(crate) use aot_main::*;
pub(crate) use backend::*;
pub(crate) use call::*;
pub(crate) use clif::*;
pub(crate) use closure::*;
pub(crate) use compiled::*;
pub(crate) use demand::*;
pub(crate) use dump::*;
pub(crate) use entry::*;
pub(crate) use env::*;
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
pub use compiled::{CompiledImage, CompiledMetadata, CompiledModule, CompiledProgram, CompiledUnit, ImageLinkError};
pub use error::CodegenError;
pub use support::{asm_record_enable, asm_record_take, ir_text_record_enable, ir_text_record_take};

pub use fz_runtime::process::{PidId, Process, ProcessState};

pub(crate) fn compile_with_backend_prepared<
    B: Backend,
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes + VisibilityTypes,
>(
    t: &mut T,
    working: &Module,
    working_module_plan: &ModulePlan,
    planned_program: &PlannedProgram,
    abi_facts: &AbiFacts,
    backend: B,
    tel: &dyn Telemetry,
) -> Result<B::Output, CodegenError> {
    driver::compile_with_backend_prepared(
        t,
        working,
        working_module_plan,
        planned_program,
        abi_facts,
        backend,
        tel,
    )
}

#[cfg(test)]
pub(crate) fn compile_with_backend_planned<
    B: Backend,
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes + VisibilityTypes,
>(
    t: &mut T,
    module: &Module,
    module_plan: &ModulePlan,
    backend: B,
    tel: &dyn Telemetry,
) -> Result<B::Output, CodegenError> {
    driver::compile_with_backend_preplanned(t, module, module_plan, backend, tel)
}

#[cfg(test)]
pub(crate) fn compile_planned<T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes + VisibilityTypes>(
    t: &mut T,
    module: &Module,
    module_plan: &ModulePlan,
    tel: &dyn Telemetry,
) -> Result<CompiledModule, CodegenError> {
    compile_with_backend_planned(t, module, module_plan, JitBackend::new(), tel)
}

#[cfg(test)]
pub(crate) fn compile_aot_planned<T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes + VisibilityTypes>(
    t: &mut T,
    module: &Module,
    module_plan: &ModulePlan,
    obj_name: &str,
    tel: &dyn Telemetry,
) -> Result<AotArtifact, CodegenError> {
    compile_with_backend_planned(t, module, module_plan, AotBackend::new(obj_name), tel)
}

#[cfg(test)]
mod ir_codegen_test;
