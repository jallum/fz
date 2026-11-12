//! Cranelift codegen for fz-IR (CPS form).
//!
//! Every fn has a native signature built per-spec from `ArgRepr` (see
//! `repr.rs`), in the `Tail` calling convention: `(args..., cont) -> i64`, or
//! `(extras..., self) -> i64` for a continuation fn, whose outer continuation
//! lives in its closure env. A return is a tail call through the continuation
//! closure's code pointer; the last continuation in a chain is a halt
//! continuation, which hands the value to the scheduler.

pub(crate) use crate::compiler2::Ty;
use crate::telemetry::RawSpanTelemetry;
pub(crate) use crate::types::{ClosureTypes, LiteralTypes, RenderTypes, Types};

mod clif;
pub(crate) mod closure;
mod delivery;
pub(crate) mod driver;
pub(crate) mod entry;
pub(crate) mod env;
mod fn_ctx;
mod function;
mod prim;
mod receive;
pub(crate) mod repr;
pub(crate) mod runtime_call;
mod runtime_test;
mod static_object;
mod support;
pub(crate) mod surface;
mod terminator;
mod type_pred;
mod value;
pub(crate) mod variadic;

// Glob re-exports keep cross-module references resolvable through
// `use super::*;` in each submodule.
pub(crate) use clif::*;
pub(crate) use closure::*;
pub(crate) use delivery::*;
pub(crate) use driver::LocalBodies;
pub(crate) use entry::*;
pub(crate) use env::*;
pub(crate) use fn_ctx::*;
pub(crate) use function::*;
pub(crate) use prim::*;
pub(crate) use repr::*;
pub(crate) use runtime_call::*;
pub(crate) use static_object::*;
pub(crate) use support::*;
pub(crate) use surface::*;
pub(crate) use terminator::*;
pub(crate) use type_pred::*;
pub(crate) use value::*;
pub(crate) use variadic::*;

pub(crate) use crate::ir_codegen::{
    AotBackend, Backend, BsConstSyms, CodegenError, CompiledMetadata, JitBackend, define_static_sharedbin,
};

pub(crate) fn compile_with_backend_native_program<
    B: Backend,
    T: Types<Ty = Ty> + ClosureTypes + LiteralTypes + RenderTypes,
>(
    t: &mut T,
    program: &crate::compiler2::NativeProgram,
    backend: B,
    tel: &impl RawSpanTelemetry,
    output: &mut dyn super::dump::RequestedOutputSink,
) -> Result<B::Output, CodegenError> {
    driver::compile_with_backend_native_program(t, program, backend, tel, output)
}
