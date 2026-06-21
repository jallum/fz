//! Shared native backend substrate used by compiler2.
//!
//! Compiler2 owns lowering and function code generation in
//! `compiler2::native_codegen`. This module only carries backend ownership,
//! runtime symbol declarations, frame schemas, emitted-module metadata, and
//! CLIF dump controls that are shared by JIT and AOT.

pub(crate) mod aot_main;
pub(crate) mod backend;
pub(crate) mod compiled;
pub(crate) mod error;
pub(crate) mod runtime_syms;
pub(crate) mod schema;
mod support;

pub(crate) use aot_main::*;
pub(crate) use backend::*;
pub(crate) use runtime_syms::*;
pub(crate) use schema::*;
pub(crate) use support::*;

pub use backend::AotArtifact;
pub use compiled::{CompiledMetadata, CompiledModule};
pub use error::CodegenError;
pub use support::{ir_text_record_enable, ir_text_record_enabled, ir_text_record_take};

pub use fz_runtime::process::{PidId, Process, ProcessState};
