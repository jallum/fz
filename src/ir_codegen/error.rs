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

/// Errors from `compile()`. Backend-plumbing failures (cranelift
/// `declare_function` / `define_function` / `finalize_definitions`) carry
/// `Span::DUMMY` because they're internal — no fz source position maps to
/// "cranelift refused to declare a host function". The verify/define
/// per-fn paths populate `span` from `module.source.fn_span_of(f.id)` so
/// the diagnostic underlines the offending fn declaration.
#[derive(Debug, Clone)]
pub struct CodegenError {
    pub message: String,
    pub span: crate::diag::Span,
}
impl CodegenError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            span: crate::diag::Span::DUMMY,
        }
    }
    pub fn with_span(mut self, span: crate::diag::Span) -> Self {
        self.span = span;
        self
    }
    pub fn to_diagnostic(&self) -> crate::diag::Diagnostic {
        crate::diag::Diagnostic::error(
            crate::diag::codes::CODEGEN_SCHEMA_MISSING,
            format!("codegen: {}", self.message),
            self.span,
        )
    }
}
impl std::fmt::Display for CodegenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "codegen: {}", self.message)
    }
}
impl std::error::Error for CodegenError {}
impl From<String> for CodegenError {
    fn from(s: String) -> Self {
        Self::new(s)
    }
}
