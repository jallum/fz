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

/// Build a [cont_ptr, ...entry_params] frame schema. The cont_ptr slot is
/// always `AnyValue`; the param slots are described by `param_kinds`.
pub(crate) fn build_frame_schema(name: &str, param_kinds: &[FieldKind]) -> Schema {
    let n_fields = 1 + param_kinds.len();
    let mut fields = Vec::with_capacity(n_fields);
    fields.push(FieldDescriptor {
        offset: 0,
        kind: FieldKind::AnyValue,
        name: None,
    });
    for (i, k) in param_kinds.iter().enumerate() {
        fields.push(FieldDescriptor {
            offset: ((i + 1) * SLOT_BYTES as usize) as u32,
            kind: k.clone(),
            name: None,
        });
    }
    Schema {
        name: format!("Frame_{}", name),
        size: HEADER_SIZE as u32 + (n_fields as u32) * SLOT_BYTES as u32,
        fields,
    }
}
