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

pub(crate) struct CodegenEnv<'a> {
    runtime: &'a RuntimeRefs,
    module: &'a crate::fz_ir::Module,
    fn_types: &'a crate::ir_typer::FnTypes,
    spec_registry: &'a SpecRegistry,
    fn_ids: &'a HashMap<u32, FuncId>,
    mid_flight_cont_tail_fn_ids: &'a HashMap<(u32, Vec<MidFlightArgShape>), FuncId>,
    spec_heap_allocates: &'a [bool],
    tuple_schema_ids: &'a HashMap<usize, u32>,
    /// fz-q8d.2 — per-payload symbol cache. Below-threshold payloads
    /// carry only `bytes_id`; above-threshold payloads additionally carry
    /// a static `SharedBin` symbol in `.data`.
    bs_const_data: &'a std::cell::RefCell<HashMap<Vec<u8>, BsConstSyms>>,
    param_reprs: &'a [Vec<ArgRepr>],
    return_reprs: &'a [ArgRepr],
    natively_callable: &'a std::collections::HashSet<crate::fz_ir::FnId>,
    cont_target_fns: &'a std::collections::HashSet<crate::fz_ir::FnId>,
    cont_fns: &'a std::collections::HashSet<crate::fz_ir::FnId>,
    closure_n_captures: &'a std::collections::HashMap<crate::fz_ir::FnId, usize>,
    /// Number of Tail-CC "extra" params before the trailing `self` closure
    /// ptr. Scheduler-resumed receive continuations use zero extras because
    /// their values are closure-env slots. Unmapped call continuations keep
    /// the normal one-result input shape.
    cont_extras_count: &'a std::collections::HashMap<crate::fz_ir::FnId, usize>,
    /// fz-70q.3 — matcher FuncId per ReceiveMatched site, keyed by
    /// `(parent_fn_id.0, block_id.0)`. Populated by the pre-pass in
    /// `compile_with_backend` and consumed by the Term::ReceiveMatched
    /// arm in `compile_block_terminator` (`fn_addr` → call site arg).
    matcher_fn_ids: &'a std::collections::HashMap<(u32, u32), FuncId>,
}

/// Per-function mutable state threaded through `lower_prim` and
/// `emit_terminator`. Holds five orthogonal caches:
///
/// - `const_cache`: per-block constant deduplication (avoids redundant iconst).
/// - `raw_int_consts`: raw i64 value for RawInt vars (drives box-int const fold).
/// - `extern_funcs`: FuncRef deduplicated per extern symbol per function.
/// - `used_vars`: all var IDs that appear as operands anywhere in the function;
///   unit-return extern results whose dest ID is absent skip the nil iconst.
/// - `if_only_conds`: var IDs used exclusively as Term::If conditions; their
///   boolean prims emit ArgRepr::Condition (raw i1) instead of bool_to_fz, so
///   the tagged form is never materialised and brif consumes the i1 directly.
#[derive(Default)]
pub(crate) struct CodegenCache {
    /// Cranelift values for small integer/atom constants, keyed by (block, value)
    /// so entries from sibling blocks are never reused (fz-bwp).
    const_cache: HashMap<(ir::Block, i64), ir::Value>,
    /// Raw (unboxed) i64 values for integer constants keyed by Var ID (fz-zj3).
    raw_int_consts: HashMap<u32, i64>,
    /// FuncRef for each extern, deduplicated per function (fz-0uu).
    extern_funcs: HashMap<crate::fz_ir::ExternId, ir::FuncRef>,
    /// Var IDs referenced anywhere in the function's IR (fz-2tc). Unit-return
    /// extern results whose dest ID is absent here can skip the nil iconst.
    used_vars: std::collections::HashSet<u32>,
    /// Var IDs used exclusively as Term::If conditions — eligible for lazy
    /// bool_to_fz (stored as ArgRepr::Condition, materialised only if tagged_get
    /// is called) (fz-h4q).
    if_only_conds: std::collections::HashSet<u32>,
    /// Proven list refs already packed in the current block, keyed by fz block
    /// and source Var. CLIF values are only reused inside their defining block.
    known_list_refs: HashMap<(crate::fz_ir::BlockId, u32), ir::Value>,
}

