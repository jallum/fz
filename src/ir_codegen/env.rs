//! CodegenEnv (immutable per-module ctx) and CodegenCache (per-fn caches).

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
    pub(super) telemetry: &'a dyn crate::telemetry::Telemetry,
    pub(super) runtime: &'a RuntimeRefs,
    pub(super) module: &'a crate::fz_ir::Module,
    pub(super) fn_types: &'a crate::ir_planner::SpecPlan,
    pub(super) active_spec_id: u32,
    pub(super) active_body_fn_id: crate::fz_ir::FnId,
    pub(super) active_body_name: &'a str,
    pub(super) spec_registry: &'a SpecRegistry,
    pub(super) fn_ids: &'a HashMap<u32, FuncId>,
    pub(super) callable_entry_fn_ids: &'a HashMap<u32, FuncId>,
    pub(super) mid_flight_cont_tail_fn_ids: &'a HashMap<(u32, Vec<MidFlightArgShape>), FuncId>,
    pub(super) tuple_schema_ids: &'a HashMap<usize, u32>,
    pub(super) named_schema_ids: &'a HashMap<String, u32>,
    /// Per-payload symbol cache. Below-threshold payloads carry only
    /// `bytes_id`; above-threshold payloads additionally carry a static
    /// `SharedBin` symbol in `.data`.
    pub(super) bs_const_data: &'a std::cell::RefCell<HashMap<Vec<u8>, BsConstSyms>>,
    pub(super) param_reprs: &'a [Vec<ArgRepr>],
    pub(super) return_reprs: &'a [ArgRepr],
    pub(super) spec_keys: &'a [crate::ir_planner::fn_types::SpecKey],
    pub(super) native_abi_fns: &'a std::collections::HashSet<crate::fz_ir::FnId>,
    pub(super) cont_target_fns: &'a std::collections::HashSet<crate::fz_ir::FnId>,
    pub(super) cont_fns: &'a std::collections::HashSet<crate::fz_ir::FnId>,
    pub(super) closure_capture_counts: &'a std::collections::HashMap<crate::fz_ir::FnId, usize>,
    /// Number of Tail-CC "extra" params before the trailing `self` closure
    /// ptr. Scheduler-resumed receive continuations use zero extras because
    /// their values are closure-env slots. Unmapped call continuations keep
    /// the normal one-result input shape.
    pub(super) cont_extras_count: &'a std::collections::HashMap<crate::fz_ir::FnId, usize>,
    /// Matcher FuncId per ReceiveMatched site, keyed by `(parent_fn_id.0,
    /// block_id.0)`. Populated by the pre-pass in `compile_with_backend`
    /// and consumed by the Term::ReceiveMatched arm in
    /// `compile_block_terminator` (`fn_addr` -> call site arg).
    pub(super) matcher_fn_ids: &'a std::collections::HashMap<(u32, u32), FuncId>,
}

/// Per-function mutable state threaded through `lower_prim` and
/// `emit_terminator`. Holds orthogonal caches and per-spec delivery plans:
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
    /// Cranelift values for small integer/atom constants, keyed by
    /// (block, value) so entries from sibling blocks are never reused.
    pub(super) const_cache: HashMap<(ir::Block, i64), ir::Value>,
    /// Raw (unboxed) i64 values for integer constants keyed by Var ID.
    pub(super) raw_int_consts: HashMap<u32, i64>,
    /// FuncRef for each extern, deduplicated per function.
    pub(super) extern_funcs: HashMap<crate::fz_ir::ExternId, ir::FuncRef>,
    /// Var IDs referenced anywhere in the function's IR. Unit-return
    /// extern results whose dest ID is absent here can skip the nil iconst.
    pub(super) used_vars: std::collections::HashSet<u32>,
    /// Var IDs used exclusively as Term::If conditions — eligible for
    /// lazy bool_to_fz (stored as ArgRepr::Condition, materialised only
    /// if tagged_get is called).
    pub(super) if_only_conds: std::collections::HashSet<u32>,
    /// Proven list refs already packed in the current block, keyed by fz block
    /// and source Var. CLIF values are only reused inside their defining block.
    pub(super) known_list_refs: HashMap<(crate::fz_ir::BlockId, u32), ir::Value>,
    /// Entry tuple fields delivered as independent Tail-CC params for
    /// ReturnDemand::TupleFields continuation specs. Keyed by the logical
    /// tuple Var and field index, so ordinary TupleField lowering can read
    /// the already-delivered value.
    pub(super) tuple_field_params: HashMap<(u32, u32), CodegenValue>,
    /// Destination tuple vars whose allocation/fill/freeze chain is replaced
    /// by field delivery at Term::Return in this spec.
    pub(super) skipped_tuple_return_vars: std::collections::HashSet<u32>,
    /// Return var -> field vars for TupleFields(N) specs whose returned tuple
    /// can be delivered to the continuation without materializing a struct.
    pub(super) tuple_return_fields: HashMap<u32, Vec<crate::fz_ir::Var>>,
    /// Hidden destination tail parameter for ReturnDemand::ListTail specs.
    /// This is a physical ABI value, not a logical fz entry parameter.
    pub(super) list_tail_param: Option<ir::Value>,
    /// Return var -> element vars for ListTail specs whose returned list
    /// literal can be rebuilt directly in front of the hidden tail.
    pub(super) list_tail_return_elems: HashMap<u32, Vec<crate::fz_ir::Var>>,
    /// MakeList return vars whose normal lowering is skipped because
    /// Term::Return rebuilds them onto the ListTail destination.
    pub(super) skipped_list_tail_return_vars: std::collections::HashSet<u32>,
    /// Head Var -> source cons Var facts for total owned-cons reuse attempts.
    pub(super) owned_cons_reuse_sources: HashMap<u32, crate::fz_ir::Var>,
}
