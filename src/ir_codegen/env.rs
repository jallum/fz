//! CodegenEnv (immutable per-module ctx) and CodegenCache (per-fn caches).

use super::*;
use crate::fz_ir::{BlockId, ExternId, FnId, Module, Var};
use crate::ir_planner::SpecPlan;
use crate::telemetry::Telemetry;
use cranelift_codegen::ir::{self};
use cranelift_module::{DataId, FuncId};
use fz_runtime::any_value::AnyValue;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

pub(crate) struct CodegenEnv<'a> {
    pub(super) telemetry: &'a dyn Telemetry,
    pub(super) runtime: &'a RuntimeRefs,
    pub(super) surface: &'a NativeCodegenSurface<'a>,
    pub(super) module: &'a Module,
    pub(super) fn_types: &'a SpecPlan,
    pub(super) active_spec_id: u32,
    pub(super) active_body_fn_id: FnId,
    pub(super) active_body_name: &'a str,
    pub(super) fn_ids: &'a HashMap<u32, FuncId>,
    pub(super) callable_entry_fn_ids: &'a HashMap<u32, FuncId>,
    pub(super) mid_flight_cont_tail_fn_ids: &'a HashMap<(u32, Vec<MidFlightArgShape>), FuncId>,
    pub(super) tuple_schema_ids: &'a HashMap<usize, u32>,
    pub(super) named_schema_ids: &'a HashMap<String, u32>,
    /// Per-payload symbol cache. Below-threshold payloads carry only
    /// `bytes_id`; above-threshold payloads additionally carry a static
    /// `SharedBin` symbol in `.data`.
    pub(super) bs_const_data: &'a RefCell<HashMap<Vec<u8>, BsConstSyms>>,
    pub(super) param_reprs: &'a [Vec<ArgRepr>],
    pub(super) return_reprs: &'a [ArgRepr],
    pub(super) native_abi_fns: &'a HashSet<FnId>,
    pub(super) cont_target_fns: &'a HashSet<FnId>,
    pub(super) cont_fns: &'a HashSet<FnId>,
    pub(super) closure_capture_counts: &'a HashMap<FnId, usize>,
    /// Number of Tail-CC "extra" params before the trailing `self` closure
    /// ptr. Scheduler-resumed receive continuations use zero extras because
    /// their values are closure-env slots. Unmapped call continuations keep
    /// the normal one-result input shape.
    pub(super) cont_extras_count: &'a HashMap<FnId, usize>,
    /// Receive-dispatch FuncId per ReceiveMatched site, keyed by `(parent_fn_id.0,
    /// block_id.0)`. Populated by the planned codegen declaration pass
    /// and consumed by the Term::ReceiveMatched arm in
    /// `compile_block_terminator` (`fn_addr` -> call site arg).
    pub(super) receive_dispatch_fn_ids: &'a HashMap<(u32, u32), FuncId>,
}

impl<'a> CodegenEnv<'a> {
    pub(super) fn body_key(&self, codegen_id: u32) -> &crate::ir_planner::fn_types::SpecKey {
        self.surface.body_key(codegen_id)
    }

    pub(super) fn body_fn_id(&self, codegen_id: u32) -> FnId {
        self.surface.body_fn_id(codegen_id)
    }

    pub(super) fn body_id_for_key<T: crate::types::Types<Ty = crate::types::Ty>>(
        &self,
        t: &T,
        key: &crate::ir_planner::fn_types::SpecKey,
    ) -> Option<u32> {
        self.surface.body_id_for_key(t, key)
    }
}

#[derive(Clone, Copy)]
pub(crate) enum StaticLiteralField {
    Scalar(AnyValue),
    Struct(DataId),
}

#[derive(Clone)]
pub(crate) struct PendingStaticTupleDest {
    pub(super) schema_id: u32,
    pub(super) fields: Vec<Option<StaticLiteralField>>,
}

#[derive(Clone, Copy)]
pub(crate) struct StaticStructRef {
    pub(super) data_id: DataId,
}

/// Per-function mutable state threaded through `lower_prim` and
/// `emit_terminator`. Holds orthogonal caches and per-spec delivery plans:
///
/// - `const_cache`: per-block constant deduplication (avoids redundant iconst).
/// - `raw_int_consts`: raw i64 value for RawInt vars (drives box-int const fold).
/// - `static_scalar_consts` / `static_struct_refs`: compile-time literal facts
///   for immutable aggregate literals whose storage may be emitted as static
///   data instead of heap construction.
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
    /// Canonical scalar values for source constants keyed by Var ID. These
    /// facts are compile-time data only; dynamic `Known` values are excluded.
    pub(super) static_scalar_consts: HashMap<u32, AnyValue>,
    /// Read-only static struct symbols produced for fully literal aggregate
    /// vars. A later literal aggregate can embed them by data relocation.
    pub(super) static_struct_refs: HashMap<u32, StaticStructRef>,
    /// Per-function counter for unique static struct data symbols.
    pub(super) static_struct_count: usize,
    /// Tuple destinations being considered for static read-only storage.
    pub(super) pending_static_tuple_dests: HashMap<u32, PendingStaticTupleDest>,
    /// Tuple destinations that fell back to ordinary heap storage after a
    /// dynamic field appeared.
    pub(super) materialized_tuple_dests: HashMap<u32, ir::Value>,
    /// FuncRef for each extern, deduplicated per function.
    pub(super) extern_funcs: HashMap<ExternId, ir::FuncRef>,
    /// Var IDs referenced anywhere in the function's IR. Unit-return
    /// extern results whose dest ID is absent here can skip the nil iconst.
    pub(super) used_vars: HashSet<u32>,
    /// Var IDs used exclusively as Term::If conditions — eligible for
    /// lazy bool_to_fz (stored as ArgRepr::Condition, materialised only
    /// if tagged_get is called).
    pub(super) if_only_conds: HashSet<u32>,
    /// Proven list refs already packed in the current block, keyed by fz block
    /// and source Var. CLIF values are only reused inside their defining block.
    pub(super) known_list_refs: HashMap<(BlockId, u32), ir::Value>,
    /// Entry tuple fields delivered as independent Tail-CC params for
    /// ReturnDemand::TupleFields continuation specs. Keyed by the logical
    /// tuple Var and field index, so ordinary TupleField lowering can read
    /// the already-delivered value.
    pub(super) tuple_field_params: HashMap<(u32, u32), CodegenValue>,
    /// Destination tuple vars whose allocation/fill/freeze chain is replaced
    /// by field delivery at Term::Return in this spec.
    pub(super) skipped_tuple_return_vars: HashSet<u32>,
    /// Return var -> field vars for TupleFields(N) specs whose returned tuple
    /// can be delivered to the continuation without materializing a struct.
    pub(super) tuple_return_fields: HashMap<u32, Vec<Var>>,
    /// Head Var -> source cons Var facts for total owned-cons reuse attempts.
    pub(super) owned_cons_reuse_sources: HashMap<u32, Var>,
}
