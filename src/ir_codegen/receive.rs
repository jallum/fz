//! Selective-receive dispatch fn codegen.
//!
//! Emits the leaf dispatch fn for a `Term::ReceiveMatched`. The runtime
//! ABI matches `fz_runtime::park::MatcherFn` (see runtime/src/park.rs):
//!
//! ```text
//! extern "C" fn(msg_ref: u64, pinned: *const AnyValueRef, out: *mut AnyValueRef) -> u32
//! ```
//!
//! - `msg_ref`: one-word tagged candidate message.
//! - `pinned`: pointer to `AnyValueRef` entries, in the order
//!   they appear in `Term::ReceiveMatched::pinned`.
//! - `out`: caller-supplied `[AnyValueRef; bound_arity]`
//!   scratch buffer; the dispatch writes the winning clause's bound-var
//!   values here.
//! - returns `0` on miss; `k > 0` is the 1-based clause index (caller
//!   indexes `clause_bodies[k-1]`).
//!
//! Production codegen consumes the cached AST-free `PatternDispatchPlan`
//! attached to `Term::ReceiveMatched`; it does not rebuild source clauses.

use crate::dispatch_matrix::pattern::{
    PatternDispatchPlan, PatternGuardBinOp, PatternGuardDispatch, PatternGuardExpr, PatternGuardUnaryOp,
    prepared_key_name,
};
use crate::dispatch_matrix::{
    BitstringEndian, BitstringFieldKind, BitstringFieldSize, BitstringShape, ComparisonValue, DispatchConst,
    DispatchNode, EdgeEvidence, GraphNodeId, ListRegion, PinnedValueId, ProjectionKind, Region, SubjectId,
    SubjectSource,
};
use crate::fz_ir::{Module, ReceiveClause, Var};
use crate::ir_codegen::{CodegenError, SLOT_BYTES, emit_fn_body_stats};
use crate::runtime_type_predicate::{ListShape, ObservedSet, RuntimeTypePredicate};
use cranelift_codegen::ir::{self, AbiParam, InstBuilder, MemFlags, Signature, condcodes::IntCC, types};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage};
use fz_runtime::any_value::{AnyValueRef, FALSE_ATOM_ID, NIL_ATOM_ID, TRUE_ATOM_ID, ValueKind};
use fz_runtime::ir_runtime::fz_bs_field_spec;
use std::collections::HashMap;

type ReceiveDispatchPlan = PatternDispatchPlan<RuntimeTypePredicate>;
type ReceiveRegion = Region<RuntimeTypePredicate>;
type ReceiveEdgeEvidence = EdgeEvidence<RuntimeTypePredicate>;
type ReceiveGuardExpr = PatternGuardExpr<RuntimeTypePredicate>;
type ReceiveGuardDispatch = PatternGuardDispatch<RuntimeTypePredicate>;

/// Cranelift signature for the receive dispatch fn family. Matches
/// `fz_runtime::park::MatcherFn`.
pub(crate) fn receive_dispatch_signature() -> Signature {
    let mut sig = Signature::new(CallConv::SystemV);
    sig.params.push(AbiParam::new(types::I64)); // process (*mut Process)
    sig.params.push(AbiParam::new(types::I64)); // msg_ref
    sig.params.push(AbiParam::new(types::I64)); // pinned_ptr
    sig.params.push(AbiParam::new(types::I64)); // out_ptr
    sig.returns.push(AbiParam::new(types::I32));
    sig
}

/// Declare a receive dispatch fn in `module`.
pub(crate) fn declare_receive_dispatch<M: cranelift_module::Module>(
    module: &mut M,
    name: &str,
) -> Result<FuncId, CodegenError> {
    module
        .declare_function(name, Linkage::Local, &receive_dispatch_signature())
        .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))
}

/// Optional runtime helper `FuncId`s required to emit the receive ABI
/// dispatch body. Each field corresponds to a `fz_runtime` helper that the
/// dispatch may call depending on the patterns it encounters; missing helpers
/// turn into specific `CodegenError`s if dispatch needs them.
#[derive(Clone, Copy)]
pub(crate) struct DispatchRuntimeHelpers {
    pub value_eq_typed_id: Option<FuncId>,
    pub matcher_eq_bytes_id: Option<FuncId>,
    pub matcher_map_get_id: Option<FuncId>,
    pub matcher_map_get_ref_id: Option<FuncId>,
    pub type_of_id: Option<FuncId>,
    pub unbox_int_id: Option<FuncId>,
    pub unbox_float_id: Option<FuncId>,
    pub unbox_atom_id: Option<FuncId>,
    pub struct_schema_id_ref_id: Option<FuncId>,
    pub truthy_ref_id: Option<FuncId>,
    pub box_int_for_any_id: Option<FuncId>,
    pub box_float_for_any_id: Option<FuncId>,
    pub box_atom_for_any_id: Option<FuncId>,
    pub map_is_map_id: Option<FuncId>,
    pub bs_reader_init_id: Option<FuncId>,
    pub bs_read_field_id: Option<FuncId>,
    pub struct_get_field_id: Option<FuncId>,
    pub list_is_cons_id: Option<FuncId>,
    pub list_head_id: Option<FuncId>,
    pub list_tail_id: Option<FuncId>,
}

/// Per-function-body `FuncRef`s for the runtime helpers in
/// [`DispatchRuntimeHelpers`], obtained by `declare_func_in_func` on the
/// dispatch function builder.
#[derive(Clone, Copy)]
struct DispatchRuntimeRefs {
    value_eq_typed_fref: Option<ir::FuncRef>,
    matcher_eq_bytes_fref: Option<ir::FuncRef>,
    // Carried for API parity with `DispatchRuntimeHelpers::matcher_map_get_id`;
    // current emit paths use the `_ref` variant instead.
    #[allow(dead_code)]
    matcher_map_get_fref: Option<ir::FuncRef>,
    matcher_map_get_ref_fref: Option<ir::FuncRef>,
    type_of_fref: Option<ir::FuncRef>,
    unbox_int_fref: Option<ir::FuncRef>,
    unbox_float_fref: Option<ir::FuncRef>,
    unbox_atom_fref: Option<ir::FuncRef>,
    struct_schema_id_ref_fref: Option<ir::FuncRef>,
    truthy_ref_fref: Option<ir::FuncRef>,
    box_int_for_any_fref: Option<ir::FuncRef>,
    box_float_for_any_fref: Option<ir::FuncRef>,
    box_atom_for_any_fref: Option<ir::FuncRef>,
    map_is_map_fref: Option<ir::FuncRef>,
    bs_reader_init_fref: Option<ir::FuncRef>,
    bs_read_field_fref: Option<ir::FuncRef>,
    struct_get_field_fref: Option<ir::FuncRef>,
    list_is_cons_fref: Option<ir::FuncRef>,
    list_head_fref: Option<ir::FuncRef>,
    list_tail_fref: Option<ir::FuncRef>,
}

/// Emit the receive ABI dispatch directly from the cached AST-free
/// [`PatternDispatchPlan`]. The clause slice is still used for ABI metadata
/// (`bound_names`), but matching control flow comes from the dispatch graph.
pub(crate) fn emit_receive_dispatch_body<M: cranelift_module::Module>(
    module: &mut M,
    fbctx: &mut FunctionBuilderContext,
    dispatch_id: FuncId,
    fz_module: &Module,
    tuple_schema_ids: &HashMap<usize, u32>,
    named_schema_ids: &HashMap<String, u32>,
    pinned: &[(String, Var)],
    clauses: &[ReceiveClause],
    dispatch: &ReceiveDispatchPlan,
    helpers: &DispatchRuntimeHelpers,
) -> Result<(usize, usize), CodegenError> {
    let DispatchRuntimeHelpers {
        value_eq_typed_id,
        matcher_eq_bytes_id,
        matcher_map_get_id,
        matcher_map_get_ref_id,
        type_of_id,
        unbox_int_id,
        unbox_float_id,
        unbox_atom_id,
        struct_schema_id_ref_id,
        truthy_ref_id,
        box_int_for_any_id,
        box_float_for_any_id,
        box_atom_for_any_id,
        map_is_map_id,
        bs_reader_init_id,
        bs_read_field_id,
        struct_get_field_id,
        list_is_cons_id,
        list_head_id,
        list_tail_id,
    } = *helpers;
    let pinned_indices: HashMap<String, usize> = pinned.iter().enumerate().map(|(i, (n, _))| (n.clone(), i)).collect();
    let bound_indices_per_clause: Vec<HashMap<String, usize>> = clauses
        .iter()
        .map(|c| c.bound_names.iter().enumerate().map(|(i, n)| (n.clone(), i)).collect())
        .collect();

    let mut unique_bytes = Vec::new();
    collect_binary_literals_in_dispatch(dispatch, &mut unique_bytes);
    let mut binary_data_ids: HashMap<Vec<u8>, DataId> = HashMap::new();
    for (idx, bytes) in unique_bytes.into_iter().enumerate() {
        if binary_data_ids.contains_key(&bytes) {
            continue;
        }
        let name = format!(".fz_dispatch_bin_{}_{}", dispatch_id.as_u32(), idx);
        let did = module
            .declare_data(&name, Linkage::Local, false, false)
            .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))?;
        let mut desc = DataDescription::new();
        desc.define(bytes.clone().into_boxed_slice());
        desc.set_align(1);
        module
            .define_data(did, &desc)
            .map_err(|e| CodegenError::new(format!("define {}: {}", name, e)))?;
        binary_data_ids.insert(bytes, did);
    }

    let mut compile_err: Option<CodegenError> = None;
    let stats = emit_fn_body_stats(module, fbctx, receive_dispatch_signature(), dispatch_id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let process = b.block_params(entry)[0];
        let msg_ref = b.block_params(entry)[1];
        let pinned_ptr = b.block_params(entry)[2];
        let out_ptr = b.block_params(entry)[3];
        let msg = receive_value_from_ref_word(b, msg_ref);

        let miss_block = b.create_block();
        let binary_data_gvs: HashMap<Vec<u8>, ir::GlobalValue> = binary_data_ids
            .iter()
            .map(|(bytes, did)| (bytes.clone(), m.declare_data_in_func(*did, b.func)))
            .collect();
        let runtime = DispatchRuntimeRefs {
            value_eq_typed_fref: value_eq_typed_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            matcher_eq_bytes_fref: matcher_eq_bytes_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            matcher_map_get_fref: matcher_map_get_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            matcher_map_get_ref_fref: matcher_map_get_ref_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            type_of_fref: type_of_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            unbox_int_fref: unbox_int_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            unbox_float_fref: unbox_float_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            unbox_atom_fref: unbox_atom_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            struct_schema_id_ref_fref: struct_schema_id_ref_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            truthy_ref_fref: truthy_ref_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            box_int_for_any_fref: box_int_for_any_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            box_float_for_any_fref: box_float_for_any_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            box_atom_for_any_fref: box_atom_for_any_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            map_is_map_fref: map_is_map_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            bs_reader_init_fref: bs_reader_init_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            bs_read_field_fref: bs_read_field_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            struct_get_field_fref: struct_get_field_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            list_is_cons_fref: list_is_cons_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            list_head_fref: list_head_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            list_tail_fref: list_tail_id.map(|fid| m.declare_func_in_func(fid, b.func)),
        };

        let ctx = DispatchCtx {
            process,
            fz_module,
            tuple_schema_ids,
            named_schema_ids,
            bound_indices_per_clause: &bound_indices_per_clause,
            pinned_indices: &pinned_indices,
            pinned_ptr,
            out_ptr,
            dispatch,
            inputs: vec![msg],
            binary_data_gvs: &binary_data_gvs,
            runtime,
        };

        let mut state = DispatchEmitState::default();
        if let Err(e) = emit_dispatch_node(b, &ctx, dispatch.graph.root, miss_block, &mut state) {
            compile_err = Some(e);
            finish_failed_dispatch_body(b, miss_block);
            return;
        }

        b.switch_to_block(miss_block);
        b.seal_block(miss_block);
        let zero = b.ins().iconst(types::I32, 0);
        b.ins().return_(&[zero]);
    })
    .map_err(|e| CodegenError::new(format!("define receive dispatch fn: {}", e)))?;

    if let Some(e) = compile_err {
        return Err(e);
    }
    Ok(stats)
}

#[derive(Clone, Copy)]
enum ReceiveValue {
    AnyRef(ir::Value),
    Int(ir::Value),
    Float(ir::Value),
    Atom(ir::Value),
    Null,
    EmptyList,
}

struct DispatchCtx<'a> {
    /// The running receiver's `Process*` (dispatch fn's first param). Field
    /// projections that need heap state (struct fields via the schema registry,
    /// map values) pass it to their BIFs. The dispatch fn is invoked from Rust,
    /// not through the pinned-register ABI, so it carries the process explicitly.
    process: ir::Value,
    fz_module: &'a Module,
    tuple_schema_ids: &'a HashMap<usize, u32>,
    named_schema_ids: &'a HashMap<String, u32>,
    bound_indices_per_clause: &'a [HashMap<String, usize>],
    pinned_indices: &'a HashMap<String, usize>,
    pinned_ptr: ir::Value,
    out_ptr: ir::Value,
    dispatch: &'a ReceiveDispatchPlan,
    inputs: Vec<ReceiveValue>,
    binary_data_gvs: &'a HashMap<Vec<u8>, ir::GlobalValue>,
    runtime: DispatchRuntimeRefs,
}

#[derive(Default, Clone)]
struct DispatchEmitState {
    values: HashMap<SubjectId, ReceiveValue>,
    bitstring_fields: HashMap<(SubjectId, u32), ReceiveValue>,
    direct_bindings: HashMap<String, ReceiveValue>,
}

fn emit_receive_value_ref(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::AnyRef(value_ref) => Ok(value_ref),
        ReceiveValue::Int(raw) => {
            let Some(fref) = ctx.runtime.box_int_for_any_fref else {
                return Err(CodegenError::new("int any-boundary requires fz_box_int_for_any"));
            };
            let inst = b.ins().call(fref, &[ctx.process, raw]);
            Ok(b.inst_results(inst)[0])
        }
        ReceiveValue::Float(raw) => {
            let Some(fref) = ctx.runtime.box_float_for_any_fref else {
                return Err(CodegenError::new("float any-boundary requires fz_box_float_for_any"));
            };
            let inst = b.ins().call(fref, &[ctx.process, raw]);
            Ok(b.inst_results(inst)[0])
        }
        ReceiveValue::Atom(raw) => {
            let Some(fref) = ctx.runtime.box_atom_for_any_fref else {
                return Err(CodegenError::new("atom any-boundary requires fz_box_atom_for_any"));
            };
            let inst = b.ins().call(fref, &[ctx.process, raw]);
            Ok(b.inst_results(inst)[0])
        }
        ReceiveValue::Null => Ok(b.ins().iconst(types::I64, 0)),
        ReceiveValue::EmptyList => Ok(b.ins().iconst(types::I64, AnyValueRef::empty_list().raw_word() as i64)),
    }
}

fn receive_value_from_ref_word(_b: &mut FunctionBuilder<'_>, value_ref: ir::Value) -> ReceiveValue {
    ReceiveValue::AnyRef(value_ref)
}

fn receive_value_tag(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::AnyRef(value_ref) => {
            let Some(fref) = ctx.runtime.type_of_fref else {
                return Err(CodegenError::new("any type test requires fz_type_of"));
            };
            let inst = b.ins().call(fref, &[value_ref]);
            Ok(b.inst_results(inst)[0])
        }
        ReceiveValue::Int(_) => Ok(b.ins().iconst(types::I8, ValueKind::INT.tag() as i64)),
        ReceiveValue::Float(_) => Ok(b.ins().iconst(types::I8, ValueKind::FLOAT.tag() as i64)),
        ReceiveValue::Atom(_) => Ok(b.ins().iconst(types::I8, ValueKind::ATOM.tag() as i64)),
        ReceiveValue::Null => Ok(b.ins().iconst(types::I8, ValueKind::NULL.tag() as i64)),
        ReceiveValue::EmptyList => Ok(b.ins().iconst(types::I8, ValueKind::LIST.tag() as i64)),
    }
}

fn receive_value_int(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::Int(raw) => Ok(raw),
        ReceiveValue::AnyRef(value_ref) => {
            let Some(fref) = ctx.runtime.unbox_int_fref else {
                return Err(CodegenError::new("int unbox requires fz_unbox_int"));
            };
            let inst = b.ins().call(fref, &[value_ref]);
            Ok(b.inst_results(inst)[0])
        }
        _ => Err(CodegenError::new("expected int receive value")),
    }
}

fn receive_value_float(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::Float(raw) => Ok(raw),
        ReceiveValue::AnyRef(value_ref) => {
            let Some(fref) = ctx.runtime.unbox_float_fref else {
                return Err(CodegenError::new("float unbox requires fz_unbox_float"));
            };
            let inst = b.ins().call(fref, &[value_ref]);
            Ok(b.inst_results(inst)[0])
        }
        _ => Err(CodegenError::new("expected float receive value")),
    }
}

fn receive_value_atom(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::Atom(raw) => Ok(raw),
        ReceiveValue::AnyRef(value_ref) => {
            let Some(fref) = ctx.runtime.unbox_atom_fref else {
                return Err(CodegenError::new("atom unbox requires fz_unbox_atom"));
            };
            let inst = b.ins().call(fref, &[value_ref]);
            Ok(b.inst_results(inst)[0])
        }
        _ => Err(CodegenError::new("expected atom receive value")),
    }
}

fn value_ref_offset(idx: usize) -> i32 {
    (idx * SLOT_BYTES as usize) as i32
}

fn load_receive_value_ref(b: &mut FunctionBuilder<'_>, base: ir::Value, idx: usize) -> ReceiveValue {
    let value_ref = b
        .ins()
        .load(types::I64, MemFlags::trusted(), base, value_ref_offset(idx));
    receive_value_from_ref_word(b, value_ref)
}

fn store_receive_value_ref(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    base: ir::Value,
    idx: usize,
    value: ReceiveValue,
) -> Result<(), CodegenError> {
    let value_ref = emit_receive_value_ref(b, ctx, value)?;
    b.ins()
        .store(MemFlags::trusted(), value_ref, base, value_ref_offset(idx));
    Ok(())
}

fn finish_failed_dispatch_body(b: &mut FunctionBuilder<'_>, miss_block: ir::Block) {
    let zero = b.ins().iconst(types::I32, 0);
    b.ins().return_(&[zero]);
    let to_miss = b.create_block();
    b.switch_to_block(to_miss);
    b.seal_block(to_miss);
    b.ins().jump(miss_block, &[]);
    b.switch_to_block(miss_block);
    b.seal_block(miss_block);
    let zero2 = b.ins().iconst(types::I32, 0);
    b.ins().return_(&[zero2]);
}

fn emit_dispatch_node(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    node_id: GraphNodeId,
    miss: ir::Block,
    state: &mut DispatchEmitState,
) -> Result<(), CodegenError> {
    let node = ctx
        .dispatch
        .graph
        .node(node_id)
        .ok_or_else(|| CodegenError::new(format!("dispatch node {:?} out of bounds", node_id)))?;
    match node {
        DispatchNode::Fail => {
            b.ins().jump(miss, &[]);
            let dead = b.create_block();
            b.switch_to_block(dead);
            b.seal_block(dead);
            Ok(())
        }
        DispatchNode::Outcome { outcome, .. } => {
            let outcome = ctx
                .dispatch
                .outcome(*outcome)
                .ok_or_else(|| CodegenError::new(format!("dispatch outcome {:?} out of bounds", outcome)))?;
            let bound = &ctx.bound_indices_per_clause[outcome.body_id as usize];
            for binding in &outcome.bindings {
                let val = resolve_dispatch_subject(b, ctx, binding.source, state)?;
                if let Some(&idx) = bound.get(&binding.name) {
                    store_receive_value_ref(b, ctx, ctx.out_ptr, idx, val)?;
                }
            }
            let k = b.ins().iconst(types::I32, (outcome.body_id + 1) as i64);
            b.ins().return_(&[k]);
            let dead = b.create_block();
            b.switch_to_block(dead);
            b.seal_block(dead);
            Ok(())
        }
        DispatchNode::Test {
            predicate,
            on_match,
            on_miss,
        } => {
            let true_b = b.create_block();
            let false_b = b.create_block();
            let true_values = emit_region_test(
                b,
                ctx,
                predicate.subject,
                &predicate.region,
                &on_match.evidence,
                true_b,
                false_b,
                state,
            )?;
            b.switch_to_block(true_b);
            b.seal_block(true_b);
            let mut true_state = state.clone();
            true_state.values.extend(true_values);
            apply_edge_evidence_to_receive_state(b, ctx, &on_match.evidence, &mut true_state)?;
            emit_dispatch_node(b, ctx, on_match.target, miss, &mut true_state)?;
            b.switch_to_block(false_b);
            b.seal_block(false_b);
            emit_dispatch_node(b, ctx, on_miss.target, miss, state)
        }
    }
}

fn resolve_dispatch_subject(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    subject: SubjectId,
    state: &mut DispatchEmitState,
) -> Result<ReceiveValue, CodegenError> {
    if let Some(v) = state.values.get(&subject).copied() {
        return Ok(v);
    }
    let subject_data = ctx
        .dispatch
        .matrix
        .subjects
        .get(subject.0 as usize)
        .ok_or_else(|| CodegenError::new(format!("dispatch subject {:?} out of bounds", subject)))?;
    let v = match &subject_data.source {
        SubjectSource::Input { ordinal } => *ctx
            .inputs
            .get(*ordinal as usize)
            .ok_or_else(|| CodegenError::new(format!("receive dispatch has no input {}", ordinal)))?,
        SubjectSource::Projection(projection) => match &projection.kind {
            ProjectionKind::TupleField(index) => {
                let parent = resolve_dispatch_subject(b, ctx, projection.source, state)?;
                emit_struct_get_field(b, ctx, parent, *index)?
            }
            ProjectionKind::ListHead => {
                let parent = resolve_dispatch_subject(b, ctx, projection.source, state)?;
                let Some(fref) = ctx.runtime.list_head_fref else {
                    return Err(CodegenError::new("ListHead dispatch projection requires fz_list_head"));
                };
                let parent_ref = emit_receive_value_ref(b, ctx, parent)?;
                let inst = b.ins().call(fref, &[parent_ref]);
                let out_ref = b.inst_results(inst)[0];
                receive_value_from_ref_word(b, out_ref)
            }
            ProjectionKind::ListTail => {
                let parent = resolve_dispatch_subject(b, ctx, projection.source, state)?;
                let Some(fref) = ctx.runtime.list_tail_fref else {
                    return Err(CodegenError::new("ListTail dispatch projection requires fz_list_tail"));
                };
                let parent_ref = emit_receive_value_ref(b, ctx, parent)?;
                let inst = b.ins().call(fref, &[parent_ref]);
                let out_ref = b.inst_results(inst)[0];
                receive_value_from_ref_word(b, out_ref)
            }
            ProjectionKind::MapValue { key } => {
                let map = resolve_dispatch_subject(b, ctx, projection.source, state)?;
                emit_dispatch_map_get_value(b, ctx, map, key)?
            }
            ProjectionKind::BitstringField(index) => *state
                .values
                .get(&subject)
                .or_else(|| state.bitstring_fields.get(&(projection.source, *index)))
                .ok_or_else(|| {
                    CodegenError::new(format!(
                        "receive dispatch bitstring field {:?}/{} not available",
                        projection.source, index
                    ))
                })?,
        },
    };
    state.values.insert(subject, v);
    Ok(v)
}

fn load_pinned_dispatch_value(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    pinned: PinnedValueId,
) -> Result<ReceiveValue, CodegenError> {
    let p = ctx
        .dispatch
        .pinned
        .get(pinned.0 as usize)
        .ok_or_else(|| CodegenError::new(format!("pinned {:?} out of bounds", pinned)))?;
    if let Some(input) = p.input {
        return ctx
            .inputs
            .get(input as usize)
            .copied()
            .ok_or_else(|| CodegenError::new(format!("pinned helper input {:?} out of bounds", input)));
    }

    let &idx = ctx
        .pinned_indices
        .get(&p.name)
        .ok_or_else(|| CodegenError::new(format!("pinned ^{} not in dispatch pinned table", p.name)))?;
    Ok(load_receive_value_ref(b, ctx.pinned_ptr, idx))
}

fn emit_region_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    subject: SubjectId,
    region: &ReceiveRegion,
    evidence: &ReceiveEdgeEvidence,
    true_b: ir::Block,
    false_b: ir::Block,
    state: &mut DispatchEmitState,
) -> Result<Vec<(SubjectId, ReceiveValue)>, CodegenError> {
    let mut true_values = Vec::new();
    match region {
        Region::Any => {
            b.ins().jump(true_b, &[]);
        }
        Region::Never => {
            b.ins().jump(false_b, &[]);
        }
        Region::Type(predicate) => {
            let val = resolve_dispatch_subject(b, ctx, subject, state)?;
            emit_runtime_type_predicate_region_test(b, ctx, val, predicate, true_b, false_b)?;
        }
        Region::Equal(ComparisonValue::Const(value)) => {
            let val = resolve_dispatch_subject(b, ctx, subject, state)?;
            emit_dispatch_const_test(b, ctx, val, value, true_b, false_b)?;
        }
        Region::Equal(ComparisonValue::Pinned(pinned)) => {
            let val = resolve_dispatch_subject(b, ctx, subject, state)?;
            let want = load_pinned_dispatch_value(b, ctx, *pinned)?;
            emit_typed_eq_branch(b, ctx, val, want, true_b, false_b)?;
        }
        Region::TupleArity(arity) => {
            let val = resolve_dispatch_subject(b, ctx, subject, state)?;
            emit_tuple_arity_test(b, ctx, ctx.tuple_schema_ids, val, *arity as usize, true_b, false_b)?;
        }
        Region::List(ListRegion::Empty) => {
            let val = resolve_dispatch_subject(b, ctx, subject, state)?;
            emit_dispatch_const_test(b, ctx, val, &DispatchConst::EmptyList, true_b, false_b)?;
        }
        Region::List(ListRegion::Cons) => {
            let val = resolve_dispatch_subject(b, ctx, subject, state)?;
            emit_list_cons_test(b, ctx, val, true_b, false_b)?;
        }
        Region::MapKind => {
            let val = resolve_dispatch_subject(b, ctx, subject, state)?;
            emit_map_kind_test(b, ctx, val, true_b, false_b)?;
        }
        Region::MapKeyPresent { key } => {
            let val = resolve_dispatch_subject(b, ctx, subject, state)?;
            let got = emit_dispatch_map_get_value(b, ctx, val, key)?;
            for projection in &evidence.projections {
                if projection.source == subject
                    && matches!(&projection.kind, ProjectionKind::MapValue { key: projection_key } if projection_key == key)
                {
                    true_values.push((projection.result, got));
                }
            }
            let cmp = emit_not_dispatch_map_miss(b, ctx, got)?;
            b.ins().brif(cmp, true_b, &[], false_b, &[]);
        }
        Region::Bitstring(shape) => {
            emit_bitstring_test(b, ctx, subject, shape, true_b, false_b, state)?;
        }
        Region::Guard(guard) => {
            let expr = ctx
                .dispatch
                .guards
                .get(guard.0 as usize)
                .ok_or_else(|| CodegenError::new(format!("dispatch guard {:?} out of bounds", guard)))?;
            let value = emit_dispatch_guard_expr(b, ctx, expr, state)?;
            let truthy = emit_truthy_cmp(b, ctx, value)?;
            b.ins().brif(truthy, true_b, &[], false_b, &[]);
        }
    }
    Ok(true_values)
}

fn emit_runtime_type_predicate_region_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
    predicate: &RuntimeTypePredicate,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let scalar = emit_runtime_type_predicate_scalar_checks(b, ctx, value, predicate)?;
    let heap = emit_runtime_type_predicate_heap_checks(b, ctx, value, predicate)?;
    let struct_flag = predicate
        .has_structs()
        .then(|| emit_runtime_type_predicate_struct_check(b, ctx, value, predicate))
        .transpose()?;
    let flag = [scalar, heap, struct_flag]
        .into_iter()
        .flatten()
        .reduce(|acc, next| b.ins().bor(acc, next))
        .unwrap_or_else(|| b.ins().iconst(types::I8, 0));
    b.ins().brif(flag, match_b, &[], next_b, &[]);
    Ok(())
}

fn emit_runtime_type_predicate_scalar_checks(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
    predicate: &RuntimeTypePredicate,
) -> Result<Option<ir::Value>, CodegenError> {
    let mut scalar = None;
    let or_in = |b: &mut FunctionBuilder<'_>, flag: ir::Value, scalar: &mut Option<ir::Value>| {
        *scalar = Some(match scalar.take() {
            None => flag,
            Some(prev) => b.ins().bor(prev, flag),
        });
    };
    if !predicate.ints.is_none() {
        let flag = emit_receive_kind_guarded_membership(b, ctx, value, ValueKind::INT, |b, ctx, value| {
            let raw = receive_value_int(b, ctx, value)?;
            Ok(emit_receive_i64_membership(b, raw, &predicate.ints))
        })?;
        or_in(b, flag, &mut scalar);
    }
    if !predicate.floats.is_none() {
        let flag = emit_receive_kind_guarded_membership(b, ctx, value, ValueKind::FLOAT, |b, ctx, value| {
            let raw = receive_value_float(b, ctx, value)?;
            let bits = b.ins().bitcast(types::I64, MemFlags::new(), raw);
            Ok(emit_receive_u64_membership(b, bits, &predicate.floats))
        })?;
        or_in(b, flag, &mut scalar);
    }
    if !predicate.atoms.is_none() {
        let name_to_id: HashMap<&str, u32> = ctx
            .fz_module
            .atom_names
            .iter()
            .enumerate()
            .map(|(i, name)| (name.as_str(), i as u32))
            .collect();
        let atom_ids = ObservedSet {
            cofinite: predicate.atoms.cofinite,
            values: predicate
                .atoms
                .values
                .iter()
                .filter_map(|name| name_to_id.get(name.as_str()).copied().map(i64::from))
                .collect(),
        };
        let flag = emit_receive_kind_guarded_membership(b, ctx, value, ValueKind::ATOM, |b, ctx, value| {
            let raw = receive_value_atom(b, ctx, value)?;
            Ok(emit_receive_i64_membership(b, raw, &atom_ids))
        })?;
        or_in(b, flag, &mut scalar);
    }
    Ok(scalar)
}

fn emit_runtime_type_predicate_heap_checks(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
    predicate: &RuntimeTypePredicate,
) -> Result<Option<ir::Value>, CodegenError> {
    let mut flag = None;
    let mut or_in = |b: &mut FunctionBuilder<'_>, next: ir::Value| {
        flag = Some(match flag.take() {
            None => next,
            Some(prev) => b.ins().bor(prev, next),
        });
    };
    if let Some(list_flag) = emit_runtime_type_predicate_list_check(b, ctx, value, &predicate.lists)? {
        or_in(b, list_flag);
    }
    if predicate.maps {
        let map_flag = emit_receive_value_kind_flag(b, ctx, value, ValueKind::MAP)?;
        or_in(b, map_flag);
    }
    if predicate.binaries {
        let binary_flag = emit_receive_value_kind_flag(b, ctx, value, ValueKind::BITSTRING)?;
        or_in(b, binary_flag);
    }
    if predicate.closures {
        let closure_flag = emit_receive_value_kind_flag(b, ctx, value, ValueKind::CLOSURE)?;
        or_in(b, closure_flag);
    }
    if predicate.resources {
        let resource_flag = emit_receive_value_kind_flag(b, ctx, value, ValueKind::RESOURCE)?;
        or_in(b, resource_flag);
    }
    Ok(flag)
}

fn emit_runtime_type_predicate_struct_check(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
    predicate: &RuntimeTypePredicate,
) -> Result<ir::Value, CodegenError> {
    if predicate.allow_other_structs && predicate.tuple_arities.is_any() && predicate.named_structs.is_any() {
        return emit_receive_value_kind_flag(b, ctx, value, ValueKind::STRUCT);
    }

    let is_struct = emit_receive_value_kind_flag(b, ctx, value, ValueKind::STRUCT)?;
    let struct_blk = b.create_block();
    let join_blk = b.create_block();
    b.append_block_param(join_blk, types::I8);
    let false8 = b.ins().iconst(types::I8, 0);
    b.ins()
        .brif(is_struct, struct_blk, &[], join_blk, &[ir::BlockArg::Value(false8)]);

    b.switch_to_block(struct_blk);
    b.seal_block(struct_blk);
    let Some(fref) = ctx.runtime.struct_schema_id_ref_fref else {
        return Err(CodegenError::new("struct type-test requires fz_struct_schema_id_ref"));
    };
    let struct_ref = emit_receive_value_ref(b, ctx, value)?;
    let inst = b.ins().call(fref, &[struct_ref]);
    let schema_raw = b.inst_results(inst)[0];
    let schema64 = b.ins().uextend(types::I64, schema_raw);

    let tuple_match =
        emit_receive_struct_tuple_membership(b, schema64, ctx.tuple_schema_ids, ctx.named_schema_ids, predicate);
    let named_match = emit_receive_struct_named_membership(b, schema64, ctx.named_schema_ids, &predicate.named_structs);
    let other_match = if predicate.allow_other_structs {
        let known_tuple = emit_receive_any_schema_id_match(b, schema64, ctx.tuple_schema_ids.values().copied());
        let known_named = emit_receive_any_schema_id_match(b, schema64, ctx.named_schema_ids.values().copied());
        let known_struct = b.ins().bor(known_tuple, known_named);
        b.ins().icmp_imm(IntCC::Equal, known_struct, 0)
    } else {
        b.ins().iconst(types::I8, 0)
    };
    let tuple_or_named = b.ins().bor(tuple_match, named_match);
    let flag = b.ins().bor(tuple_or_named, other_match);
    b.ins().jump(join_blk, &[ir::BlockArg::Value(flag)]);

    b.switch_to_block(join_blk);
    b.seal_block(join_blk);
    Ok(b.block_params(join_blk)[0])
}

fn emit_runtime_type_predicate_list_check(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
    lists: &ObservedSet<ListShape>,
) -> Result<Option<ir::Value>, CodegenError> {
    if lists.is_none() {
        return Ok(None);
    }
    let allow_empty = lists.contains(&ListShape::Empty);
    let allow_non_empty = lists.contains(&ListShape::NonEmpty);
    Ok(match (allow_empty, allow_non_empty) {
        (false, false) => None,
        (true, true) => Some(emit_receive_value_kind_flag(b, ctx, value, ValueKind::LIST)?),
        (true, false) => Some(emit_receive_is_empty_list_flag(b, ctx, value)?),
        (false, true) => Some(emit_receive_is_list_cons_flag(b, ctx, value)?),
    })
}

fn emit_receive_kind_guarded_membership(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
    kind: ValueKind,
    build: impl FnOnce(&mut FunctionBuilder<'_>, &DispatchCtx<'_>, ReceiveValue) -> Result<ir::Value, CodegenError>,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::AnyRef(_) => {
            let is_kind = emit_receive_value_kind_flag(b, ctx, value, kind)?;
            let match_blk = b.create_block();
            let join_blk = b.create_block();
            b.append_block_param(join_blk, types::I8);
            let false8 = b.ins().iconst(types::I8, 0);
            b.ins()
                .brif(is_kind, match_blk, &[], join_blk, &[ir::BlockArg::Value(false8)]);
            b.switch_to_block(match_blk);
            b.seal_block(match_blk);
            let matched = build(b, ctx, value)?;
            b.ins().jump(join_blk, &[ir::BlockArg::Value(matched)]);
            b.switch_to_block(join_blk);
            b.seal_block(join_blk);
            Ok(b.block_params(join_blk)[0])
        }
        ReceiveValue::Int(_) if kind == ValueKind::INT => build(b, ctx, value),
        ReceiveValue::Float(_) if kind == ValueKind::FLOAT => build(b, ctx, value),
        ReceiveValue::Atom(_) if kind == ValueKind::ATOM => build(b, ctx, value),
        _ => Ok(b.ins().iconst(types::I8, 0)),
    }
}

fn emit_receive_value_kind_flag(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
    kind: ValueKind,
) -> Result<ir::Value, CodegenError> {
    let tag = receive_value_tag(b, ctx, value)?;
    let tag64 = b.ins().uextend(types::I64, tag);
    Ok(b.ins().icmp_imm(IntCC::Equal, tag64, kind.tag() as i64))
}

fn emit_receive_i64_membership(b: &mut FunctionBuilder<'_>, raw: ir::Value, values: &ObservedSet<i64>) -> ir::Value {
    if values.is_any() {
        return b.ins().iconst(types::I8, 1);
    }
    let mut eq_any = b.ins().iconst(types::I8, 0);
    for want in &values.values {
        let next = b.ins().icmp_imm(IntCC::Equal, raw, *want);
        eq_any = b.ins().bor(eq_any, next);
    }
    if values.cofinite {
        b.ins().icmp_imm(IntCC::Equal, eq_any, 0)
    } else {
        eq_any
    }
}

fn emit_receive_u64_membership(b: &mut FunctionBuilder<'_>, raw: ir::Value, values: &ObservedSet<u64>) -> ir::Value {
    if values.is_any() {
        return b.ins().iconst(types::I8, 1);
    }
    let mut eq_any = b.ins().iconst(types::I8, 0);
    for want in &values.values {
        let want = b.ins().iconst(types::I64, *want as i64);
        let next = b.ins().icmp(IntCC::Equal, raw, want);
        eq_any = b.ins().bor(eq_any, next);
    }
    if values.cofinite {
        b.ins().icmp_imm(IntCC::Equal, eq_any, 0)
    } else {
        eq_any
    }
}

fn emit_receive_any_schema_id_match(
    b: &mut FunctionBuilder<'_>,
    schema64: ir::Value,
    ids: impl IntoIterator<Item = u32>,
) -> ir::Value {
    let mut matched = b.ins().iconst(types::I8, 0);
    for id in ids {
        let want = b.ins().iconst(types::I64, id as i64);
        let next = b.ins().icmp(IntCC::Equal, schema64, want);
        matched = b.ins().bor(matched, next);
    }
    matched
}

fn emit_receive_struct_tuple_membership(
    b: &mut FunctionBuilder<'_>,
    schema64: ir::Value,
    tuple_schema_ids: &HashMap<usize, u32>,
    named_schema_ids: &HashMap<String, u32>,
    predicate: &RuntimeTypePredicate,
) -> ir::Value {
    if predicate.tuple_arities.is_none() {
        return b.ins().iconst(types::I8, 0);
    }
    if predicate.tuple_arities.is_any() {
        let known_named = emit_receive_any_schema_id_match(b, schema64, named_schema_ids.values().copied());
        return b.ins().icmp_imm(IntCC::Equal, known_named, 0);
    }
    if predicate.tuple_arities.cofinite {
        let excluded = predicate
            .tuple_arities
            .values
            .iter()
            .filter_map(|arity| tuple_schema_ids.get(arity).copied())
            .collect::<Vec<_>>();
        let known_named = emit_receive_any_schema_id_match(b, schema64, named_schema_ids.values().copied());
        let is_named = b.ins().icmp_imm(IntCC::NotEqual, known_named, 0);
        let excluded_match = emit_receive_any_schema_id_match(b, schema64, excluded);
        let excluded_ok = b.ins().icmp_imm(IntCC::Equal, excluded_match, 0);
        let not_named = b.ins().bxor_imm(is_named, 1);
        b.ins().band(not_named, excluded_ok)
    } else {
        emit_receive_any_schema_id_match(
            b,
            schema64,
            predicate
                .tuple_arities
                .values
                .iter()
                .filter_map(|arity| tuple_schema_ids.get(arity).copied()),
        )
    }
}

fn emit_receive_struct_named_membership(
    b: &mut FunctionBuilder<'_>,
    schema64: ir::Value,
    named_schema_ids: &HashMap<String, u32>,
    names: &ObservedSet<String>,
) -> ir::Value {
    if names.is_none() {
        return b.ins().iconst(types::I8, 0);
    }
    if names.is_any() {
        return emit_receive_any_schema_id_match(b, schema64, named_schema_ids.values().copied());
    }
    let relevant_ids = names
        .values
        .iter()
        .filter_map(|name| named_schema_ids.get(name).copied())
        .collect::<Vec<_>>();
    let matched = emit_receive_any_schema_id_match(b, schema64, relevant_ids);
    if names.cofinite {
        let any_named = emit_receive_any_schema_id_match(b, schema64, named_schema_ids.values().copied());
        let not_excluded = b.ins().icmp_imm(IntCC::Equal, matched, 0);
        b.ins().band(any_named, not_excluded)
    } else {
        matched
    }
}

fn emit_receive_is_empty_list_flag(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    Ok(match value {
        ReceiveValue::EmptyList => b.ins().iconst(types::I8, 1),
        ReceiveValue::AnyRef(value_ref) => {
            let tag = receive_value_tag(b, ctx, value)?;
            let tag64 = b.ins().uextend(types::I64, tag);
            let empty = b.ins().iconst(types::I64, AnyValueRef::empty_list().raw_word() as i64);
            let is_list = b.ins().icmp_imm(IntCC::Equal, tag64, ValueKind::LIST.tag() as i64);
            let is_empty = b.ins().icmp(IntCC::Equal, value_ref, empty);
            b.ins().band(is_list, is_empty)
        }
        ReceiveValue::Null | ReceiveValue::Int(_) | ReceiveValue::Float(_) | ReceiveValue::Atom(_) => {
            b.ins().iconst(types::I8, 0)
        }
    })
}

fn emit_receive_is_list_cons_flag(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    Ok(match value {
        ReceiveValue::AnyRef(value_ref) => {
            let tag = receive_value_tag(b, ctx, value)?;
            let tag64 = b.ins().uextend(types::I64, tag);
            let empty = b.ins().iconst(types::I64, AnyValueRef::empty_list().raw_word() as i64);
            let is_list = b.ins().icmp_imm(IntCC::Equal, tag64, ValueKind::LIST.tag() as i64);
            let is_empty = b.ins().icmp(IntCC::Equal, value_ref, empty);
            let not_empty = b.ins().icmp_imm(IntCC::Equal, is_empty, 0);
            b.ins().band(is_list, not_empty)
        }
        ReceiveValue::Null
        | ReceiveValue::Int(_)
        | ReceiveValue::Float(_)
        | ReceiveValue::Atom(_)
        | ReceiveValue::EmptyList => b.ins().iconst(types::I8, 0),
    })
}

fn apply_edge_evidence_to_receive_state(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    evidence: &ReceiveEdgeEvidence,
    state: &mut DispatchEmitState,
) -> Result<(), CodegenError> {
    for projection in &evidence.projections {
        if state.values.contains_key(&projection.result) {
            continue;
        }

        if let ProjectionKind::BitstringField(index) = projection.kind
            && let Some(value) = state.bitstring_fields.get(&(projection.source, index)).copied()
        {
            state.values.insert(projection.result, value);
            continue;
        }

        let value = resolve_dispatch_subject(b, ctx, projection.result, state)?;
        state.values.insert(projection.result, value);
    }
    Ok(())
}

fn emit_dispatch_side_tag_const_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    val: ReceiveValue,
    value: &DispatchConst,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<bool, CodegenError> {
    let Some(want) = dispatch_const_value(ctx.fz_module, value)? else {
        return Ok(false);
    };
    match (want.kind, val) {
        (ValueKind::INT, ReceiveValue::Int(raw)) => {
            let ok = b.ins().icmp_imm(IntCC::Equal, raw, want.raw as i64);
            b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        (ValueKind::FLOAT, ReceiveValue::Float(raw)) => {
            let raw_bits = b.ins().bitcast(types::I64, MemFlags::new(), raw);
            let want_bits = b.ins().iconst(types::I64, want.raw as i64);
            let ok = b.ins().icmp(IntCC::Equal, raw_bits, want_bits);
            b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        (ValueKind::ATOM, ReceiveValue::Atom(raw)) => {
            let ok = b.ins().icmp_imm(IntCC::Equal, raw, want.raw as i64);
            b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        (ValueKind::LIST, ReceiveValue::EmptyList) if want.raw == 0 => {
            b.ins().jump(match_b, &[]);
        }
        (_, ReceiveValue::AnyRef(value_ref)) => {
            emit_any_ref_const_test(b, ctx, value_ref, want, match_b, next_b)?;
        }
        _ => {
            b.ins().jump(next_b, &[]);
        }
    }
    Ok(true)
}

fn emit_any_ref_const_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    value_ref: ir::Value,
    want: DispatchConstValue,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    if want.kind == ValueKind::LIST && want.raw == 0 {
        let empty = b.ins().iconst(types::I64, AnyValueRef::empty_list().raw_word() as i64);
        let ok = b.ins().icmp(IntCC::Equal, value_ref, empty);
        b.ins().brif(ok, match_b, &[], next_b, &[]);
        return Ok(());
    }
    let want_tag = want.kind;
    if want_tag.is_heap() {
        b.ins().jump(next_b, &[]);
        return Ok(());
    };
    let tag = receive_value_tag(b, ctx, ReceiveValue::AnyRef(value_ref))?;
    let tag64 = b.ins().uextend(types::I64, tag);
    let type_ok = b.ins().icmp_imm(IntCC::Equal, tag64, want_tag.tag() as i64);
    let value_block = b.create_block();
    b.ins().brif(type_ok, value_block, &[], next_b, &[]);
    b.switch_to_block(value_block);
    b.seal_block(value_block);
    match want.kind {
        ValueKind::INT => {
            let raw = receive_value_int(b, ctx, ReceiveValue::AnyRef(value_ref))?;
            let ok = b.ins().icmp_imm(IntCC::Equal, raw, want.raw as i64);
            b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        ValueKind::FLOAT => {
            let raw = receive_value_float(b, ctx, ReceiveValue::AnyRef(value_ref))?;
            let raw_bits = b.ins().bitcast(types::I64, MemFlags::new(), raw);
            let want_bits = b.ins().iconst(types::I64, want.raw as i64);
            let ok = b.ins().icmp(IntCC::Equal, raw_bits, want_bits);
            b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        ValueKind::ATOM => {
            let raw = receive_value_atom(b, ctx, ReceiveValue::AnyRef(value_ref))?;
            let ok = b.ins().icmp_imm(IntCC::Equal, raw, want.raw as i64);
            b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        ValueKind::LIST if want.raw == 0 => {
            b.ins().jump(match_b, &[]);
        }
        _ => {
            b.ins().jump(next_b, &[]);
        }
    }
    Ok(())
}

fn dispatch_const_value(module: &Module, value: &DispatchConst) -> Result<Option<DispatchConstValue>, CodegenError> {
    Ok(match value {
        DispatchConst::Int(n) => Some(DispatchConstValue {
            raw: *n as u64,
            kind: ValueKind::INT,
        }),
        DispatchConst::FloatBits(bits) => Some(DispatchConstValue {
            raw: *bits,
            kind: ValueKind::FLOAT,
        }),
        DispatchConst::AtomName(name) => {
            module
                .atom_names
                .iter()
                .position(|n| n == name)
                .map(|id| DispatchConstValue {
                    raw: id as u64,
                    kind: ValueKind::ATOM,
                })
        }
        DispatchConst::Bool(v) => Some(DispatchConstValue {
            raw: if *v { TRUE_ATOM_ID as u64 } else { FALSE_ATOM_ID as u64 },
            kind: ValueKind::ATOM,
        }),
        DispatchConst::Nil => Some(DispatchConstValue {
            raw: NIL_ATOM_ID as u64,
            kind: ValueKind::ATOM,
        }),
        DispatchConst::EmptyList => Some(DispatchConstValue {
            raw: 0,
            kind: ValueKind::LIST,
        }),
        DispatchConst::Utf8Binary(_) => None,
    })
}

#[derive(Clone, Copy)]
struct DispatchConstValue {
    raw: u64,
    kind: ValueKind,
}

fn dispatch_const_receive_value(b: &mut FunctionBuilder<'_>, value: DispatchConstValue) -> ReceiveValue {
    match value.kind {
        ValueKind::INT => ReceiveValue::Int(b.ins().iconst(types::I64, value.raw as i64)),
        ValueKind::FLOAT => {
            let bits = b.ins().iconst(types::I64, value.raw as i64);
            ReceiveValue::Float(b.ins().bitcast(types::F64, MemFlags::new(), bits))
        }
        ValueKind::ATOM => ReceiveValue::Atom(b.ins().iconst(types::I64, value.raw as i64)),
        ValueKind::NULL => ReceiveValue::Null,
        ValueKind::LIST if value.raw == 0 => ReceiveValue::EmptyList,
        _ => unreachable!("dispatch constants only materialize scalar, null, or empty list values"),
    }
}

fn emit_dispatch_const_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    val: ReceiveValue,
    value: &DispatchConst,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    match value {
        DispatchConst::FloatBits(_)
        | DispatchConst::Int(_)
        | DispatchConst::AtomName(_)
        | DispatchConst::Bool(_)
        | DispatchConst::Nil
        | DispatchConst::EmptyList => {
            let emitted = emit_dispatch_side_tag_const_test(b, ctx, val, value, match_b, next_b)?;
            if !emitted {
                b.ins().jump(next_b, &[]);
            }
            Ok(())
        }
        DispatchConst::Utf8Binary(bytes) => {
            let bits = emit_receive_value_ref(b, ctx, val)?;
            emit_binary_literal_test(
                b,
                ctx.binary_data_gvs,
                ctx.runtime.matcher_eq_bytes_fref,
                bits,
                bytes,
                match_b,
                next_b,
            )
        }
    }
}

fn emit_dispatch_map_get_value(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    map: ReceiveValue,
    key: &DispatchConst,
) -> Result<ReceiveValue, CodegenError> {
    if let Some(index) = prepared_dispatch_key_index(ctx.dispatch, key) {
        let Some(map_get_ref_fref) = ctx.runtime.matcher_map_get_ref_fref else {
            return Err(CodegenError::new(
                "prepared map dispatch key requires fz_matcher_map_get_ref",
            ));
        };
        let name = prepared_key_name(index);
        let &idx = ctx
            .pinned_indices
            .get(&name)
            .ok_or_else(|| CodegenError::new(format!("prepared dispatch key {} not in pinned table", index)))?;
        let key = load_receive_value_ref(b, ctx.pinned_ptr, idx);
        let map_ref = emit_receive_value_ref(b, ctx, map)?;
        let key_ref = emit_receive_value_ref(b, ctx, key)?;
        let inst = b.ins().call(map_get_ref_fref, &[ctx.process, map_ref, key_ref]);
        let out_ref = b.inst_results(inst)[0];
        return Ok(receive_value_from_ref_word(b, out_ref));
    }
    let Some(map_get_ref_fref) = ctx.runtime.matcher_map_get_ref_fref else {
        return Err(CodegenError::new(
            "map dispatch test requires fz_matcher_map_get_ref; runtime not linked in this context",
        ));
    };
    let Some(key_value) = dispatch_const_value(ctx.fz_module, key)? else {
        return Err(CodegenError::new(format!(
            "map-pattern key {:?} cannot be materialized in receive dispatch",
            key
        )));
    };
    let map_ref = emit_receive_value_ref(b, ctx, map)?;
    let key_value = dispatch_const_receive_value(b, key_value);
    let key_ref = emit_receive_value_ref(b, ctx, key_value)?;
    let inst = b.ins().call(map_get_ref_fref, &[ctx.process, map_ref, key_ref]);
    let out_ref = b.inst_results(inst)[0];
    Ok(receive_value_from_ref_word(b, out_ref))
}

fn prepared_dispatch_key_index(dispatch: &ReceiveDispatchPlan, key: &DispatchConst) -> Option<usize> {
    dispatch.prepared_keys.iter().position(|prepared| prepared == key)
}

fn emit_bitstring_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    subject: SubjectId,
    shape: &BitstringShape,
    true_b: ir::Block,
    false_b: ir::Block,
    state: &mut DispatchEmitState,
) -> Result<(), CodegenError> {
    let Some(init_fref) = ctx.runtime.bs_reader_init_fref else {
        return Err(CodegenError::new("bitstring dispatch test requires fz_bs_reader_init"));
    };
    let Some(read_fref) = ctx.runtime.bs_read_field_fref else {
        return Err(CodegenError::new("bitstring dispatch test requires fz_bs_read_field"));
    };
    let value = resolve_dispatch_subject(b, ctx, subject, state)?;
    emit_bitstring_like_guard(b, ctx, value, false_b)?;
    let value_ref = emit_receive_value_ref(b, ctx, value)?;
    let init = b.ins().call(init_fref, &[ctx.process, value_ref]);
    let mut reader = b.inst_results(init)[0];

    for (index, field) in shape.fields.iter().enumerate() {
        let (size_present, size_value) = emit_dispatch_bit_size(b, ctx, field, state)?;
        let field_spec = fz_bs_field_spec(
            dispatch_bit_type_tag(field.kind),
            size_present,
            field.unit.unwrap_or(default_dispatch_bit_unit(field.kind)),
            dispatch_endian_tag(field.endian),
            field.signed as u32,
            (index + 1 == shape.fields.len()) as u32,
        );
        let field_spec = b.ins().iconst(types::I64, field_spec as i64);
        let inst = b.ins().call(read_fref, &[ctx.process, reader, field_spec, size_value]);
        let result = b.inst_results(inst)[0];
        let result_value = ReceiveValue::AnyRef(result);
        let ok = emit_struct_get_field(b, ctx, result_value, 0)?;
        let ok_truthy = emit_truthy_cmp(b, ctx, ok)?;
        let next_b = b.create_block();
        b.ins().brif(ok_truthy, next_b, &[], false_b, &[]);
        b.switch_to_block(next_b);
        b.seal_block(next_b);
        let extracted = emit_struct_get_field(b, ctx, result_value, 1)?;
        let next_reader = emit_struct_get_field(b, ctx, result_value, 2)?;
        reader = emit_receive_value_ref(b, ctx, next_reader)?;
        let index = index as u32;
        state.bitstring_fields.insert((subject, index), extracted);
        if let Some(field_subject) = bitstring_field_subject(ctx.dispatch, subject, index) {
            state.values.insert(field_subject, extracted);
            if let Some(names) = ctx.dispatch.bitstring_direct_bindings.get(&field_subject) {
                for name in names {
                    state.direct_bindings.insert(name.clone(), extracted);
                }
            }
        }
    }

    if !shape.require_done {
        b.ins().jump(true_b, &[]);
        return Ok(());
    }
    let reader_value = ReceiveValue::AnyRef(reader);
    let bit_len_value = emit_struct_get_field(b, ctx, reader_value, 1)?;
    let bit_len = receive_value_int(b, ctx, bit_len_value)?;
    let pos_value = emit_struct_get_field(b, ctx, reader_value, 2)?;
    let pos = receive_value_int(b, ctx, pos_value)?;
    let done = b.ins().icmp(IntCC::Equal, bit_len, pos);
    b.ins().brif(done, true_b, &[], false_b, &[]);
    Ok(())
}

fn bitstring_field_subject<TypeHandle>(
    dispatch: &PatternDispatchPlan<TypeHandle>,
    source: SubjectId,
    index: u32,
) -> Option<SubjectId> {
    dispatch
        .matrix
        .subjects
        .iter()
        .find_map(|subject| match &subject.source {
            SubjectSource::Projection(projection)
                if projection.source == source && projection.kind == ProjectionKind::BitstringField(index) =>
            {
                Some(subject.id)
            }
            _ => None,
        })
}

fn emit_struct_get_field(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    struct_value: ReceiveValue,
    field_index: u32,
) -> Result<ReceiveValue, CodegenError> {
    emit_struct_get_field_value(b, ctx, struct_value, field_index)
}

fn emit_struct_get_field_value(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    struct_value: ReceiveValue,
    field_index: u32,
) -> Result<ReceiveValue, CodegenError> {
    let Some(fref) = ctx.runtime.struct_get_field_fref else {
        return Err(CodegenError::new(
            "struct field projection requires fz_struct_get_field",
        ));
    };
    let field_offset = b.ins().iconst(types::I32, field_index as i64 * SLOT_BYTES as i64);
    let struct_ref = emit_receive_value_ref(b, ctx, struct_value)?;
    let inst = b.ins().call(fref, &[ctx.process, struct_ref, field_offset]);
    let out_ref = b.inst_results(inst)[0];
    Ok(receive_value_from_ref_word(b, out_ref))
}

fn emit_bitstring_like_guard(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    val: ReceiveValue,
    miss: ir::Block,
) -> Result<(), CodegenError> {
    let tag8 = receive_value_tag(b, ctx, val)?;
    let tag = b.ins().uextend(types::I64, tag8);
    let cont = b.create_block();
    let ptr_path = b.create_block();
    let is_strict_bs = b.ins().icmp_imm(IntCC::Equal, tag, ValueKind::BITSTRING.tag() as i64);
    let is_strict_proc = b.ins().icmp_imm(IntCC::Equal, tag, ValueKind::PROCBIN.tag() as i64);
    let is_strict = b.ins().bor(is_strict_bs, is_strict_proc);
    b.ins().brif(is_strict, cont, &[], ptr_path, &[]);
    b.switch_to_block(ptr_path);
    b.seal_block(ptr_path);
    b.ins().jump(miss, &[]);
    b.switch_to_block(cont);
    b.seal_block(cont);
    Ok(())
}

fn emit_dispatch_bit_size(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    field: &crate::dispatch_matrix::BitstringFieldShape,
    state: &DispatchEmitState,
) -> Result<(u32, ir::Value), CodegenError> {
    match &field.size {
        None => Ok((0, b.ins().iconst(types::I32, 0))),
        Some(BitstringFieldSize::Literal(n)) => Ok((1, b.ins().iconst(types::I32, *n as i64))),
        Some(BitstringFieldSize::Binding(subject)) => {
            let value = state
                .values
                .get(subject)
                .copied()
                .ok_or_else(|| CodegenError::new(format!("bitstring size subject {:?} not available", subject)))?;
            Ok((1, strict_int_i32(b, ctx, value)?))
        }
        Some(BitstringFieldSize::BindingName(name)) => {
            let value = state
                .direct_bindings
                .get(name)
                .copied()
                .ok_or_else(|| CodegenError::new(format!("bitstring size binding `{}` not available", name)))?;
            Ok((1, strict_int_i32(b, ctx, value)?))
        }
    }
}

fn strict_int_i32(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    v: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    let raw = receive_value_int(b, ctx, v)?;
    Ok(b.ins().ireduce(types::I32, raw))
}

fn dispatch_bit_type_tag(ty: BitstringFieldKind) -> u32 {
    match ty {
        BitstringFieldKind::Integer => 0,
        BitstringFieldKind::Float => 1,
        BitstringFieldKind::Binary => 2,
        BitstringFieldKind::Bits => 3,
        BitstringFieldKind::Utf8 => 4,
        BitstringFieldKind::Utf16 => 5,
        BitstringFieldKind::Utf32 => 6,
    }
}

fn dispatch_endian_tag(endian: BitstringEndian) -> u32 {
    match endian {
        BitstringEndian::Big => 0,
        BitstringEndian::Little => 1,
        BitstringEndian::Native => 2,
    }
}

fn default_dispatch_bit_unit(ty: BitstringFieldKind) -> u32 {
    match ty {
        BitstringFieldKind::Integer | BitstringFieldKind::Float | BitstringFieldKind::Bits => 1,
        BitstringFieldKind::Binary => 8,
        BitstringFieldKind::Utf8 | BitstringFieldKind::Utf16 | BitstringFieldKind::Utf32 => 1,
    }
}

fn emit_dispatch_guard_expr(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    expr: &ReceiveGuardExpr,
    state: &mut DispatchEmitState,
) -> Result<ReceiveValue, CodegenError> {
    Ok(match expr {
        PatternGuardExpr::Const(c) => {
            let Some(value) = dispatch_const_value(ctx.fz_module, c)? else {
                return Err(CodegenError::new(format!(
                    "guard const {:?} cannot be materialized in receive dispatch",
                    c
                )));
            };
            dispatch_const_receive_value(b, value)
        }
        PatternGuardExpr::Subject(subject) => resolve_dispatch_subject(b, ctx, *subject, state)?,
        PatternGuardExpr::Pinned(pinned) => load_pinned_dispatch_value(b, ctx, *pinned)?,
        PatternGuardExpr::Unary { op, expr } => {
            let v = emit_dispatch_guard_expr(b, ctx, expr, state)?;
            match op {
                PatternGuardUnaryOp::Not => {
                    let truthy = emit_truthy_cmp(b, ctx, v)?;
                    emit_bool_value_from_truthy(b, truthy, true)
                }
                PatternGuardUnaryOp::Neg => {
                    let z = b.ins().iconst(types::I64, 0);
                    let raw = receive_value_int(b, ctx, v)?;
                    let neg = b.ins().isub(z, raw);
                    int_value(b, neg)
                }
            }
        }
        PatternGuardExpr::Binary { op, lhs, rhs } => {
            if matches!(op, PatternGuardBinOp::And | PatternGuardBinOp::Or) {
                return emit_short_circuit_guard(b, ctx, *op, lhs, rhs, state);
            }
            let l = emit_dispatch_guard_expr(b, ctx, lhs, state)?;
            let r = emit_dispatch_guard_expr(b, ctx, rhs, state)?;
            match op {
                PatternGuardBinOp::Add => {
                    let l = receive_value_int(b, ctx, l)?;
                    let r = receive_value_int(b, ctx, r)?;
                    let sum = b.ins().iadd(l, r);
                    int_value(b, sum)
                }
                PatternGuardBinOp::Sub => {
                    let l = receive_value_int(b, ctx, l)?;
                    let r = receive_value_int(b, ctx, r)?;
                    let diff = b.ins().isub(l, r);
                    int_value(b, diff)
                }
                PatternGuardBinOp::Mul => {
                    let l = receive_value_int(b, ctx, l)?;
                    let r = receive_value_int(b, ctx, r)?;
                    let prod = b.ins().imul(l, r);
                    int_value(b, prod)
                }
                PatternGuardBinOp::Div => {
                    let l = receive_value_int(b, ctx, l)?;
                    let r = receive_value_int(b, ctx, r)?;
                    let quot = b.ins().sdiv(l, r);
                    int_value(b, quot)
                }
                PatternGuardBinOp::Rem => {
                    let l = receive_value_int(b, ctx, l)?;
                    let r = receive_value_int(b, ctx, r)?;
                    let rem = b.ins().srem(l, r);
                    int_value(b, rem)
                }
                PatternGuardBinOp::Eq => {
                    let cmp = emit_typed_eq_cmp(b, ctx, l, r)?;
                    emit_bool_value(b, cmp)
                }
                PatternGuardBinOp::Neq => {
                    let eq = emit_typed_eq_cmp(b, ctx, l, r)?;
                    let neq = b.ins().bxor_imm(eq, 1);
                    emit_bool_value(b, neq)
                }
                PatternGuardBinOp::Lt => emit_int_cmp_value(b, ctx, IntCC::SignedLessThan, l, r)?,
                PatternGuardBinOp::LtEq => emit_int_cmp_value(b, ctx, IntCC::SignedLessThanOrEqual, l, r)?,
                PatternGuardBinOp::Gt => emit_int_cmp_value(b, ctx, IntCC::SignedGreaterThan, l, r)?,
                PatternGuardBinOp::GtEq => emit_int_cmp_value(b, ctx, IntCC::SignedGreaterThanOrEqual, l, r)?,
                PatternGuardBinOp::And => {
                    unreachable!("short-circuit guard op handled before eager operands")
                }
                PatternGuardBinOp::Or => {
                    unreachable!("short-circuit guard op handled before eager operands")
                }
            }
        }
        PatternGuardExpr::Dispatch { inputs, dispatch } => {
            let values = inputs
                .iter()
                .map(|input| emit_dispatch_guard_expr(b, ctx, input, state))
                .collect::<Result<Vec<_>, _>>()?;
            emit_guard_dispatch(b, ctx, dispatch, values)?
        }
    })
}

fn emit_guard_dispatch(
    b: &mut FunctionBuilder<'_>,
    parent: &DispatchCtx<'_>,
    dispatch: &ReceiveGuardDispatch,
    inputs: Vec<ReceiveValue>,
) -> Result<ReceiveValue, CodegenError> {
    let done = b.create_block();
    b.append_block_param(done, types::I64);
    let ctx = DispatchCtx {
        process: parent.process,
        fz_module: parent.fz_module,
        tuple_schema_ids: parent.tuple_schema_ids,
        named_schema_ids: parent.named_schema_ids,
        bound_indices_per_clause: parent.bound_indices_per_clause,
        pinned_indices: parent.pinned_indices,
        pinned_ptr: parent.pinned_ptr,
        out_ptr: parent.out_ptr,
        dispatch: &dispatch.plan,
        inputs,
        binary_data_gvs: parent.binary_data_gvs,
        runtime: parent.runtime,
    };
    let mut state = DispatchEmitState::default();
    emit_guard_dispatch_node(b, &ctx, &dispatch.bodies, dispatch.plan.graph.root, done, &mut state)?;
    b.switch_to_block(done);
    b.seal_block(done);
    Ok(ReceiveValue::AnyRef(b.block_params(done)[0]))
}

fn emit_guard_dispatch_node(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    bodies: &[ReceiveGuardExpr],
    node_id: GraphNodeId,
    done: ir::Block,
    state: &mut DispatchEmitState,
) -> Result<(), CodegenError> {
    let node = ctx
        .dispatch
        .graph
        .node(node_id)
        .ok_or_else(|| CodegenError::new(format!("guard dispatch node {:?} out of bounds", node_id)))?;
    match node {
        DispatchNode::Fail => {
            let false_value = bool_const_value(b, false);
            let false_ref = emit_receive_value_ref(b, ctx, false_value)?;
            b.ins().jump(done, &[ir::BlockArg::Value(false_ref)]);
            let dead = b.create_block();
            b.switch_to_block(dead);
            b.seal_block(dead);
            Ok(())
        }
        DispatchNode::Outcome { outcome, .. } => {
            let outcome = ctx
                .dispatch
                .outcome(*outcome)
                .ok_or_else(|| CodegenError::new(format!("guard dispatch outcome {:?} out of bounds", outcome)))?;
            let body = bodies
                .get(outcome.body_id as usize)
                .ok_or_else(|| CodegenError::new(format!("guard dispatch body {} out of bounds", outcome.body_id)))?;
            let value = emit_dispatch_guard_expr(b, ctx, body, state)?;
            let value_ref = emit_receive_value_ref(b, ctx, value)?;
            b.ins().jump(done, &[ir::BlockArg::Value(value_ref)]);
            let dead = b.create_block();
            b.switch_to_block(dead);
            b.seal_block(dead);
            Ok(())
        }
        DispatchNode::Test {
            predicate,
            on_match,
            on_miss,
        } => {
            let true_b = b.create_block();
            let false_b = b.create_block();
            let true_values = emit_region_test(
                b,
                ctx,
                predicate.subject,
                &predicate.region,
                &on_match.evidence,
                true_b,
                false_b,
                state,
            )?;
            b.switch_to_block(true_b);
            b.seal_block(true_b);
            let mut true_state = state.clone();
            true_state.values.extend(true_values);
            apply_edge_evidence_to_receive_state(b, ctx, &on_match.evidence, &mut true_state)?;
            emit_guard_dispatch_node(b, ctx, bodies, on_match.target, done, &mut true_state)?;
            b.switch_to_block(false_b);
            b.seal_block(false_b);
            emit_guard_dispatch_node(b, ctx, bodies, on_miss.target, done, state)
        }
    }
}

fn emit_short_circuit_guard(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    op: PatternGuardBinOp,
    lhs: &ReceiveGuardExpr,
    rhs: &ReceiveGuardExpr,
    state: &mut DispatchEmitState,
) -> Result<ReceiveValue, CodegenError> {
    let lhs_value = emit_dispatch_guard_expr(b, ctx, lhs, state)?;
    let lhs_truthy = emit_truthy_cmp(b, ctx, lhs_value)?;
    let rhs_b = b.create_block();
    let done_b = b.create_block();
    b.append_block_param(done_b, types::I64);

    let true_value = bool_const_value(b, true);
    let false_value = bool_const_value(b, false);
    let true_ref = emit_receive_value_ref(b, ctx, true_value)?;
    let false_ref = emit_receive_value_ref(b, ctx, false_value)?;
    match op {
        PatternGuardBinOp::And => b
            .ins()
            .brif(lhs_truthy, rhs_b, &[], done_b, &[ir::BlockArg::Value(false_ref)]),
        PatternGuardBinOp::Or => b
            .ins()
            .brif(lhs_truthy, done_b, &[ir::BlockArg::Value(true_ref)], rhs_b, &[]),
        _ => unreachable!("non-short-circuit guard op"),
    };

    b.switch_to_block(rhs_b);
    b.seal_block(rhs_b);
    let mut rhs_state = state.clone();
    let rhs_value = emit_dispatch_guard_expr(b, ctx, rhs, &mut rhs_state)?;
    let rhs_truthy = emit_truthy_cmp(b, ctx, rhs_value)?;
    let rhs_bool = emit_bool_value_from_truthy(b, rhs_truthy, false);
    let rhs_ref = emit_receive_value_ref(b, ctx, rhs_bool)?;
    b.ins().jump(done_b, &[ir::BlockArg::Value(rhs_ref)]);

    b.switch_to_block(done_b);
    b.seal_block(done_b);
    Ok(ReceiveValue::AnyRef(b.block_params(done_b)[0]))
}

fn int_value(_b: &mut FunctionBuilder<'_>, raw: ir::Value) -> ReceiveValue {
    ReceiveValue::Int(raw)
}

fn bool_const_value(b: &mut FunctionBuilder<'_>, value: bool) -> ReceiveValue {
    let raw = if value { TRUE_ATOM_ID } else { FALSE_ATOM_ID };
    ReceiveValue::Atom(b.ins().iconst(types::I64, raw as i64))
}

fn emit_int_cmp_value(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    cc: IntCC,
    lhs: ReceiveValue,
    rhs: ReceiveValue,
) -> Result<ReceiveValue, CodegenError> {
    let lhs = receive_value_int(b, ctx, lhs)?;
    let rhs = receive_value_int(b, ctx, rhs)?;
    let cmp = b.ins().icmp(cc, lhs, rhs);
    Ok(emit_bool_value(b, cmp))
}

fn emit_bool_value(b: &mut FunctionBuilder<'_>, cmp: ir::Value) -> ReceiveValue {
    emit_bool_value_from_truthy(b, cmp, false)
}

fn emit_bool_value_from_truthy(b: &mut FunctionBuilder<'_>, truthy: ir::Value, invert: bool) -> ReceiveValue {
    let t = b.ins().iconst(types::I64, TRUE_ATOM_ID as i64);
    let f = b.ins().iconst(types::I64, FALSE_ATOM_ID as i64);
    let raw = if invert {
        b.ins().select(truthy, f, t)
    } else {
        b.ins().select(truthy, t, f)
    };
    ReceiveValue::Atom(raw)
}

fn emit_truthy_cmp(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    v: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match v {
        ReceiveValue::AnyRef(value_ref) => {
            let Some(fref) = ctx.runtime.truthy_ref_fref else {
                return Err(CodegenError::new("any truthiness requires fz_truthy_ref"));
            };
            let inst = b.ins().call(fref, &[value_ref]);
            let truthy = b.inst_results(inst)[0];
            let zero = b.ins().iconst(types::I8, 0);
            Ok(b.ins().icmp(IntCC::NotEqual, truthy, zero))
        }
        ReceiveValue::Atom(raw) => {
            let is_false = b.ins().icmp_imm(IntCC::Equal, raw, FALSE_ATOM_ID as i64);
            let is_nil = b.ins().icmp_imm(IntCC::Equal, raw, NIL_ATOM_ID as i64);
            let false_or_nil = b.ins().bor(is_false, is_nil);
            Ok(b.ins().bxor_imm(false_or_nil, 1))
        }
        ReceiveValue::Null => Ok(b.ins().iconst(types::I8, 0)),
        ReceiveValue::Int(_) | ReceiveValue::Float(_) | ReceiveValue::EmptyList => Ok(b.ins().iconst(types::I8, 1)),
    }
}

fn emit_typed_eq_cmp(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    lhs: ReceiveValue,
    rhs: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match (lhs, rhs) {
        (ReceiveValue::Int(a), ReceiveValue::Int(bv)) => {
            return Ok(b.ins().icmp(IntCC::Equal, a, bv));
        }
        (ReceiveValue::Float(a), ReceiveValue::Float(bv)) => {
            let a = b.ins().bitcast(types::I64, MemFlags::new(), a);
            let bv = b.ins().bitcast(types::I64, MemFlags::new(), bv);
            return Ok(b.ins().icmp(IntCC::Equal, a, bv));
        }
        (ReceiveValue::Atom(a), ReceiveValue::Atom(bv)) => {
            return Ok(b.ins().icmp(IntCC::Equal, a, bv));
        }
        (ReceiveValue::Null, ReceiveValue::Null) | (ReceiveValue::EmptyList, ReceiveValue::EmptyList) => {
            return Ok(b.ins().iconst(types::I8, 1));
        }
        _ => {}
    }
    let Some(fref) = ctx.runtime.value_eq_typed_fref else {
        return Err(CodegenError::new("mixed/ref equality requires fz_value_eq_ref"));
    };
    let lhs_ref = emit_receive_value_ref(b, ctx, lhs)?;
    let rhs_ref = emit_receive_value_ref(b, ctx, rhs)?;
    let call = b.ins().call(fref, &[ctx.process, lhs_ref, rhs_ref]);
    let eq = b.inst_results(call)[0];
    Ok(b.ins().icmp_imm(IntCC::NotEqual, eq, 0))
}

fn emit_typed_eq_branch(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    lhs: ReceiveValue,
    rhs: ReceiveValue,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let cmp = emit_typed_eq_cmp(b, ctx, lhs, rhs)?;
    b.ins().brif(cmp, match_b, &[], next_b, &[]);
    Ok(())
}

fn emit_not_dispatch_map_miss(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::Null => Ok(b.ins().iconst(types::I8, 0)),
        ReceiveValue::AnyRef(_) => {
            let tag = receive_value_tag(b, ctx, value)?;
            let tag64 = b.ins().uextend(types::I64, tag);
            Ok(b.ins().icmp_imm(IntCC::NotEqual, tag64, ValueKind::NULL.tag() as i64))
        }
        _ => Ok(b.ins().iconst(types::I8, 1)),
    }
}

fn emit_map_kind_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    val: ReceiveValue,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let Some(fref) = ctx.runtime.map_is_map_fref else {
        return Err(CodegenError::new("map-kind dispatch test requires fz_map_is_map"));
    };
    let map_ref = emit_receive_value_ref(b, ctx, val)?;
    let inst = b.ins().call(fref, &[map_ref]);
    let ok = b.inst_results(inst)[0];
    let zero = b.ins().iconst(types::I8, 0);
    let cmp = b.ins().icmp(IntCC::NotEqual, ok, zero);
    b.ins().brif(cmp, match_b, &[], next_b, &[]);
    Ok(())
}

/// Chain of equality / load checks that verifies `val` is a tuple of
/// the given arity. Branches to `match_b` on success, `next_b` on any
/// mismatch. Mirrors `compile_tuple_shape` but parameterised on match
/// vs miss target blocks.
fn emit_tuple_arity_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    tuple_schema_ids: &HashMap<usize, u32>,
    val: ReceiveValue,
    arity: usize,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let expected_schema_id = *tuple_schema_ids.get(&arity).ok_or_else(|| {
        CodegenError::new(format!(
            "dispatch tuple arity {} not pre-registered (compile() walk missed it?)",
            arity
        ))
    })?;

    let tag = receive_value_tag(b, ctx, val)?;
    let tag64 = b.ins().uextend(types::I64, tag);
    let c0 = b.create_block();
    let cmp0 = b.ins().icmp_imm(IntCC::Equal, tag64, ValueKind::STRUCT.tag() as i64);
    b.ins().brif(cmp0, c0, &[], next_b, &[]);
    b.switch_to_block(c0);
    b.seal_block(c0);

    let Some(fref) = ctx.runtime.struct_schema_id_ref_fref else {
        return Err(CodegenError::new(
            "tuple arity dispatch test requires fz_struct_schema_id_ref",
        ));
    };
    let struct_ref = emit_receive_value_ref(b, ctx, val)?;
    let inst = b.ins().call(fref, &[struct_ref]);
    let schema = b.inst_results(inst)[0];
    let schema_want = b.ins().iconst(types::I32, expected_schema_id as i64);
    let cmp4 = b.ins().icmp(IntCC::Equal, schema, schema_want);
    b.ins().brif(cmp4, match_b, &[], next_b, &[]);
    Ok(())
}

fn collect_binary_literals_in_dispatch(dispatch: &ReceiveDispatchPlan, out: &mut Vec<Vec<u8>>) {
    for key in &dispatch.prepared_keys {
        collect_binary_literals_in_const(key, out);
    }
    for arm in &dispatch.matrix.arms {
        for question in &arm.questions {
            collect_binary_literals_in_region(&question.predicate.region, out);
        }
    }
    for guard in &dispatch.guards {
        collect_binary_literals_in_guard(guard, out);
    }
}

fn collect_binary_literals_in_region(region: &ReceiveRegion, out: &mut Vec<Vec<u8>>) {
    match region {
        Region::Equal(ComparisonValue::Const(value)) | Region::MapKeyPresent { key: value } => {
            collect_binary_literals_in_const(value, out);
        }
        Region::Any
        | Region::Never
        | Region::Type(_)
        | Region::Equal(ComparisonValue::Pinned(_))
        | Region::TupleArity(_)
        | Region::List(_)
        | Region::MapKind
        | Region::Bitstring(_)
        | Region::Guard(_) => {}
    }
}

fn collect_binary_literals_in_guard(expr: &ReceiveGuardExpr, out: &mut Vec<Vec<u8>>) {
    match expr {
        PatternGuardExpr::Const(value) => collect_binary_literals_in_const(value, out),
        PatternGuardExpr::Unary { expr, .. } => collect_binary_literals_in_guard(expr, out),
        PatternGuardExpr::Binary { lhs, rhs, .. } => {
            collect_binary_literals_in_guard(lhs, out);
            collect_binary_literals_in_guard(rhs, out);
        }
        PatternGuardExpr::Dispatch { inputs, dispatch } => {
            for input in inputs {
                collect_binary_literals_in_guard(input, out);
            }
            collect_binary_literals_in_dispatch(&dispatch.plan, out);
            for body in &dispatch.bodies {
                collect_binary_literals_in_guard(body, out);
            }
        }
        PatternGuardExpr::Subject(_) | PatternGuardExpr::Pinned(_) => {}
    }
}

fn collect_binary_literals_in_const(value: &DispatchConst, out: &mut Vec<Vec<u8>>) {
    if let DispatchConst::Utf8Binary(bytes) = value {
        out.push(bytes.clone());
    }
}

/// Emit the call sequence that compares `val` against a constant byte
/// literal via `fz_matcher_eq_bytes`. Branches to `match_b` when the
/// helper returns 1, `next_b` when it returns 0. Errors when the runtime
/// helper isn't linked (unit-test mode).
fn emit_binary_literal_test(
    b: &mut FunctionBuilder<'_>,
    binary_data_gvs: &HashMap<Vec<u8>, ir::GlobalValue>,
    matcher_eq_bytes_fref: Option<ir::FuncRef>,
    val: ir::Value,
    bytes: &[u8],
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let Some(fref) = matcher_eq_bytes_fref else {
        return Err(CodegenError::new(
            "Pattern::Binary in receive dispatch requires fz_matcher_eq_bytes; \
             runtime not linked in this context",
        ));
    };
    let gv = binary_data_gvs.get(bytes).ok_or_else(|| {
        CodegenError::new(format!(
            "Binary literal of {} bytes missing pre-declared .data symbol",
            bytes.len()
        ))
    })?;
    let bytes_ptr = b.ins().symbol_value(types::I64, *gv);
    let byte_len = b.ins().iconst(types::I64, bytes.len() as i64);
    let inst = b.ins().call(fref, &[val, bytes_ptr, byte_len]);
    let res = b.inst_results(inst)[0];
    let zero = b.ins().iconst(types::I32, 0);
    let cmp = b.ins().icmp(IntCC::NotEqual, res, zero);
    b.ins().brif(cmp, match_b, &[], next_b, &[]);
    Ok(())
}

/// Verify `val` is a List cons cell. Strict list cells are headerless
/// and carried by the `TAG_LIST` low nibble, so this routes through the
/// runtime predicate instead of reading a prefix kind.
fn emit_list_cons_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &DispatchCtx<'_>,
    val: ReceiveValue,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let Some(fref) = ctx.runtime.list_is_cons_fref else {
        return Err(CodegenError::new("list-cons dispatch test requires fz_list_is_cons"));
    };
    let list_ref = emit_receive_value_ref(b, ctx, val)?;
    let inst = b.ins().call(fref, &[list_ref]);
    let ok = b.inst_results(inst)[0];
    let zero = b.ins().iconst(types::I8, 0);
    let cmp = b.ins().icmp(IntCC::NotEqual, ok, zero);
    b.ins().brif(cmp, match_b, &[], next_b, &[]);
    Ok(())
}

#[cfg(test)]
#[path = "receive_test.rs"]
mod receive_test;
