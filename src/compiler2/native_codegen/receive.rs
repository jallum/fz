//! Selective-receive dispatch fn codegen.
//!
//! Emits the leaf dispatch fn for a `Term::ReceiveMatched`. The runtime
//! ABI matches `fz_runtime::park::MatcherFn` (see runtime/src/park.rs):
//!
//! ```text
//! extern "C" fn(
//!     process: *mut Process,
//!     msg_ref: u64,
//!     pinned: *const AnyValueRef,
//!     out: *mut AnyValueRef,
//! ) -> u32
//! ```
//!
//! - `process`: the receiving process the dispatch runs under.
//! - `msg_ref`: one-word tagged candidate message.
//! - `pinned`: pointer to `AnyValueRef` entries, in the order
//!   they appear in `Term::ReceiveMatched::pinned`.
//! - `out`: caller-supplied `[AnyValueRef; bound_arity]`
//!   scratch buffer; the dispatch writes the winning edge's semantic and
//!   physical arguments at the receiving parameter slots.
//! - returns `0` on miss; `k > 0` is the 1-based clause index (caller
//!   indexes `clause_bodies[k-1]`).
//!
//! Production codegen consumes the cached AST-free `PatternDispatchPlan`
//! attached to `Term::ReceiveMatched`; it does not rebuild source clauses.

use crate::dispatch_matrix::pattern::{
    PatternDispatchPlan, PatternGuardBinOp, PatternGuardDispatch, PatternGuardExpr, PatternGuardUnaryOp,
};
use crate::dispatch_matrix::{
    BitstringEndian, BitstringFieldKind, BitstringFieldSize, BitstringShape, ComparisonValue, DispatchNode,
    EdgeEvidence, GraphNodeId, GroundValue, ListRegion, PinnedValueId, ProjectionKind, Region, SubjectId,
    SubjectSource,
};
use crate::fz_ir::{Module, ReceiveClause, Var};

use super::runtime_test::{KindEvidence, RuntimeTestEmitter, emit_runtime_type_test};
use crate::runtime_type_predicate::{CallableShapes, RuntimeTypePredicate};
use cranelift_codegen::ir::{self, AbiParam, InstBuilder, MemFlags, Signature, condcodes::IntCC, types};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage};
use fz_runtime::any_value::{AnyValueRef, FALSE_ATOM_ID, NIL_ATOM_ID, TRUE_ATOM_ID, ValueKind};
use fz_runtime::ir_runtime::{
    fz_box_atom_for_any, fz_box_float_for_any, fz_box_int_for_any, fz_bs_field_spec, fz_bs_read_field_ref,
    fz_bs_reader_init_ref, fz_list_head_ref, fz_list_is_cons, fz_list_tail_ref, fz_map_is_map, fz_matcher_eq_bytes,
    fz_matcher_map_get_ref, fz_struct_get_field_ref, fz_struct_get_named_field_ref, fz_struct_schema_id_ref,
    fz_truthy_ref, fz_type_of, fz_unbox_atom, fz_unbox_float, fz_unbox_int, fz_value_eq_ref,
};
use std::collections::HashMap;

use super::runtime_call::{RuntimeCaller, RuntimeFn, declare_runtime_fn, runtime_call, runtime_call1};
use super::{CodegenError, SLOT_BYTES, emit_fn_body};

type ReceiveDispatchPlan = PatternDispatchPlan<RuntimeTypePredicate>;
type ReceiveRegion = Region<RuntimeTypePredicate>;
type ReceiveEdgeEvidence = EdgeEvidence<RuntimeTypePredicate>;
type ReceiveGuardExpr = PatternGuardExpr<RuntimeTypePredicate>;
type ReceiveGuardDispatch = PatternGuardDispatch<RuntimeTypePredicate>;

/// Cranelift signature for the receive dispatch fn family. The runtime keeps a
/// dispatch fn's address in a `fz_runtime::park::MatcherFn` pointer and calls
/// it as a C function, so the target names the convention.
pub(crate) fn receive_dispatch_signature<M: cranelift_module::Module>(module: &mut M) -> Signature {
    let mut sig = module.make_signature();
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
    let sig = receive_dispatch_signature(module);
    module
        .declare_function(name, Linkage::Local, &sig)
        .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))
}

/// The dispatch body under construction: the module that declares a runtime
/// helper's symbol, the builder that emits the call, and the helpers this
/// body has already declared. A helper is declared on first use and reused
/// afterwards, so a body names each symbol once however often it calls it.
///
/// The dispatch body is not a `CodegenFn`: it is entered from Rust rather
/// than through the pinned-register ABI, so it carries its `Process*` as an
/// ordinary parameter (see [`DispatchCtx::process`]).
struct DispatchBody<'a, 'fb, M: cranelift_module::Module> {
    b: &'a mut FunctionBuilder<'fb>,
    module: &'a mut M,
    runtime_funcs: HashMap<&'static str, ir::FuncRef>,
}

impl<'a, 'fb, M: cranelift_module::Module> DispatchBody<'a, 'fb, M> {
    fn new(b: &'a mut FunctionBuilder<'fb>, module: &'a mut M) -> Self {
        Self {
            b,
            module,
            runtime_funcs: HashMap::new(),
        }
    }
}

impl<M: cranelift_module::Module> RuntimeCaller for DispatchBody<'_, '_, M> {
    fn runtime_func_ref<F: RuntimeFn + Copy>(&mut self, name: &'static str, item: F) -> ir::FuncRef {
        if let Some(&callee) = self.runtime_funcs.get(name) {
            return callee;
        }
        let id = declare_runtime_fn(self.module, name, item);
        let callee = self.module.declare_func_in_func(id, self.b.func);
        self.runtime_funcs.insert(name, callee);
        callee
    }

    fn emit_call(&mut self, callee: ir::FuncRef, args: &[ir::Value]) -> ir::Inst {
        self.b.ins().call(callee, args)
    }

    fn sole_result(&self, call: ir::Inst) -> ir::Value {
        self.b.inst_results(call)[0]
    }
}

/// Emit the receive ABI dispatch directly from the cached AST-free
/// [`PatternDispatchPlan`]. Each winning edge names exact subjects and the
/// receiving function's actual parameter identities.
pub(crate) fn emit_receive_dispatch_body<M: cranelift_module::Module>(
    module: &mut M,
    fbctx: &mut FunctionBuilderContext,
    dispatch_id: FuncId,
    fz_module: &Module,
    tuple_schema_ids: &HashMap<usize, u32>,
    named_schema_ids: &HashMap<fz_runtime::module_name::ModuleName, u32>,
    pinned: &[Var],
    clauses: &[ReceiveClause],
    dispatch: &ReceiveDispatchPlan,
) -> Result<(), CodegenError> {
    let expected = dispatch.pinned.len() + dispatch.prepared_keys.len();
    if pinned.len() != expected {
        return Err(CodegenError::new(format!(
            "receive dispatch expects {expected} plan operands, got {}",
            pinned.len()
        )));
    }

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
    let sig = receive_dispatch_signature(module);
    let defined = emit_fn_body(module, fbctx, sig, dispatch_id, |m, b| {
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
        let mut body = DispatchBody::new(b, m);

        let ctx = DispatchCtx {
            process,
            fz_module,
            tuple_schema_ids,
            named_schema_ids,
            outcomes: clauses,
            bindings: crate::compiler2::DispatchBindings {
                pinned: (0..dispatch.pinned.len())
                    .map(|index| load_receive_value_ref(body.b, pinned_ptr, index))
                    .collect(),
                prepared: (0..dispatch.prepared_keys.len())
                    .map(|index| load_receive_value_ref(body.b, pinned_ptr, dispatch.pinned.len() + index))
                    .collect(),
            },
            out_ptr,
            dispatch,
            inputs: vec![msg],
            binary_data_gvs: &binary_data_gvs,
        };

        let mut state = DispatchEmitState::default();
        if let Err(e) = emit_dispatch_node(&mut body, &ctx, dispatch.graph.root, miss_block, &mut state) {
            compile_err = Some(e);
            finish_failed_dispatch_body(body.b, miss_block);
            return;
        }

        body.b.switch_to_block(miss_block);
        body.b.seal_block(miss_block);
        let zero = body.b.ins().iconst(types::I32, 0);
        body.b.ins().return_(&[zero]);
    })
    .map_err(|e| CodegenError::new(format!("define receive dispatch fn: {}", e)));

    if let Some(e) = compile_err {
        return Err(e);
    }
    defined
}

#[derive(Clone, Copy)]
enum ReceiveValue {
    AnyRef(ir::Value),
    Int(ir::Value),
    Float(ir::Value),
    Atom(ir::Value),
}

struct DispatchCtx<'a> {
    /// The running receiver's `Process*` (dispatch fn's first param). Field
    /// projections that need heap state (struct fields via the schema registry,
    /// map values) pass it to their BIFs. The dispatch fn is invoked from Rust,
    /// not through the pinned-register ABI, so it carries the process explicitly.
    process: ir::Value,
    fz_module: &'a Module,
    tuple_schema_ids: &'a HashMap<usize, u32>,
    named_schema_ids: &'a HashMap<fz_runtime::module_name::ModuleName, u32>,
    outcomes: &'a [ReceiveClause],
    bindings: crate::compiler2::DispatchBindings<ReceiveValue>,
    out_ptr: ir::Value,
    dispatch: &'a ReceiveDispatchPlan,
    inputs: Vec<ReceiveValue>,
    binary_data_gvs: &'a HashMap<Vec<u8>, ir::GlobalValue>,
}

#[derive(Default, Clone)]
struct DispatchEmitState {
    values: HashMap<SubjectId, ReceiveValue>,
}

fn emit_receive_value_ref<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::AnyRef(value_ref) => Ok(value_ref),
        ReceiveValue::Int(raw) => Ok(runtime_call1!(body, fz_box_int_for_any, [ctx.process, raw])),
        ReceiveValue::Float(raw) => Ok(runtime_call1!(body, fz_box_float_for_any, [ctx.process, raw])),
        ReceiveValue::Atom(raw) => Ok(runtime_call1!(body, fz_box_atom_for_any, [ctx.process, raw])),
    }
}

fn receive_value_from_ref_word(_b: &mut FunctionBuilder<'_>, value_ref: ir::Value) -> ReceiveValue {
    ReceiveValue::AnyRef(value_ref)
}

fn receive_value_tag<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::AnyRef(value_ref) => Ok(runtime_call1!(body, fz_type_of, [value_ref])),
        ReceiveValue::Int(_) => Ok(body.b.ins().iconst(types::I8, ValueKind::INT.tag() as i64)),
        ReceiveValue::Float(_) => Ok(body.b.ins().iconst(types::I8, ValueKind::FLOAT.tag() as i64)),
        ReceiveValue::Atom(_) => Ok(body.b.ins().iconst(types::I8, ValueKind::ATOM.tag() as i64)),
    }
}

fn receive_value_int<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::Int(raw) => Ok(raw),
        ReceiveValue::AnyRef(value_ref) => Ok(runtime_call1!(body, fz_unbox_int, [value_ref])),
        ReceiveValue::Float(_) | ReceiveValue::Atom(_) => Err(CodegenError::new("expected int receive value")),
    }
}

fn receive_value_float<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::Float(raw) => Ok(raw),
        ReceiveValue::AnyRef(value_ref) => Ok(runtime_call1!(body, fz_unbox_float, [value_ref])),
        ReceiveValue::Int(_) | ReceiveValue::Atom(_) => Err(CodegenError::new("expected float receive value")),
    }
}

fn receive_value_atom<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::Atom(raw) => Ok(raw),
        ReceiveValue::AnyRef(value_ref) => Ok(runtime_call1!(body, fz_unbox_atom, [value_ref])),
        ReceiveValue::Int(_) | ReceiveValue::Float(_) => Err(CodegenError::new("expected atom receive value")),
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

fn store_receive_value_ref<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    ctx: &DispatchCtx<'_>,
    base: ir::Value,
    idx: usize,
    value: ReceiveValue,
) -> Result<(), CodegenError> {
    let value_ref = emit_receive_value_ref(body, ctx, value)?;
    body.b
        .ins()
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

fn emit_dispatch_node<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
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
            body.b.ins().jump(miss, &[]);
            let dead = body.b.create_block();
            body.b.switch_to_block(dead);
            body.b.seal_block(dead);
            Ok(())
        }
        DispatchNode::Outcome { outcome, .. } => {
            let (clause_index, edge) = ctx
                .outcomes
                .iter()
                .enumerate()
                .find(|(_, edge)| edge.outcome == *outcome)
                .ok_or_else(|| CodegenError::new(format!("dispatch outcome {:?} has no target edge", outcome)))?;
            let target = ctx.fz_module.fn_by_id(edge.body);
            let parameters = &target.blocks[target.entry.0 as usize].params;
            for (subject, parameter) in &edge.arguments {
                let value = resolve_dispatch_subject(body, ctx, *subject, state)?;
                let slot = parameters
                    .iter()
                    .position(|candidate| candidate == parameter)
                    .expect("receive argument names an actual target parameter");
                assert!(slot < edge.arguments.len(), "receive arguments precede captures");
                store_receive_value_ref(body, ctx, ctx.out_ptr, slot, value)?;
            }
            let k = body.b.ins().iconst(types::I32, (clause_index + 1) as i64);
            body.b.ins().return_(&[k]);
            let dead = body.b.create_block();
            body.b.switch_to_block(dead);
            body.b.seal_block(dead);
            Ok(())
        }
        DispatchNode::Test {
            predicate,
            on_match,
            on_miss,
        } => {
            let true_b = body.b.create_block();
            let false_b = body.b.create_block();
            let true_values = emit_region_test(
                body,
                ctx,
                predicate.subject,
                &predicate.region,
                &on_match.evidence,
                true_b,
                false_b,
                state,
            )?;
            body.b.switch_to_block(true_b);
            body.b.seal_block(true_b);
            let mut true_state = state.clone();
            true_state.values.extend(true_values);
            apply_edge_evidence_to_receive_state(body, ctx, &on_match.evidence, &mut true_state)?;
            emit_dispatch_node(body, ctx, on_match.target, miss, &mut true_state)?;
            body.b.switch_to_block(false_b);
            body.b.seal_block(false_b);
            emit_dispatch_node(body, ctx, on_miss.target, miss, state)
        }
    }
}

fn resolve_dispatch_subject<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
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
                let parent = resolve_dispatch_subject(body, ctx, projection.source, state)?;
                emit_struct_get_field(body, ctx, parent, *index)?
            }
            ProjectionKind::StructField(field) => {
                let parent = resolve_dispatch_subject(body, ctx, projection.source, state)?;
                let atom_id = ctx
                    .fz_module
                    .atom_names
                    .iter()
                    .position(|name| name == field)
                    .ok_or_else(|| CodegenError::new(format!("field atom `{field}` not interned")))?;
                let parent = emit_receive_value_ref(body, ctx, parent)?;
                let atom = body.b.ins().iconst(types::I64, atom_id as i64);
                let field_ref = runtime_call1!(body, fz_struct_get_named_field_ref, [ctx.process, parent, atom]);
                receive_value_from_ref_word(body.b, field_ref)
            }
            ProjectionKind::ListHead => {
                let parent = resolve_dispatch_subject(body, ctx, projection.source, state)?;
                let parent_ref = emit_receive_value_ref(body, ctx, parent)?;
                let out_ref = runtime_call1!(body, fz_list_head_ref, [parent_ref]);
                receive_value_from_ref_word(body.b, out_ref)
            }
            ProjectionKind::ListTail => {
                let parent = resolve_dispatch_subject(body, ctx, projection.source, state)?;
                let parent_ref = emit_receive_value_ref(body, ctx, parent)?;
                let out_ref = runtime_call1!(body, fz_list_tail_ref, [parent_ref]);
                receive_value_from_ref_word(body.b, out_ref)
            }
            ProjectionKind::MapValue { key } => {
                let map = resolve_dispatch_subject(body, ctx, projection.source, state)?;
                emit_dispatch_map_get_value(body, ctx, map, key)?
            }
            ProjectionKind::BitstringField(_) => {
                return Err(CodegenError::new(
                    "receive bitstring subject lacks successful extraction evidence",
                ));
            }
        },
    };
    state.values.insert(subject, v);
    Ok(v)
}

fn load_pinned_dispatch_value(ctx: &DispatchCtx<'_>, pinned: PinnedValueId) -> Result<ReceiveValue, CodegenError> {
    ctx.bindings.pinned.get(pinned.0 as usize).copied().ok_or_else(|| {
        CodegenError::new(format!(
            "dispatch pinned operand {:?} is missing from its owning plan",
            pinned
        ))
    })
}

fn emit_region_test<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
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
        Region::Type(predicate) => {
            let val = resolve_dispatch_subject(body, ctx, subject, state)?;
            emit_runtime_type_predicate_region_test(body, ctx, val, predicate, true_b, false_b)?;
        }
        Region::Equal(ComparisonValue::Const(value)) => {
            let val = resolve_dispatch_subject(body, ctx, subject, state)?;
            emit_dispatch_const_test(body, ctx, val, value, true_b, false_b)?;
        }
        Region::Equal(ComparisonValue::Pinned(pinned)) => {
            let val = resolve_dispatch_subject(body, ctx, subject, state)?;
            let want = load_pinned_dispatch_value(ctx, *pinned)?;
            emit_typed_eq_branch(body, ctx, val, want, true_b, false_b)?;
        }
        Region::TupleArity(arity) => {
            let val = resolve_dispatch_subject(body, ctx, subject, state)?;
            emit_tuple_arity_test(body, ctx, ctx.tuple_schema_ids, val, *arity as usize, true_b, false_b)?;
        }
        Region::List(ListRegion::Empty) => {
            let val = resolve_dispatch_subject(body, ctx, subject, state)?;
            emit_list_empty_test(body.b, val, true_b, false_b);
        }
        Region::List(ListRegion::Cons) => {
            let val = resolve_dispatch_subject(body, ctx, subject, state)?;
            emit_list_cons_test(body, ctx, val, true_b, false_b)?;
        }
        Region::MapKind => {
            let val = resolve_dispatch_subject(body, ctx, subject, state)?;
            emit_map_kind_test(body, ctx, val, true_b, false_b)?;
        }
        Region::MapKeyPresent { key } => {
            let val = resolve_dispatch_subject(body, ctx, subject, state)?;
            let got = emit_dispatch_map_get_value(body, ctx, val, key)?;
            for result in &evidence.projections {
                if let SubjectSource::Projection(projection) = ctx.dispatch.subject(*result)
                    && projection.source == subject
                    && matches!(&projection.kind, ProjectionKind::MapValue { key: projection_key } if projection_key == key)
                {
                    true_values.push((*result, got));
                }
            }
            let cmp = emit_not_dispatch_map_miss(body, got)?;
            body.b.ins().brif(cmp, true_b, &[], false_b, &[]);
        }
        Region::Bitstring(shape) => {
            emit_bitstring_test(body, ctx, subject, shape, true_b, false_b, state)?;
        }
        Region::Guard(guard) => {
            let expr = ctx
                .dispatch
                .guards
                .get(guard.0 as usize)
                .ok_or_else(|| CodegenError::new(format!("dispatch guard {:?} out of bounds", guard)))?;
            let value = emit_dispatch_guard_expr(body, ctx, expr, state)?;
            let truthy = emit_truthy_cmp(body, value)?;
            body.b.ins().brif(truthy, true_b, &[], false_b, &[]);
        }
    }
    Ok(true_values)
}

/// A receive plan's runtime type test, asked through the one shared emitter.
fn emit_runtime_type_predicate_region_test<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    ctx: &DispatchCtx<'_>,
    value: ReceiveValue,
    predicate: &RuntimeTypePredicate,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let flag = {
        let mut emitter = ReceiveTestEmitter { body: &mut *body, ctx };
        emit_runtime_type_test(&mut emitter, value, predicate)?
    };
    body.b.ins().brif(flag, match_b, &[], next_b, &[]);
    Ok(())
}

/// The receive-plan door onto the shared runtime-test emitter.
struct ReceiveTestEmitter<'a, 'b, 'f, 'c, M: cranelift_module::Module> {
    body: &'a mut DispatchBody<'b, 'f, M>,
    ctx: &'a DispatchCtx<'c>,
}

impl<'f, M: cranelift_module::Module> RuntimeTestEmitter<'f> for ReceiveTestEmitter<'_, '_, 'f, '_, M> {
    type Value = ReceiveValue;

    fn builder(&mut self) -> &mut FunctionBuilder<'f> {
        self.body.b
    }

    fn atom_names(&self) -> &[String] {
        &self.ctx.fz_module.atom_names
    }

    fn tuple_schema_ids(&self) -> &HashMap<usize, u32> {
        self.ctx.tuple_schema_ids
    }

    fn named_schema_ids(&self) -> &HashMap<fz_runtime::module_name::ModuleName, u32> {
        self.ctx.named_schema_ids
    }

    fn kind_evidence(&self, value: ReceiveValue) -> KindEvidence {
        match value {
            ReceiveValue::AnyRef(_) => KindEvidence::Tagged,
            ReceiveValue::Int(_) => KindEvidence::Unboxed(ValueKind::INT),
            ReceiveValue::Float(_) => KindEvidence::Unboxed(ValueKind::FLOAT),
            ReceiveValue::Atom(_) => KindEvidence::Unboxed(ValueKind::ATOM),
        }
    }

    fn kind_flag(&mut self, value: ReceiveValue, kind: ValueKind) -> Result<ir::Value, CodegenError> {
        emit_receive_value_kind_flag(self.body, value, kind)
    }

    fn raw_int(&mut self, value: ReceiveValue) -> Result<ir::Value, CodegenError> {
        receive_value_int(self.body, value)
    }

    fn raw_float_bits(&mut self, value: ReceiveValue) -> Result<ir::Value, CodegenError> {
        let raw = receive_value_float(self.body, value)?;
        Ok(self.body.b.ins().bitcast(types::I64, MemFlags::new(), raw))
    }

    fn raw_atom(&mut self, value: ReceiveValue) -> Result<ir::Value, CodegenError> {
        receive_value_atom(self.body, value)
    }

    fn empty_list_flag(&mut self, value: ReceiveValue) -> Result<ir::Value, CodegenError> {
        emit_receive_is_empty_list_flag(self.body, value)
    }

    fn cons_flag(&mut self, value: ReceiveValue) -> Result<ir::Value, CodegenError> {
        emit_receive_is_list_cons_flag(self.body, value)
    }

    fn schema_id(&mut self, value: ReceiveValue) -> Result<ir::Value, CodegenError> {
        let struct_ref = emit_receive_value_ref(self.body, self.ctx, value)?;
        let raw = runtime_call1!(self.body, fz_struct_schema_id_ref, [struct_ref]);
        Ok(self.body.b.ins().uextend(types::I64, raw))
    }

    fn tuple_field(&mut self, value: ReceiveValue, index: usize) -> Result<ReceiveValue, CodegenError> {
        emit_struct_get_field_value(self.body, self.ctx, value, index as u32)
    }

    fn list_head(&mut self, value: ReceiveValue) -> Result<ReceiveValue, CodegenError> {
        let list_ref = emit_receive_value_ref(self.body, self.ctx, value)?;
        let head_ref = runtime_call1!(self.body, fz_list_head_ref, [list_ref]);
        Ok(receive_value_from_ref_word(self.body.b, head_ref))
    }

    fn closure_code(&mut self, _value: ReceiveValue) -> Result<ir::Value, CodegenError> {
        Err(CodegenError::new(RECEIVE_NAMES_NO_CALLABLE))
    }

    fn callable_addresses(&mut self, _callables: &CallableShapes) -> Result<Vec<ir::Value>, CodegenError> {
        // A receive plan's questions come from message PATTERNS and from
        // parameter annotations, and neither language can name one callable:
        // the finest a source can say is "a function". So the callable axis
        // arrives here as all-or-nothing, and a finite set would mean some
        // other producer started routing on callable identity without teaching
        // this door to read one (fz-kdt.125).
        Err(CodegenError::new(RECEIVE_NAMES_NO_CALLABLE))
    }
}

const RECEIVE_NAMES_NO_CALLABLE: &str =
    "receive dispatch cannot test callable identity: no message pattern can name one callable";

fn emit_receive_value_kind_flag<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    value: ReceiveValue,
    kind: ValueKind,
) -> Result<ir::Value, CodegenError> {
    let tag = receive_value_tag(body, value)?;
    let tag64 = body.b.ins().uextend(types::I64, tag);
    Ok(body.b.ins().icmp_imm(IntCC::Equal, tag64, kind.tag() as i64))
}

fn emit_receive_is_empty_list_flag<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    Ok(match value {
        ReceiveValue::AnyRef(value_ref) => {
            let tag = receive_value_tag(body, value)?;
            let tag64 = body.b.ins().uextend(types::I64, tag);
            let empty = body
                .b
                .ins()
                .iconst(types::I64, AnyValueRef::empty_list().raw_word() as i64);
            let is_list = body.b.ins().icmp_imm(IntCC::Equal, tag64, ValueKind::LIST.tag() as i64);
            let is_empty = body.b.ins().icmp(IntCC::Equal, value_ref, empty);
            body.b.ins().band(is_list, is_empty)
        }
        ReceiveValue::Int(_) | ReceiveValue::Float(_) | ReceiveValue::Atom(_) => body.b.ins().iconst(types::I8, 0),
    })
}

fn emit_receive_is_list_cons_flag<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    Ok(match value {
        ReceiveValue::AnyRef(value_ref) => {
            let tag = receive_value_tag(body, value)?;
            let tag64 = body.b.ins().uextend(types::I64, tag);
            let empty = body
                .b
                .ins()
                .iconst(types::I64, AnyValueRef::empty_list().raw_word() as i64);
            let is_list = body.b.ins().icmp_imm(IntCC::Equal, tag64, ValueKind::LIST.tag() as i64);
            let is_empty = body.b.ins().icmp(IntCC::Equal, value_ref, empty);
            let not_empty = body.b.ins().icmp_imm(IntCC::Equal, is_empty, 0);
            body.b.ins().band(is_list, not_empty)
        }
        ReceiveValue::Int(_) | ReceiveValue::Float(_) | ReceiveValue::Atom(_) => body.b.ins().iconst(types::I8, 0),
    })
}

fn apply_edge_evidence_to_receive_state<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    ctx: &DispatchCtx<'_>,
    evidence: &ReceiveEdgeEvidence,
    state: &mut DispatchEmitState,
) -> Result<(), CodegenError> {
    for projection in &evidence.projections {
        if state.values.contains_key(projection) {
            continue;
        }

        let value = resolve_dispatch_subject(body, ctx, *projection, state)?;
        state.values.insert(*projection, value);
    }
    Ok(())
}

fn emit_dispatch_side_tag_const_test<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    ctx: &DispatchCtx<'_>,
    val: ReceiveValue,
    value: &GroundValue,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<bool, CodegenError> {
    let Some(want) = dispatch_const_value(ctx.fz_module, value)? else {
        return Ok(false);
    };
    match val {
        ReceiveValue::Int(raw) => {
            let DispatchConstValue::Int(want) = want else {
                body.b.ins().jump(next_b, &[]);
                return Ok(true);
            };
            let ok = body.b.ins().icmp_imm(IntCC::Equal, raw, want);
            body.b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        ReceiveValue::Float(raw) => {
            let DispatchConstValue::Float(want) = want else {
                body.b.ins().jump(next_b, &[]);
                return Ok(true);
            };
            let raw_bits = body.b.ins().bitcast(types::I64, MemFlags::new(), raw);
            let want_bits = body.b.ins().iconst(types::I64, want as i64);
            let ok = body.b.ins().icmp(IntCC::Equal, raw_bits, want_bits);
            body.b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        ReceiveValue::Atom(raw) => {
            let DispatchConstValue::Atom(want) = want else {
                body.b.ins().jump(next_b, &[]);
                return Ok(true);
            };
            let ok = body.b.ins().icmp_imm(IntCC::Equal, raw, want as i64);
            body.b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        ReceiveValue::AnyRef(value_ref) => {
            emit_any_ref_const_test(body, value_ref, want, match_b, next_b)?;
        }
    }
    Ok(true)
}

fn emit_any_ref_const_test<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    value_ref: ir::Value,
    want: DispatchConstValue,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let want_tag = want.kind();
    let tag = receive_value_tag(body, ReceiveValue::AnyRef(value_ref))?;
    let tag64 = body.b.ins().uextend(types::I64, tag);
    let type_ok = body.b.ins().icmp_imm(IntCC::Equal, tag64, want_tag.tag() as i64);
    let value_block = body.b.create_block();
    body.b.ins().brif(type_ok, value_block, &[], next_b, &[]);
    body.b.switch_to_block(value_block);
    body.b.seal_block(value_block);
    match want {
        DispatchConstValue::Int(want) => {
            let raw = receive_value_int(body, ReceiveValue::AnyRef(value_ref))?;
            let ok = body.b.ins().icmp_imm(IntCC::Equal, raw, want);
            body.b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        DispatchConstValue::Float(want) => {
            let raw = receive_value_float(body, ReceiveValue::AnyRef(value_ref))?;
            let raw_bits = body.b.ins().bitcast(types::I64, MemFlags::new(), raw);
            let want_bits = body.b.ins().iconst(types::I64, want as i64);
            let ok = body.b.ins().icmp(IntCC::Equal, raw_bits, want_bits);
            body.b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        DispatchConstValue::Atom(want) => {
            let raw = receive_value_atom(body, ReceiveValue::AnyRef(value_ref))?;
            let ok = body.b.ins().icmp_imm(IntCC::Equal, raw, want as i64);
            body.b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
    }
    Ok(())
}

fn dispatch_const_value(module: &Module, value: &GroundValue) -> Result<Option<DispatchConstValue>, CodegenError> {
    use crate::ground_value::DispatchShape;
    Ok(
        match value
            .as_dispatch_shape()
            .expect("dispatch_const_value only ever sees a dispatch-matrix const")
        {
            DispatchShape::Int(n) => Some(DispatchConstValue::Int(n)),
            DispatchShape::Float(bits) => Some(DispatchConstValue::Float(bits)),
            DispatchShape::Atom(name) => module
                .atom_names
                .iter()
                .position(|n| n == name)
                .map(|id| DispatchConstValue::Atom(id as u64)),
            DispatchShape::Bool(v) => Some(DispatchConstValue::Atom(if v {
                TRUE_ATOM_ID as u64
            } else {
                FALSE_ATOM_ID as u64
            })),
            DispatchShape::Nil => Some(DispatchConstValue::Atom(NIL_ATOM_ID as u64)),
            DispatchShape::Utf8Binary(_) => None,
        },
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DispatchConstValue {
    Int(i64),
    Float(u64),
    Atom(u64),
}

impl DispatchConstValue {
    fn kind(self) -> ValueKind {
        match self {
            DispatchConstValue::Int(_) => ValueKind::INT,
            DispatchConstValue::Float(_) => ValueKind::FLOAT,
            DispatchConstValue::Atom(_) => ValueKind::ATOM,
        }
    }
}

fn dispatch_const_receive_value(b: &mut FunctionBuilder<'_>, value: DispatchConstValue) -> ReceiveValue {
    match value {
        DispatchConstValue::Int(raw) => ReceiveValue::Int(b.ins().iconst(types::I64, raw)),
        DispatchConstValue::Float(raw) => {
            let bits = b.ins().iconst(types::I64, raw as i64);
            ReceiveValue::Float(b.ins().bitcast(types::F64, MemFlags::new(), bits))
        }
        DispatchConstValue::Atom(raw) => ReceiveValue::Atom(b.ins().iconst(types::I64, raw as i64)),
    }
}

fn emit_dispatch_const_test<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    ctx: &DispatchCtx<'_>,
    val: ReceiveValue,
    value: &GroundValue,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    use crate::ground_value::DispatchShape;
    match value
        .as_dispatch_shape()
        .expect("emit_dispatch_const_test only ever sees a dispatch-matrix const")
    {
        DispatchShape::Float(_)
        | DispatchShape::Int(_)
        | DispatchShape::Atom(_)
        | DispatchShape::Bool(_)
        | DispatchShape::Nil => {
            let emitted = emit_dispatch_side_tag_const_test(body, ctx, val, value, match_b, next_b)?;
            if !emitted {
                body.b.ins().jump(next_b, &[]);
            }
            Ok(())
        }
        DispatchShape::Utf8Binary(bytes) => {
            let bits = emit_receive_value_ref(body, ctx, val)?;
            emit_binary_literal_test(body, ctx.binary_data_gvs, bits, bytes, match_b, next_b)
        }
    }
}

fn emit_dispatch_map_get_value<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    ctx: &DispatchCtx<'_>,
    map: ReceiveValue,
    key: &GroundValue,
) -> Result<ReceiveValue, CodegenError> {
    if let Some(id) = ctx.dispatch.prepared_key_id(key) {
        let key = ctx.bindings.prepared.get(id.0 as usize).copied().ok_or_else(|| {
            CodegenError::new(format!(
                "dispatch prepared operand {:?} is missing from its owning plan",
                id
            ))
        })?;
        let map_ref = emit_receive_value_ref(body, ctx, map)?;
        let key_ref = emit_receive_value_ref(body, ctx, key)?;
        let out_ref = runtime_call1!(body, fz_matcher_map_get_ref, [ctx.process, map_ref, key_ref]);
        return Ok(receive_value_from_ref_word(body.b, out_ref));
    }
    let Some(key_value) = dispatch_const_value(ctx.fz_module, key)? else {
        return Err(CodegenError::new(format!(
            "map-pattern key {:?} cannot be materialized in receive dispatch",
            key
        )));
    };
    let map_ref = emit_receive_value_ref(body, ctx, map)?;
    let key_value = dispatch_const_receive_value(body.b, key_value);
    let key_ref = emit_receive_value_ref(body, ctx, key_value)?;
    let out_ref = runtime_call1!(body, fz_matcher_map_get_ref, [ctx.process, map_ref, key_ref]);
    Ok(receive_value_from_ref_word(body.b, out_ref))
}

fn emit_bitstring_test<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    ctx: &DispatchCtx<'_>,
    subject: SubjectId,
    shape: &BitstringShape,
    true_b: ir::Block,
    false_b: ir::Block,
    state: &mut DispatchEmitState,
) -> Result<(), CodegenError> {
    let value = resolve_dispatch_subject(body, ctx, subject, state)?;
    emit_bitstring_like_guard(body, value, false_b)?;
    let value_ref = emit_receive_value_ref(body, ctx, value)?;
    let mut reader = runtime_call1!(body, fz_bs_reader_init_ref, [ctx.process, value_ref]);

    for field_subject in &shape.fields {
        let extraction = ctx.dispatch.bitstring_extraction(*field_subject);
        let field = &extraction.spec;
        let (size_present, size_value) = emit_dispatch_bit_size(body, ctx, field, state)?;
        let field_spec = fz_bs_field_spec(
            dispatch_bit_type_tag(field.kind),
            size_present,
            field.unit.unwrap_or(default_dispatch_bit_unit(field.kind)),
            dispatch_endian_tag(field.endian),
            field.signed as u32,
            extraction.is_last as u32,
        );
        let field_spec = body.b.ins().iconst(types::I64, field_spec as i64);
        let result = runtime_call1!(
            body,
            fz_bs_read_field_ref,
            [ctx.process, reader, field_spec, size_value]
        );
        let result_value = ReceiveValue::AnyRef(result);
        let ok = emit_struct_get_field(body, ctx, result_value, 0)?;
        let ok_truthy = emit_truthy_cmp(body, ok)?;
        let next_b = body.b.create_block();
        body.b.ins().brif(ok_truthy, next_b, &[], false_b, &[]);
        body.b.switch_to_block(next_b);
        body.b.seal_block(next_b);
        let extracted = emit_struct_get_field(body, ctx, result_value, 1)?;
        let next_reader = emit_struct_get_field(body, ctx, result_value, 2)?;
        reader = emit_receive_value_ref(body, ctx, next_reader)?;
        state.values.insert(*field_subject, extracted);
    }

    if !shape.require_done {
        body.b.ins().jump(true_b, &[]);
        return Ok(());
    }
    let reader_value = ReceiveValue::AnyRef(reader);
    let bit_len_value = emit_struct_get_field(body, ctx, reader_value, 1)?;
    let bit_len = receive_value_int(body, bit_len_value)?;
    let pos_value = emit_struct_get_field(body, ctx, reader_value, 2)?;
    let pos = receive_value_int(body, pos_value)?;
    let done = body.b.ins().icmp(IntCC::Equal, bit_len, pos);
    body.b.ins().brif(done, true_b, &[], false_b, &[]);
    Ok(())
}

fn emit_struct_get_field<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    ctx: &DispatchCtx<'_>,
    struct_value: ReceiveValue,
    field_index: u32,
) -> Result<ReceiveValue, CodegenError> {
    emit_struct_get_field_value(body, ctx, struct_value, field_index)
}

fn emit_struct_get_field_value<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    ctx: &DispatchCtx<'_>,
    struct_value: ReceiveValue,
    field_index: u32,
) -> Result<ReceiveValue, CodegenError> {
    let field_offset = body.b.ins().iconst(types::I32, field_index as i64 * SLOT_BYTES as i64);
    let struct_ref = emit_receive_value_ref(body, ctx, struct_value)?;
    let out_ref = runtime_call1!(body, fz_struct_get_field_ref, [ctx.process, struct_ref, field_offset]);
    Ok(receive_value_from_ref_word(body.b, out_ref))
}

fn emit_bitstring_like_guard<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    val: ReceiveValue,
    miss: ir::Block,
) -> Result<(), CodegenError> {
    let tag8 = receive_value_tag(body, val)?;
    let tag = body.b.ins().uextend(types::I64, tag8);
    let cont = body.b.create_block();
    let ptr_path = body.b.create_block();
    let is_strict_bs = body
        .b
        .ins()
        .icmp_imm(IntCC::Equal, tag, ValueKind::BITSTRING.tag() as i64);
    let is_strict_proc = body
        .b
        .ins()
        .icmp_imm(IntCC::Equal, tag, ValueKind::PROCBIN.tag() as i64);
    let is_strict = body.b.ins().bor(is_strict_bs, is_strict_proc);
    body.b.ins().brif(is_strict, cont, &[], ptr_path, &[]);
    body.b.switch_to_block(ptr_path);
    body.b.seal_block(ptr_path);
    body.b.ins().jump(miss, &[]);
    body.b.switch_to_block(cont);
    body.b.seal_block(cont);
    Ok(())
}

fn emit_dispatch_bit_size<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    ctx: &DispatchCtx<'_>,
    field: &crate::dispatch_matrix::BitstringFieldShape,
    state: &DispatchEmitState,
) -> Result<(u32, ir::Value), CodegenError> {
    match &field.size {
        None => Ok((0, body.b.ins().iconst(types::I32, 0))),
        Some(BitstringFieldSize::Literal(n)) => Ok((1, body.b.ins().iconst(types::I32, *n as i64))),
        Some(BitstringFieldSize::Binding(subject)) => {
            let value = state
                .values
                .get(subject)
                .copied()
                .ok_or_else(|| CodegenError::new(format!("bitstring size subject {:?} not available", subject)))?;
            Ok((1, strict_int_i32(body, value)?))
        }
        // A size bound before the pattern began arrives as a PIN.
        Some(BitstringFieldSize::Pinned(pinned)) => {
            let value = load_pinned_dispatch_value(ctx, *pinned)?;
            Ok((1, strict_int_i32(body, value)?))
        }
    }
}

fn strict_int_i32<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    v: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    let raw = receive_value_int(body, v)?;
    Ok(body.b.ins().ireduce(types::I32, raw))
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

fn emit_dispatch_guard_expr<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
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
            dispatch_const_receive_value(body.b, value)
        }
        PatternGuardExpr::Subject(subject) => resolve_dispatch_subject(body, ctx, *subject, state)?,
        PatternGuardExpr::Pinned(pinned) => load_pinned_dispatch_value(ctx, *pinned)?,
        PatternGuardExpr::Unary { op, expr } => {
            let v = emit_dispatch_guard_expr(body, ctx, expr, state)?;
            match op {
                PatternGuardUnaryOp::Not => {
                    let truthy = emit_truthy_cmp(body, v)?;
                    emit_bool_value_from_truthy(body.b, truthy, true)
                }
                PatternGuardUnaryOp::Neg => {
                    let z = body.b.ins().iconst(types::I64, 0);
                    let raw = receive_value_int(body, v)?;
                    let neg = body.b.ins().isub(z, raw);
                    int_value(body.b, neg)
                }
            }
        }
        PatternGuardExpr::Binary { op, lhs, rhs } => {
            if matches!(op, PatternGuardBinOp::And | PatternGuardBinOp::Or) {
                return emit_short_circuit_guard(body, ctx, *op, lhs, rhs, state);
            }
            let l = emit_dispatch_guard_expr(body, ctx, lhs, state)?;
            let r = emit_dispatch_guard_expr(body, ctx, rhs, state)?;
            match op {
                PatternGuardBinOp::Add => {
                    let l = receive_value_int(body, l)?;
                    let r = receive_value_int(body, r)?;
                    let sum = body.b.ins().iadd(l, r);
                    int_value(body.b, sum)
                }
                PatternGuardBinOp::Sub => {
                    let l = receive_value_int(body, l)?;
                    let r = receive_value_int(body, r)?;
                    let diff = body.b.ins().isub(l, r);
                    int_value(body.b, diff)
                }
                PatternGuardBinOp::Mul => {
                    let l = receive_value_int(body, l)?;
                    let r = receive_value_int(body, r)?;
                    let prod = body.b.ins().imul(l, r);
                    int_value(body.b, prod)
                }
                PatternGuardBinOp::Div => {
                    let l = receive_value_int(body, l)?;
                    let r = receive_value_int(body, r)?;
                    let quot = body.b.ins().sdiv(l, r);
                    int_value(body.b, quot)
                }
                PatternGuardBinOp::Rem => {
                    let l = receive_value_int(body, l)?;
                    let r = receive_value_int(body, r)?;
                    let rem = body.b.ins().srem(l, r);
                    int_value(body.b, rem)
                }
                PatternGuardBinOp::Eq => {
                    let cmp = emit_typed_eq_cmp(body, ctx, l, r)?;
                    emit_bool_value(body.b, cmp)
                }
                PatternGuardBinOp::Neq => {
                    let eq = emit_typed_eq_cmp(body, ctx, l, r)?;
                    let neq = body.b.ins().bxor_imm(eq, 1);
                    emit_bool_value(body.b, neq)
                }
                PatternGuardBinOp::Lt => emit_int_cmp_value(body, IntCC::SignedLessThan, l, r)?,
                PatternGuardBinOp::LtEq => emit_int_cmp_value(body, IntCC::SignedLessThanOrEqual, l, r)?,
                PatternGuardBinOp::Gt => emit_int_cmp_value(body, IntCC::SignedGreaterThan, l, r)?,
                PatternGuardBinOp::GtEq => emit_int_cmp_value(body, IntCC::SignedGreaterThanOrEqual, l, r)?,
                PatternGuardBinOp::And => {
                    unreachable!("short-circuit guard op handled before eager operands")
                }
                PatternGuardBinOp::Or => {
                    unreachable!("short-circuit guard op handled before eager operands")
                }
            }
        }
        PatternGuardExpr::Dispatch {
            inputs,
            prepared,
            dispatch,
        } => {
            let values = inputs
                .iter()
                .map(|input| emit_dispatch_guard_expr(body, ctx, input, state))
                .collect::<Result<Vec<_>, _>>()?;
            emit_guard_dispatch(body, ctx, dispatch, prepared, values)?
        }
    })
}

fn emit_guard_dispatch<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    parent: &DispatchCtx<'_>,
    dispatch: &ReceiveGuardDispatch,
    prepared_keys: &[crate::dispatch_matrix::PreparedKeyId],
    inputs: Vec<ReceiveValue>,
) -> Result<ReceiveValue, CodegenError> {
    let done = body.b.create_block();
    body.b.append_block_param(done, types::I64);
    let ctx = DispatchCtx {
        process: parent.process,
        fz_module: parent.fz_module,
        tuple_schema_ids: parent.tuple_schema_ids,
        named_schema_ids: parent.named_schema_ids,
        outcomes: parent.outcomes,
        bindings: crate::compiler2::DispatchBindings {
            pinned: Vec::new(),
            prepared: prepared_keys
                .iter()
                .map(|id| {
                    parent.bindings.prepared.get(id.0 as usize).copied().ok_or_else(|| {
                        CodegenError::new(format!("guard prepared operand {:?} is missing from its caller", id))
                    })
                })
                .collect::<Result<Vec<_>, _>>()?,
        },
        out_ptr: parent.out_ptr,
        dispatch: &dispatch.plan,
        inputs,
        binary_data_gvs: parent.binary_data_gvs,
    };
    let mut state = DispatchEmitState::default();
    emit_guard_dispatch_node(body, &ctx, &dispatch.bodies, dispatch.plan.graph.root, done, &mut state)?;
    body.b.switch_to_block(done);
    body.b.seal_block(done);
    Ok(ReceiveValue::AnyRef(body.b.block_params(done)[0]))
}

fn emit_guard_dispatch_node<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
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
            let false_value = bool_const_value(body.b, false);
            let false_ref = emit_receive_value_ref(body, ctx, false_value)?;
            body.b.ins().jump(done, &[ir::BlockArg::Value(false_ref)]);
            let dead = body.b.create_block();
            body.b.switch_to_block(dead);
            body.b.seal_block(dead);
            Ok(())
        }
        DispatchNode::Outcome { outcome, .. } => {
            let outcome = ctx
                .dispatch
                .outcome(*outcome)
                .ok_or_else(|| CodegenError::new(format!("guard dispatch outcome {:?} out of bounds", outcome)))?;
            let guard_body = bodies
                .get(outcome.body_id as usize)
                .ok_or_else(|| CodegenError::new(format!("guard dispatch body {} out of bounds", outcome.body_id)))?;
            let value = emit_dispatch_guard_expr(body, ctx, guard_body, state)?;
            let value_ref = emit_receive_value_ref(body, ctx, value)?;
            body.b.ins().jump(done, &[ir::BlockArg::Value(value_ref)]);
            let dead = body.b.create_block();
            body.b.switch_to_block(dead);
            body.b.seal_block(dead);
            Ok(())
        }
        DispatchNode::Test {
            predicate,
            on_match,
            on_miss,
        } => {
            let true_b = body.b.create_block();
            let false_b = body.b.create_block();
            let true_values = emit_region_test(
                body,
                ctx,
                predicate.subject,
                &predicate.region,
                &on_match.evidence,
                true_b,
                false_b,
                state,
            )?;
            body.b.switch_to_block(true_b);
            body.b.seal_block(true_b);
            let mut true_state = state.clone();
            true_state.values.extend(true_values);
            apply_edge_evidence_to_receive_state(body, ctx, &on_match.evidence, &mut true_state)?;
            emit_guard_dispatch_node(body, ctx, bodies, on_match.target, done, &mut true_state)?;
            body.b.switch_to_block(false_b);
            body.b.seal_block(false_b);
            emit_guard_dispatch_node(body, ctx, bodies, on_miss.target, done, state)
        }
    }
}

fn emit_short_circuit_guard<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    ctx: &DispatchCtx<'_>,
    op: PatternGuardBinOp,
    lhs: &ReceiveGuardExpr,
    rhs: &ReceiveGuardExpr,
    state: &mut DispatchEmitState,
) -> Result<ReceiveValue, CodegenError> {
    let lhs_value = emit_dispatch_guard_expr(body, ctx, lhs, state)?;
    let lhs_truthy = emit_truthy_cmp(body, lhs_value)?;
    let rhs_b = body.b.create_block();
    let done_b = body.b.create_block();
    body.b.append_block_param(done_b, types::I64);

    let true_value = bool_const_value(body.b, true);
    let false_value = bool_const_value(body.b, false);
    let true_ref = emit_receive_value_ref(body, ctx, true_value)?;
    let false_ref = emit_receive_value_ref(body, ctx, false_value)?;
    match op {
        PatternGuardBinOp::And => body
            .b
            .ins()
            .brif(lhs_truthy, rhs_b, &[], done_b, &[ir::BlockArg::Value(false_ref)]),
        PatternGuardBinOp::Or => body
            .b
            .ins()
            .brif(lhs_truthy, done_b, &[ir::BlockArg::Value(true_ref)], rhs_b, &[]),
        _ => unreachable!("non-short-circuit guard op"),
    };

    body.b.switch_to_block(rhs_b);
    body.b.seal_block(rhs_b);
    let mut rhs_state = state.clone();
    let rhs_value = emit_dispatch_guard_expr(body, ctx, rhs, &mut rhs_state)?;
    let rhs_truthy = emit_truthy_cmp(body, rhs_value)?;
    let rhs_bool = emit_bool_value_from_truthy(body.b, rhs_truthy, false);
    let rhs_ref = emit_receive_value_ref(body, ctx, rhs_bool)?;
    body.b.ins().jump(done_b, &[ir::BlockArg::Value(rhs_ref)]);

    body.b.switch_to_block(done_b);
    body.b.seal_block(done_b);
    Ok(ReceiveValue::AnyRef(body.b.block_params(done_b)[0]))
}

fn int_value(_b: &mut FunctionBuilder<'_>, raw: ir::Value) -> ReceiveValue {
    ReceiveValue::Int(raw)
}

fn bool_const_value(b: &mut FunctionBuilder<'_>, value: bool) -> ReceiveValue {
    let raw = if value { TRUE_ATOM_ID } else { FALSE_ATOM_ID };
    ReceiveValue::Atom(b.ins().iconst(types::I64, raw as i64))
}

fn emit_int_cmp_value<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    cc: IntCC,
    lhs: ReceiveValue,
    rhs: ReceiveValue,
) -> Result<ReceiveValue, CodegenError> {
    let lhs = receive_value_int(body, lhs)?;
    let rhs = receive_value_int(body, rhs)?;
    let cmp = body.b.ins().icmp(cc, lhs, rhs);
    Ok(emit_bool_value(body.b, cmp))
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

fn emit_truthy_cmp<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    v: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match v {
        ReceiveValue::AnyRef(value_ref) => {
            let truthy = runtime_call1!(body, fz_truthy_ref, [value_ref]);
            let zero = body.b.ins().iconst(types::I8, 0);
            Ok(body.b.ins().icmp(IntCC::NotEqual, truthy, zero))
        }
        ReceiveValue::Atom(raw) => {
            let is_false = body.b.ins().icmp_imm(IntCC::Equal, raw, FALSE_ATOM_ID as i64);
            let is_nil = body.b.ins().icmp_imm(IntCC::Equal, raw, NIL_ATOM_ID as i64);
            let false_or_nil = body.b.ins().bor(is_false, is_nil);
            Ok(body.b.ins().bxor_imm(false_or_nil, 1))
        }
        ReceiveValue::Int(_) | ReceiveValue::Float(_) => Ok(body.b.ins().iconst(types::I8, 1)),
    }
}

fn emit_typed_eq_cmp<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    ctx: &DispatchCtx<'_>,
    lhs: ReceiveValue,
    rhs: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match lhs {
        ReceiveValue::Int(a) => match rhs {
            ReceiveValue::Int(bv) => return Ok(body.b.ins().icmp(IntCC::Equal, a, bv)),
            ReceiveValue::AnyRef(_) | ReceiveValue::Float(_) | ReceiveValue::Atom(_) => {}
        },
        ReceiveValue::Float(a) => match rhs {
            ReceiveValue::Float(bv) => {
                let a = body.b.ins().bitcast(types::I64, MemFlags::new(), a);
                let bv = body.b.ins().bitcast(types::I64, MemFlags::new(), bv);
                return Ok(body.b.ins().icmp(IntCC::Equal, a, bv));
            }
            ReceiveValue::AnyRef(_) | ReceiveValue::Int(_) | ReceiveValue::Atom(_) => {}
        },
        ReceiveValue::Atom(a) => match rhs {
            ReceiveValue::Atom(bv) => return Ok(body.b.ins().icmp(IntCC::Equal, a, bv)),
            ReceiveValue::AnyRef(_) | ReceiveValue::Int(_) | ReceiveValue::Float(_) => {}
        },
        ReceiveValue::AnyRef(_) => match rhs {
            ReceiveValue::AnyRef(_) | ReceiveValue::Int(_) | ReceiveValue::Float(_) | ReceiveValue::Atom(_) => {}
        },
    }
    let lhs_ref = emit_receive_value_ref(body, ctx, lhs)?;
    let rhs_ref = emit_receive_value_ref(body, ctx, rhs)?;
    let eq = runtime_call1!(body, fz_value_eq_ref, [ctx.process, lhs_ref, rhs_ref]);
    Ok(body.b.ins().icmp_imm(IntCC::NotEqual, eq, 0))
}

fn emit_typed_eq_branch<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    ctx: &DispatchCtx<'_>,
    lhs: ReceiveValue,
    rhs: ReceiveValue,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let cmp = emit_typed_eq_cmp(body, ctx, lhs, rhs)?;
    body.b.ins().brif(cmp, match_b, &[], next_b, &[]);
    Ok(())
}

fn emit_not_dispatch_map_miss<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::AnyRef(_) => {
            let tag = receive_value_tag(body, value)?;
            let tag64 = body.b.ins().uextend(types::I64, tag);
            Ok(body
                .b
                .ins()
                .icmp_imm(IntCC::NotEqual, tag64, ValueKind::NULL.tag() as i64))
        }
        ReceiveValue::Int(_) | ReceiveValue::Float(_) | ReceiveValue::Atom(_) => Ok(body.b.ins().iconst(types::I8, 1)),
    }
}

fn emit_map_kind_test<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    ctx: &DispatchCtx<'_>,
    val: ReceiveValue,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let map_ref = emit_receive_value_ref(body, ctx, val)?;
    let ok = runtime_call1!(body, fz_map_is_map, [map_ref]);
    let zero = body.b.ins().iconst(types::I8, 0);
    let cmp = body.b.ins().icmp(IntCC::NotEqual, ok, zero);
    body.b.ins().brif(cmp, match_b, &[], next_b, &[]);
    Ok(())
}

/// Chain of equality / load checks that verifies `val` is a tuple of
/// the given arity. Branches to `match_b` on success, `next_b` on any
/// mismatch. Mirrors `compile_tuple_shape` but parameterised on match
/// vs miss target blocks.
fn emit_tuple_arity_test<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
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

    let tag = receive_value_tag(body, val)?;
    let tag64 = body.b.ins().uextend(types::I64, tag);
    let c0 = body.b.create_block();
    let cmp0 = body
        .b
        .ins()
        .icmp_imm(IntCC::Equal, tag64, ValueKind::STRUCT.tag() as i64);
    body.b.ins().brif(cmp0, c0, &[], next_b, &[]);
    body.b.switch_to_block(c0);
    body.b.seal_block(c0);

    let struct_ref = emit_receive_value_ref(body, ctx, val)?;
    let schema = runtime_call1!(body, fz_struct_schema_id_ref, [struct_ref]);
    let schema_want = body.b.ins().iconst(types::I32, expected_schema_id as i64);
    let cmp4 = body.b.ins().icmp(IntCC::Equal, schema, schema_want);
    body.b.ins().brif(cmp4, match_b, &[], next_b, &[]);
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
        Region::Type(_)
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
        PatternGuardExpr::Dispatch { inputs, dispatch, .. } => {
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

fn collect_binary_literals_in_const(value: &GroundValue, out: &mut Vec<Vec<u8>>) {
    if let GroundValue::Utf8Binary(bytes) = value {
        out.push(bytes.clone());
    }
}

/// Emit the call sequence that compares `val` against a constant byte
/// literal via `fz_matcher_eq_bytes`. Branches to `match_b` when the
/// helper returns 1, `next_b` when it returns 0.
fn emit_binary_literal_test<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    binary_data_gvs: &HashMap<Vec<u8>, ir::GlobalValue>,
    val: ir::Value,
    bytes: &[u8],
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let gv = binary_data_gvs.get(bytes).ok_or_else(|| {
        CodegenError::new(format!(
            "Binary literal of {} bytes missing pre-declared .data symbol",
            bytes.len()
        ))
    })?;
    let bytes_ptr = body.b.ins().symbol_value(types::I64, *gv);
    let byte_len = body.b.ins().iconst(types::I64, bytes.len() as i64);
    let res = runtime_call1!(body, fz_matcher_eq_bytes, [val, bytes_ptr, byte_len]);
    let zero = body.b.ins().iconst(types::I32, 0);
    let cmp = body.b.ins().icmp(IntCC::NotEqual, res, zero);
    body.b.ins().brif(cmp, match_b, &[], next_b, &[]);
    Ok(())
}

/// Verify `val` is the canonical empty list (`[]`). The empty list is a
/// single interned sentinel ref (`ValueKind::LIST` with raw word `0`), so
/// this compares directly instead of routing through a runtime predicate.
fn emit_list_empty_test(b: &mut FunctionBuilder<'_>, val: ReceiveValue, match_b: ir::Block, next_b: ir::Block) {
    match val {
        ReceiveValue::AnyRef(value_ref) => {
            let empty = b.ins().iconst(types::I64, AnyValueRef::empty_list().raw_word() as i64);
            let ok = b.ins().icmp(IntCC::Equal, value_ref, empty);
            b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        ReceiveValue::Int(_) | ReceiveValue::Float(_) | ReceiveValue::Atom(_) => {
            b.ins().jump(next_b, &[]);
        }
    }
}

/// Verify `val` is a List cons cell. Strict list cells are headerless
/// and carried by the `TAG_LIST` low nibble, so this routes through the
/// runtime predicate instead of reading a prefix kind.
fn emit_list_cons_test<M: cranelift_module::Module>(
    body: &mut DispatchBody<'_, '_, M>,
    ctx: &DispatchCtx<'_>,
    val: ReceiveValue,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let list_ref = emit_receive_value_ref(body, ctx, val)?;
    let ok = runtime_call1!(body, fz_list_is_cons, [list_ref]);
    let zero = body.b.ins().iconst(types::I8, 0);
    let cmp = body.b.ins().icmp(IntCC::NotEqual, ok, zero);
    body.b.ins().brif(cmp, match_b, &[], next_b, &[]);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::super::host_isa_with;
    use super::*;
    use crate::compiler2::native_codegen::runtime_call::runtime_func_ref;
    use cranelift_module::{Module as ClModule, default_libcall_names};
    use cranelift_object::{ObjectBuilder, ObjectModule};

    /// A dispatch body asks for a helper by its Rust item, and the first ask
    /// declares the symbol. Asking again reuses that declaration, so a body
    /// names each helper once however many times its plan calls it.
    #[test]
    fn a_body_declares_each_runtime_helper_once() {
        let isa = host_isa_with(true);
        let object = ObjectBuilder::new(isa, "receive_dispatch_test", default_libcall_names())
            .expect("an object builder for the host");
        let mut module = ObjectModule::new(object);
        let mut ctx = module.make_context();
        ctx.func.signature = receive_dispatch_signature(&mut module);
        let mut fbctx = FunctionBuilderContext::new();
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);

        let mut body = DispatchBody::new(&mut b, &mut module);
        let first = runtime_func_ref!(body, fz_type_of(_));
        let again = runtime_func_ref!(body, fz_type_of(_));
        let other = runtime_func_ref!(body, fz_truthy_ref(_));
        let declared = body.b.func.dfg.ext_funcs.len();

        assert_eq!(first, again, "a second ask for one helper reuses its declaration");
        assert_ne!(first, other, "distinct helpers are distinct declarations");
        assert_eq!(declared, 2, "the body declares one symbol per helper it calls");
    }

    #[test]
    fn dispatch_const_value_materializes_only_receive_scalar_consts() {
        let module = Module {
            atom_names: vec!["ok".to_string()],
            ..Module::default()
        };

        let cases = [
            (GroundValue::Int(-7), Some(DispatchConstValue::Int(-7))),
            (GroundValue::Float(12), Some(DispatchConstValue::Float(12))),
            (GroundValue::Atom("ok".to_string()), Some(DispatchConstValue::Atom(0))),
            (
                GroundValue::Bool(true),
                Some(DispatchConstValue::Atom(TRUE_ATOM_ID as u64)),
            ),
            (
                GroundValue::Bool(false),
                Some(DispatchConstValue::Atom(FALSE_ATOM_ID as u64)),
            ),
            (GroundValue::Nil, Some(DispatchConstValue::Atom(NIL_ATOM_ID as u64))),
            (GroundValue::Utf8Binary(b"ok".to_vec()), None),
        ];

        for (value, expected) in cases {
            let actual = dispatch_const_value(&module, &value).expect("dispatch const lowering should not fail");
            assert_eq!(
                actual, expected,
                "unexpected native receive dispatch const for {value:?}"
            );
            if let Some(actual) = actual {
                assert_ne!(
                    actual.kind(),
                    ValueKind::NULL,
                    "native receive dispatch const materialized null"
                );
            }
        }
    }
}
