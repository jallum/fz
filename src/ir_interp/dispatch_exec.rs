use std::collections::HashMap;
use std::slice::from_raw_parts;

use super::backend::{materialize_transport_value, transport_field_view};
use super::*;
use crate::compiler2::transport::TransportStore;
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardBinOp, PatternGuardExpr, PatternGuardUnaryOp};
use crate::dispatch_matrix::{
    BitstringEndian, BitstringFieldKind, BitstringFieldSize, BitstringShape, ComparisonValue, DispatchNode,
    EdgeEvidence, GraphNodeId, GroundValue, ListRegion, PinnedValueId, ProjectionKind, Region, SubjectId,
    SubjectSource,
};
use crate::fz_ir::Module;
use fz_runtime::any_value::{AnyValue as RuntimeAnyValue, AnyValueRef, TRUE_ATOM_ID, ValueKind, struct_schema_id};
use fz_runtime::ir_runtime::{
    fz_bs_begin, fz_bs_field_spec, fz_bs_finalize, fz_bs_read_field_ref, fz_bs_reader_init_ref, fz_bs_write_field_ref,
    fz_matcher_map_get_ref, fz_struct_get_field_ref,
};
use fz_runtime::procbin::{bitstring_bit_len, bitstring_byte_ptr, is_bitstring_like};
use fz_runtime::process::Process;

pub(super) type DispatchValues = crate::compiler2::DispatchBindings<AnyValue>;

/// Why a dispatch step produced no value.
///
/// The two reasons are not the same: a subject that does not match hands the
/// next edge its turn, while a question the executor cannot answer means the
/// plan and the values it was given disagree, and no edge can repair that.
#[derive(Debug)]
pub(super) enum DispatchStop {
    NoMatch,
    Broken(String),
}

impl DispatchStop {
    pub(super) fn broken(message: impl Into<String>) -> Self {
        Self::Broken(message.into())
    }
}

/// A result that is `Ok(None)` where the subject simply did not match, so a
/// caller can fall to its miss edge without swallowing a broken plan.
fn or_miss<T>(result: Result<T, DispatchStop>) -> Result<Option<T>, DispatchStop> {
    match result {
        Ok(value) => Ok(Some(value)),
        Err(DispatchStop::NoMatch) => Ok(None),
        Err(broken) => Err(broken),
    }
}

fn required<T>(value: Option<T>) -> Result<T, DispatchStop> {
    value.ok_or(DispatchStop::NoMatch)
}

/// Everything a dispatch run reads but never writes: the values it is deciding
/// about, the operands its pattern named, and the transport store that says how
/// a lane-form value is laid out.
pub(super) struct DispatchOperands<'a> {
    pub(super) transport: &'a TransportStore,
    pub(super) inputs: &'a [BackendBoundValue],
    pub(super) pinned: &'a DispatchValues,
}

#[derive(Default, Clone)]
pub(super) struct DispatchExecState {
    values: HashMap<SubjectId, BackendBoundValue>,
}

pub(super) struct DispatchMatch {
    pub(super) outcome: crate::dispatch_matrix::OutcomeId,
    pub(super) state: DispatchExecState,
}

pub(super) fn execute_dispatch_inputs<TypeHandle, F>(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    operands: &DispatchOperands<'_>,
    state: &mut DispatchExecState,
    type_match: &mut F,
) -> Result<DispatchMatch, DispatchStop>
where
    F: FnMut(&mut IrInterpRuntime, &Module, &TypeHandle, &BackendBoundValue) -> Result<bool, DispatchStop>,
{
    execute_dispatch_node(runtime, module, plan, plan.graph.root, operands, state, type_match)
}

pub(super) fn execute_dispatch_node<TypeHandle, F>(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    node_id: GraphNodeId,
    operands: &DispatchOperands<'_>,
    state: &mut DispatchExecState,
    type_match: &mut F,
) -> Result<DispatchMatch, DispatchStop>
where
    F: FnMut(&mut IrInterpRuntime, &Module, &TypeHandle, &BackendBoundValue) -> Result<bool, DispatchStop>,
{
    match required(plan.graph.node(node_id))? {
        DispatchNode::Fail => Err(DispatchStop::NoMatch),
        DispatchNode::Outcome { outcome, .. } => Ok(DispatchMatch {
            outcome: *outcome,
            state: state.clone(),
        }),
        DispatchNode::Test {
            predicate,
            on_match,
            on_miss,
        } => {
            let mut true_state = state.clone();
            let hit = dispatch_region_hit(
                runtime,
                module,
                plan,
                predicate.subject,
                &predicate.region,
                &on_match.evidence,
                operands,
                &mut true_state,
                type_match,
            )?;
            let took_match = hit
                && or_miss(apply_edge_evidence(
                    runtime,
                    module,
                    plan,
                    &on_match.evidence,
                    operands,
                    &mut true_state,
                ))?
                .is_some();
            if took_match {
                execute_dispatch_node(
                    runtime,
                    module,
                    plan,
                    on_match.target,
                    operands,
                    &mut true_state,
                    type_match,
                )
            } else {
                execute_dispatch_node(runtime, module, plan, on_miss.target, operands, state, type_match)
            }
        }
    }
}

fn apply_edge_evidence<TypeHandle>(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    evidence: &EdgeEvidence<TypeHandle>,
    operands: &DispatchOperands<'_>,
    state: &mut DispatchExecState,
) -> Result<(), DispatchStop> {
    for projection in &evidence.projections {
        if state.values.contains_key(projection) {
            continue;
        }
        let value = resolve_dispatch_subject(runtime.cur_proc(), module, plan, *projection, operands, state)?;
        state.values.insert(*projection, value);
    }
    Ok(())
}

/// The one runtime word a subject denotes.
///
/// A tuple's arity, its field projections and a type test all read a subject in
/// the lane form its caller delivered. What is left are the questions that want
/// the whole value and cannot be decomposed: a pinned equality, a guard, and the
/// map, list and bitstring regions. Those build the value here, at the question
/// that asks for it, and keep it for the rest of this branch.
pub(super) fn subject_word<TypeHandle>(
    proc: *mut Process,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    subject: SubjectId,
    operands: &DispatchOperands<'_>,
    state: &mut DispatchExecState,
) -> Result<AnyValue, DispatchStop> {
    let value = resolve_dispatch_subject(proc, module, plan, subject, operands, state)?;
    word_of(proc, operands, subject, value, state)
}

/// The same answer for a caller that has already resolved the subject.
fn word_of(
    proc: *mut Process,
    operands: &DispatchOperands<'_>,
    subject: SubjectId,
    value: BackendBoundValue,
    state: &mut DispatchExecState,
) -> Result<AnyValue, DispatchStop> {
    let word = match value {
        BackendBoundValue::Runtime(value) => return Ok(value),
        BackendBoundValue::Absent => {
            return Err(DispatchStop::broken(format!(
                "dispatch subject {subject:?} carries no runtime value"
            )));
        }
        BackendBoundValue::Transport { shape, lanes } => {
            materialize_transport_value(operands.transport, proc, shape, &lanes).map_err(DispatchStop::broken)?
        }
    };
    state.values.insert(subject, BackendBoundValue::Runtime(word));
    Ok(word)
}

/// The i-th field of a lane-form tuple, as a view over lanes already in hand.
///
/// `None` where the subject is not a lane-form tuple, which is the signal to
/// read the field out of a runtime value instead. Only that field's own lanes
/// are read: a dispatch asks about one position at a time.
fn transport_tuple_field(
    transport: &TransportStore,
    value: &BackendBoundValue,
    index: usize,
) -> Result<Option<BackendBoundValue>, DispatchStop> {
    let BackendBoundValue::Transport { shape, lanes } = value else {
        return Ok(None);
    };
    if transport.interners().tuple_arity(*shape).is_none() {
        return Ok(None);
    }
    transport_field_view(transport, *shape, lanes, index)
        .map_err(DispatchStop::broken)?
        .map(Some)
        .ok_or_else(|| DispatchStop::broken(format!("dispatch tuple field {index} is out of bounds for {shape:?}")))
}

/// What a subject holds, in whatever form it already has.
///
/// A tuple field of a lane-form subject is a view over lanes the caller already
/// delivered, so reading it allocates nothing. Every other projection reads
/// through a runtime value.
pub(super) fn resolve_dispatch_subject<TypeHandle>(
    proc: *mut Process,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    subject: SubjectId,
    operands: &DispatchOperands<'_>,
    state: &mut DispatchExecState,
) -> Result<BackendBoundValue, DispatchStop> {
    if let Some(value) = state.values.get(&subject) {
        return Ok(value.clone());
    }
    let subject_data = required(plan.matrix.subjects.get(subject.0 as usize))?;
    let value = match &subject_data.source {
        SubjectSource::Input { ordinal } => required(operands.inputs.get(*ordinal as usize).cloned())?,
        SubjectSource::Projection(projection) => match &projection.kind {
            ProjectionKind::TupleField(index) => {
                let parent = resolve_dispatch_subject(proc, module, plan, projection.source, operands, state)?;
                match transport_tuple_field(operands.transport, &parent, *index as usize)? {
                    Some(field) => field,
                    None => {
                        let parent = subject_word(proc, module, plan, projection.source, operands, state)?;
                        let parent_slot = required(parent.value(proc).ok())?;
                        if parent_slot.kind() != ValueKind::STRUCT {
                            return Err(DispatchStop::NoMatch);
                        }
                        let field = required(
                            with_value_ref(proc, parent, "dispatch tuple field", |struct_ref| {
                                fz_struct_get_field_ref(proc, struct_ref, index * 8)
                            })
                            .ok()
                            .and_then(|ref_word| interp_value_from_ref_word(ref_word, "dispatch tuple field").ok()),
                        )?;
                        BackendBoundValue::Runtime(field)
                    }
                }
            }
            ProjectionKind::StructField(field) => {
                let parent = subject_word(proc, module, plan, projection.source, operands, state)?;
                let parent = required(parent.as_ref_word(proc).ok())?;
                let parent = required(AnyValueRef::from_raw_word(parent).ok())?;
                let value = required(unsafe { &*proc }.heap.read_struct_named_field_ref(parent, field).ok())?;
                BackendBoundValue::Runtime(required(
                    interp_value_from_ref_word(value.raw_word(), "dispatch struct field").ok(),
                )?)
            }
            ProjectionKind::ListHead => {
                let parent = subject_word(proc, module, plan, projection.source, operands, state)?;
                BackendBoundValue::Runtime(required(interp_list_head(proc, parent).ok())?)
            }
            ProjectionKind::ListTail => {
                let parent = subject_word(proc, module, plan, projection.source, operands, state)?;
                BackendBoundValue::Runtime(required(interp_list_tail(proc, parent).ok())?)
            }
            ProjectionKind::MapValue { key } => {
                let map = subject_word(proc, module, plan, projection.source, operands, state)?;
                BackendBoundValue::Runtime(required(dispatch_map_lookup(
                    proc,
                    plan,
                    module,
                    map,
                    key,
                    operands.pinned,
                ))?)
            }
            ProjectionKind::BitstringField(_) => return Err(DispatchStop::NoMatch),
        },
    };
    state.values.insert(subject, value.clone());
    Ok(value)
}

/// Decide one region question about one subject.
///
/// A subject that cannot be produced fails its test, so the next edge gets its
/// turn; only a plan the executor cannot answer stops the run.
fn dispatch_region_hit<TypeHandle, F>(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    subject: SubjectId,
    region: &Region<TypeHandle>,
    evidence: &EdgeEvidence<TypeHandle>,
    operands: &DispatchOperands<'_>,
    state: &mut DispatchExecState,
    type_match: &mut F,
) -> Result<bool, DispatchStop>
where
    F: FnMut(&mut IrInterpRuntime, &Module, &TypeHandle, &BackendBoundValue) -> Result<bool, DispatchStop>,
{
    match region {
        Region::Type(ty) => {
            // The value is asked in the form it is held: a tuple delivered as
            // lanes is decided per position, without one being built.
            let Some(value) = subject_bound_value(runtime, module, plan, subject, operands, state)? else {
                return Ok(false);
            };
            type_match(runtime, module, ty, &value)
        }
        Region::Equal(ComparisonValue::Const(value)) => {
            let Some(word) = subject_value(runtime, module, plan, subject, operands, state)? else {
                return Ok(false);
            };
            Ok(dispatch_const_eq(runtime.cur_proc(), module, word, value))
        }
        Region::Equal(ComparisonValue::Pinned(pin_id)) => {
            let Some(word) = subject_value(runtime, module, plan, subject, operands, state)? else {
                return Ok(false);
            };
            Ok(load_pinned_dispatch_value(*pin_id, operands.pinned)
                .is_some_and(|want| interp_value_eq(runtime.cur_proc(), want, word).unwrap_or(false)))
        }
        Region::TupleArity(arity) => {
            let Some(value) = subject_bound_value(runtime, module, plan, subject, operands, state)? else {
                return Ok(false);
            };
            // A lane-form subject knows its own arity: the transport shape its
            // caller delivered settles the question, with no value to inspect.
            if let BackendBoundValue::Transport { shape, .. } = &value
                && let Some(known) = operands.transport.interners().tuple_arity(*shape)
            {
                return Ok(known == *arity as usize);
            }
            let Some(word) = or_miss(word_of(runtime.cur_proc(), operands, subject, value, state))? else {
                return Ok(false);
            };
            Ok(word.value(runtime.cur_proc()).ok().is_some_and(|value| {
                value.kind() == ValueKind::STRUCT
                    && value.heap_addr().is_some_and(|p| {
                        (unsafe { struct_schema_id(p) }) == interp_tuple_schema_id(runtime, *arity as usize)
                    })
            }))
        }
        Region::List(ListRegion::Empty) => {
            let Some(word) = subject_value(runtime, module, plan, subject, operands, state)? else {
                return Ok(false);
            };
            Ok(word.is_empty_list())
        }
        Region::List(ListRegion::Cons) => {
            let Some(word) = subject_value(runtime, module, plan, subject, operands, state)? else {
                return Ok(false);
            };
            Ok(word.value(runtime.cur_proc()).ok().is_some_and(interp_is_list_cons))
        }
        Region::MapKind => {
            let Some(word) = subject_value(runtime, module, plan, subject, operands, state)? else {
                return Ok(false);
            };
            Ok(word.value(runtime.cur_proc()).ok().is_some_and(is_map_value))
        }
        Region::MapKeyPresent { key } => {
            let Some(map) = subject_value(runtime, module, plan, subject, operands, state)? else {
                return Ok(false);
            };
            let Some(value) = dispatch_map_lookup(runtime.cur_proc(), plan, module, map, key, operands.pinned) else {
                return Ok(false);
            };
            for result in &evidence.projections {
                if let SubjectSource::Projection(projection) = plan.subject(*result)
                    && projection.source == subject
                    && matches!(&projection.kind, ProjectionKind::MapValue { key: projection_key } if projection_key == key)
                {
                    state.values.insert(*result, BackendBoundValue::Runtime(value));
                }
            }
            Ok(true)
        }
        Region::Bitstring(shape) => {
            let Some(word) = subject_value(runtime, module, plan, subject, operands, state)? else {
                return Ok(false);
            };
            Ok(word.value(runtime.cur_proc()).ok().is_some_and(|value| {
                dispatch_read_bitstring(runtime.cur_proc(), plan, value, shape, operands.pinned, state)
            }))
        }
        Region::Guard(guard) => {
            let Some(expr) = plan.guards.get(guard.0 as usize) else {
                return Ok(false);
            };
            let Some(value) = or_miss(eval_dispatch_guard(
                runtime, module, plan, expr, operands, state, type_match,
            ))?
            else {
                return Ok(false);
            };
            Ok(!(value.is_false() || value.is_nil()))
        }
    }
}

/// The subject's runtime word, or `None` where it cannot be produced and the
/// region therefore fails.
fn subject_value<TypeHandle>(
    runtime: &IrInterpRuntime,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    subject: SubjectId,
    operands: &DispatchOperands<'_>,
    state: &mut DispatchExecState,
) -> Result<Option<AnyValue>, DispatchStop> {
    or_miss(subject_word(runtime.cur_proc(), module, plan, subject, operands, state))
}

/// The subject in whatever form it is held, or `None` where it cannot be
/// produced and the region therefore fails.
fn subject_bound_value<TypeHandle>(
    runtime: &IrInterpRuntime,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    subject: SubjectId,
    operands: &DispatchOperands<'_>,
    state: &mut DispatchExecState,
) -> Result<Option<BackendBoundValue>, DispatchStop> {
    or_miss(resolve_dispatch_subject(
        runtime.cur_proc(),
        module,
        plan,
        subject,
        operands,
        state,
    ))
}

/// fz-5xp.18 — one dynamic ordering, shared with native codegen and with the
/// `Kernel` operators, so a guard cannot answer a comparison differently from
/// the expression that spells it out.
fn guard_cmp(proc: *mut Process, left: AnyValue, right: AnyValue) -> Option<i64> {
    interp_cmp(proc, left, right).ok()
}

pub(super) fn eval_dispatch_guard<TypeHandle, F>(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    expr: &PatternGuardExpr<TypeHandle>,
    operands: &DispatchOperands<'_>,
    state: &mut DispatchExecState,
    type_match: &mut F,
) -> Result<AnyValue, DispatchStop>
where
    F: FnMut(&mut IrInterpRuntime, &Module, &TypeHandle, &BackendBoundValue) -> Result<bool, DispatchStop>,
{
    Ok(match expr {
        PatternGuardExpr::Const(c) => required(dispatch_const_to_value(runtime.cur_proc(), module, c))?,
        PatternGuardExpr::Subject(subject) => {
            subject_word(runtime.cur_proc(), module, plan, *subject, operands, state)?
        }
        PatternGuardExpr::Pinned(pinned_id) => required(load_pinned_dispatch_value(*pinned_id, operands.pinned))?,
        PatternGuardExpr::Unary { op, expr } => {
            let v = eval_dispatch_guard(runtime, module, plan, expr, operands, state, type_match)?;
            match op {
                PatternGuardUnaryOp::Not => interp_bool_value(v.is_false() || v.is_nil()),
                // The same negation an EXPRESSION gets. Forcing the operand to
                // an integer here made `when -x > 0.0` silently fail its guard
                // for a float and fall to the next clause, so `interp` answered
                // a different clause than `run` and `build` (fz-5xp.46).
                PatternGuardUnaryOp::Neg => required(super::binop::eval_unop(crate::fz_ir::UnOp::Neg, v).ok())?,
            }
        }
        PatternGuardExpr::Binary { op, lhs, rhs } => {
            let l = eval_dispatch_guard(runtime, module, plan, lhs, operands, state, type_match)?;
            let short = match op {
                PatternGuardBinOp::And if l.is_false() || l.is_nil() => Some(interp_bool_value(false)),
                PatternGuardBinOp::Or if !(l.is_false() || l.is_nil()) => Some(interp_bool_value(true)),
                _ => None,
            };
            if let Some(v) = short {
                return Ok(v);
            }
            let r = eval_dispatch_guard(runtime, module, plan, rhs, operands, state, type_match)?;
            match op {
                PatternGuardBinOp::Add => AnyValue::Int(required(guard_int(l))? + required(guard_int(r))?),
                PatternGuardBinOp::Sub => AnyValue::Int(required(guard_int(l))? - required(guard_int(r))?),
                PatternGuardBinOp::Mul => AnyValue::Int(required(guard_int(l))? * required(guard_int(r))?),
                PatternGuardBinOp::Div => AnyValue::Int(required(guard_int(l))? / required(guard_int(r))?),
                PatternGuardBinOp::Rem => AnyValue::Int(required(guard_int(l))? % required(guard_int(r))?),
                // fz-5xp.24 — a guard's `==` is the `==` OPERATOR, so it widens:
                // `when a == b` with a = 1 and b = 1.0 is true. It was strict
                // here because native guards lowered through Prim::BinOp(Eq),
                // which pattern MATCHING also used, and matching must stay
                // strict. The IR now names the two questions separately, so
                // both doors can ask this one.
                PatternGuardBinOp::Eq => {
                    interp_bool_value(required(interp_operator_eq(runtime.cur_proc(), l, r).ok())?)
                }
                PatternGuardBinOp::Neq => {
                    interp_bool_value(!required(interp_operator_eq(runtime.cur_proc(), l, r).ok())?)
                }
                // fz-5xp.18 — a guard orders its operands the same way the rest
                // of the language does, through `fz_value_cmp_ref`. Comparing
                // as integers could not see a float at all: `when a >= b` with
                // a = 2 and b = 1.0 failed the conversion and fell through to
                // the next clause instead of answering true.
                PatternGuardBinOp::Lt => interp_bool_value(required(guard_cmp(runtime.cur_proc(), l, r))? < 0),
                PatternGuardBinOp::LtEq => interp_bool_value(required(guard_cmp(runtime.cur_proc(), l, r))? <= 0),
                PatternGuardBinOp::Gt => interp_bool_value(required(guard_cmp(runtime.cur_proc(), l, r))? > 0),
                PatternGuardBinOp::GtEq => interp_bool_value(required(guard_cmp(runtime.cur_proc(), l, r))? >= 0),
                PatternGuardBinOp::And | PatternGuardBinOp::Or => interp_bool_value(!(r.is_false() || r.is_nil())),
            }
        }
        PatternGuardExpr::Dispatch {
            inputs: dispatch_inputs,
            bindings,
            dispatch,
        } => {
            let values = dispatch_inputs
                .iter()
                .map(|input| eval_dispatch_guard(runtime, module, plan, input, operands, state, type_match))
                .collect::<Result<Vec<_>, _>>()?;
            let child_bindings = DispatchValues {
                pinned: required(
                    bindings
                        .pinned
                        .iter()
                        .map(|id| values.get(id.0 as usize).copied())
                        .collect::<Option<Vec<_>>>(),
                )?,
                prepared: required(
                    bindings
                        .prepared
                        .iter()
                        .map(|id| operands.pinned.prepared.get(id.0 as usize).copied())
                        .collect::<Option<Vec<_>>>(),
                )?,
            };
            let child_inputs = values
                .iter()
                .copied()
                .map(BackendBoundValue::Runtime)
                .collect::<Vec<_>>();
            let child_operands = DispatchOperands {
                transport: operands.transport,
                inputs: &child_inputs,
                pinned: &child_bindings,
            };
            let mut dispatch_state = DispatchExecState::default();
            let mut matched = execute_dispatch_inputs(
                runtime,
                module,
                &dispatch.plan,
                &child_operands,
                &mut dispatch_state,
                type_match,
            )?;
            let body_id = required(dispatch.plan.outcome(matched.outcome))?.body_id;
            let body = required(dispatch.bodies.get(body_id as usize))?;
            eval_dispatch_guard(
                runtime,
                module,
                &dispatch.plan,
                body,
                &child_operands,
                &mut matched.state,
                type_match,
            )?
        }
    })
}

fn load_pinned_dispatch_value(pinned: PinnedValueId, pinned_values: &DispatchValues) -> Option<AnyValue> {
    pinned_values.pinned.get(pinned.0 as usize).copied()
}

pub(super) fn dispatch_const_to_value(proc: *mut Process, module: &Module, c: &GroundValue) -> Option<AnyValue> {
    use crate::ground_value::DispatchShape;
    match c
        .as_dispatch_shape()
        .expect("dispatch_const_to_value only ever sees a dispatch-matrix const")
    {
        DispatchShape::Int(n) => Some(AnyValue::Int(n)),
        DispatchShape::Float(bits) => Some(AnyValue::Float(f64::from_bits(bits))),
        DispatchShape::Atom(name) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .map(|id| AnyValue::Atom(id as u32)),
        DispatchShape::Bool(value) => Some(interp_bool_value(value)),
        DispatchShape::Nil => Some(interp_nil_value()),
        DispatchShape::Utf8Binary(bytes) => utf8_binary_const_value(proc, bytes),
    }
}

fn utf8_binary_const_value(proc: *mut Process, bytes: &[u8]) -> Option<AnyValue> {
    fz_bs_begin(proc);
    for byte in bytes {
        fz_bs_write_field_ref(
            proc,
            AnyValue::Int(i64::from(*byte)).as_ref_word(proc).ok()?,
            dispatch_bit_type_tag(BitstringFieldKind::Integer),
            1,
            8,
            1,
            dispatch_endian_tag(BitstringEndian::Big),
            0,
        );
    }
    interp_value_from_ref_word(fz_bs_finalize(proc), "dispatch utf8 guard literal").ok()
}

pub(super) fn dispatch_const_eq(proc: *mut Process, module: &Module, val: AnyValue, value: &GroundValue) -> bool {
    use crate::ground_value::DispatchShape;
    match value
        .as_dispatch_shape()
        .expect("dispatch_const_eq only ever sees a dispatch-matrix const")
    {
        DispatchShape::Int(n) => val.as_i64() == Some(n),
        DispatchShape::Float(bits) => {
            matches!(val, AnyValue::Float(f) if f.to_bits() == bits)
        }
        DispatchShape::Atom(name) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .is_some_and(|id| val.is_atom_id(id as u32)),
        DispatchShape::Bool(true) => val.is_atom_id(TRUE_ATOM_ID),
        DispatchShape::Bool(false) => val.is_false(),
        DispatchShape::Nil => val.is_nil(),
        DispatchShape::Utf8Binary(bytes) => match val {
            AnyValue::FnRef(..) => false,
            other => other.value(proc).ok().is_some_and(|val| {
                val.heap_object_word().and_then(bitstring_like_ptr).is_some_and(|p| {
                    if !unsafe { is_bitstring_like(p) } {
                        return false;
                    }
                    let bit_len = unsafe { bitstring_bit_len(p) };
                    if bit_len != (bytes.len() as u64) * 8 {
                        return false;
                    }
                    let ptr = unsafe { bitstring_byte_ptr(p) };
                    let slice = unsafe { from_raw_parts(ptr, bytes.len()) };
                    slice == bytes
                })
            }),
        },
    }
}

pub(super) fn dispatch_map_lookup<TypeHandle>(
    proc: *mut Process,
    plan: &PatternDispatchPlan<TypeHandle>,
    module: &Module,
    map: AnyValue,
    key: &GroundValue,
    pinned: &DispatchValues,
) -> Option<AnyValue> {
    if !map.value(proc).ok().is_some_and(is_map_value) {
        return None;
    }
    let key = dispatch_const_key_value(plan, module, key, pinned)?;
    let ref_word = with_value_ref(proc, map, "DispatchMapGet map", |map_ref| {
        with_value_ref(proc, key, "DispatchMapGet key", |key_ref| {
            fz_matcher_map_get_ref(proc, map_ref, key_ref)
        })
    })
    .ok()?
    .ok()?;
    let value = interp_value_from_ref_word(ref_word, "DispatchMapGet").ok()?;
    match value {
        AnyValue::Null => None,
        _ => Some(value),
    }
}

pub(super) fn dispatch_const_key_value<TypeHandle>(
    plan: &PatternDispatchPlan<TypeHandle>,
    module: &Module,
    key: &GroundValue,
    pinned: &DispatchValues,
) -> Option<AnyValue> {
    use crate::ground_value::DispatchShape;
    match key
        .as_dispatch_shape()
        .expect("dispatch_const_key_value only ever sees a dispatch-matrix const")
    {
        DispatchShape::Int(n) => Some(AnyValue::Int(n)),
        DispatchShape::Float(bits) => Some(AnyValue::Float(f64::from_bits(bits))),
        DispatchShape::Bool(value) => Some(interp_bool_value(value)),
        DispatchShape::Nil => Some(interp_nil_value()),
        DispatchShape::Atom(name) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .map(|id| AnyValue::Atom(id as u32)),
        DispatchShape::Utf8Binary(_) => plan
            .prepared_key_id(key)
            .and_then(|id| pinned.prepared.get(id.0 as usize).copied()),
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn dispatch_read_bitstring<TypeHandle>(
    proc: *mut Process,
    plan: &PatternDispatchPlan<TypeHandle>,
    value: RuntimeAnyValue,
    shape: &BitstringShape,
    pinned: &DispatchValues,
    state: &mut DispatchExecState,
) -> bool {
    let Some(value_bits) = value.heap_object_word() else {
        return false;
    };
    let Some(p) = bitstring_like_ptr(value_bits) else {
        return false;
    };
    if !unsafe { is_bitstring_like(p) } {
        return false;
    }
    let mut reader = fz_bs_reader_init_ref(proc, value.ref_word().raw_word());
    for field_subject in &shape.fields {
        let extraction = plan.bitstring_extraction(*field_subject);
        let field = &extraction.spec;
        let Some((size_present, size_value)) = dispatch_bit_size_value(&field.size, pinned, state) else {
            return false;
        };
        let Ok(reader_any) = interp_value_from_ref_word(reader, "bitstring dispatch reader") else {
            return false;
        };
        let Ok(reader_ref) = reader_any.as_ref_word(proc) else {
            return false;
        };
        let field_spec = fz_bs_field_spec(
            dispatch_bit_type_tag(field.kind),
            size_present,
            field.unit.unwrap_or(default_dispatch_bit_unit(field.kind)),
            dispatch_endian_tag(field.endian),
            field.signed as u32,
            extraction.is_last as u32,
        );
        let result = fz_bs_read_field_ref(proc, reader_ref, field_spec, size_value);
        let Ok(ok) = interp_struct_field_from_tagged_bits(proc, result, 0, "bitstring dispatch ok") else {
            return false;
        };
        if ok.is_false() || ok.is_nil() {
            return false;
        }
        let Ok(extracted) = interp_struct_field_from_tagged_bits(proc, result, 8, "bitstring dispatch extracted")
        else {
            return false;
        };
        let Ok(next_reader) = interp_struct_field_from_tagged_bits(proc, result, 16, "bitstring dispatch next reader")
        else {
            return false;
        };
        state
            .values
            .insert(*field_subject, BackendBoundValue::Runtime(extracted));
        let Ok(next_reader_ref) = next_reader.as_ref_word(proc) else {
            return false;
        };
        reader = next_reader_ref;
    }
    if !shape.require_done {
        return true;
    }
    let Ok(bit_len) = interp_struct_field_from_tagged_bits(proc, reader, 8, "bitstring dispatch bit_len") else {
        return false;
    };
    let Ok(pos) = interp_struct_field_from_tagged_bits(proc, reader, 16, "bitstring dispatch pos") else {
        return false;
    };
    bit_len.as_i64() == pos.as_i64()
}

pub(super) fn dispatch_bit_size_value(
    size: &Option<BitstringFieldSize>,
    pinned: &DispatchValues,
    state: &DispatchExecState,
) -> Option<(u32, u32)> {
    match size {
        None => Some((0, 0)),
        Some(BitstringFieldSize::Literal(n)) => Some((1, *n)),
        Some(BitstringFieldSize::Binding(subject)) => state
            .values
            .get(subject)
            .and_then(BackendBoundValue::runtime_word)
            .and_then(|v| v.as_i64())
            .map(|n| (1, n as u32)),
        // A size from the ENCLOSING SCOPE -- a function parameter, or anything
        // bound before the `case`. It arrives as a PIN, which is the same
        // mechanism `Pattern::Pinned` uses, because it is the same question: a
        // name the pattern USES but does not BIND (fz-5xp.54).
        Some(BitstringFieldSize::Pinned(pin_id)) => load_pinned_dispatch_value(*pin_id, pinned)
            .and_then(|value| value.as_i64())
            .map(|n| (1, n as u32)),
    }
}

pub(super) fn dispatch_bit_type_tag(ty: BitstringFieldKind) -> u32 {
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

pub(super) fn dispatch_endian_tag(endian: BitstringEndian) -> u32 {
    match endian {
        BitstringEndian::Big => 0,
        BitstringEndian::Little => 1,
        BitstringEndian::Native => 2,
    }
}

pub(super) fn default_dispatch_bit_unit(ty: BitstringFieldKind) -> u32 {
    match ty {
        BitstringFieldKind::Integer | BitstringFieldKind::Float | BitstringFieldKind::Bits => 1,
        BitstringFieldKind::Binary => 8,
        BitstringFieldKind::Utf8 | BitstringFieldKind::Utf16 | BitstringFieldKind::Utf32 => 1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dispatch_matrix::pattern::{PatternRow, SourcePatternRows, pattern_dispatch_from_source};

    /// A subject the executor cannot produce fails its test, whatever the test
    /// is, so the next edge gets its turn.
    ///
    /// Every region routes an unresolvable subject to the miss edge. The
    /// arity question reads its subject in lane form before it reads a value,
    /// and that earlier read answers no differently.
    #[test]
    fn an_unresolvable_subject_misses_its_arity_question() {
        let plan = pattern_dispatch_from_source(SourcePatternRows {
            input_count: 1,
            rows: vec![PatternRow {
                patterns: vec![crate::ast::Spanned::dummy(crate::ast::Pattern::Tuple(vec![
                    crate::ast::Spanned::dummy(crate::ast::Pattern::Wildcard),
                ]))],
                preconditions: Vec::new(),
                guard: None,
                body_id: 0,
            }],
        })
        .expect("a one-field tuple head compiles");
        let mut runtime = IrInterpRuntime::fresh_with_atoms(Vec::new());
        runtime.current_proc = runtime.process_ptr(1).unwrap();
        let transport = TransportStore::new();
        let pinned = DispatchValues::default();
        // No input was delivered, so the plan's only subject resolves to
        // nothing at all.
        let operands = DispatchOperands {
            transport: &transport,
            inputs: &[],
            pinned: &pinned,
        };
        let mut state = DispatchExecState::default();
        let mut type_match =
            |_: &mut IrInterpRuntime, _: &Module, _: &crate::compiler2::Ty, _: &BackendBoundValue| Ok(false);
        let hit = dispatch_region_hit(
            &mut runtime,
            &Module::default(),
            &plan,
            SubjectId(0),
            &Region::TupleArity(1),
            &EdgeEvidence::empty(),
            &operands,
            &mut state,
            &mut type_match,
        );
        assert!(
            matches!(hit, Ok(false)),
            "an unresolvable subject misses its arity question rather than stopping the walk"
        );
    }
}
