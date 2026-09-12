use std::collections::HashMap;
use std::slice::from_raw_parts;

use super::*;
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

#[derive(Default, Clone)]
pub(super) struct DispatchExecState {
    values: HashMap<SubjectId, AnyValue>,
}

pub(super) struct DispatchMatch {
    pub(super) outcome: crate::dispatch_matrix::OutcomeId,
    pub(super) state: DispatchExecState,
}

pub(super) fn execute_dispatch_inputs<TypeHandle, F>(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    inputs: &[AnyValue],
    pinned: &DispatchValues,
    state: &mut DispatchExecState,
    type_match: &mut F,
) -> Option<DispatchMatch>
where
    F: FnMut(&mut IrInterpRuntime, &Module, &TypeHandle, AnyValue) -> Option<bool>,
{
    execute_dispatch_node(
        runtime,
        module,
        plan,
        plan.graph.root,
        inputs,
        pinned,
        state,
        type_match,
    )
}

pub(super) fn execute_dispatch_node<TypeHandle, F>(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    node_id: GraphNodeId,
    inputs: &[AnyValue],
    pinned: &DispatchValues,
    state: &mut DispatchExecState,
    type_match: &mut F,
) -> Option<DispatchMatch>
where
    F: FnMut(&mut IrInterpRuntime, &Module, &TypeHandle, AnyValue) -> Option<bool>,
{
    match plan.graph.node(node_id)? {
        DispatchNode::Fail => None,
        DispatchNode::Outcome { outcome, .. } => Some(DispatchMatch {
            outcome: *outcome,
            state: state.clone(),
        }),
        DispatchNode::Test {
            predicate,
            on_match,
            on_miss,
        } => {
            let mut true_state = state.clone();
            if dispatch_region_hit(
                runtime,
                module,
                plan,
                predicate.subject,
                &predicate.region,
                &on_match.evidence,
                inputs,
                pinned,
                &mut true_state,
                type_match,
            ) {
                if apply_edge_evidence(
                    runtime,
                    module,
                    plan,
                    &on_match.evidence,
                    inputs,
                    pinned,
                    &mut true_state,
                ) {
                    execute_dispatch_node(
                        runtime,
                        module,
                        plan,
                        on_match.target,
                        inputs,
                        pinned,
                        &mut true_state,
                        type_match,
                    )
                } else {
                    execute_dispatch_node(runtime, module, plan, on_miss.target, inputs, pinned, state, type_match)
                }
            } else {
                execute_dispatch_node(runtime, module, plan, on_miss.target, inputs, pinned, state, type_match)
            }
        }
    }
}

fn apply_edge_evidence<TypeHandle>(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    evidence: &EdgeEvidence<TypeHandle>,
    inputs: &[AnyValue],
    pinned: &DispatchValues,
    state: &mut DispatchExecState,
) -> bool {
    for projection in &evidence.projections {
        if state.values.contains_key(projection) {
            continue;
        }

        let Some(value) =
            resolve_dispatch_subject(runtime.cur_proc(), module, plan, *projection, inputs, pinned, state)
        else {
            return false;
        };
        state.values.insert(*projection, value);
    }
    true
}

fn cache_dispatch_subject(
    subject: SubjectId,
    value: Option<AnyValue>,
    state: &mut DispatchExecState,
) -> Option<AnyValue> {
    if let Some(value) = value {
        state.values.insert(subject, value);
        Some(value)
    } else {
        None
    }
}

pub(super) fn resolve_dispatch_subject<TypeHandle>(
    proc: *mut Process,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    subject: SubjectId,
    inputs: &[AnyValue],
    pinned: &DispatchValues,
    state: &mut DispatchExecState,
) -> Option<AnyValue> {
    if let Some(value) = state.values.get(&subject).copied() {
        return Some(value);
    }
    let subject_data = plan.matrix.subjects.get(subject.0 as usize)?;
    let value = match &subject_data.source {
        SubjectSource::Input { ordinal } => inputs.get(*ordinal as usize).copied(),
        SubjectSource::Projection(projection) => match &projection.kind {
            ProjectionKind::TupleField(index) => {
                let parent = resolve_dispatch_subject(proc, module, plan, projection.source, inputs, pinned, state)?;
                let parent_slot = parent.value(proc).ok()?;
                if parent_slot.kind() != ValueKind::STRUCT {
                    return None;
                }
                with_value_ref(proc, parent, "dispatch tuple field", |struct_ref| {
                    fz_struct_get_field_ref(proc, struct_ref, index * 8)
                })
                .ok()
                .and_then(|ref_word| interp_value_from_ref_word(ref_word, "dispatch tuple field").ok())
            }
            ProjectionKind::StructField(field) => {
                let parent = resolve_dispatch_subject(proc, module, plan, projection.source, inputs, pinned, state)?;
                let parent = parent.as_ref_word(proc).ok()?;
                let parent = AnyValueRef::from_raw_word(parent).ok()?;
                let value = unsafe { &*proc }.heap.read_struct_named_field_ref(parent, field).ok()?;
                interp_value_from_ref_word(value.raw_word(), "dispatch struct field").ok()
            }
            ProjectionKind::ListHead => {
                let parent = resolve_dispatch_subject(proc, module, plan, projection.source, inputs, pinned, state)?;
                interp_list_head(proc, parent).ok()
            }
            ProjectionKind::ListTail => {
                let parent = resolve_dispatch_subject(proc, module, plan, projection.source, inputs, pinned, state)?;
                interp_list_tail(proc, parent).ok()
            }
            ProjectionKind::MapValue { key } => {
                let map = resolve_dispatch_subject(proc, module, plan, projection.source, inputs, pinned, state)?;
                dispatch_map_lookup(proc, plan, module, map, key, pinned)
            }
            ProjectionKind::BitstringField(_) => None,
        },
    };
    cache_dispatch_subject(subject, value, state)
}

fn dispatch_region_hit<TypeHandle, F>(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    subject: SubjectId,
    region: &Region<TypeHandle>,
    evidence: &EdgeEvidence<TypeHandle>,
    inputs: &[AnyValue],
    pinned: &DispatchValues,
    state: &mut DispatchExecState,
    type_match: &mut F,
) -> bool
where
    F: FnMut(&mut IrInterpRuntime, &Module, &TypeHandle, AnyValue) -> Option<bool>,
{
    match region {
        Region::Type(ty) => {
            let Some(value) =
                resolve_dispatch_subject(runtime.cur_proc(), module, plan, subject, inputs, pinned, state)
            else {
                return false;
            };
            type_match(runtime, module, ty, value).unwrap_or(false)
        }
        Region::Equal(ComparisonValue::Const(value)) => {
            resolve_dispatch_subject(runtime.cur_proc(), module, plan, subject, inputs, pinned, state)
                .is_some_and(|v| dispatch_const_eq(runtime.cur_proc(), module, v, value))
        }
        Region::Equal(ComparisonValue::Pinned(pin_id)) => {
            let Some(value) =
                resolve_dispatch_subject(runtime.cur_proc(), module, plan, subject, inputs, pinned, state)
            else {
                return false;
            };
            load_pinned_dispatch_value(*pin_id, pinned)
                .is_some_and(|want| interp_value_eq(runtime.cur_proc(), want, value).unwrap_or(false))
        }
        Region::TupleArity(arity) => {
            resolve_dispatch_subject(runtime.cur_proc(), module, plan, subject, inputs, pinned, state).is_some_and(
                |v| {
                    v.value(runtime.cur_proc()).ok().is_some_and(|v| {
                        v.kind() == ValueKind::STRUCT
                            && v.heap_addr().is_some_and(|p| {
                                (unsafe { struct_schema_id(p) }) == interp_tuple_schema_id(runtime, *arity as usize)
                            })
                    })
                },
            )
        }
        Region::List(ListRegion::Empty) => {
            resolve_dispatch_subject(runtime.cur_proc(), module, plan, subject, inputs, pinned, state)
                .is_some_and(|v| v.is_empty_list())
        }
        Region::List(ListRegion::Cons) => {
            resolve_dispatch_subject(runtime.cur_proc(), module, plan, subject, inputs, pinned, state)
                .is_some_and(|v| v.value(runtime.cur_proc()).ok().is_some_and(interp_is_list_cons))
        }
        Region::MapKind => resolve_dispatch_subject(runtime.cur_proc(), module, plan, subject, inputs, pinned, state)
            .is_some_and(|v| v.value(runtime.cur_proc()).ok().is_some_and(is_map_value)),
        Region::MapKeyPresent { key } => {
            let Some(map) = resolve_dispatch_subject(runtime.cur_proc(), module, plan, subject, inputs, pinned, state)
            else {
                return false;
            };
            let Some(value) = dispatch_map_lookup(runtime.cur_proc(), plan, module, map, key, pinned) else {
                return false;
            };
            for result in &evidence.projections {
                if let SubjectSource::Projection(projection) = plan.subject(*result)
                    && projection.source == subject
                    && matches!(&projection.kind, ProjectionKind::MapValue { key: projection_key } if projection_key == key)
                {
                    state.values.insert(*result, value);
                }
            }
            true
        }
        Region::Bitstring(shape) => {
            let Some(value) =
                resolve_dispatch_subject(runtime.cur_proc(), module, plan, subject, inputs, pinned, state)
            else {
                return false;
            };
            value
                .value(runtime.cur_proc())
                .ok()
                .is_some_and(|value| dispatch_read_bitstring(runtime.cur_proc(), plan, value, shape, pinned, state))
        }
        Region::Guard(guard) => plan
            .guards
            .get(guard.0 as usize)
            .and_then(|expr| eval_dispatch_guard(runtime, module, plan, expr, inputs, pinned, state, type_match))
            .is_some_and(|value| !(value.is_false() || value.is_nil())),
    }
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
    inputs: &[AnyValue],
    pinned: &DispatchValues,
    state: &mut DispatchExecState,
    type_match: &mut F,
) -> Option<AnyValue>
where
    F: FnMut(&mut IrInterpRuntime, &Module, &TypeHandle, AnyValue) -> Option<bool>,
{
    Some(match expr {
        PatternGuardExpr::Const(c) => dispatch_const_to_value(runtime.cur_proc(), module, c)?,
        PatternGuardExpr::Subject(subject) => {
            resolve_dispatch_subject(runtime.cur_proc(), module, plan, *subject, inputs, pinned, state)?
        }
        PatternGuardExpr::Pinned(pinned_id) => load_pinned_dispatch_value(*pinned_id, pinned)?,
        PatternGuardExpr::Unary { op, expr } => {
            let v = eval_dispatch_guard(runtime, module, plan, expr, inputs, pinned, state, type_match)?;
            match op {
                PatternGuardUnaryOp::Not => interp_bool_value(v.is_false() || v.is_nil()),
                // The same negation an EXPRESSION gets. Forcing the operand to
                // an integer here made `when -x > 0.0` silently fail its guard
                // for a float and fall to the next clause, so `interp` answered
                // a different clause than `run` and `build` (fz-5xp.46).
                PatternGuardUnaryOp::Neg => super::binop::eval_unop(crate::fz_ir::UnOp::Neg, v).ok()?,
            }
        }
        PatternGuardExpr::Binary { op, lhs, rhs } => {
            let l = eval_dispatch_guard(runtime, module, plan, lhs, inputs, pinned, state, type_match)?;
            let short = match op {
                PatternGuardBinOp::And if !l.is_truthy() => Some(l),
                PatternGuardBinOp::Or if l.is_truthy() => Some(l),
                _ => None,
            };
            if let Some(v) = short {
                return Some(v);
            }
            let r = eval_dispatch_guard(runtime, module, plan, rhs, inputs, pinned, state, type_match)?;
            match op {
                PatternGuardBinOp::Add => AnyValue::Int(guard_int(l)? + guard_int(r)?),
                PatternGuardBinOp::Sub => AnyValue::Int(guard_int(l)? - guard_int(r)?),
                PatternGuardBinOp::Mul => AnyValue::Int(guard_int(l)? * guard_int(r)?),
                PatternGuardBinOp::Div => AnyValue::Int(guard_int(l)? / guard_int(r)?),
                PatternGuardBinOp::Rem => AnyValue::Int(guard_int(l)? % guard_int(r)?),
                // fz-5xp.24 — a guard's `==` is the `==` OPERATOR, so it widens:
                // `when a == b` with a = 1 and b = 1.0 is true. It was strict
                // here because native guards lowered through Prim::BinOp(Eq),
                // which pattern MATCHING also used, and matching must stay
                // strict. The IR now names the two questions separately, so
                // both doors can ask this one.
                PatternGuardBinOp::Eq => interp_bool_value(interp_operator_eq(runtime.cur_proc(), l, r).ok()?),
                PatternGuardBinOp::Neq => interp_bool_value(!interp_operator_eq(runtime.cur_proc(), l, r).ok()?),
                // fz-5xp.18 — a guard orders its operands the same way the rest
                // of the language does, through `fz_value_cmp_ref`. Comparing
                // as integers could not see a float at all: `when a >= b` with
                // a = 2 and b = 1.0 failed the conversion and fell through to
                // the next clause instead of answering true.
                PatternGuardBinOp::Lt => interp_bool_value(guard_cmp(runtime.cur_proc(), l, r)? < 0),
                PatternGuardBinOp::LtEq => interp_bool_value(guard_cmp(runtime.cur_proc(), l, r)? <= 0),
                PatternGuardBinOp::Gt => interp_bool_value(guard_cmp(runtime.cur_proc(), l, r)? > 0),
                PatternGuardBinOp::GtEq => interp_bool_value(guard_cmp(runtime.cur_proc(), l, r)? >= 0),
                PatternGuardBinOp::And | PatternGuardBinOp::Or => r,
            }
        }
        PatternGuardExpr::Dispatch {
            inputs: dispatch_inputs,
            bindings,
            dispatch,
        } => {
            let values = dispatch_inputs
                .iter()
                .map(|input| eval_dispatch_guard(runtime, module, plan, input, inputs, pinned, state, type_match))
                .collect::<Option<Vec<_>>>()?;
            let child_bindings = DispatchValues {
                pinned: bindings
                    .pinned
                    .iter()
                    .map(|id| values.get(id.0 as usize).copied())
                    .collect::<Option<Vec<_>>>()?,
                prepared: bindings
                    .prepared
                    .iter()
                    .map(|id| pinned.prepared.get(id.0 as usize).copied())
                    .collect::<Option<Vec<_>>>()?,
            };
            let mut dispatch_state = DispatchExecState::default();
            let mut matched = execute_dispatch_inputs(
                runtime,
                module,
                &dispatch.plan,
                &values,
                &child_bindings,
                &mut dispatch_state,
                type_match,
            )?;
            let body_id = dispatch.plan.outcome(matched.outcome)?.body_id;
            let body = dispatch.bodies.get(body_id as usize)?;
            eval_dispatch_guard(
                runtime,
                module,
                &dispatch.plan,
                body,
                &values,
                &child_bindings,
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
        state.values.insert(*field_subject, extracted);
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
