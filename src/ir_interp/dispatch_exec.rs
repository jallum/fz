use std::collections::HashMap;
use std::slice::from_raw_parts;

use super::*;
use crate::dispatch_matrix::pattern::{
    PatternDispatchPlan, PatternGuardBinOp, PatternGuardExpr, PatternGuardUnaryOp, prepared_key_name,
};
use crate::dispatch_matrix::{
    BitstringEndian, BitstringFieldKind, BitstringFieldSize, BitstringShape, ComparisonValue, DispatchConst,
    DispatchNode, EdgeEvidence, GraphNodeId, ListRegion, PinnedValueId, ProjectionKind, Region, SubjectId,
    SubjectSource,
};
use crate::fz_ir::Module;
use crate::runtime_type_predicate::{RuntimeTypePredicate, matches_runtime_type_predicate};
use fz_runtime::any_value::{AnyValue as RuntimeAnyValue, TRUE_ATOM_ID, ValueKind, struct_schema_id};
use fz_runtime::ir_runtime::{
    fz_bs_field_spec, fz_bs_read_field_ref, fz_bs_reader_init_ref, fz_matcher_map_get_ref, fz_struct_get_field_ref,
};
use fz_runtime::procbin::{bitstring_bit_len, bitstring_byte_ptr, is_bitstring_like};
use fz_runtime::process::Process;

#[derive(Default, Clone)]
pub(super) struct DispatchExecState {
    values: HashMap<SubjectId, AnyValue>,
    bitstring_fields: HashMap<(SubjectId, u32), AnyValue>,
    direct_bindings: HashMap<String, AnyValue>,
}

pub(super) fn execute_dispatch(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    plan: &PatternDispatchPlan<RuntimeTypePredicate>,
    root: AnyValue,
    pinned: &HashMap<String, AnyValue>,
) -> Option<(u32, Vec<(String, AnyValue)>)> {
    let mut state = DispatchExecState::default();
    let mut type_match =
        |runtime: &mut IrInterpRuntime, module: &Module, predicate: &RuntimeTypePredicate, value: AnyValue| {
            let runtime_value = value.value(runtime.cur_proc()).ok()?;
            let (tuple_schema_ids, named_schema_ids) =
                interp_runtime_type_predicate_schema_ids(runtime, module, predicate);
            Some(matches_runtime_type_predicate(
                predicate,
                module,
                runtime_value,
                &tuple_schema_ids,
                &named_schema_ids,
            ))
        };
    execute_dispatch_inputs(runtime, module, plan, &[root], pinned, &mut state, &mut type_match)
}

pub(super) fn execute_dispatch_inputs<TypeHandle, F>(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    inputs: &[AnyValue],
    pinned: &HashMap<String, AnyValue>,
    state: &mut DispatchExecState,
    type_match: &mut F,
) -> Option<(u32, Vec<(String, AnyValue)>)>
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
    pinned: &HashMap<String, AnyValue>,
    state: &mut DispatchExecState,
    type_match: &mut F,
) -> Option<(u32, Vec<(String, AnyValue)>)>
where
    F: FnMut(&mut IrInterpRuntime, &Module, &TypeHandle, AnyValue) -> Option<bool>,
{
    match plan.graph.node(node_id)? {
        DispatchNode::Fail => None,
        DispatchNode::Outcome { outcome, .. } => {
            let outcome = plan.outcome(*outcome)?;
            let mut out = Vec::with_capacity(outcome.bindings.len());
            for binding in &outcome.bindings {
                let value =
                    resolve_dispatch_subject(runtime.cur_proc(), module, plan, binding.source, inputs, pinned, state)?;
                out.push((binding.name.clone(), value));
            }
            Some((outcome.body_id, out))
        }
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
    pinned: &HashMap<String, AnyValue>,
    state: &mut DispatchExecState,
) -> bool {
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

        let Some(value) = resolve_dispatch_subject(
            runtime.cur_proc(),
            module,
            plan,
            projection.result,
            inputs,
            pinned,
            state,
        ) else {
            return false;
        };
        state.values.insert(projection.result, value);
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
    pinned: &HashMap<String, AnyValue>,
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
            ProjectionKind::BitstringField(index) => state
                .values
                .get(&subject)
                .copied()
                .or_else(|| state.bitstring_fields.get(&(projection.source, *index)).copied()),
        },
    };
    cache_dispatch_subject(subject, value, state)
}

fn apply_direct_bitstring_bindings<TypeHandle>(
    plan: &PatternDispatchPlan<TypeHandle>,
    field_subject: SubjectId,
    value: AnyValue,
    state: &mut DispatchExecState,
) {
    state.values.insert(field_subject, value);
    if let Some(names) = plan.bitstring_direct_bindings.get(&field_subject) {
        for name in names {
            state.direct_bindings.insert(name.clone(), value);
        }
    }
}

fn dispatch_region_hit<TypeHandle, F>(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    subject: SubjectId,
    region: &Region<TypeHandle>,
    evidence: &EdgeEvidence<TypeHandle>,
    inputs: &[AnyValue],
    pinned: &HashMap<String, AnyValue>,
    state: &mut DispatchExecState,
    type_match: &mut F,
) -> bool
where
    F: FnMut(&mut IrInterpRuntime, &Module, &TypeHandle, AnyValue) -> Option<bool>,
{
    match region {
        Region::Any => true,
        Region::Never => false,
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
            load_pinned_dispatch_value(plan, *pin_id, inputs, pinned)
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
            for projection in &evidence.projections {
                if projection.source == subject
                    && matches!(&projection.kind, ProjectionKind::MapValue { key: projection_key } if projection_key == key)
                {
                    state.values.insert(projection.result, value);
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
                .is_some_and(|value| dispatch_read_bitstring(runtime.cur_proc(), plan, subject, value, shape, state))
        }
        Region::Guard(guard) => plan
            .guards
            .get(guard.0 as usize)
            .and_then(|expr| eval_dispatch_guard(runtime, module, plan, expr, inputs, pinned, state, type_match))
            .is_some_and(|value| !(value.is_false() || value.is_nil())),
    }
}

pub(super) fn eval_dispatch_guard<TypeHandle, F>(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    plan: &PatternDispatchPlan<TypeHandle>,
    expr: &PatternGuardExpr<TypeHandle>,
    inputs: &[AnyValue],
    pinned: &HashMap<String, AnyValue>,
    state: &mut DispatchExecState,
    type_match: &mut F,
) -> Option<AnyValue>
where
    F: FnMut(&mut IrInterpRuntime, &Module, &TypeHandle, AnyValue) -> Option<bool>,
{
    Some(match expr {
        PatternGuardExpr::Const(c) => dispatch_const_to_value(module, c)?,
        PatternGuardExpr::Subject(subject) => {
            resolve_dispatch_subject(runtime.cur_proc(), module, plan, *subject, inputs, pinned, state)?
        }
        PatternGuardExpr::Pinned(pinned_id) => load_pinned_dispatch_value(plan, *pinned_id, inputs, pinned)?,
        PatternGuardExpr::Unary { op, expr } => {
            let v = eval_dispatch_guard(runtime, module, plan, expr, inputs, pinned, state, type_match)?;
            match op {
                PatternGuardUnaryOp::Not => interp_bool_value(v.is_false() || v.is_nil()),
                PatternGuardUnaryOp::Neg => AnyValue::Int(-guard_int(v)?),
            }
        }
        PatternGuardExpr::Binary { op, lhs, rhs } => {
            let l = eval_dispatch_guard(runtime, module, plan, lhs, inputs, pinned, state, type_match)?;
            let short = match op {
                PatternGuardBinOp::And if l.is_false() || l.is_nil() => Some(interp_bool_value(false)),
                PatternGuardBinOp::Or if !(l.is_false() || l.is_nil()) => Some(interp_bool_value(true)),
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
                PatternGuardBinOp::Eq => interp_bool_value(interp_value_eq(runtime.cur_proc(), l, r).ok()?),
                PatternGuardBinOp::Neq => interp_bool_value(!interp_value_eq(runtime.cur_proc(), l, r).ok()?),
                PatternGuardBinOp::Lt => interp_bool_value(guard_int(l)? < guard_int(r)?),
                PatternGuardBinOp::LtEq => interp_bool_value(guard_int(l)? <= guard_int(r)?),
                PatternGuardBinOp::Gt => interp_bool_value(guard_int(l)? > guard_int(r)?),
                PatternGuardBinOp::GtEq => interp_bool_value(guard_int(l)? >= guard_int(r)?),
                PatternGuardBinOp::And | PatternGuardBinOp::Or => interp_bool_value(!(r.is_false() || r.is_nil())),
            }
        }
        PatternGuardExpr::Dispatch {
            inputs: dispatch_inputs,
            dispatch,
        } => {
            let values = dispatch_inputs
                .iter()
                .map(|input| eval_dispatch_guard(runtime, module, plan, input, inputs, pinned, state, type_match))
                .collect::<Option<Vec<_>>>()?;
            let mut dispatch_state = DispatchExecState::default();
            let (body_id, _) = execute_dispatch_inputs(
                runtime,
                module,
                &dispatch.plan,
                &values,
                pinned,
                &mut dispatch_state,
                type_match,
            )?;
            let body = dispatch.bodies.get(body_id as usize)?;
            eval_dispatch_guard(
                runtime,
                module,
                &dispatch.plan,
                body,
                &values,
                pinned,
                &mut dispatch_state,
                type_match,
            )?
        }
    })
}

fn load_pinned_dispatch_value<TypeHandle>(
    plan: &PatternDispatchPlan<TypeHandle>,
    pinned: PinnedValueId,
    inputs: &[AnyValue],
    pinned_values: &HashMap<String, AnyValue>,
) -> Option<AnyValue> {
    let p = plan.pinned.get(pinned.0 as usize)?;
    if let Some(input) = p.input {
        return inputs.get(input as usize).copied();
    }
    pinned_values.get(&p.name).copied()
}

pub(super) fn dispatch_const_to_value(module: &Module, c: &DispatchConst) -> Option<AnyValue> {
    match c {
        DispatchConst::Int(n) => Some(AnyValue::Int(*n)),
        DispatchConst::FloatBits(bits) => Some(AnyValue::Float(f64::from_bits(*bits))),
        DispatchConst::AtomName(name) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .map(|id| AnyValue::Atom(id as u32)),
        DispatchConst::Bool(value) => Some(interp_bool_value(*value)),
        DispatchConst::Nil => Some(interp_nil_value()),
        DispatchConst::EmptyList => Some(interp_empty_list_value()),
        DispatchConst::Utf8Binary(_) => None,
    }
}

pub(super) fn dispatch_const_eq(proc: *mut Process, module: &Module, val: AnyValue, value: &DispatchConst) -> bool {
    match value {
        DispatchConst::Int(n) => val.as_i64() == Some(*n),
        DispatchConst::FloatBits(bits) => {
            matches!(val, AnyValue::Float(f) if f.to_bits() == *bits)
        }
        DispatchConst::AtomName(name) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .is_some_and(|id| val.is_atom_id(id as u32)),
        DispatchConst::Bool(true) => val.is_atom_id(TRUE_ATOM_ID),
        DispatchConst::Bool(false) => val.is_false(),
        DispatchConst::Nil => val.is_nil(),
        DispatchConst::EmptyList => val.is_empty_list(),
        DispatchConst::Utf8Binary(bytes) => match val {
            AnyValue::FnRef(_) => false,
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
                    slice == bytes.as_slice()
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
    key: &DispatchConst,
    pinned: &HashMap<String, AnyValue>,
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
    key: &DispatchConst,
    pinned: &HashMap<String, AnyValue>,
) -> Option<AnyValue> {
    match key {
        DispatchConst::Int(n) => Some(AnyValue::Int(*n)),
        DispatchConst::FloatBits(bits) => Some(AnyValue::Float(f64::from_bits(*bits))),
        DispatchConst::Bool(value) => Some(interp_bool_value(*value)),
        DispatchConst::Nil => Some(interp_nil_value()),
        DispatchConst::AtomName(name) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .map(|id| AnyValue::Atom(id as u32)),
        DispatchConst::Utf8Binary(_) => plan
            .prepared_keys
            .iter()
            .position(|prepared| prepared == key)
            .and_then(|index| pinned.get(&prepared_key_name(index)).copied()),
        DispatchConst::EmptyList => None,
    }
}

pub(super) fn dispatch_read_bitstring<TypeHandle>(
    proc: *mut Process,
    plan: &PatternDispatchPlan<TypeHandle>,
    subject: SubjectId,
    value: RuntimeAnyValue,
    shape: &BitstringShape,
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
    for (index, field) in shape.fields.iter().enumerate() {
        let Some((size_present, size_value)) = dispatch_bit_size_value(&field.size, state) else {
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
            (index + 1 == shape.fields.len()) as u32,
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
        let index = index as u32;
        state.bitstring_fields.insert((subject, index), extracted);
        if let Some(field_subject) = bitstring_field_subject(plan, subject, index) {
            apply_direct_bitstring_bindings(plan, field_subject, extracted, state);
        }
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

fn bitstring_field_subject<TypeHandle>(
    plan: &PatternDispatchPlan<TypeHandle>,
    source: SubjectId,
    index: u32,
) -> Option<SubjectId> {
    plan.matrix.subjects.iter().find_map(|subject| match &subject.source {
        SubjectSource::Projection(projection)
            if projection.source == source && projection.kind == ProjectionKind::BitstringField(index) =>
        {
            Some(subject.id)
        }
        _ => None,
    })
}

pub(super) fn dispatch_bit_size_value(
    size: &Option<BitstringFieldSize>,
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
        Some(BitstringFieldSize::BindingName(name)) => state
            .direct_bindings
            .get(name)
            .and_then(|v| v.as_i64())
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
