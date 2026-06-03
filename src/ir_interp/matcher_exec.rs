use std::collections::HashMap;
use std::slice::from_raw_parts;

use super::*;
use crate::exec::matcher::{
    BodyId, GuardBinOp, GuardExpr, GuardUnaryOp, Matcher, MatcherBitField, MatcherBitSize, MatcherBitType,
    MatcherConst, MatcherEndian, MatcherNode, MatcherTest, NodeId, SubjectRef, SwitchKey, SwitchKind,
    map_value_subject, prepared_key_name,
};
use crate::fz_ir::Module;
use fz_runtime::any_value::{AnyValue as RuntimeAnyValue, TRUE_ATOM_ID, ValueKind, struct_schema_id};
use fz_runtime::ir_runtime::{
    fz_bs_field_spec, fz_bs_read_field_ref, fz_bs_reader_init_ref, fz_matcher_map_get_ref, fz_struct_get_field_ref,
};
use fz_runtime::procbin::{bitstring_bit_len, bitstring_byte_ptr, is_bitstring_like};
use fz_runtime::process::Process;

#[derive(Default)]
pub(super) struct MatcherExecState {
    pub(super) values: HashMap<SubjectRef, AnyValue>,
    pub(super) bitstring_fields: HashMap<(SubjectRef, u32), AnyValue>,
}

pub(super) fn execute_matcher(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    matcher: &Matcher,
    root: AnyValue,
    pinned: &HashMap<String, AnyValue>,
) -> Option<(BodyId, Vec<(String, AnyValue)>)> {
    let mut state = MatcherExecState::default();
    execute_matcher_node(runtime, module, matcher, matcher.root, &[root], pinned, &mut state)
}

pub(super) fn execute_matcher_node(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    matcher: &Matcher,
    node_id: NodeId,
    inputs: &[AnyValue],
    pinned: &HashMap<String, AnyValue>,
    state: &mut MatcherExecState,
) -> Option<(BodyId, Vec<(String, AnyValue)>)> {
    match matcher.node(node_id)? {
        MatcherNode::Fail { .. } => None,
        MatcherNode::Leaf(leaf) => {
            let mut out = Vec::with_capacity(leaf.bindings.len());
            for binding in &leaf.bindings {
                let value = resolve_matcher_subject(
                    runtime.cur_proc(),
                    module,
                    matcher,
                    &binding.source,
                    inputs,
                    pinned,
                    state,
                )?;
                out.push((binding.name.clone(), value));
            }
            Some((leaf.body_id, out))
        }
        MatcherNode::Switch {
            subject,
            kind,
            cases,
            default,
            ..
        } => {
            let value = resolve_matcher_subject(runtime.cur_proc(), module, matcher, subject, inputs, pinned, state)?;
            for (key, case_node) in cases {
                if matcher_switch_hit(runtime, module, value, kind, key) {
                    return execute_matcher_node(runtime, module, matcher, *case_node, inputs, pinned, state);
                }
            }
            execute_matcher_node(runtime, module, matcher, *default, inputs, pinned, state)
        }
        MatcherNode::Test {
            test,
            on_true,
            on_false,
            ..
        } => {
            let next = if matcher_test_hit(runtime, module, matcher, test, inputs, pinned, state) {
                *on_true
            } else {
                *on_false
            };
            execute_matcher_node(runtime, module, matcher, next, inputs, pinned, state)
        }
        MatcherNode::Guard {
            expr,
            on_true,
            on_false,
            ..
        } => {
            let value = eval_matcher_guard(runtime, module, matcher, expr, inputs, pinned, state)?;
            let next = if value.is_false() || value.is_nil() {
                *on_false
            } else {
                *on_true
            };
            execute_matcher_node(runtime, module, matcher, next, inputs, pinned, state)
        }
    }
}

pub(super) fn eval_matcher_guard(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    matcher: &Matcher,
    expr: &GuardExpr,
    inputs: &[AnyValue],
    pinned: &HashMap<String, AnyValue>,
    state: &MatcherExecState,
) -> Option<AnyValue> {
    Some(match expr {
        GuardExpr::Const(c) => matcher_const_to_value(module, c)?,
        GuardExpr::Subject(subject) => {
            resolve_matcher_subject(runtime.cur_proc(), module, matcher, subject, inputs, pinned, state)?
        }
        GuardExpr::Pinned(pinned_id) => {
            let p = matcher.pinned.get(pinned_id.0 as usize)?;
            if let Some(var) = p.var {
                return inputs.get(var.0 as usize).copied();
            }
            *pinned.get(&p.name)?
        }
        GuardExpr::Unary { op, expr } => {
            let v = eval_matcher_guard(runtime, module, matcher, expr, inputs, pinned, state)?;
            match op {
                GuardUnaryOp::Not => interp_bool_value(v.is_false() || v.is_nil()),
                GuardUnaryOp::Neg => AnyValue::Int(-guard_int(v)?),
            }
        }
        GuardExpr::Binary { op, lhs, rhs } => {
            let l = eval_matcher_guard(runtime, module, matcher, lhs, inputs, pinned, state)?;
            let short = match op {
                GuardBinOp::And if l.is_false() || l.is_nil() => Some(interp_bool_value(false)),
                GuardBinOp::Or if !(l.is_false() || l.is_nil()) => Some(interp_bool_value(true)),
                _ => None,
            };
            if let Some(v) = short {
                return Some(v);
            }
            let r = eval_matcher_guard(runtime, module, matcher, rhs, inputs, pinned, state)?;
            match op {
                GuardBinOp::Add => AnyValue::Int(guard_int(l)? + guard_int(r)?),
                GuardBinOp::Sub => AnyValue::Int(guard_int(l)? - guard_int(r)?),
                GuardBinOp::Mul => AnyValue::Int(guard_int(l)? * guard_int(r)?),
                GuardBinOp::Div => AnyValue::Int(guard_int(l)? / guard_int(r)?),
                GuardBinOp::Rem => AnyValue::Int(guard_int(l)? % guard_int(r)?),
                GuardBinOp::Eq => interp_bool_value(interp_value_eq(runtime.cur_proc(), l, r).ok()?),
                GuardBinOp::Neq => interp_bool_value(!interp_value_eq(runtime.cur_proc(), l, r).ok()?),
                GuardBinOp::Lt => interp_bool_value(guard_int(l)? < guard_int(r)?),
                GuardBinOp::LtEq => interp_bool_value(guard_int(l)? <= guard_int(r)?),
                GuardBinOp::Gt => interp_bool_value(guard_int(l)? > guard_int(r)?),
                GuardBinOp::GtEq => interp_bool_value(guard_int(l)? >= guard_int(r)?),
                GuardBinOp::And | GuardBinOp::Or => interp_bool_value(!(r.is_false() || r.is_nil())),
            }
        }
        GuardExpr::Dispatch {
            inputs: dispatch_inputs,
            dispatch,
        } => {
            let values = dispatch_inputs
                .iter()
                .map(|input| eval_matcher_guard(runtime, module, matcher, input, inputs, pinned, state))
                .collect::<Option<Vec<_>>>()?;
            let mut dispatch_state = MatcherExecState::default();
            let (body_id, _) = execute_matcher_node(
                runtime,
                module,
                &dispatch.matcher,
                dispatch.matcher.root,
                &values,
                pinned,
                &mut dispatch_state,
            )?;
            let body = dispatch.bodies.get(body_id as usize)?;
            eval_matcher_guard(
                runtime,
                module,
                &dispatch.matcher,
                body,
                &values,
                pinned,
                &dispatch_state,
            )?
        }
    })
}

pub(super) fn matcher_const_to_value(module: &Module, c: &MatcherConst) -> Option<AnyValue> {
    match c {
        MatcherConst::Int(n) => Some(AnyValue::Int(*n)),
        MatcherConst::AtomName(name) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .map(|id| AnyValue::Atom(id as u32)),
        MatcherConst::Bool(value) => Some(interp_bool_value(*value)),
        MatcherConst::Nil => Some(interp_nil_value()),
        MatcherConst::EmptyList => Some(interp_empty_list_value()),
        MatcherConst::FloatBits(_) | MatcherConst::Utf8Binary(_) | MatcherConst::PreparedKey(_) => None,
    }
}

pub(super) fn resolve_matcher_subject(
    proc: *mut Process,
    module: &Module,
    matcher: &Matcher,
    subject: &SubjectRef,
    inputs: &[AnyValue],
    pinned: &HashMap<String, AnyValue>,
    state: &MatcherExecState,
) -> Option<AnyValue> {
    if let Some(value) = state.values.get(subject).copied() {
        return Some(value);
    }
    match subject {
        SubjectRef::Input(id) => inputs.get(id.0 as usize).copied(),
        SubjectRef::TupleField { tuple, index } => {
            let parent = resolve_matcher_subject(proc, module, matcher, tuple, inputs, pinned, state)?;
            let parent_slot = parent.value().ok()?;
            if parent_slot.kind() != ValueKind::STRUCT {
                return None;
            }
            with_value_ref(proc, parent, "matcher tuple field", |struct_ref| {
                fz_struct_get_field_ref(proc, struct_ref, index * 8)
            })
            .ok()
            .and_then(|ref_word| interp_value_from_ref_word(ref_word, "matcher tuple field").ok())
        }
        SubjectRef::ListHead(list) => {
            let parent = resolve_matcher_subject(proc, module, matcher, list, inputs, pinned, state)?;
            interp_list_head(proc, parent).ok()
        }
        SubjectRef::ListTail(list) => {
            let parent = resolve_matcher_subject(proc, module, matcher, list, inputs, pinned, state)?;
            interp_list_tail(proc, parent).ok()
        }
        SubjectRef::MapValue { map, key } => {
            let map = resolve_matcher_subject(proc, module, matcher, map, inputs, pinned, state)?;
            matcher_map_lookup(proc, matcher, module, map, key, pinned)
        }
        SubjectRef::BitstringField { bitstring, index } => {
            state.bitstring_fields.get(&((**bitstring).clone(), *index)).copied()
        }
    }
}

pub(super) fn matcher_test_hit(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    matcher: &Matcher,
    test: &MatcherTest,
    inputs: &[AnyValue],
    pinned: &HashMap<String, AnyValue>,
    state: &mut MatcherExecState,
) -> bool {
    match test {
        MatcherTest::EqConst { subject, value } => {
            resolve_matcher_subject(runtime.cur_proc(), module, matcher, subject, inputs, pinned, state)
                .is_some_and(|v| matcher_const_eq(module, v, value))
        }
        MatcherTest::EqPinned {
            subject,
            pinned: pin_id,
        } => {
            let Some(value) =
                resolve_matcher_subject(runtime.cur_proc(), module, matcher, subject, inputs, pinned, state)
            else {
                return false;
            };
            let Some(pin) = matcher.pinned.get(pin_id.0 as usize) else {
                return false;
            };
            if let Some(var) = pin.var {
                return inputs
                    .get(var.0 as usize)
                    .is_some_and(|want| interp_value_eq(runtime.cur_proc(), *want, value).unwrap_or(false));
            }
            pinned
                .get(&pin.name)
                .is_some_and(|want| interp_value_eq(runtime.cur_proc(), *want, value).unwrap_or(false))
        }
        MatcherTest::TupleArity { subject, arity } => {
            resolve_matcher_subject(runtime.cur_proc(), module, matcher, subject, inputs, pinned, state).is_some_and(
                |v| {
                    v.value().ok().is_some_and(|v| {
                        v.kind() == ValueKind::STRUCT
                            && v.heap_addr().is_some_and(|p| {
                                (unsafe { struct_schema_id(p) }) == interp_tuple_schema_id(runtime, *arity as usize)
                            })
                    })
                },
            )
        }
        MatcherTest::ListCons { subject } => {
            resolve_matcher_subject(runtime.cur_proc(), module, matcher, subject, inputs, pinned, state)
                .is_some_and(|v| v.value().ok().is_some_and(interp_is_list_cons))
        }
        MatcherTest::MapKind { subject } => {
            resolve_matcher_subject(runtime.cur_proc(), module, matcher, subject, inputs, pinned, state)
                .is_some_and(|v| v.value().ok().is_some_and(is_map_value))
        }
        MatcherTest::MapHasKey { subject, key } => {
            let Some(v) = resolve_matcher_subject(runtime.cur_proc(), module, matcher, subject, inputs, pinned, state)
            else {
                return false;
            };
            let Some(value) = matcher_map_lookup(runtime.cur_proc(), matcher, module, v, key, pinned) else {
                return false;
            };
            state.values.insert(map_value_subject(subject, key), value);
            true
        }
        MatcherTest::Bitstring { subject, fields } => {
            let Some(value) =
                resolve_matcher_subject(runtime.cur_proc(), module, matcher, subject, inputs, pinned, state)
            else {
                return false;
            };
            value
                .value()
                .ok()
                .is_some_and(|value| matcher_read_bitstring(runtime.cur_proc(), subject, value, fields, state))
        }
        MatcherTest::Type { .. } => true,
    }
}

pub(super) fn matcher_switch_hit(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    val: AnyValue,
    kind: &SwitchKind,
    key: &SwitchKey,
) -> bool {
    match (kind, key) {
        (SwitchKind::Atom, SwitchKey::AtomName(name)) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .is_some_and(|id| val.is_atom_id(id as u32)),
        (SwitchKind::Int, SwitchKey::Int(n)) => val.as_i64() == Some(*n),
        (SwitchKind::Bool, SwitchKey::Bool(true)) => val.is_atom_id(TRUE_ATOM_ID),
        (SwitchKind::Bool, SwitchKey::Bool(false)) => val.is_false(),
        (SwitchKind::Nil, SwitchKey::Nil) => val.is_nil(),
        (SwitchKind::TupleArity, SwitchKey::Arity(arity)) => val.value().ok().is_some_and(|val| {
            val.kind() == ValueKind::STRUCT
                && val.heap_addr().is_some_and(|p| {
                    (unsafe { struct_schema_id(p) }) == interp_tuple_schema_id(runtime, *arity as usize)
                })
        }),
        (SwitchKind::Float, SwitchKey::FloatBits(bits)) => {
            matcher_const_eq(module, val, &MatcherConst::FloatBits(*bits))
        }
        (SwitchKind::Binary, SwitchKey::Utf8Binary(bytes)) => {
            matcher_const_eq(module, val, &MatcherConst::Utf8Binary(bytes.clone()))
        }
        (SwitchKind::ListCons, SwitchKey::Nil) => val.is_nil(),
        (SwitchKind::ListCons, SwitchKey::EmptyList) => val.is_empty_list(),
        (SwitchKind::ListCons, SwitchKey::Cons) => val.value().ok().is_some_and(interp_is_list_cons),
        _ => false,
    }
}

pub(super) fn matcher_const_eq(module: &Module, val: AnyValue, value: &MatcherConst) -> bool {
    match value {
        MatcherConst::Int(n) => val.as_i64() == Some(*n),
        MatcherConst::FloatBits(bits) => {
            matches!(val, AnyValue::Float(f) if f.to_bits() == *bits)
        }
        MatcherConst::AtomName(name) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .is_some_and(|id| val.is_atom_id(id as u32)),
        MatcherConst::Bool(true) => val.is_atom_id(TRUE_ATOM_ID),
        MatcherConst::Bool(false) => val.is_false(),
        MatcherConst::Nil => val.is_nil(),
        MatcherConst::EmptyList => val.is_empty_list(),
        MatcherConst::Utf8Binary(bytes) => val.value().ok().is_some_and(|val| {
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
        MatcherConst::PreparedKey(_) => false,
    }
}

pub(super) fn matcher_map_lookup(
    proc: *mut Process,
    matcher: &Matcher,
    module: &Module,
    map: AnyValue,
    key: &MatcherConst,
    pinned: &HashMap<String, AnyValue>,
) -> Option<AnyValue> {
    if !map.value().ok().is_some_and(is_map_value) {
        return None;
    }
    let key = matcher_const_key_value(matcher, module, key, pinned)?;
    let ref_word = with_value_ref(proc, map, "MatcherMapGet map", |map_ref| {
        with_value_ref(proc, key, "MatcherMapGet key", |key_ref| {
            fz_matcher_map_get_ref(proc, map_ref, key_ref)
        })
    })
    .ok()?
    .ok()?;
    let value = interp_value_from_ref_word(ref_word, "MatcherMapGet").ok()?;
    match value {
        AnyValue::Null => None,
        _ => Some(value),
    }
}

pub(super) fn matcher_const_key_value(
    matcher: &Matcher,
    module: &Module,
    key: &MatcherConst,
    pinned: &HashMap<String, AnyValue>,
) -> Option<AnyValue> {
    match key {
        MatcherConst::Int(n) => Some(AnyValue::Int(*n)),
        MatcherConst::FloatBits(bits) => Some(AnyValue::Float(f64::from_bits(*bits))),
        MatcherConst::Bool(value) => Some(interp_bool_value(*value)),
        MatcherConst::Nil => Some(interp_nil_value()),
        MatcherConst::AtomName(name) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .map(|id| AnyValue::Atom(id as u32)),
        MatcherConst::PreparedKey(index) => matcher
            .prepared_keys
            .get(*index as usize)
            .and_then(|_| pinned.get(&prepared_key_name(*index as usize)))
            .copied(),
        _ => None,
    }
}

pub(super) fn matcher_read_bitstring(
    proc: *mut Process,
    subject: &SubjectRef,
    value: RuntimeAnyValue,
    fields: &[MatcherBitField],
    state: &mut MatcherExecState,
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
    let mut size_bindings: HashMap<String, AnyValue> = HashMap::new();
    for (index, field) in fields.iter().enumerate() {
        let Some((size_present, size_value)) = matcher_bit_size_value(&field.size, &size_bindings) else {
            return false;
        };
        let Ok(reader_any) = interp_value_from_ref_word(reader, "bitstring matcher reader") else {
            return false;
        };
        let Ok(reader_ref) = reader_any.as_ref_word(proc) else {
            return false;
        };
        let field_spec = fz_bs_field_spec(
            matcher_bit_type_tag(field.ty),
            size_present,
            field.unit.unwrap_or(default_matcher_bit_unit(field.ty)),
            matcher_endian_tag(field.endian),
            field.signed as u32,
            (index + 1 == fields.len()) as u32,
        );
        let result = fz_bs_read_field_ref(proc, reader_ref, field_spec, size_value);
        let Ok(ok) = interp_struct_field_from_tagged_bits(proc, result, 0, "bitstring matcher ok") else {
            return false;
        };
        if ok.is_false() || ok.is_nil() {
            return false;
        }
        let Ok(extracted) = interp_struct_field_from_tagged_bits(proc, result, 8, "bitstring matcher extracted") else {
            return false;
        };
        let Ok(next_reader) = interp_struct_field_from_tagged_bits(proc, result, 16, "bitstring matcher next reader")
        else {
            return false;
        };
        state
            .bitstring_fields
            .insert((subject.clone(), index as u32), extracted);
        for name in &field.direct_bindings {
            size_bindings.insert(name.clone(), extracted);
        }
        let Ok(next_reader_ref) = next_reader.as_ref_word(proc) else {
            return false;
        };
        reader = next_reader_ref;
    }
    let Ok(bit_len) = interp_struct_field_from_tagged_bits(proc, reader, 8, "bitstring matcher bit_len") else {
        return false;
    };
    let Ok(pos) = interp_struct_field_from_tagged_bits(proc, reader, 16, "bitstring matcher pos") else {
        return false;
    };
    bit_len.as_i64() == pos.as_i64()
}

pub(super) fn matcher_bit_size_value(
    size: &Option<MatcherBitSize>,
    bindings: &HashMap<String, AnyValue>,
) -> Option<(u32, u32)> {
    match size {
        None => Some((0, 0)),
        Some(MatcherBitSize::Literal(n)) => Some((1, *n)),
        Some(MatcherBitSize::BindingName(name)) => bindings.get(name).and_then(|v| v.as_i64()).map(|n| (1, n as u32)),
    }
}

pub(super) fn matcher_bit_type_tag(ty: MatcherBitType) -> u32 {
    match ty {
        MatcherBitType::Integer => 0,
        MatcherBitType::Float => 1,
        MatcherBitType::Binary => 2,
        MatcherBitType::Bits => 3,
        MatcherBitType::Utf8 => 4,
        MatcherBitType::Utf16 => 5,
        MatcherBitType::Utf32 => 6,
    }
}

pub(super) fn matcher_endian_tag(endian: MatcherEndian) -> u32 {
    match endian {
        MatcherEndian::Big => 0,
        MatcherEndian::Little => 1,
        MatcherEndian::Native => 2,
    }
}

pub(super) fn default_matcher_bit_unit(ty: MatcherBitType) -> u32 {
    match ty {
        MatcherBitType::Integer | MatcherBitType::Float | MatcherBitType::Bits => 1,
        MatcherBitType::Binary => 8,
        MatcherBitType::Utf8 | MatcherBitType::Utf16 | MatcherBitType::Utf32 => 1,
    }
}
