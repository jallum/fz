use std::collections::HashMap;

use super::*;
use crate::fz_ir::Module;
use fz_runtime::any_value::{AnyValue as RuntimeAnyValue, ValueKind};

#[derive(Default)]
pub(super) struct MatcherExecState {
    pub(super) values: HashMap<crate::matcher::SubjectRef, AnyValue>,
    pub(super) bitstring_fields: HashMap<(crate::matcher::SubjectRef, u32), AnyValue>,
}

pub(super) fn execute_matcher(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    matcher: &crate::matcher::Matcher,
    root: AnyValue,
    pinned: &HashMap<String, AnyValue>,
) -> Option<(crate::matcher::BodyId, Vec<(String, AnyValue)>)> {
    let mut state = MatcherExecState::default();
    execute_matcher_node(
        runtime,
        module,
        matcher,
        matcher.root,
        &[root],
        pinned,
        &mut state,
    )
}

pub(super) fn execute_matcher_node(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    matcher: &crate::matcher::Matcher,
    node_id: crate::matcher::NodeId,
    inputs: &[AnyValue],
    pinned: &HashMap<String, AnyValue>,
    state: &mut MatcherExecState,
) -> Option<(crate::matcher::BodyId, Vec<(String, AnyValue)>)> {
    use crate::matcher::MatcherNode;
    match matcher.node(node_id)? {
        MatcherNode::Fail { .. } => None,
        MatcherNode::Leaf(leaf) => {
            let mut out = Vec::with_capacity(leaf.bindings.len());
            for binding in &leaf.bindings {
                let value = resolve_matcher_subject(
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
            let value = resolve_matcher_subject(module, matcher, subject, inputs, pinned, state)?;
            for (key, case_node) in cases {
                if matcher_switch_hit(runtime, module, value, kind, key) {
                    return execute_matcher_node(
                        runtime, module, matcher, *case_node, inputs, pinned, state,
                    );
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
    matcher: &crate::matcher::Matcher,
    expr: &crate::matcher::GuardExpr,
    inputs: &[AnyValue],
    pinned: &HashMap<String, AnyValue>,
    state: &MatcherExecState,
) -> Option<AnyValue> {
    use crate::matcher::{GuardBinOp, GuardExpr, GuardUnaryOp};
    Some(match expr {
        GuardExpr::Const(c) => matcher_const_to_value(module, c)?,
        GuardExpr::Subject(subject) => {
            resolve_matcher_subject(module, matcher, subject, inputs, pinned, state)?
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
                GuardBinOp::Eq => interp_bool_value(interp_value_eq(l, r).ok()?),
                GuardBinOp::Neq => interp_bool_value(!interp_value_eq(l, r).ok()?),
                GuardBinOp::Lt => interp_bool_value(guard_int(l)? < guard_int(r)?),
                GuardBinOp::LtEq => interp_bool_value(guard_int(l)? <= guard_int(r)?),
                GuardBinOp::Gt => interp_bool_value(guard_int(l)? > guard_int(r)?),
                GuardBinOp::GtEq => interp_bool_value(guard_int(l)? >= guard_int(r)?),
                GuardBinOp::And | GuardBinOp::Or => {
                    interp_bool_value(!(r.is_false() || r.is_nil()))
                }
            }
        }
        GuardExpr::Dispatch {
            inputs: dispatch_inputs,
            dispatch,
        } => {
            let values = dispatch_inputs
                .iter()
                .map(|input| {
                    eval_matcher_guard(runtime, module, matcher, input, inputs, pinned, state)
                })
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

pub(super) fn matcher_const_to_value(
    module: &Module,
    c: &crate::matcher::MatcherConst,
) -> Option<AnyValue> {
    use crate::matcher::MatcherConst;
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
        MatcherConst::FloatBits(_) | MatcherConst::Utf8Binary(_) | MatcherConst::PreparedKey(_) => {
            None
        }
    }
}

pub(super) fn resolve_matcher_subject(
    module: &Module,
    matcher: &crate::matcher::Matcher,
    subject: &crate::matcher::SubjectRef,
    inputs: &[AnyValue],
    pinned: &HashMap<String, AnyValue>,
    state: &MatcherExecState,
) -> Option<AnyValue> {
    if let Some(value) = state.values.get(subject).copied() {
        return Some(value);
    }
    match subject {
        crate::matcher::SubjectRef::Input(id) => inputs.get(id.0 as usize).copied(),
        crate::matcher::SubjectRef::TupleField { tuple, index } => {
            let parent = resolve_matcher_subject(module, matcher, tuple, inputs, pinned, state)?;
            let parent_slot = parent.value().ok()?;
            if parent_slot.kind() != ValueKind::STRUCT {
                return None;
            }
            with_value_ref(parent, "matcher tuple field", |struct_ref| {
                fz_runtime::ir_runtime::fz_struct_get_field_ref(
                    fz_runtime::process::current_process(),
                    struct_ref,
                    index * 8,
                )
            })
            .ok()
            .and_then(|ref_word| interp_value_from_ref_word(ref_word, "matcher tuple field").ok())
        }
        crate::matcher::SubjectRef::ListHead(list) => {
            let parent = resolve_matcher_subject(module, matcher, list, inputs, pinned, state)?;
            interp_list_head(parent).ok()
        }
        crate::matcher::SubjectRef::ListTail(list) => {
            let parent = resolve_matcher_subject(module, matcher, list, inputs, pinned, state)?;
            interp_list_tail(parent).ok()
        }
        crate::matcher::SubjectRef::MapValue { map, key } => {
            let map = resolve_matcher_subject(module, matcher, map, inputs, pinned, state)?;
            matcher_map_lookup(matcher, module, map, key, pinned)
        }
        crate::matcher::SubjectRef::BitstringField { bitstring, index } => state
            .bitstring_fields
            .get(&((**bitstring).clone(), *index))
            .copied(),
    }
}

pub(super) fn matcher_test_hit(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    matcher: &crate::matcher::Matcher,
    test: &crate::matcher::MatcherTest,
    inputs: &[AnyValue],
    pinned: &HashMap<String, AnyValue>,
    state: &mut MatcherExecState,
) -> bool {
    match test {
        crate::matcher::MatcherTest::EqConst { subject, value } => {
            resolve_matcher_subject(module, matcher, subject, inputs, pinned, state)
                .is_some_and(|v| matcher_const_eq(module, v, value))
        }
        crate::matcher::MatcherTest::EqPinned {
            subject,
            pinned: pin_id,
        } => {
            let Some(value) =
                resolve_matcher_subject(module, matcher, subject, inputs, pinned, state)
            else {
                return false;
            };
            let Some(pin) = matcher.pinned.get(pin_id.0 as usize) else {
                return false;
            };
            if let Some(var) = pin.var {
                return inputs
                    .get(var.0 as usize)
                    .is_some_and(|want| interp_value_eq(*want, value).unwrap_or(false));
            }
            pinned
                .get(&pin.name)
                .is_some_and(|want| interp_value_eq(*want, value).unwrap_or(false))
        }
        crate::matcher::MatcherTest::TupleArity { subject, arity } => resolve_matcher_subject(
            module, matcher, subject, inputs, pinned, state,
        )
        .is_some_and(|v| {
            v.value().ok().is_some_and(|v| {
                v.kind() == ValueKind::STRUCT
                    && v.heap_addr().is_some_and(|p| {
                        (unsafe { fz_runtime::any_value::struct_schema_id(p) })
                            == interp_tuple_schema_id(runtime, *arity as usize)
                    })
            })
        }),
        crate::matcher::MatcherTest::ListCons { subject } => {
            resolve_matcher_subject(module, matcher, subject, inputs, pinned, state)
                .is_some_and(|v| v.value().ok().is_some_and(interp_is_list_cons))
        }
        crate::matcher::MatcherTest::MapKind { subject } => {
            resolve_matcher_subject(module, matcher, subject, inputs, pinned, state)
                .is_some_and(|v| v.value().ok().is_some_and(is_map_value))
        }
        crate::matcher::MatcherTest::MapHasKey { subject, key } => {
            let Some(v) = resolve_matcher_subject(module, matcher, subject, inputs, pinned, state)
            else {
                return false;
            };
            let Some(value) = matcher_map_lookup(matcher, module, v, key, pinned) else {
                return false;
            };
            state
                .values
                .insert(crate::matcher::map_value_subject(subject, key), value);
            true
        }
        crate::matcher::MatcherTest::Bitstring { subject, fields } => {
            let Some(value) =
                resolve_matcher_subject(module, matcher, subject, inputs, pinned, state)
            else {
                return false;
            };
            value
                .value()
                .ok()
                .is_some_and(|value| matcher_read_bitstring(subject, value, fields, state))
        }
        crate::matcher::MatcherTest::Type { .. } => true,
    }
}

pub(super) fn matcher_switch_hit(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    val: AnyValue,
    kind: &crate::matcher::SwitchKind,
    key: &crate::matcher::SwitchKey,
) -> bool {
    match (kind, key) {
        (crate::matcher::SwitchKind::Atom, crate::matcher::SwitchKey::AtomName(name)) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .is_some_and(|id| val.is_atom_id(id as u32)),
        (crate::matcher::SwitchKind::Int, crate::matcher::SwitchKey::Int(n)) => {
            val.as_i64() == Some(*n)
        }
        (crate::matcher::SwitchKind::Bool, crate::matcher::SwitchKey::Bool(true)) => {
            val.is_atom_id(fz_runtime::any_value::TRUE_ATOM_ID)
        }
        (crate::matcher::SwitchKind::Bool, crate::matcher::SwitchKey::Bool(false)) => {
            val.is_false()
        }
        (crate::matcher::SwitchKind::Nil, crate::matcher::SwitchKey::Nil) => val.is_nil(),
        (crate::matcher::SwitchKind::TupleArity, crate::matcher::SwitchKey::Arity(arity)) => {
            val.value().ok().is_some_and(|val| {
                val.kind() == ValueKind::STRUCT
                    && val.heap_addr().is_some_and(|p| {
                        (unsafe { fz_runtime::any_value::struct_schema_id(p) })
                            == interp_tuple_schema_id(runtime, *arity as usize)
                    })
            })
        }
        (crate::matcher::SwitchKind::Float, crate::matcher::SwitchKey::FloatBits(bits)) => {
            matcher_const_eq(module, val, &crate::matcher::MatcherConst::FloatBits(*bits))
        }
        (crate::matcher::SwitchKind::Binary, crate::matcher::SwitchKey::Utf8Binary(bytes)) => {
            matcher_const_eq(
                module,
                val,
                &crate::matcher::MatcherConst::Utf8Binary(bytes.clone()),
            )
        }
        (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::Nil) => val.is_nil(),
        (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::EmptyList) => {
            val.is_empty_list()
        }
        (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::Cons) => {
            val.value().ok().is_some_and(interp_is_list_cons)
        }
        _ => false,
    }
}

pub(super) fn matcher_const_eq(
    module: &Module,
    val: AnyValue,
    value: &crate::matcher::MatcherConst,
) -> bool {
    match value {
        crate::matcher::MatcherConst::Int(n) => val.as_i64() == Some(*n),
        crate::matcher::MatcherConst::FloatBits(bits) => {
            matches!(val, AnyValue::Float(f) if f.to_bits() == *bits)
        }
        crate::matcher::MatcherConst::AtomName(name) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .is_some_and(|id| val.is_atom_id(id as u32)),
        crate::matcher::MatcherConst::Bool(true) => {
            val.is_atom_id(fz_runtime::any_value::TRUE_ATOM_ID)
        }
        crate::matcher::MatcherConst::Bool(false) => val.is_false(),
        crate::matcher::MatcherConst::Nil => val.is_nil(),
        crate::matcher::MatcherConst::EmptyList => val.is_empty_list(),
        crate::matcher::MatcherConst::Utf8Binary(bytes) => val.value().ok().is_some_and(|val| {
            val.heap_object_word()
                .and_then(bitstring_like_ptr)
                .is_some_and(|p| {
                    if !unsafe { fz_runtime::procbin::is_bitstring_like(p) } {
                        return false;
                    }
                    let bit_len = unsafe { fz_runtime::procbin::bitstring_bit_len(p) };
                    if bit_len != (bytes.len() as u64) * 8 {
                        return false;
                    }
                    let ptr = unsafe { fz_runtime::procbin::bitstring_byte_ptr(p) };
                    let slice = unsafe { std::slice::from_raw_parts(ptr, bytes.len()) };
                    slice == bytes.as_slice()
                })
        }),
        crate::matcher::MatcherConst::PreparedKey(_) => false,
    }
}

pub(super) fn matcher_map_lookup(
    matcher: &crate::matcher::Matcher,
    module: &Module,
    map: AnyValue,
    key: &crate::matcher::MatcherConst,
    pinned: &HashMap<String, AnyValue>,
) -> Option<AnyValue> {
    if !map.value().ok().is_some_and(is_map_value) {
        return None;
    }
    let key = matcher_const_key_value(matcher, module, key, pinned)?;
    let ref_word = with_value_ref(map, "MatcherMapGet map", |map_ref| {
        with_value_ref(key, "MatcherMapGet key", |key_ref| {
            fz_runtime::ir_runtime::fz_matcher_map_get_ref(
                fz_runtime::process::current_process(),
                map_ref,
                key_ref,
            )
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
    matcher: &crate::matcher::Matcher,
    module: &Module,
    key: &crate::matcher::MatcherConst,
    pinned: &HashMap<String, AnyValue>,
) -> Option<AnyValue> {
    match key {
        crate::matcher::MatcherConst::Int(n) => Some(AnyValue::Int(*n)),
        crate::matcher::MatcherConst::FloatBits(bits) => {
            Some(AnyValue::Float(f64::from_bits(*bits)))
        }
        crate::matcher::MatcherConst::Bool(value) => Some(interp_bool_value(*value)),
        crate::matcher::MatcherConst::Nil => Some(interp_nil_value()),
        crate::matcher::MatcherConst::AtomName(name) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .map(|id| AnyValue::Atom(id as u32)),
        crate::matcher::MatcherConst::PreparedKey(index) => matcher
            .prepared_keys
            .get(*index as usize)
            .and_then(|_| pinned.get(&crate::matcher::prepared_key_name(*index as usize)))
            .copied(),
        _ => None,
    }
}

pub(super) fn matcher_read_bitstring(
    subject: &crate::matcher::SubjectRef,
    value: RuntimeAnyValue,
    fields: &[crate::matcher::MatcherBitField],
    state: &mut MatcherExecState,
) -> bool {
    let Some(value_bits) = value.heap_object_word() else {
        return false;
    };
    let Some(p) = bitstring_like_ptr(value_bits) else {
        return false;
    };
    if !unsafe { fz_runtime::procbin::is_bitstring_like(p) } {
        return false;
    }
    let mut reader = fz_runtime::ir_runtime::fz_bs_reader_init_ref(value.ref_word().raw_word());
    let mut size_bindings: HashMap<String, AnyValue> = HashMap::new();
    for (index, field) in fields.iter().enumerate() {
        let Some((size_present, size_value)) = matcher_bit_size_value(&field.size, &size_bindings)
        else {
            return false;
        };
        let Ok(reader_any) = interp_value_from_ref_word(reader, "bitstring matcher reader") else {
            return false;
        };
        let Ok(reader_ref) = reader_any.as_ref_word() else {
            return false;
        };
        let field_spec = fz_runtime::ir_runtime::fz_bs_field_spec(
            matcher_bit_type_tag(field.ty),
            size_present,
            field.unit.unwrap_or(default_matcher_bit_unit(field.ty)),
            matcher_endian_tag(field.endian),
            field.signed as u32,
            (index + 1 == fields.len()) as u32,
        );
        let result =
            fz_runtime::ir_runtime::fz_bs_read_field_ref(reader_ref, field_spec, size_value);
        let Ok(ok) = interp_struct_field_from_tagged_bits(result, 0, "bitstring matcher ok") else {
            return false;
        };
        if ok.is_false() || ok.is_nil() {
            return false;
        }
        let Ok(extracted) =
            interp_struct_field_from_tagged_bits(result, 8, "bitstring matcher extracted")
        else {
            return false;
        };
        let Ok(next_reader) =
            interp_struct_field_from_tagged_bits(result, 16, "bitstring matcher next reader")
        else {
            return false;
        };
        state
            .bitstring_fields
            .insert((subject.clone(), index as u32), extracted);
        for name in &field.direct_bindings {
            size_bindings.insert(name.clone(), extracted);
        }
        let Ok(next_reader_ref) = next_reader.as_ref_word() else {
            return false;
        };
        reader = next_reader_ref;
    }
    let Ok(bit_len) = interp_struct_field_from_tagged_bits(reader, 8, "bitstring matcher bit_len")
    else {
        return false;
    };
    let Ok(pos) = interp_struct_field_from_tagged_bits(reader, 16, "bitstring matcher pos") else {
        return false;
    };
    bit_len.as_i64() == pos.as_i64()
}

pub(super) fn matcher_bit_size_value(
    size: &Option<crate::matcher::MatcherBitSize>,
    bindings: &HashMap<String, AnyValue>,
) -> Option<(u32, u32)> {
    match size {
        None => Some((0, 0)),
        Some(crate::matcher::MatcherBitSize::Literal(n)) => Some((1, *n)),
        Some(crate::matcher::MatcherBitSize::BindingName(name)) => bindings
            .get(name)
            .and_then(|v| v.as_i64())
            .map(|n| (1, n as u32)),
    }
}

pub(super) fn matcher_bit_type_tag(ty: crate::matcher::MatcherBitType) -> u32 {
    match ty {
        crate::matcher::MatcherBitType::Integer => 0,
        crate::matcher::MatcherBitType::Float => 1,
        crate::matcher::MatcherBitType::Binary => 2,
        crate::matcher::MatcherBitType::Bits => 3,
        crate::matcher::MatcherBitType::Utf8 => 4,
        crate::matcher::MatcherBitType::Utf16 => 5,
        crate::matcher::MatcherBitType::Utf32 => 6,
    }
}

pub(super) fn matcher_endian_tag(endian: crate::matcher::MatcherEndian) -> u32 {
    match endian {
        crate::matcher::MatcherEndian::Big => 0,
        crate::matcher::MatcherEndian::Little => 1,
        crate::matcher::MatcherEndian::Native => 2,
    }
}

pub(super) fn default_matcher_bit_unit(ty: crate::matcher::MatcherBitType) -> u32 {
    match ty {
        crate::matcher::MatcherBitType::Integer
        | crate::matcher::MatcherBitType::Float
        | crate::matcher::MatcherBitType::Bits => 1,
        crate::matcher::MatcherBitType::Binary => 8,
        crate::matcher::MatcherBitType::Utf8
        | crate::matcher::MatcherBitType::Utf16
        | crate::matcher::MatcherBitType::Utf32 => 1,
    }
}
