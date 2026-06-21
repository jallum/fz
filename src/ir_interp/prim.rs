use super::value::{AnyValue, interp_is_list_cons, interp_nil_value, interp_value_from_ref_word, with_value_ref};
use fz_runtime::any_value::ValueKind;
use fz_runtime::ir_runtime::{
    fz_list_head_ref, fz_list_tail_ref, fz_map_get_ref, fz_map_put_atom, fz_map_put_float, fz_map_put_int,
    fz_map_put_ref,
};
use fz_runtime::process::Process;

pub(super) fn interp_list_cons(
    proc: *mut Process,
    head: AnyValue,
    tail: AnyValue,
    context: &str,
) -> Result<AnyValue, String> {
    let head = head
        .value(proc)
        .map_err(|err| format!("{context}: cannot materialize list head: {err}"))?;
    let tail = tail
        .as_any_value_ref(proc)
        .map_err(|err| format!("{context}: cannot materialize list tail: {err}"))?;
    let list = unsafe { &mut *proc }
        .heap
        .alloc_list_cons_any(head, tail)
        .map_err(|err| format!("{context}: cannot allocate list cons: {err:?}"))?;
    Ok(AnyValue::Ref(list))
}

pub(super) fn interp_map_put(
    proc: *mut Process,
    map_bits: u64,
    key: AnyValue,
    value: AnyValue,
    context: &str,
) -> Result<u64, String> {
    with_value_ref(proc, key, context, |key_ref| match value {
        AnyValue::Int(value) => Ok::<u64, String>(fz_map_put_int(proc, map_bits, key_ref, value)),
        AnyValue::Float(value) => Ok::<u64, String>(fz_map_put_float(proc, map_bits, key_ref, value)),
        AnyValue::Atom(value) => Ok::<u64, String>(fz_map_put_atom(proc, map_bits, key_ref, value as u64)),
        AnyValue::Null | AnyValue::EmptyList | AnyValue::FnRef(_) | AnyValue::Ref(_) => {
            let value_ref = value
                .as_ref_word(proc)
                .map_err(|err| format!("{context}: cannot create value ref: {err}"))?;
            Ok(fz_map_put_ref(proc, map_bits, key_ref, value_ref))
        }
    })?
}

pub(super) fn interp_list_head(proc: *mut Process, value: AnyValue) -> Result<AnyValue, String> {
    let slot = value.value(proc)?;
    if !interp_is_list_cons(slot) {
        return Err(format!("ListHead: subject is not a list cons ({:?})", slot));
    }
    with_value_ref(proc, value, "ListHead", |list_ref| fz_list_head_ref(list_ref))
        .and_then(|ref_word| interp_value_from_ref_word(ref_word, "ListHead"))
}

pub(super) fn interp_list_tail(proc: *mut Process, value: AnyValue) -> Result<AnyValue, String> {
    let slot = value.value(proc)?;
    if !interp_is_list_cons(slot) {
        return Err(format!("ListTail: subject is not a list cons ({:?})", slot));
    }
    with_value_ref(proc, value, "ListTail", |list_ref| fz_list_tail_ref(list_ref))
        .and_then(|ref_word| interp_value_from_ref_word(ref_word, "ListTail"))
}

pub(super) fn interp_map_get(proc: *mut Process, map: AnyValue, key: AnyValue) -> Result<AnyValue, String> {
    let map_slot = map.value(proc)?;
    if map_slot.kind() != ValueKind::RESOURCE
        && map_slot.kind() != ValueKind::STRUCT
        && !super::value::is_map_value(map_slot)
    {
        return Ok(interp_nil_value());
    }
    with_value_ref(proc, map, "MapGet map", |map_ref| {
        with_value_ref(proc, key, "MapGet key", |key_ref| {
            fz_map_get_ref(proc, map_ref, key_ref)
        })
    })?
    .and_then(|ref_word| interp_value_from_ref_word(ref_word, "MapGet"))
}
