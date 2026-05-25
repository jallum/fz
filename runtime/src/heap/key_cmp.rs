//! Map-key ordering + value equality helpers.

use super::ref_io::value_ref_sort_payload;
use crate::any_value::AnyValueRef;
use crate::any_value::{AnyValue, ValueKind};

pub(super) fn same_value_ref(a: AnyValueRef, b: AnyValueRef) -> bool {
    if matches!(a.tag(), ValueKind::BITSTRING | ValueKind::PROCBIN)
        && matches!(b.tag(), ValueKind::BITSTRING | ValueKind::PROCBIN)
    {
        let a_bits = a.heap_object_word().expect("bitstring lhs");
        let b_bits = b.heap_object_word().expect("bitstring rhs");
        return unsafe {
            crate::procbin::bitstring_like_eq(a_bits as *const u8, b_bits as *const u8)
        };
    }
    a.tag() == b.tag() && value_ref_sort_payload(a) == value_ref_sort_payload(b)
}

pub(super) fn same_any_value(a: AnyValue, b: AnyValue) -> bool {
    if matches!(a.kind(), ValueKind::BITSTRING | ValueKind::PROCBIN)
        && matches!(b.kind(), ValueKind::BITSTRING | ValueKind::PROCBIN)
    {
        let ap = a.heap_object_word().expect("bitstring lhs") as *const u8;
        let bp = b.heap_object_word().expect("bitstring rhs") as *const u8;
        return unsafe { crate::procbin::bitstring_like_eq(ap, bp) };
    }
    a.kind() == b.kind() && a.raw() == b.raw()
}

pub(super) fn map_key_cmp_any(a: AnyValue, b: AnyValue) -> std::cmp::Ordering {
    map_key_category_any(a)
        .cmp(&map_key_category_any(b))
        .then_with(|| a.kind().tag().cmp(&b.kind().tag()))
        .then_with(|| {
            if a.kind() == ValueKind::INT {
                (a.raw() as i64).cmp(&(b.raw() as i64))
            } else {
                a.raw().cmp(&b.raw())
            }
        })
}

pub(super) fn map_key_category_any(value: AnyValue) -> u8 {
    match value.kind() {
        ValueKind::INT => 0,
        ValueKind::ATOM => 1,
        ValueKind::NULL => 2,
        kind if kind.is_heap() => 3,
        ValueKind::FLOAT => 4,
        _ => 5,
    }
}

pub(super) fn map_key_category_ref(value: AnyValueRef) -> u8 {
    match value.tag() {
        ValueKind::INT => 0,
        ValueKind::ATOM => 1,
        ValueKind::NULL => 2,
        ValueKind::FLOAT => 4,
        _ => 3,
    }
}

pub(super) fn map_key_cmp_refs(a: AnyValueRef, b: AnyValueRef) -> std::cmp::Ordering {
    map_key_category_ref(a)
        .cmp(&map_key_category_ref(b))
        .then_with(|| (a.tag().tag()).cmp(&b.tag().tag()))
        .then_with(|| {
            if a.tag() == ValueKind::INT {
                a.load_int()
                    .expect("int key")
                    .cmp(&b.load_int().expect("int key"))
            } else {
                value_ref_sort_payload(a).cmp(&value_ref_sort_payload(b))
            }
        })
}
