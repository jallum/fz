//! Map-key ordering + value equality helpers.

use super::ref_io::value_ref_sort_payload;
use crate::any_value::AnyValueRef;
use crate::any_value::{AnyValue, ValueKind};
use crate::ir_runtime::cmp_bitstring;
use crate::procbin::bitstring_like_eq;
use crate::process::Node;
use std::cmp::Ordering;

pub(super) fn same_value_ref(a: AnyValueRef, b: AnyValueRef) -> bool {
    if matches!(a.tag(), ValueKind::BITSTRING | ValueKind::PROCBIN)
        && matches!(b.tag(), ValueKind::BITSTRING | ValueKind::PROCBIN)
    {
        let a_bits = a.heap_object_word().expect("bitstring lhs");
        let b_bits = b.heap_object_word().expect("bitstring rhs");
        return unsafe { bitstring_like_eq(a_bits as *const u8, b_bits as *const u8) };
    }
    a.tag() == b.tag() && value_ref_sort_payload(a) == value_ref_sort_payload(b)
}

pub(super) fn same_any_value(a: AnyValue, b: AnyValue) -> bool {
    if matches!(a.kind(), ValueKind::BITSTRING | ValueKind::PROCBIN)
        && matches!(b.kind(), ValueKind::BITSTRING | ValueKind::PROCBIN)
    {
        let ap = a.heap_object_word().expect("bitstring lhs") as *const u8;
        let bp = b.heap_object_word().expect("bitstring rhs") as *const u8;
        return unsafe { bitstring_like_eq(ap, bp) };
    }
    a.kind() == b.kind() && a.raw() == b.raw()
}

/// The `AnyValue` sibling of [`map_key_cmp_refs`], and it has to agree with it:
/// the two order the same array from different construction paths, and the
/// interpreter and the JIT each reach one of them.
pub(super) fn map_key_cmp_any(node: &Node, a: AnyValue, b: AnyValue) -> Ordering {
    let category = map_key_category_any(a).cmp(&map_key_category_any(b));
    if category != Ordering::Equal {
        return category;
    }
    if is_bitstring_like_any(a) && is_bitstring_like_any(b) {
        let ap = a.heap_object_word().expect("bitstring key lhs") as *mut u8;
        let bp = b.heap_object_word().expect("bitstring key rhs") as *mut u8;
        return cmp_bitstring(ap, bp).cmp(&0);
    }
    if a.kind() == ValueKind::ATOM && b.kind() == ValueKind::ATOM {
        return node.cmp_atom_names(a.raw() as u32, b.raw() as u32);
    }
    a.kind().tag().cmp(&b.kind().tag()).then_with(|| {
        if a.kind() == ValueKind::INT {
            (a.raw() as i64).cmp(&(b.raw() as i64))
        } else {
            a.raw().cmp(&b.raw())
        }
    })
}

fn is_bitstring_like_any(value: AnyValue) -> bool {
    matches!(value.kind(), ValueKind::BITSTRING | ValueKind::PROCBIN)
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

/// A map is a flat SORTED array, so its key ORDER has to agree with its key
/// EQUALITY -- otherwise two equal keys are not adjacent, a dedup driven by the
/// order never sees them collide, and a binary search over the array misses
/// what a linear scan finds.
///
/// Bitstrings are where the two used to disagree. `same_value_ref` compares
/// them structurally while this ordered them by `value_ref_sort_payload`, which
/// for a heap value is its ADDRESS, and it split BITSTRING from PROCBIN on the
/// tag although equal content in the two representations is the same key. So
/// `%{"ab" => 1, ("a" <> "b") => 2}` kept BOTH entries in the array and the JIT
/// door answered `1` where Elixir and the interpreter answer `2` (fz-5xp.48).
///
/// Other heap keys -- lists, tuples, maps -- are still ordered by address and
/// still compared by address, so they agree with each other but not with
/// structural equality. That is fz-5xp.27, a wider fix than this one.
pub(super) fn map_key_cmp_refs(node: &Node, a: AnyValueRef, b: AnyValueRef) -> Ordering {
    let category = map_key_category_ref(a).cmp(&map_key_category_ref(b));
    if category != Ordering::Equal {
        return category;
    }
    if is_bitstring_like_ref(a) && is_bitstring_like_ref(b) {
        return bitstring_content_cmp_refs(a, b);
    }
    if a.tag() == ValueKind::ATOM && b.tag() == ValueKind::ATOM {
        let left_id = a.load_atom().expect("atom key lhs") as u32;
        let right_id = b.load_atom().expect("atom key rhs") as u32;
        return node.cmp_atom_names(left_id, right_id);
    }
    (a.tag().tag()).cmp(&b.tag().tag()).then_with(|| {
        if a.tag() == ValueKind::INT {
            a.load_int().expect("int key").cmp(&b.load_int().expect("int key"))
        } else {
            value_ref_sort_payload(a).cmp(&value_ref_sort_payload(b))
        }
    })
}

fn is_bitstring_like_ref(value: AnyValueRef) -> bool {
    matches!(value.tag(), ValueKind::BITSTRING | ValueKind::PROCBIN)
}

fn bitstring_content_cmp_refs(a: AnyValueRef, b: AnyValueRef) -> Ordering {
    let ap = a.heap_object_word().expect("bitstring key lhs") as *mut u8;
    let bp = b.heap_object_word().expect("bitstring key rhs") as *mut u8;
    cmp_bitstring(ap, bp).cmp(&0)
}
