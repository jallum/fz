//! Tagged-ref <-> storage conversions and small helpers.

use std::ptr::{read, write};

use super::schema::SchemaRegistry;
use crate::any_value::{
    AnyValue, AnyValueRef, AnyValueRefError, EMPTY_LIST, ValueKind, heap_object_word, map_count, map_key_kind,
    map_keys_ptr, map_locate, map_node_child, map_node_child_count, map_node_entry_count, map_tag_ptr, map_value_kind,
    map_values_ptr, object_size_with_struct_payload,
};

pub(super) fn strict_object_size(kind: ValueKind, addr: *const u8, schemas: &SchemaRegistry) -> usize {
    object_size_with_struct_payload(heap_object_word(addr, kind), |schema_id| {
        schemas.get(schema_id).allocation_payload_size()
    })
}

pub(super) fn any_value_ref_from_storage(
    raw_slot: *const u64,
    kind: ValueKind,
) -> Result<AnyValueRef, AnyValueRefError> {
    let raw = unsafe { read(raw_slot) };
    match kind {
        ValueKind::NULL => Ok(AnyValueRef::null()),
        ValueKind::LIST if raw == 0 => Ok(AnyValueRef::empty_list()),
        ValueKind::ATOM => Ok(AnyValueRef::atom(raw as u32)),
        tag if tag.is_scalar() => AnyValueRef::from_scalar_slot(tag, raw_slot),
        tag => AnyValueRef::from_heap_object(tag, raw as *const u8),
    }
}

pub(super) fn write_any_value_to_storage(raw_slot: *mut u64, kind_slot: Option<*mut u8>, value: AnyValue) {
    unsafe { write(raw_slot, value.raw()) };
    if let Some(kind_slot) = kind_slot {
        unsafe { write(kind_slot, value.kind().tag()) };
    }
}

/// The key and value of entry `index` of the map at `addr`, in node order, as
/// references into the node that holds them.
///
/// # Safety
///
/// `addr` must point to the start of an initialized published Map object and
/// `index` must be in bounds for its entry count.
pub unsafe fn map_entry_refs(addr: *mut u8, index: usize) -> (AnyValueRef, AnyValueRef) {
    let (node, slot) = unsafe { map_locate(addr, index) };
    unsafe { map_slot_refs(node, slot) }
}

/// Every entry of the map at `addr` as references, in the map's own order, in
/// one walk: the cost of reading all of them by index grows with the depth of
/// a trie.
///
/// # Safety
///
/// `addr` must point to the start of an initialized published Map object.
pub unsafe fn map_entries_refs(addr: *mut u8) -> Vec<(AnyValueRef, AnyValueRef)> {
    let mut entries = Vec::with_capacity(unsafe { map_count(addr) });
    unsafe { push_node_entry_refs(addr, &mut entries) };
    entries
}

unsafe fn push_node_entry_refs(node: *mut u8, entries: &mut Vec<(AnyValueRef, AnyValueRef)>) {
    for slot in 0..unsafe { map_node_entry_count(node) } {
        entries.push(unsafe { map_slot_refs(node, slot) });
    }
    for child in 0..unsafe { map_node_child_count(node) } {
        unsafe { push_node_entry_refs(map_node_child(node, child), entries) };
    }
}

/// The key and value of entry `slot` of the node at `addr`, as references into
/// it.
///
/// # Safety
///
/// `addr` must point to the start of an initialized published Map object and
/// `slot` must be below its own entry count.
pub unsafe fn map_slot_refs(addr: *const u8, slot: usize) -> (AnyValueRef, AnyValueRef) {
    let count = unsafe { map_node_entry_count(addr) };
    assert!(slot < count, "map entry index out of bounds");
    let tag = unsafe { read(map_tag_ptr(addr).add(slot)) };
    let keys = unsafe { map_keys_ptr(addr, count) };
    let values = unsafe { map_values_ptr(addr, count) };
    let key = any_value_ref_from_storage(unsafe { keys.add(slot) }, map_key_kind(tag)).expect("map key ref");
    let value = any_value_ref_from_storage(unsafe { values.add(slot) }, map_value_kind(tag)).expect("map value ref");
    (key, value)
}

pub(super) fn reject_scalar_ref_write(context: &str, value: AnyValueRef) {
    let tag = value.tag();
    if tag.is_scalar() {
        panic!("{context} requires a heap/sentinel ref; use the typed scalar write path");
    }
}

pub(super) fn list_tail_bits_from_ref(value: AnyValueRef) -> Result<u64, AnyValueRefError> {
    match value.tag() {
        ValueKind::LIST if value.is_empty_list() => Ok(EMPTY_LIST),
        ValueKind::LIST => value.heap_object_word(),
        found => Err(AnyValueRefError::ExpectedTag {
            expected: ValueKind::LIST,
            found,
        }),
    }
}

/// `p` lies in one of the half-open ranges. The collector uses it only to
/// cross-check the literal bit in debug builds; `Heap::contains_heap_addr` asks
/// it of a heap's own blocks.
pub(super) fn ptr_in_ranges(p: *mut u8, ranges: impl IntoIterator<Item = (*mut u8, *mut u8)>) -> bool {
    ranges.into_iter().any(|(start, end)| p >= start && p < end)
}
