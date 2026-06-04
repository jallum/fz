//! Tagged-ref <-> storage conversions and small helpers.

use std::ptr::{read, write};

use super::YIELD_CONTINUATION_RESERVE_BYTES;
use super::fragment::{Fragment, classify_fragment};
use super::schema::SchemaRegistry;
use crate::any_value::{
    AnyValue, AnyValueRef, AnyValueRefError, EMPTY_LIST, ValueKind, map_count, map_key_kind, map_keys_ptr, map_tag_ptr,
    map_value_kind, map_values_ptr, object_size_with_struct_payload,
};

pub(super) fn allocation_watermark_for(block_start: *mut u8, block_size: usize) -> *mut u8 {
    assert!(
        block_size > YIELD_CONTINUATION_RESERVE_BYTES,
        "heap block must leave continuation reserve"
    );
    let offset = block_size - YIELD_CONTINUATION_RESERVE_BYTES;
    unsafe { block_start.add(offset) }
}

pub(super) fn strict_object_size(bits: u64, schemas: &SchemaRegistry) -> usize {
    object_size_with_struct_payload(bits, |schema_id| schemas.get(schema_id).allocation_payload_size())
}

pub(super) fn any_value_ref_from_storage(
    raw_slot: *const u64,
    kind: ValueKind,
) -> Result<AnyValueRef, AnyValueRefError> {
    let raw = unsafe { read(raw_slot) };
    match kind {
        ValueKind::NULL => Ok(AnyValueRef::null()),
        ValueKind::LIST if raw == 0 => Ok(AnyValueRef::empty_list()),
        tag if tag.is_scalar() => AnyValueRef::from_scalar_slot(tag, raw_slot),
        tag => AnyValueRef::from_heap_object(tag, raw as *const u8),
    }
}

pub(super) fn write_ref_to_storage(raw_slot: *mut u64, kind_slot: Option<*mut u8>, value: AnyValueRef) {
    unsafe { write(raw_slot, value.storage_raw().expect("ref storage raw")) };
    if let Some(kind_slot) = kind_slot {
        unsafe { write(kind_slot, value.tag().tag()) };
    }
}

pub(super) fn write_any_value_to_storage(raw_slot: *mut u64, kind_slot: Option<*mut u8>, value: AnyValue) {
    unsafe { write(raw_slot, value.raw()) };
    if let Some(kind_slot) = kind_slot {
        unsafe { write(kind_slot, value.kind().tag()) };
    }
}

pub(crate) unsafe fn map_entry_refs(addr: *mut u8, index: usize) -> (AnyValueRef, AnyValueRef) {
    let count = unsafe { map_count(addr) };
    let tag = unsafe { read(map_tag_ptr(addr).add(index)) };
    let keys = unsafe { map_keys_ptr(addr, count) };
    let values = unsafe { map_values_ptr(addr, count) };
    let key = any_value_ref_from_storage(unsafe { keys.add(index) }, map_key_kind(tag)).expect("map key ref");
    let value = any_value_ref_from_storage(unsafe { values.add(index) }, map_value_kind(tag)).expect("map value ref");
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

pub(super) fn value_ref_sort_payload(value: AnyValueRef) -> u64 {
    value.storage_raw().expect("ref sort payload")
}

pub(super) fn is_active_from_space_object(
    p: *mut u8,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &[Fragment],
) -> bool {
    !p.is_null() && (ptr_in_from_space(p, from_ranges) || classify_fragment(p, fragments).is_some())
}

pub(super) fn ptr_in_from_space(p: *mut u8, from_ranges: &[(*mut u8, *mut u8)]) -> bool {
    from_ranges.iter().any(|&(start, end)| p >= start && p < end)
}
