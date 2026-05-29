//! Tagged-ref <-> storage conversions and small helpers.

use super::fragment::{Fragment, classify_fragment};
use super::schema::SchemaRegistry;
use crate::any_value::{AnyValue, ValueKind};
use crate::any_value::{AnyValueRef, AnyValueRefError};

pub(super) fn allocation_watermark_for(block_start: *mut u8, block_size: usize) -> *mut u8 {
    assert!(
        block_size > super::YIELD_CONTINUATION_RESERVE_BYTES,
        "heap block must leave continuation reserve"
    );
    let offset = block_size - super::YIELD_CONTINUATION_RESERVE_BYTES;
    unsafe { block_start.add(offset) }
}

pub(super) fn strict_object_size(bits: u64, schemas: &SchemaRegistry) -> usize {
    crate::any_value::object_size_with_struct_payload(bits, |schema_id| {
        schemas.get(schema_id).allocation_payload_size()
    })
}

pub(super) fn any_value_ref_from_storage(
    raw_slot: *const u64,
    kind: ValueKind,
) -> Result<AnyValueRef, AnyValueRefError> {
    let raw = unsafe { std::ptr::read(raw_slot) };
    match kind {
        ValueKind::NULL => Ok(AnyValueRef::null()),
        ValueKind::LIST if raw == 0 => Ok(AnyValueRef::empty_list()),
        tag if tag.is_scalar() => AnyValueRef::from_scalar_slot(tag, raw_slot),
        tag => AnyValueRef::from_heap_object(tag, raw as *const u8),
    }
}

pub(super) fn write_ref_to_storage(
    raw_slot: *mut u64,
    kind_slot: Option<*mut u8>,
    value: AnyValueRef,
) {
    unsafe { std::ptr::write(raw_slot, value.storage_raw().expect("ref storage raw")) };
    if let Some(kind_slot) = kind_slot {
        unsafe { std::ptr::write(kind_slot, value.tag().tag()) };
    }
}

pub(super) fn write_any_value_to_storage(
    raw_slot: *mut u64,
    kind_slot: Option<*mut u8>,
    value: AnyValue,
) {
    unsafe { std::ptr::write(raw_slot, value.raw()) };
    if let Some(kind_slot) = kind_slot {
        unsafe { std::ptr::write(kind_slot, value.kind().tag()) };
    }
}

pub(super) unsafe fn map_entry_refs(addr: *mut u8, index: usize) -> (AnyValueRef, AnyValueRef) {
    let count = unsafe { crate::any_value::map_count(addr) };
    let tag = unsafe { std::ptr::read(crate::any_value::map_tag_ptr(addr).add(index)) };
    let keys = unsafe { crate::any_value::map_keys_ptr(addr, count) };
    let values = unsafe { crate::any_value::map_values_ptr(addr, count) };
    let key = any_value_ref_from_storage(
        unsafe { keys.add(index) },
        crate::any_value::map_key_kind(tag),
    )
    .expect("map key ref");
    let value = any_value_ref_from_storage(
        unsafe { values.add(index) },
        crate::any_value::map_value_kind(tag),
    )
    .expect("map value ref");
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
        ValueKind::LIST if value.is_empty_list() => Ok(crate::any_value::EMPTY_LIST),
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
    from_ranges
        .iter()
        .any(|&(start, end)| p >= start && p < end)
}
