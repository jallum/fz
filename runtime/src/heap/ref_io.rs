//! Tagged-ref <-> storage conversions and small helpers.

use super::fragment::{Fragment, classify_fragment};
use super::schema::SchemaRegistry;
use crate::fz_value::{AnyValue, ValueKind};
use crate::tagged_value_ref::{
    TaggedRefPacking, TaggedValueRef, TaggedValueRefError, TaggedValueTag,
};

pub(super) fn watermark_for(block_start: *mut u8, block_size: usize) -> *mut u8 {
    let offset = (block_size * 3) / 4;
    unsafe { block_start.add(offset) }
}

pub(super) fn value_ref_addr(value: TaggedValueRef) -> *mut u8 {
    (value.raw_word() & TaggedRefPacking::current().address_mask()) as *mut u8
}

pub(super) fn value_ref_heap_bits(value: TaggedValueRef) -> u64 {
    let addr = value_ref_addr(value) as u64;
    let tag = match value.tag() {
        TaggedValueTag::List => crate::fz_value::TAG_LIST,
        TaggedValueTag::Map => crate::fz_value::TAG_MAP,
        TaggedValueTag::Struct => crate::fz_value::TAG_STRUCT,
        TaggedValueTag::Closure => crate::fz_value::TAG_CLOSURE,
        TaggedValueTag::Bitstring => crate::fz_value::TAG_BITSTRING,
        TaggedValueTag::ProcBin => crate::fz_value::TAG_PROCBIN,
        TaggedValueTag::Resource => crate::fz_value::TAG_RESOURCE,
        tag => panic!("expected heap-object ref, got {tag:?}"),
    };
    addr | tag
}

pub(in crate::heap) fn strict_object_size(bits: u64, schemas: &SchemaRegistry) -> usize {
    crate::fz_value::object_size_with_struct_payload(bits, |schema_id| {
        schemas.get(schema_id).allocation_payload_size()
    })
}

pub(super) fn tagged_ref_from_storage(
    raw_slot: *const u64,
    kind: ValueKind,
) -> Result<TaggedValueRef, TaggedValueRefError> {
    let raw = unsafe { std::ptr::read(raw_slot) };
    match tagged_ref_tag_from_value_kind(raw, kind) {
        TaggedValueTag::Null => Ok(TaggedValueRef::null()),
        TaggedValueTag::EmptyList => Ok(TaggedValueRef::empty_list()),
        tag if tag.is_scalar() => TaggedValueRef::from_scalar_slot(tag, raw_slot),
        tag => TaggedValueRef::from_heap_object(tag, raw as *const u8),
    }
}

pub(super) fn tagged_ref_tag_from_value_kind(raw: u64, kind: ValueKind) -> TaggedValueTag {
    match kind.tag() as u64 {
        crate::fz_value::TAG_NULL => TaggedValueTag::Null,
        crate::fz_value::TAG_KIND_INT => TaggedValueTag::Int,
        crate::fz_value::TAG_KIND_FLOAT => TaggedValueTag::Float,
        crate::fz_value::TAG_KIND_ATOM => TaggedValueTag::Atom,
        crate::fz_value::TAG_LIST if raw == 0 => TaggedValueTag::EmptyList,
        crate::fz_value::TAG_LIST => TaggedValueTag::List,
        crate::fz_value::TAG_MAP => TaggedValueTag::Map,
        crate::fz_value::TAG_STRUCT => TaggedValueTag::Struct,
        crate::fz_value::TAG_CLOSURE => TaggedValueTag::Closure,
        crate::fz_value::TAG_BITSTRING => TaggedValueTag::Bitstring,
        crate::fz_value::TAG_PROCBIN => TaggedValueTag::ProcBin,
        crate::fz_value::TAG_RESOURCE => TaggedValueTag::Resource,
        _ => unreachable!("unknown ValueKind"),
    }
}

pub fn any_value_from_ref(value: TaggedValueRef) -> Result<AnyValue, TaggedValueRefError> {
    Ok(match value.tag() {
        TaggedValueTag::Null => AnyValue::null(),
        TaggedValueTag::EmptyList => AnyValue::empty_list(),
        TaggedValueTag::Int => AnyValue::int(value.load_int()?),
        TaggedValueTag::Float => AnyValue::Float(value.load_float()?.to_bits()),
        TaggedValueTag::Atom => AnyValue::atom(value.load_atom()? as u32),
        tag if tag.is_heap_object() => AnyValue::HeapRef(value),
        _ => unreachable!("TaggedValueRef tag set is exhaustive"),
    })
}

pub(super) fn write_ref_to_storage(
    raw_slot: *mut u64,
    kind_slot: Option<*mut u8>,
    value: TaggedValueRef,
) {
    let raw = match value.tag() {
        TaggedValueTag::Null | TaggedValueTag::EmptyList => 0,
        TaggedValueTag::Int => value.load_int().expect("int ref") as u64,
        TaggedValueTag::Float => value.load_float().expect("float ref").to_bits(),
        TaggedValueTag::Atom => value.load_atom().expect("atom ref"),
        TaggedValueTag::List => value.list_addr().expect("list ref") as u64,
        TaggedValueTag::Map => value.map_addr().expect("map ref") as u64,
        TaggedValueTag::Struct => value.struct_addr().expect("struct ref") as u64,
        TaggedValueTag::Closure => value.closure_addr().expect("closure ref") as u64,
        TaggedValueTag::Bitstring => value.bitstring_addr().expect("bitstring ref") as u64,
        TaggedValueTag::ProcBin => value.procbin_addr().expect("procbin ref") as u64,
        TaggedValueTag::Resource => value.resource_addr().expect("resource ref") as u64,
    };
    unsafe { std::ptr::write(raw_slot, raw) };
    if let Some(kind_slot) = kind_slot {
        let kind = crate::fz_value::value_kind_from_ref_tag(value.tag()).expect("value kind");
        unsafe { std::ptr::write(kind_slot, kind.tag()) };
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

pub(super) unsafe fn map_entry_refs(
    addr: *mut u8,
    index: usize,
) -> (TaggedValueRef, TaggedValueRef) {
    let count = unsafe { crate::fz_value::map_count(addr) };
    let tag = unsafe { std::ptr::read(crate::fz_value::map_tag_ptr(addr).add(index)) };
    let keys = unsafe { crate::fz_value::map_keys_ptr(addr, count) };
    let values = unsafe { crate::fz_value::map_values_ptr(addr, count) };
    let key = tagged_ref_from_storage(
        unsafe { keys.add(index) },
        crate::fz_value::map_key_kind(tag),
    )
    .expect("map key ref");
    let value = tagged_ref_from_storage(
        unsafe { values.add(index) },
        crate::fz_value::map_value_kind(tag),
    )
    .expect("map value ref");
    (key, value)
}

pub(super) fn reject_scalar_ref_write(context: &str, value: TaggedValueRef) {
    let tag = value.tag();
    if tag.is_scalar() {
        panic!("{context} requires a heap/sentinel ref; use the typed scalar write path");
    }
}

pub(super) fn list_tail_bits_from_ref(value: TaggedValueRef) -> Result<u64, TaggedValueRefError> {
    match value.tag() {
        TaggedValueTag::EmptyList => Ok(crate::fz_value::EMPTY_LIST),
        TaggedValueTag::List => Ok(value.list_addr()? as u64 | crate::fz_value::TAG_LIST),
        found => Err(TaggedValueRefError::ExpectedTag {
            expected: TaggedValueTag::List,
            found,
        }),
    }
}

pub(super) fn value_ref_sort_payload(value: TaggedValueRef) -> u64 {
    match value.tag() {
        TaggedValueTag::Null | TaggedValueTag::EmptyList => 0,
        TaggedValueTag::Int => value.load_int().expect("int") as u64,
        TaggedValueTag::Float => value.load_float().expect("float").to_bits(),
        TaggedValueTag::Atom => value.load_atom().expect("atom"),
        TaggedValueTag::List => value.list_addr().expect("list") as u64,
        TaggedValueTag::Map => value.map_addr().expect("map") as u64,
        TaggedValueTag::Struct => value.struct_addr().expect("struct") as u64,
        TaggedValueTag::Closure => value.closure_addr().expect("closure") as u64,
        TaggedValueTag::Bitstring => value.bitstring_addr().expect("bitstring") as u64,
        TaggedValueTag::ProcBin => value.procbin_addr().expect("procbin") as u64,
        TaggedValueTag::Resource => value.resource_addr().expect("resource") as u64,
    }
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
