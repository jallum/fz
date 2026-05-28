//! Cheney tracing: scan each copied object and forward its child edges.

use super::super::fragment::{CopiedObject, Fragment};
use super::super::schema::SchemaRegistry;
use super::super::stats::GcStats;
use super::forward::forward_heap_value;
use crate::any_value::{AnyValue, ListCons, ValueKind};

pub fn cheney_trace_list(
    obj: *mut ListCons,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) {
    let cons = unsafe { &mut *obj };
    if cons.head_kind().is_heap() {
        stats.list_head_heap_edges += 1;
        let head = forward_heap_value(
            cons.head_value(),
            from_ranges,
            fragments,
            frag_queue,
            free,
            to_end,
            schemas,
            copied_objects,
            stats,
        );
        cons.head = head.raw();
    } else {
        stats.list_head_scalar_slots += 1;
    }

    let tail_addr = cons.tail_addr();
    if tail_addr != 0 {
        stats.list_tail_edges += 1;
        let tail = forward_heap_value(
            AnyValue::heap_ptr(tail_addr as *mut u8, ValueKind::LIST),
            from_ranges,
            fragments,
            frag_queue,
            free,
            to_end,
            schemas,
            copied_objects,
            stats,
        );
        cons.set_tail_bits(tail.heap_object_word().expect("forwarded list tail"));
    }
}

#[allow(clippy::too_many_arguments)]
pub fn cheney_trace_struct(
    obj: *mut u8,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) {
    let schema_id = unsafe { crate::any_value::struct_schema_id(obj as *const u8) };
    let schema = schemas.get(schema_id);
    for (field, kind_offset) in schema.any_value_fields_with_kind_offsets() {
        let value = unsafe {
            let raw = std::ptr::read(crate::any_value::struct_field_raw_slot(
                obj as *const u8,
                field.offset,
            ));
            let kind = std::ptr::read(crate::any_value::struct_field_kind_slot(
                obj as *const u8,
                kind_offset,
            ));
            AnyValue::decode_parts(raw, kind).expect("struct field kind")
        };
        if value.kind().is_heap() {
            stats.struct_heap_edges += 1;
            let forwarded = forward_heap_value(
                value,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                schemas,
                copied_objects,
                stats,
            );
            let raw = forwarded.raw() & !crate::any_value::TAG_MASK;
            unsafe {
                std::ptr::write(
                    crate::any_value::struct_field_raw_slot(obj as *const u8, field.offset),
                    raw,
                );
                std::ptr::write(
                    crate::any_value::struct_field_kind_slot(obj as *const u8, kind_offset),
                    forwarded.kind().tag(),
                );
            }
        } else {
            stats.struct_scalar_slots += 1;
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub fn cheney_trace_resource(
    obj: *mut u8,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) {
    let resource = unsafe { crate::resource::ResourceStub::from_raw(obj) };
    let closure = resource.closure_value();
    if closure.kind().is_heap() {
        stats.resource_heap_edges += 1;
        let forwarded = forward_heap_value(
            closure,
            from_ranges,
            fragments,
            frag_queue,
            free,
            to_end,
            schemas,
            copied_objects,
            stats,
        );
        resource.closure_value_set(forwarded);
    } else {
        stats.resource_scalar_slots += 1;
    }
}

#[allow(clippy::too_many_arguments)]
pub fn cheney_trace_map(
    obj: *mut u8,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) {
    let count = unsafe { crate::any_value::map_count(obj as *const u8) };
    let tags = unsafe { crate::any_value::map_tag_ptr(obj as *const u8) };
    let keys = unsafe { crate::any_value::map_keys_ptr(obj as *const u8, count) };
    let values = unsafe { crate::any_value::map_values_ptr(obj as *const u8, count) };
    for i in 0..count {
        let tag = unsafe { std::ptr::read(tags.add(i)) };
        let key_kind = crate::any_value::map_key_kind(tag);
        if key_kind.is_heap() {
            stats.map_heap_edges += 1;
            let key =
                AnyValue::heap_ptr(unsafe { std::ptr::read(keys.add(i)) } as *mut u8, key_kind);
            let forwarded = forward_heap_value(
                key,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                schemas,
                copied_objects,
                stats,
            );
            unsafe { std::ptr::write(keys.add(i), forwarded.raw()) };
        } else {
            stats.map_scalar_slots += 1;
        }
        let value_kind = crate::any_value::map_value_kind(tag);
        if value_kind.is_heap() {
            stats.map_heap_edges += 1;
            let value = AnyValue::heap_ptr(
                unsafe { std::ptr::read(values.add(i)) } as *mut u8,
                value_kind,
            );
            let forwarded = forward_heap_value(
                value,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                schemas,
                copied_objects,
                stats,
            );
            unsafe { std::ptr::write(values.add(i), forwarded.raw()) };
        } else {
            stats.map_scalar_slots += 1;
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub fn cheney_trace_closure(
    obj: *mut u8,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) {
    let captured_count = unsafe { crate::any_value::closure_captured_count(obj as *const u8) };
    for idx in 0..captured_count {
        let value = unsafe { crate::any_value::closure_capture_value(obj as *const u8, idx) };
        if value.kind().is_heap() {
            stats.closure_heap_edges += 1;
            let forwarded = forward_heap_value(
                value,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                schemas,
                copied_objects,
                stats,
            );
            unsafe { crate::any_value::closure_capture_set(obj as *const u8, idx, forwarded) };
        } else {
            stats.closure_scalar_slots += 1;
        }
    }
}
