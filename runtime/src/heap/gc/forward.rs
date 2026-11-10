//! Cheney forwarding: copy objects from from-space into to-space.

use super::super::Heap;
use super::super::ref_io::{is_active_from_space_object, strict_object_size};
use super::super::schema::SchemaRegistry;
use super::super::stats::GcStats;
use super::CopiedObject;
use super::forwarding::{forwarded_target, write_forwarding_marker};
use crate::any_value::{AnyValue, AnyValueRef, ValueKind};
use std::ptr::copy_nonoverlapping;

pub fn forward_any_value_ref_root(
    value: &mut AnyValueRef,
    from_ranges: &[(*mut u8, *mut u8)],
    heap: &mut Heap,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) {
    if value.is_empty_list() {
        stats.root_scalar_slots += 1;
        return;
    }
    match value.tag() {
        ValueKind::NULL => {
            stats.root_scalar_slots += 1;
        }
        tag if tag.is_scalar() => {
            stats.root_scalar_slots += 1;
            let p = value.storage_addr();
            if !is_active_from_space_object(p, from_ranges) {
                return;
            }
            let dst = copy_scalar_box_to_space(p, heap, stats);
            *value = AnyValueRef::from_scalar_slot(tag, dst as *const u64).expect("forwarded scalar root ref");
        }
        tag if tag.is_heap() => {
            stats.root_heap_edges += 1;
            let p = value.storage_addr();
            if !is_active_from_space_object(p, from_ranges) {
                return;
            }
            let new_p = cheney_forward_object(tag, p, heap, schemas, copied_objects, stats);
            *value = AnyValueRef::from_heap_object(tag, new_p).expect("forwarded heap root");
        }
        _ => unreachable!("AnyValueRef tag set is exhaustive"),
    }
}

pub fn copy_scalar_box_to_space(p: *mut u8, heap: &mut Heap, stats: &mut GcStats) -> *mut u8 {
    let dst = copy_object_to_space(p, 16, heap);
    stats.copied_objects += 1;
    stats.copied_bytes += 16;
    dst
}

/// Move the object of `kind` at `p` into to-space unless an earlier visit
/// already did, and return its to-space address.
pub fn cheney_forward_object(
    kind: ValueKind,
    p: *mut u8,
    heap: &mut Heap,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> *mut u8 {
    if let Some(forwarded) = forwarded_target(p, kind) {
        return forwarded;
    }
    let size = strict_object_size(kind, p, schemas);
    let dst = copy_object_to_space(p, size, heap);
    stats.copied_objects += 1;
    stats.copied_bytes += size as u64;
    write_forwarding_marker(p, kind, dst);
    copied_objects.push(CopiedObject { ptr: dst, kind });
    dst
}

/// Copy `size` bytes at `p` to wherever the heap's ordinary bump path places
/// them, so to-space is the tip plus the blocks it parks.
pub fn copy_object_to_space(p: *mut u8, size: usize, heap: &mut Heap) -> *mut u8 {
    let dst = heap.bump(size);
    unsafe {
        copy_nonoverlapping(p, dst, size);
    }
    dst
}

pub fn forward_heap_value(
    value: AnyValue,
    from_ranges: &[(*mut u8, *mut u8)],
    heap: &mut Heap,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> AnyValue {
    let kind = value.kind();
    let Some(p) = value.heap_addr() else {
        return value;
    };
    if !is_active_from_space_object(p, from_ranges) {
        return value;
    }
    let new = cheney_forward_object(kind, p, heap, schemas, copied_objects, stats);
    AnyValue::heap_ptr(new, kind)
}
