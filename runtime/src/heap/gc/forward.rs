//! Cheney forwarding: copy objects from from-space into to-space.

use super::super::fragment::{CopiedObject, Fragment, classify_fragment, mark_fragment_for_tracing};
use super::super::ref_io::{
    is_active_from_space_object, ptr_in_from_space, value_ref_addr, value_ref_heap_bits,
};
use super::super::schema::SchemaRegistry;
use super::super::stats::GcStats;
use super::forwarding::{
    is_forwarded_headerless, is_forwarded_list, is_forwarded_procbin, is_forwarded_resource,
    write_forwarding_marker,
};
use crate::fz_value::ValueKind;
use crate::tagged_value_ref::{TaggedValueRef, TaggedValueTag};

pub(in crate::heap) fn cheney_forward_strict_bits(
    bits: u64,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> Option<u64> {
    let kind = crate::fz_value::heap_kind_from_tagged(bits)?;
    let addr = bits & !crate::fz_value::TAG_MASK;
    if addr == 0 {
        return None;
    }
    let p = addr as *mut u8;
    let in_block = ptr_in_from_space(p, from_ranges);
    let in_frag = classify_fragment(p, fragments).is_some();
    if !in_block && !in_frag {
        return None;
    }
    let new_p = cheney_forward_object(
        kind,
        bits,
        p,
        fragments,
        frag_queue,
        free,
        to_end,
        schemas,
        copied_objects,
        stats,
    );
    Some((new_p as u64) | kind.tag() as u64)
}

#[allow(clippy::too_many_arguments)]
pub(in crate::heap) fn forward_tagged_ref_root(
    value: &mut TaggedValueRef,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) {
    match value.tag() {
        TaggedValueTag::Null | TaggedValueTag::EmptyList => {
            stats.root_scalar_slots += 1;
        }
        tag if tag.is_scalar() => {
            stats.root_scalar_slots += 1;
            let p = value_ref_addr(*value);
            if !is_active_from_space_object(p, from_ranges, fragments) {
                return;
            }
            let dst = copy_scalar_box_to_space(p, free, to_end, stats);
            *value = TaggedValueRef::from_scalar_slot(tag, dst as *const u64)
                .expect("forwarded scalar root ref");
        }
        tag if tag.is_heap_object() => {
            stats.root_heap_edges += 1;
            let bits = value_ref_heap_bits(*value);
            if let Some(new_bits) = cheney_forward_strict_bits(
                bits,
                from_ranges,
                fragments,
                frag_queue,
                free,
                to_end,
                schemas,
                copied_objects,
                stats,
            ) {
                let new_addr = (new_bits & !crate::fz_value::TAG_MASK) as *const u8;
                *value =
                    TaggedValueRef::from_heap_object(tag, new_addr).expect("forwarded heap root");
            }
        }
        _ => unreachable!("TaggedValueRef tag set is exhaustive"),
    }
}

pub(in crate::heap) fn copy_scalar_box_to_space(
    p: *mut u8,
    free: &mut *mut u8,
    to_end: *mut u8,
    stats: &mut GcStats,
) -> *mut u8 {
    let dst = copy_object_to_space(p, 16, free, to_end);
    stats.copied_objects += 1;
    stats.copied_bytes += 16;
    dst
}

pub(in crate::heap) fn cheney_forward_object(
    kind: ValueKind,
    bits: u64,
    p: *mut u8,
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> *mut u8 {
    match kind {
        ValueKind::LIST => cheney_forward_list(
            p,
            fragments,
            frag_queue,
            free,
            to_end,
            copied_objects,
            stats,
        ),
        ValueKind::PROCBIN => cheney_forward_procbin(
            p,
            fragments,
            frag_queue,
            free,
            to_end,
            copied_objects,
            stats,
        ),
        ValueKind::RESOURCE => cheney_forward_resource(
            p,
            fragments,
            frag_queue,
            free,
            to_end,
            copied_objects,
            stats,
        ),
        kind if kind.is_heap() => cheney_forward_headerless(
            p,
            kind.tag() as u64,
            bits,
            schemas,
            fragments,
            frag_queue,
            free,
            to_end,
            copied_objects,
            stats,
        ),
        _ => unreachable!("Cheney forwarding requires a heap kind"),
    }
}

pub(in crate::heap) fn cheney_forward_list(
    p: *mut u8,
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> *mut u8 {
    if mark_fragment_for_tracing(p, crate::fz_value::TAG_LIST, fragments, frag_queue) {
        return p;
    }
    if let Some(fwd) = is_forwarded_list(p) {
        return fwd as *mut u8;
    }
    copy_to_space_with_confirmed_forwarding(
        p,
        16,
        crate::fz_value::TAG_LIST,
        free,
        to_end,
        copied_objects,
        stats,
    )
}

pub(in crate::heap) fn cheney_forward_headerless(
    p: *mut u8,
    tag: u64,
    bits: u64,
    schemas: &SchemaRegistry,
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> *mut u8 {
    if mark_fragment_for_tracing(p, tag, fragments, frag_queue) {
        return p;
    }
    if let Some(fwd) = is_forwarded_headerless(p) {
        return fwd as *mut u8;
    }
    let size = strict_object_size(bits, schemas);
    copy_to_space_with_confirmed_forwarding(p, size, tag, free, to_end, copied_objects, stats)
}

pub(in crate::heap) fn cheney_forward_procbin(
    p: *mut u8,
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> *mut u8 {
    if mark_fragment_for_tracing(p, crate::fz_value::TAG_PROCBIN, fragments, frag_queue) {
        return p;
    }
    if let Some(fwd) = is_forwarded_procbin(p) {
        return fwd as *mut u8;
    }
    copy_to_space_with_first_word_forwarding(
        p,
        16,
        crate::fz_value::TAG_PROCBIN,
        free,
        to_end,
        copied_objects,
        stats,
    )
}

pub(in crate::heap) fn cheney_forward_resource(
    p: *mut u8,
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> *mut u8 {
    if mark_fragment_for_tracing(p, crate::fz_value::TAG_RESOURCE, fragments, frag_queue) {
        return p;
    }
    if let Some(fwd) = is_forwarded_resource(p) {
        return fwd as *mut u8;
    }
    copy_to_space_with_first_word_forwarding(
        p,
        32,
        crate::fz_value::TAG_RESOURCE,
        free,
        to_end,
        copied_objects,
        stats,
    )
}

pub(in crate::heap) fn copy_to_space_with_confirmed_forwarding(
    p: *mut u8,
    size: usize,
    tag: u64,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> *mut u8 {
    let dst = copy_object_to_space(p, size, free, to_end);
    stats.copied_objects += 1;
    stats.copied_bytes += size as u64;
    write_forwarding_marker(p, dst);
    unsafe {
        std::ptr::write(p.add(8) as *mut u64, crate::fz_value::TAG_FWD);
    }
    copied_objects.push(CopiedObject { ptr: dst, tag });
    dst
}

pub(in crate::heap) fn copy_to_space_with_first_word_forwarding(
    p: *mut u8,
    size: usize,
    tag: u64,
    free: &mut *mut u8,
    to_end: *mut u8,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> *mut u8 {
    let dst = copy_object_to_space(p, size, free, to_end);
    stats.copied_objects += 1;
    stats.copied_bytes += size as u64;
    write_forwarding_marker(p, dst);
    copied_objects.push(CopiedObject { ptr: dst, tag });
    dst
}

pub(in crate::heap) fn copy_object_to_space(p: *mut u8, size: usize, free: &mut *mut u8, to_end: *mut u8) -> *mut u8 {
    let dst = *free;
    let new_top = unsafe { dst.add(size) };
    assert!(new_top <= to_end, "Cheney: to-space exhausted");
    unsafe {
        std::ptr::copy_nonoverlapping(p, dst, size);
    }
    *free = new_top;
    dst
}

pub(in crate::heap) fn forward_heap_value(
    value: AnyValue,
    from_ranges: &[(*mut u8, *mut u8)],
    fragments: &mut [Fragment],
    frag_queue: &mut Vec<CopiedObject>,
    free: &mut *mut u8,
    to_end: *mut u8,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) -> AnyValue {
    let kind = value.kind();
    let Some(p) = value.heap_addr() else {
        return value;
    };
    if !is_active_from_space_object(p, from_ranges, fragments) {
        return value;
    }
    let new = cheney_forward_object(
        kind,
        value.heap_object_word().expect("heap object word"),
        p,
        fragments,
        frag_queue,
        free,
        to_end,
        schemas,
        copied_objects,
        stats,
    );
    AnyValue::heap_ptr(new, kind)
}
