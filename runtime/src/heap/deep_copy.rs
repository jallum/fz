//! Deep copies between heaps and into a heap's own gift window.
//!
//! A copy reads one heap and allocates into another. The source is read
//! through a `HeapView`, an owned snapshot of the source's address ranges and
//! schema table, so a sender that copies into a gift window on its own heap
//! holds one `&mut Heap` and no second reference to the same heap.

use std::cell::RefCell;
use std::collections::HashMap;
use std::ptr::{copy_nonoverlapping, null_mut, read, write};
use std::rc::Rc;
use std::slice::from_raw_parts;

use super::ref_io::ptr_in_ranges;
use super::schema::{FieldKind, SchemaRegistry};
use super::{Heap, HeapAllocKind};
use crate::any_value::AnyValueRef;
use crate::any_value::{
    AnyValue, EMPTY_LIST, ListCons, TAG_MASK, ValueKind, bitstring_bit_len, bitstring_bytes_ptr,
    closure_addr_from_tagged, closure_arity, closure_capture_set, closure_capture_value, closure_captured_count,
    closure_fn_ptr, closure_halt_kind, list_addr_from_tagged, map_addr_from_tagged, map_count, map_entry,
    struct_field_kind_slot, struct_field_raw_slot, struct_schema_id,
};
use crate::procbin::{ProcBin, SharedBinHandle, alloc_procbin};
use crate::resource::{ResourceHandle, ResourceStub, alloc_resource};

/// What a deep copy needs to know about the heap it reads: which addresses
/// belong to it, and how its structs are laid out. Taken by value, so reading
/// a heap and allocating into a gift window on that same heap needs no second
/// reference to it.
pub struct HeapView {
    ranges: Vec<(*mut u8, *mut u8)>,
    schemas: Rc<RefCell<SchemaRegistry>>,
}

impl HeapView {
    fn contains(&self, p: *mut u8) -> bool {
        ptr_in_ranges(p, self.ranges.iter().copied())
    }

    fn read_field_slot(&self, obj: *mut u8, field_offset: u32) -> AnyValue {
        let schema_id = unsafe { struct_schema_id(obj as *const u8) };
        let schema = self.schemas.borrow();
        let kind_offset = schema.get(schema_id).value_field_kind_offset(field_offset);
        unsafe {
            let raw = read(struct_field_raw_slot(obj as *const u8, field_offset));
            let kind = read(struct_field_kind_slot(obj as *const u8, kind_offset));
            AnyValue::decode_parts(raw, kind).expect("struct field kind")
        }
    }
}

impl Heap {
    /// A snapshot of every address range this heap owns right now: the tip,
    /// the tip set aside by an open gift window, and parked blocks.
    pub fn view(&self) -> HeapView {
        HeapView {
            ranges: self.block_ranges().collect(),
            schemas: Rc::clone(&self.schemas),
        }
    }
}

pub fn deep_copy_any_value_ref(
    value: AnyValueRef,
    src_heap: &HeapView,
    dst_heap: &mut Heap,
    forwarding: &mut HashMap<*mut u8, *mut u8>,
) -> AnyValueRef {
    if value.is_empty_list() {
        return value;
    }
    match value.tag() {
        ValueKind::NULL => value,
        tag if tag.is_scalar() => {
            let src = value.storage_addr();
            let dst = dst_heap.alloc_kind(HeapAllocKind::ScalarBox, 8);
            unsafe {
                write(dst as *mut u64, read(src as *const u64));
            }
            AnyValueRef::from_scalar_slot(tag, dst as *const u64).expect("deep-copied scalar ref")
        }
        tag if tag.is_heap() => {
            let bits = value.heap_object_word().expect("heap ref bits");
            let copied = deep_copy_tagged_bits(bits, src_heap, dst_heap, forwarding);
            let addr = (copied & !TAG_MASK) as *const u8;
            AnyValueRef::from_heap_object(tag, addr).expect("deep-copied heap ref")
        }
        _ => unreachable!("AnyValueRef tag set is exhaustive"),
    }
}

pub fn deep_copy_tagged_bits(
    bits: u64,
    src_heap: &HeapView,
    dst_heap: &mut Heap,
    forwarding: &mut HashMap<*mut u8, *mut u8>,
) -> u64 {
    let copied = deep_copy_any_value(
        AnyValue::decode_tagged_heap_bits(bits).expect("deep_copy_tagged_bits expects heap bits"),
        src_heap,
        dst_heap,
        forwarding,
    );
    copied
        .heap_object_word()
        .expect("deep_copy_tagged_bits copied heap bits")
}

pub fn deep_copy_any_value(
    src: AnyValue,
    src_heap: &HeapView,
    dst_heap: &mut Heap,
    forwarding: &mut HashMap<*mut u8, *mut u8>,
) -> AnyValue {
    let Some(sp) = src.heap_addr() else {
        return src;
    };
    if sp.is_null() || !src_heap.contains(sp) {
        return src;
    }

    match src.kind() {
        ValueKind::MAP => {
            if let Some(&dp) = forwarding.get(&sp) {
                return AnyValue::heap_ptr(dp, ValueKind::MAP);
            }
            let count = unsafe { map_count(sp as *const u8) };
            forwarding.insert(sp, null_mut());
            let mut copied_entries: Vec<(AnyValue, AnyValue)> = Vec::with_capacity(count);
            for i in 0..count {
                let (key, value) = unsafe { map_entry(sp as *const u8, i) };
                let new_key = if key.kind().is_heap() {
                    deep_copy_any_value(key, src_heap, dst_heap, forwarding)
                } else {
                    key
                };
                let new_value = if value.kind().is_heap() {
                    deep_copy_any_value(value, src_heap, dst_heap, forwarding)
                } else {
                    value
                };
                copied_entries.push((new_key, new_value));
            }
            let new_bits = dst_heap.alloc_ordered_map_entries(copied_entries.into_iter());
            let new_p = map_addr_from_tagged(new_bits).expect("new map ptr");
            forwarding.insert(sp, new_p);
            AnyValue::heap_ptr(new_p, ValueKind::MAP)
        }
        ValueKind::LIST => deep_copy_list(sp, src_heap, dst_heap, forwarding),
        ValueKind::CLOSURE => deep_copy_strict_closure(sp, src_heap, dst_heap, forwarding),
        ValueKind::STRUCT => deep_copy_strict_struct(sp, src_heap, dst_heap, forwarding),
        ValueKind::BITSTRING => {
            if let Some(&dp) = forwarding.get(&sp) {
                return AnyValue::heap_ptr(dp, ValueKind::BITSTRING);
            }
            let bit_len = unsafe { bitstring_bit_len(sp as *const u8) };
            let bytes_len = (bit_len as usize).div_ceil(8);
            let bytes = unsafe { from_raw_parts(bitstring_bytes_ptr(sp as *const u8), bytes_len) };
            // The copy classifies itself: an inline bitstring stays inline
            // because it is under the threshold by construction, but nothing
            // here has to know that.
            let copied = dst_heap.alloc_bitstring(bytes, bit_len);
            forwarding.insert(sp, copied.heap_addr().expect("copied bitstring"));
            copied
        }
        ValueKind::PROCBIN => {
            if let Some(&dp) = forwarding.get(&sp) {
                return AnyValue::heap_ptr(dp, ValueKind::PROCBIN);
            }
            let src_pb = unsafe { ProcBin::from_raw(sp) };
            let handle = unsafe { SharedBinHandle::retain_from_raw(src_pb.shared_raw()) };
            // The copy views the same suffix of the same bytes.
            let new_p = alloc_procbin(dst_heap, handle, src_pb.byte_offset()).as_raw();
            forwarding.insert(sp, new_p);
            AnyValue::heap_ptr(new_p, ValueKind::PROCBIN)
        }
        ValueKind::RESOURCE => {
            if let Some(&dp) = forwarding.get(&sp) {
                return AnyValue::heap_ptr(dp, ValueKind::RESOURCE);
            }
            let src_rs = unsafe { ResourceStub::from_raw(sp) };
            let handle = unsafe { ResourceHandle::retain_from_raw(src_rs.shared_raw()) };
            forwarding.insert(sp, null_mut());
            let src_closure = src_rs.closure_value();
            let dst_closure = if src_closure.kind().is_heap() {
                deep_copy_any_value(src_closure, src_heap, dst_heap, forwarding)
            } else {
                src_closure
            };
            let new_p = alloc_resource(dst_heap, handle, dst_closure).as_raw();
            forwarding.insert(sp, new_p);
            AnyValue::heap_ptr(new_p, ValueKind::RESOURCE)
        }
        _ => src,
    }
}

/// Copy a list cell by cell along its spine, so a long list costs stack for
/// its deepest head, not for its length. The spine stops at the empty list, at
/// a cell already copied (which is then shared and published in the
/// destination), or at a tail that is not this heap's.
fn deep_copy_list(
    sp: *mut u8,
    src_heap: &HeapView,
    dst_heap: &mut Heap,
    forwarding: &mut HashMap<*mut u8, *mut u8>,
) -> AnyValue {
    if let Some(&dp) = forwarding.get(&sp) {
        return share_copied_list(dp, dst_heap);
    }
    let first = copy_list_cell(sp, src_heap, dst_heap, forwarding);
    let mut prev = first;
    let mut cur = unsafe { &*(sp as *const ListCons) }.tail_addr() as *mut u8;
    loop {
        let tail_bits = if cur.is_null() {
            EMPTY_LIST
        } else if !src_heap.contains(cur) {
            AnyValue::heap_ptr(cur, ValueKind::LIST)
                .heap_object_word()
                .expect("foreign list tail")
        } else if let Some(&dp) = forwarding.get(&cur) {
            share_copied_list(dp, dst_heap)
                .heap_object_word()
                .expect("shared list tail")
        } else {
            let next = copy_list_cell(cur, src_heap, dst_heap, forwarding);
            link_list_tail(
                prev.0,
                prev.1,
                AnyValue::heap_ptr(next.0, ValueKind::LIST)
                    .heap_object_word()
                    .expect("copied list tail"),
            );
            prev = next;
            cur = unsafe { &*(cur as *const ListCons) }.tail_addr() as *mut u8;
            continue;
        };
        link_list_tail(prev.0, prev.1, tail_bits);
        return AnyValue::heap_ptr(first.0, ValueKind::LIST);
    }
}

/// A list reached twice inside one copy is one list in the destination too;
/// the second holder makes it published there.
fn share_copied_list(dp: *mut u8, dst_heap: &mut Heap) -> AnyValue {
    let shared = AnyValueRef::from_heap_object(ValueKind::LIST, dp).expect("copied list ref");
    dst_heap
        .mark_published_ref_aliased(shared)
        .expect("receiver-owned list sharing");
    AnyValue::heap_ptr(dp, ValueKind::LIST)
}

/// Allocate the copy of one cell, copy its head, and record the forwarding.
/// The tail is written by `link_list_tail` once the caller knows it.
fn copy_list_cell(
    sp: *mut u8,
    src_heap: &HeapView,
    dst_heap: &mut Heap,
    forwarding: &mut HashMap<*mut u8, *mut u8>,
) -> (*mut u8, AnyValue) {
    let bits = dst_heap.alloc_list_cons_slot(AnyValue::nil_atom(), EMPTY_LIST);
    let dp = list_addr_from_tagged(bits).expect("new list ptr");
    forwarding.insert(sp, dp);
    let cons = unsafe { &*(sp as *const ListCons) };
    let new_head = if cons.head_kind().is_heap() {
        deep_copy_any_value(cons.head_value(), src_heap, dst_heap, forwarding)
    } else {
        cons.head_value()
    };
    dst_heap.publish_contained_parts(new_head.raw(), new_head.kind());
    (dp, new_head)
}

fn link_list_tail(dp: *mut u8, head: AnyValue, tail_bits: u64) {
    unsafe {
        write(dp as *mut ListCons, ListCons::new(head.raw(), head.kind(), tail_bits));
    }
}

fn deep_copy_strict_closure(
    sp: *mut u8,
    src_heap: &HeapView,
    dst_heap: &mut Heap,
    forwarding: &mut HashMap<*mut u8, *mut u8>,
) -> AnyValue {
    if let Some(&dp) = forwarding.get(&sp) {
        return AnyValue::heap_ptr(dp, ValueKind::CLOSURE);
    }
    let captured_count = unsafe { closure_captured_count(sp as *const u8) };
    let halt_kind = unsafe { closure_halt_kind(sp as *const u8) };
    let fn_ptr = unsafe { closure_fn_ptr(sp as *const u8) };
    let arity = unsafe { closure_arity(sp as *const u8) };
    let denotation = unsafe { crate::any_value::closure_denotation(sp) };
    let new_bits = dst_heap.alloc_closure_slots(denotation, arity, captured_count, halt_kind);
    let dp = closure_addr_from_tagged(new_bits).expect("new closure ptr");
    forwarding.insert(sp, dp);
    unsafe { write(dp.add(8) as *mut u64, fn_ptr) };
    for i in 0..captured_count {
        let cv = unsafe { closure_capture_value(sp as *const u8, i) };
        let copied = if cv.kind().is_heap() {
            deep_copy_any_value(cv, src_heap, dst_heap, forwarding)
        } else {
            cv
        };
        dst_heap.publish_contained_parts(copied.raw(), copied.kind());
        unsafe { closure_capture_set(dp as *const u8, i, copied) };
    }
    AnyValue::heap_ptr(dp, ValueKind::CLOSURE)
}

fn deep_copy_strict_struct(
    sp: *mut u8,
    src_heap: &HeapView,
    dst_heap: &mut Heap,
    forwarding: &mut HashMap<*mut u8, *mut u8>,
) -> AnyValue {
    if let Some(&dp) = forwarding.get(&sp) {
        return AnyValue::heap_ptr(dp, ValueKind::STRUCT);
    }
    let schema_id = unsafe { struct_schema_id(sp as *const u8) };
    let dp = dst_heap.alloc_struct(schema_id);
    forwarding.insert(sp, dp);
    let registry = src_heap.schemas.borrow();
    let schema = registry.get(schema_id);
    for (f, _) in schema.any_value_fields_with_kind_offsets() {
        let child = src_heap.read_field_slot(sp, f.offset);
        let copied = if child.kind().is_heap() {
            deep_copy_any_value(child, src_heap, dst_heap, forwarding)
        } else {
            child
        };
        dst_heap.publish_contained_parts(copied.raw(), copied.kind());
        unsafe { dst_heap.write_field_slot(dp, f.offset, copied) };
    }
    for f in &schema.fields {
        match f.kind {
            FieldKind::AnyValue => {}
            FieldKind::RawF64 | FieldKind::RawI64 | FieldKind::RawBytes(_) => unsafe {
                let width = match f.kind {
                    FieldKind::RawBytes(n) => n as usize,
                    _ => 8,
                };
                copy_nonoverlapping(sp.add(8 + f.offset as usize), dp.add(8 + f.offset as usize), width);
            },
        }
    }
    AnyValue::heap_ptr(dp, ValueKind::STRUCT)
}

pub fn deep_copy_slot(
    src: AnyValue,
    src_heap: &HeapView,
    dst_heap: &mut Heap,
    forwarding: &mut HashMap<*mut u8, *mut u8>,
) -> AnyValue {
    deep_copy_any_value(src, src_heap, dst_heap, forwarding)
}
