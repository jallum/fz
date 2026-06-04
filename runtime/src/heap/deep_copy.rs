//! Cross-heap deep copies (mailbox send, message dup).

use std::collections::HashMap;
use std::ptr::{copy_nonoverlapping, null_mut, read, write};
use std::slice::from_raw_parts;

use super::schema::FieldKind;
use super::{Heap, HeapAllocKind};
use crate::any_value::AnyValueRef;
use crate::any_value::{
    AnyValue, EMPTY_LIST, ListCons, TAG_MASK, ValueKind, bitstring_bit_len, bitstring_bytes_ptr,
    closure_addr_from_tagged, closure_capture_set, closure_capture_value, closure_captured_count, closure_fn_ptr,
    closure_halt_kind, list_addr_from_tagged, map_addr_from_tagged, map_count, map_entry, struct_schema_id,
};
use crate::procbin::{ProcBin, SharedBinHandle, alloc_procbin};
use crate::resource::{ResourceHandle, ResourceStub, alloc_resource};

pub fn deep_copy_any_value_ref(
    value: AnyValueRef,
    src_heap: &Heap,
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
    src_heap: &Heap,
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
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut HashMap<*mut u8, *mut u8>,
) -> AnyValue {
    let Some(sp) = src.heap_addr() else {
        return src;
    };
    if sp.is_null() || !src_heap.contains_heap_addr(sp) {
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
            let new_bits = dst_heap.alloc_map_slots(&copied_entries);
            let new_p = map_addr_from_tagged(new_bits).expect("new map ptr");
            forwarding.insert(sp, new_p);
            AnyValue::heap_ptr(new_p, ValueKind::MAP)
        }
        ValueKind::LIST => {
            if let Some(&dp) = forwarding.get(&sp) {
                return AnyValue::heap_ptr(dp, ValueKind::LIST);
            }
            let bits = dst_heap.alloc_list_cons_slot(AnyValue::nil_atom(), EMPTY_LIST);
            let dp = list_addr_from_tagged(bits).expect("new list ptr");
            forwarding.insert(sp, dp);
            let cons = unsafe { &*(sp as *const ListCons) };
            let new_head = if cons.head_kind().is_heap() {
                deep_copy_any_value(cons.head_value(), src_heap, dst_heap, forwarding)
            } else {
                cons.head_value()
            };
            let new_tail = if cons.tail_addr() == 0 {
                AnyValue::empty_list()
            } else {
                deep_copy_any_value(
                    AnyValue::heap_ptr(cons.tail_addr() as *mut u8, ValueKind::LIST),
                    src_heap,
                    dst_heap,
                    forwarding,
                )
            };
            unsafe {
                write(
                    dp as *mut ListCons,
                    ListCons::new(
                        new_head.raw(),
                        new_head.kind(),
                        if new_tail.kind() == ValueKind::LIST && new_tail.raw() == 0 {
                            EMPTY_LIST
                        } else {
                            new_tail.heap_object_word().expect("list tail")
                        },
                    ),
                );
            }
            AnyValue::heap_ptr(dp, ValueKind::LIST)
        }
        ValueKind::CLOSURE => deep_copy_strict_closure(sp, src_heap, dst_heap, forwarding),
        ValueKind::STRUCT => deep_copy_strict_struct(sp, src_heap, dst_heap, forwarding),
        ValueKind::BITSTRING => {
            if let Some(&dp) = forwarding.get(&sp) {
                return AnyValue::heap_ptr(dp, ValueKind::BITSTRING);
            }
            let bit_len = unsafe { bitstring_bit_len(sp as *const u8) };
            let bytes_len = (bit_len as usize).div_ceil(8);
            let bytes = unsafe { from_raw_parts(bitstring_bytes_ptr(sp as *const u8), bytes_len) };
            let new_p = dst_heap.alloc_bitstring(bytes, bit_len);
            forwarding.insert(sp, new_p);
            AnyValue::heap_ptr(new_p, ValueKind::BITSTRING)
        }
        ValueKind::PROCBIN => {
            if let Some(&dp) = forwarding.get(&sp) {
                return AnyValue::heap_ptr(dp, ValueKind::PROCBIN);
            }
            let src_pb = unsafe { ProcBin::from_raw(sp) };
            let handle = unsafe { SharedBinHandle::retain_from_raw(src_pb.shared_raw()) };
            let new_p = alloc_procbin(dst_heap, handle).as_raw();
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

fn deep_copy_strict_closure(
    sp: *mut u8,
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut HashMap<*mut u8, *mut u8>,
) -> AnyValue {
    if let Some(&dp) = forwarding.get(&sp) {
        return AnyValue::heap_ptr(dp, ValueKind::CLOSURE);
    }
    let captured_count = unsafe { closure_captured_count(sp as *const u8) };
    let halt_kind = unsafe { closure_halt_kind(sp as *const u8) };
    let fn_ptr = unsafe { closure_fn_ptr(sp as *const u8) };
    let new_bits = dst_heap.alloc_closure_slots(0, captured_count, halt_kind);
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
        unsafe { closure_capture_set(dp as *const u8, i, copied) };
    }
    AnyValue::heap_ptr(dp, ValueKind::CLOSURE)
}

fn deep_copy_strict_struct(
    sp: *mut u8,
    src_heap: &Heap,
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
        dst_heap.write_field_slot(dp, f.offset, copied);
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
    src_heap: &Heap,
    dst_heap: &mut Heap,
    forwarding: &mut HashMap<*mut u8, *mut u8>,
) -> AnyValue {
    deep_copy_any_value(src, src_heap, dst_heap, forwarding)
}
