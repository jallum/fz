//! The measuring pass states, before a gift window opens, the bytes the copy
//! will allocate. Each test copies a value set through the production gift
//! path and holds the measurement to the segment's fill.

use super::*;
use crate::any_value::{
    AnyValue, AnyValueRef, ClosureDenotationId, EMPTY_LIST, ValueKind, closure_addr_from_tagged,
    closure_size_for_count, list_addr_from_tagged, map_addr_from_tagged, map_size_for_count, struct_size_for_payload,
};
use crate::procbin::{PROCBIN_BYTES, SharedBinHandle, alloc_procbin};
use crate::resource::{RESOURCE_STUB_SIZE, ResourceHandle, alloc_resource, fz_resource_destructor_noop};
use crate::sched::gift_copy;
use std::cell::RefCell;
use std::rc::Rc;

const CELL: usize = 16;

fn fresh_registry() -> Rc<RefCell<SchemaRegistry>> {
    Rc::new(RefCell::new(SchemaRegistry::new()))
}

fn int_list(heap: &mut Heap, tail_bits: u64, items: std::ops::Range<i64>) -> u64 {
    items
        .rev()
        .fold(tail_bits, |tail, i| heap.alloc_list_cons_slot(AnyValue::int(i), tail))
}

fn list_ref(bits: u64) -> AnyValueRef {
    AnyValueRef::from_heap_object(ValueKind::LIST, list_addr_from_tagged(bits).expect("list addr")).expect("list ref")
}

fn struct_bytes(reg: &Rc<RefCell<SchemaRegistry>>, schema_id: u32) -> usize {
    struct_size_for_payload(reg.borrow().get(schema_id).allocation_payload_size())
}

fn heap_value(kind: ValueKind, addr: *mut u8) -> AnyValue {
    AnyValue::heap_ptr(addr, kind)
}

fn heap_ref(kind: ValueKind, addr: *mut u8) -> AnyValueRef {
    AnyValueRef::from_heap_object(kind, addr).expect("heap ref")
}

/// Measure `values`, copy them through the production gift path, and require
/// the measurement to equal what the copy wrote and the copy to occupy one
/// block. Returns the measured bytes.
fn measured_equals_copied(sender: &mut Heap, values: &[AnyValueRef]) -> usize {
    let measured = measure_deep_copy(values, &sender.view());
    let (segment, _copied) = gift_copy(sender, values);
    assert_eq!(
        measured,
        segment.fill_bytes(),
        "the measure is the bytes the copy writes"
    );
    assert_eq!(segment.block_count(), 1, "the copy fills one block");
    measured
}

#[test]
fn a_list_measures_one_cell_per_element() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bits = int_list(&mut sender, EMPTY_LIST, 0..100);
    assert_eq!(measured_equals_copied(&mut sender, &[list_ref(bits)]), 100 * CELL);
}

#[test]
fn a_list_far_larger_than_the_table_ceiling_measures_exactly() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bits = int_list(&mut sender, EMPTY_LIST, 0..500_000);
    assert_eq!(measured_equals_copied(&mut sender, &[list_ref(bits)]), 500_000 * CELL);
}

#[test]
fn a_tail_shared_by_two_values_is_measured_once() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let shared_tail = int_list(&mut sender, EMPTY_LIST, 10..20);
    let first = sender.alloc_list_cons_slot(AnyValue::int(1), shared_tail);
    let second = sender.alloc_list_cons_slot(AnyValue::int(2), shared_tail);
    let bytes = measured_equals_copied(&mut sender, &[list_ref(first), list_ref(second)]);
    assert_eq!(
        bytes,
        (10 + 2) * CELL,
        "ten shared cells and the two heads in front of them"
    );
}

#[test]
fn a_value_repeated_in_the_set_is_measured_once() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bits = int_list(&mut sender, EMPTY_LIST, 0..7);
    let bytes = measured_equals_copied(&mut sender, &[list_ref(bits), list_ref(bits)]);
    assert_eq!(bytes, 7 * CELL);
}

#[test]
fn a_struct_whose_fields_share_one_list_measures_the_list_once() {
    let reg = fresh_registry();
    let pair = reg.borrow_mut().register(Schema::tuple_of_arity(2));
    let pair_bytes = struct_bytes(&reg, pair);
    let mut sender = Heap::new(SIZE_TABLE[0], reg);
    let list = int_list(&mut sender, EMPTY_LIST, 0..5);
    let list_value = heap_value(ValueKind::LIST, list_addr_from_tagged(list).expect("addr"));
    let pair_p = sender.alloc_struct(pair);
    unsafe {
        sender.write_field_slot(pair_p, 0, list_value);
        sender.write_field_slot(pair_p, 8, list_value);
    }
    let bytes = measured_equals_copied(&mut sender, &[heap_ref(ValueKind::STRUCT, pair_p)]);
    assert_eq!(
        bytes,
        pair_bytes + 5 * CELL,
        "the struct and one copy of the shared list"
    );
}

#[test]
fn a_struct_nested_in_a_struct_is_measured_through_the_schema() {
    let reg = fresh_registry();
    let pair = reg.borrow_mut().register(Schema::tuple_of_arity(2));
    let pair_bytes = struct_bytes(&reg, pair);
    let mut sender = Heap::new(SIZE_TABLE[0], reg);
    let inner = sender.alloc_struct(pair);
    unsafe {
        sender.write_field_slot(inner, 0, AnyValue::int(1));
        sender.write_field_slot(inner, 8, AnyValue::int(2));
    }
    let outer = sender.alloc_struct(pair);
    unsafe {
        sender.write_field_slot(outer, 0, heap_value(ValueKind::STRUCT, inner));
        sender.write_field_slot(outer, 8, heap_value(ValueKind::STRUCT, inner));
    }
    let bytes = measured_equals_copied(&mut sender, &[heap_ref(ValueKind::STRUCT, outer)]);
    assert_eq!(bytes, 2 * pair_bytes);
}

#[test]
fn a_map_measures_its_entries_and_everything_they_reach() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let keys = ["a", "b"].map(|name| sender.node.intern_atom(name));
    let list = int_list(&mut sender, EMPTY_LIST, 0..3);
    let list_value = heap_value(ValueKind::LIST, list_addr_from_tagged(list).expect("addr"));
    let inner_bits = sender.alloc_map_slots(&[(AnyValue::atom(keys[0]), AnyValue::int(1))]);
    let inner = heap_value(ValueKind::MAP, map_addr_from_tagged(inner_bits).expect("inner map"));
    let outer_bits = sender.alloc_map_slots(&[(AnyValue::atom(keys[0]), list_value), (AnyValue::atom(keys[1]), inner)]);
    let outer = heap_ref(ValueKind::MAP, map_addr_from_tagged(outer_bits).expect("outer map"));
    let bytes = measured_equals_copied(&mut sender, &[outer]);
    assert_eq!(bytes, map_size_for_count(2) + map_size_for_count(1) + 3 * CELL);
}

#[test]
fn a_closure_measures_itself_and_what_it_captures() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let list = int_list(&mut sender, EMPTY_LIST, 0..4);
    let list_value = heap_value(ValueKind::LIST, list_addr_from_tagged(list).expect("addr"));
    let bits = sender.alloc_closure(
        ClosureDenotationId::user(0),
        0,
        2,
        0,
        0x1234,
        &[AnyValue::int(9), list_value],
    );
    let closure = heap_ref(ValueKind::CLOSURE, closure_addr_from_tagged(bits).expect("closure"));
    let bytes = measured_equals_copied(&mut sender, &[closure]);
    assert_eq!(bytes, closure_size_for_count(2) + 4 * CELL);
}

#[test]
fn a_procbin_stub_measures_the_stub_and_not_the_shared_bytes() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let stub = alloc_procbin(&mut sender, SharedBinHandle::from_bytes(&[7; 4096], 4096 * 8), 0);
    let bytes = measured_equals_copied(&mut sender, &[heap_ref(ValueKind::PROCBIN, stub.as_raw())]);
    assert_eq!(bytes, PROCBIN_BYTES);
}

#[test]
fn a_resource_measures_its_stub_and_its_closure() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let closure_bits = sender.alloc_closure(ClosureDenotationId::user(0), 0, 0, 0, 0x1234, &[]);
    let closure = heap_value(
        ValueKind::CLOSURE,
        closure_addr_from_tagged(closure_bits).expect("closure"),
    );
    let resource = alloc_resource(
        &mut sender,
        ResourceHandle::new(0xfeed, fz_resource_destructor_noop),
        closure,
    );
    let bytes = measured_equals_copied(&mut sender, &[heap_ref(ValueKind::RESOURCE, resource.as_raw())]);
    assert_eq!(bytes, RESOURCE_STUB_SIZE + closure_size_for_count(0));
}

#[test]
fn an_inline_bitstring_measures_its_padded_size() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let value = sender.alloc_bitstring(b"hello world", 88);
    let bytes = measured_equals_copied(
        &mut sender,
        &[heap_ref(ValueKind::BITSTRING, value.heap_addr().expect("addr"))],
    );
    assert_eq!(bytes, 32);
}

#[test]
fn a_scalar_measures_the_box_the_copy_allocates_for_it() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let slot = Box::leak(Box::new(42u64));
    let int = AnyValueRef::from_scalar_slot(ValueKind::INT, slot as *const u64).expect("int ref");
    assert_eq!(measured_equals_copied(&mut sender, &[int]), 16);
}

#[test]
fn values_the_copy_returns_as_they_are_measure_nothing() {
    let reg = fresh_registry();
    let mut sender = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut elsewhere = Heap::new(SIZE_TABLE[0], reg);
    let foreign = int_list(&mut elsewhere, EMPTY_LIST, 0..3);
    let values = [AnyValueRef::empty_list(), AnyValueRef::null(), list_ref(foreign)];
    assert_eq!(measure_deep_copy(&values, &sender.view()), 0);
    let (segment, copied) = gift_copy(&mut sender, &values);
    assert_eq!(segment.block_count(), 0, "a copy that allocates nothing takes no block");
    assert_eq!(copied, values, "the values cross as they are");
}

#[test]
fn a_mixed_message_measures_what_it_copies() {
    let reg = fresh_registry();
    let pair = reg.borrow_mut().register(Schema::tuple_of_arity(2));
    let mut sender = Heap::new(SIZE_TABLE[0], reg);
    let list = int_list(&mut sender, EMPTY_LIST, 0..40);
    let list_value = heap_value(ValueKind::LIST, list_addr_from_tagged(list).expect("addr"));
    let stub = alloc_procbin(&mut sender, SharedBinHandle::from_bytes(&[1; 200], 1600), 0);
    let map_bits = sender.alloc_map_slots(&[(
        AnyValue::atom(sender.node.intern_atom("k")),
        heap_value(ValueKind::PROCBIN, stub.as_raw()),
    )]);
    let pair_p = sender.alloc_struct(pair);
    unsafe {
        sender.write_field_slot(pair_p, 0, list_value);
        sender.write_field_slot(
            pair_p,
            8,
            heap_value(ValueKind::MAP, map_addr_from_tagged(map_bits).expect("map")),
        );
    }
    measured_equals_copied(&mut sender, &[heap_ref(ValueKind::STRUCT, pair_p), list_ref(list)]);
}
