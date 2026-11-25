//! The measuring pass states, before a gift window opens, the bytes the copy
//! will allocate. Each test copies a value set through the production gift
//! path and holds the measurement to the segment's fill.

use super::*;
use crate::any_value::{
    AnyValue, AnyValueRef, ClosureDenotationId, EMPTY_LIST, ValueKind, closure_addr_from_tagged,
    closure_size_for_count, list_addr_from_tagged, map_addr_from_tagged, map_size_for_count, struct_size_for_payload,
};
use crate::bits::{BINREF_BYTES, BINVIEW_BYTES, SharedBinHandle, alloc_buffer_view};
use crate::heap::StubSite;
use crate::resource::{RESOURCE_STUB_SIZE, ResourceHandle, alloc_resource};
use crate::sched::gift_copy;
use std::cell::RefCell;
use std::rc::Rc;

/// A destructor word the test never dispatches: the resource only carries it.
const TEST_DESTRUCTOR: u64 = 0xD7;

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

fn struct_bytes_of(heap: &Heap, schema_id: u32) -> usize {
    struct_size_for_payload(heap.schemas.borrow().get(schema_id).allocation_payload_size())
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
fn a_tail_shared_by_two_values_is_measured_once_per_holder() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let shared_tail = int_list(&mut sender, EMPTY_LIST, 10..20);
    let first = sender.alloc_list_cons_slot(AnyValue::int(1), shared_tail);
    let second = sender.alloc_list_cons_slot(AnyValue::int(2), shared_tail);
    let bytes = measured_equals_copied(&mut sender, &[list_ref(first), list_ref(second)]);
    assert_eq!(
        bytes,
        (10 + 10 + 2) * CELL,
        "each holder carries its own ten cells and its head"
    );
}

#[test]
fn a_value_repeated_in_the_set_is_measured_each_time() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bits = int_list(&mut sender, EMPTY_LIST, 0..7);
    let bytes = measured_equals_copied(&mut sender, &[list_ref(bits), list_ref(bits)]);
    assert_eq!(bytes, 2 * 7 * CELL);
}

/// A send copies a term without preserving sharing: a list a message holds
/// twice arrives as two lists, and the measure counts both.
#[test]
fn a_list_a_message_holds_twice_arrives_as_two_copies() {
    let reg = fresh_registry();
    let pair = reg.borrow_mut().register(Schema::tuple_of_arity(2));
    let mut sender = Heap::new(SIZE_TABLE[0], reg);
    let list = int_list(&mut sender, EMPTY_LIST, 0..5);
    let list_value = heap_value(ValueKind::LIST, list_addr_from_tagged(list).expect("addr"));
    let pair_p = sender.alloc_struct(pair);
    unsafe {
        sender.write_field_slot(pair_p, 0, list_value);
        sender.write_field_slot(pair_p, 8, list_value);
    }
    let message = heap_ref(ValueKind::STRUCT, pair_p);
    let measured = measured_equals_copied(&mut sender, &[message]);
    assert_eq!(measured, struct_bytes_of(&sender, pair) + 2 * 5 * CELL);
    let (_segment, copied) = gift_copy(&mut sender, &[message]);
    let copied_pair = copied[0].storage_addr();
    let left = sender.read_field_slot(copied_pair, 0);
    let right = sender.read_field_slot(copied_pair, 8);
    assert_ne!(
        left.heap_addr(),
        right.heap_addr(),
        "each field holds a copy of its own"
    );
    assert_ne!(left.heap_addr(), list_value.heap_addr(), "neither is the sender's list");
}

#[test]
fn a_struct_whose_fields_share_one_list_measures_the_list_per_field() {
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
        pair_bytes + 2 * 5 * CELL,
        "the struct and one copy of the list for each field"
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
    assert_eq!(bytes, 3 * pair_bytes);
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
fn a_view_measures_its_view_and_its_binref_and_not_the_shared_bytes() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let stub = alloc_buffer_view(
        &mut sender,
        SharedBinHandle::from_bytes(&[7; 4096]),
        4096 * 8,
        StubSite::FilledBuffer,
    );
    let bytes = measured_equals_copied(&mut sender, &[heap_ref(ValueKind::BINVIEW, stub.as_raw())]);
    assert_eq!(bytes, BINVIEW_BYTES + BINREF_BYTES);
}

#[test]
fn a_resource_measures_its_stub_alone() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let resource = alloc_resource(&mut sender, ResourceHandle::new(0xfeed, TEST_DESTRUCTOR));
    let bytes = measured_equals_copied(&mut sender, &[heap_ref(ValueKind::RESOURCE, resource.as_raw())]);
    assert_eq!(bytes, RESOURCE_STUB_SIZE, "a copied stub carries no destructor closure");
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
    let mut sender = Heap::new(SIZE_TABLE[0], reg);
    let values = [AnyValueRef::empty_list(), AnyValueRef::null()];
    assert_eq!(measure_deep_copy(&values, &sender.view()), 0);
    let (segment, copied) = gift_copy(&mut sender, &values);
    assert_eq!(segment.block_count(), 0, "a copy that allocates nothing takes no block");
    assert_eq!(copied.as_slice(), values.as_slice(), "the values cross as they are");
}

#[test]
fn a_mixed_message_measures_what_it_copies() {
    let reg = fresh_registry();
    let pair = reg.borrow_mut().register(Schema::tuple_of_arity(2));
    let mut sender = Heap::new(SIZE_TABLE[0], reg);
    let list = int_list(&mut sender, EMPTY_LIST, 0..40);
    let list_value = heap_value(ValueKind::LIST, list_addr_from_tagged(list).expect("addr"));
    let stub = alloc_buffer_view(
        &mut sender,
        SharedBinHandle::from_bytes(&[1; 200]),
        1600,
        StubSite::FilledBuffer,
    );
    let map_bits = sender.alloc_map_slots(&[(
        AnyValue::atom(sender.node.intern_atom("k")),
        heap_value(ValueKind::BINVIEW, stub.as_raw()),
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

#[test]
fn an_atom_ref_measures_nothing_and_crosses_as_it_is() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let atoms = [AnyValueRef::atom(0), AnyValueRef::atom(41), AnyValueRef::atom(u32::MAX)];
    assert_eq!(measure_deep_copy(&atoms, &sender.view()), 0);

    let (segment, copied) = gift_copy(&mut sender, &atoms);

    assert_eq!(segment.block_count(), 0, "an atom ref needs no block");
    assert_eq!(copied.as_slice(), atoms.as_slice(), "the atoms cross as they are");
}

#[test]
fn deep_copying_an_atom_ref_to_another_heap_allocates_nothing() {
    let source = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut destination = Heap::new(SIZE_TABLE[0], fresh_registry());
    let before = destination.node.alloc_stats();

    let copy = deep_copy_any_value_ref(AnyValueRef::atom(7), &source.view(), &mut destination);

    assert_eq!(copy, AnyValueRef::atom(7));
    assert_eq!(destination.node.alloc_stats().total.allocs, before.total.allocs);
}

#[test]
fn a_pid_ref_measures_nothing_and_crosses_as_it_is() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let pids =
        [0, 41, u64::from(u32::MAX)].map(|word| sender.box_any_value_ref(AnyValue::Opaque(ValueKind::PID, word)));
    assert_eq!(measure_deep_copy(&pids, &sender.view()), 0);

    let (segment, copied) = gift_copy(&mut sender, &pids);

    assert_eq!(segment.block_count(), 0, "a pid ref needs no block");
    assert_eq!(copied.as_slice(), pids.as_slice(), "the pids cross as they are");
}

#[test]
fn deep_copying_a_pid_ref_to_another_heap_allocates_nothing() {
    let mut source = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut destination = Heap::new(SIZE_TABLE[0], fresh_registry());
    let pid = source.box_any_value_ref(AnyValue::Opaque(ValueKind::PID, 7));
    let before = destination.node.alloc_stats();

    let copy = deep_copy_any_value_ref(pid, &source.view(), &mut destination);

    assert_eq!(copy, pid);
    assert_eq!(destination.node.alloc_stats().total.allocs, before.total.allocs);
}
