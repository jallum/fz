//! A field destination names one open field of a cell: its word, the fill
//! that closes it, and the refusals that keep an open field from being read
//! as a value.

use super::*;
use crate::any_value::{
    AnyValue, AnyValueRef, AnyValueRefPacking, ListCons, ListTail, MAP_FLAT_MAX, Stored, ValueKind,
    closure_addr_from_tagged, closure_capture_value, list_addr_from_tagged, map_entry,
};
use crate::heap::{SIZE_TABLE, SchemaRegistry, deep_copy_any_value_ref, measure_deep_copy};
use crate::term::{NumericMode, TermComparator};
use crate::term_hash::TermHasher;
use std::cell::RefCell;
use std::rc::Rc;

fn fresh_registry() -> Rc<RefCell<SchemaRegistry>> {
    Rc::new(RefCell::new(SchemaRegistry::new()))
}

fn heap_with_pair() -> (Heap, u32) {
    let registry = fresh_registry();
    let pair = registry.borrow_mut().tuple(2);
    (Heap::new(SIZE_TABLE[0], registry), pair)
}

/// A pair whose second field is open, and the destination naming it.
fn pair_with_open_second(heap: &mut Heap, pair: u32) -> (*mut u8, FieldDestination) {
    let object = heap.alloc_struct(pair);
    unsafe {
        heap.store_struct_field(object, 8, 24, AnyValue::int(1))
            .expect("first field");
        let dest = heap.open_struct_field(object, 1);
        (object, dest)
    }
}

/// A one-entry map whose value is open, and the destination naming it.
fn map_with_open_value(heap: &mut Heap) -> (*mut u8, FieldDestination) {
    let bits = heap.alloc_map_slots(&[(AnyValue::int(1), AnyValue::int(0))]);
    let node = crate::any_value::map_addr_from_tagged(bits).expect("map");
    let dest = unsafe { heap.open_map_value(node, 0) };
    (node, dest)
}

fn list_ref(bits: u64) -> AnyValue {
    AnyValue::heap_ptr(list_addr_from_tagged(bits).expect("list"), ValueKind::LIST)
}

#[test]
fn the_selector_space_is_exactly_the_list_tail_the_struct_fields_and_the_map_slots() {
    let space = 1usize << (64 - AnyValueRefPacking::current().tag_shift());
    assert_eq!(
        1 + FieldDestination::STRUCT_FIELD_LIMIT + FieldDestination::MAP_SLOT_LIMIT,
        space
    );
    assert_eq!(FieldDestination::MAP_SLOT_LIMIT, MAP_FLAT_MAX);
}

#[test]
fn a_field_ordinal_fits_below_its_limit_and_not_at_it() {
    let (fields, slots) = (FieldDestination::STRUCT_FIELD_LIMIT, FieldDestination::MAP_SLOT_LIMIT);
    assert!(FieldDestination::fits(Layout::ListTail));
    assert!(FieldDestination::fits(Layout::StructField(0)));
    assert!(FieldDestination::fits(Layout::StructField(fields - 1)));
    assert!(!FieldDestination::fits(Layout::StructField(fields)));
    assert!(FieldDestination::fits(Layout::MapValue(0)));
    assert!(FieldDestination::fits(Layout::MapValue(slots - 1)));
    assert!(!FieldDestination::fits(Layout::MapValue(slots)));
}

#[test]
#[should_panic(expected = "does not fit a destination")]
fn naming_a_field_past_the_limit_is_refused() {
    FieldDestination::new(
        0x1000 as *mut u8,
        Layout::StructField(FieldDestination::STRUCT_FIELD_LIMIT),
    );
}

#[test]
fn a_destination_word_round_trips_its_cell_and_layout_at_the_edges_of_each_range() {
    let cell = 0x7f00_1234_5670usize as *mut u8;
    for layout in [
        Layout::ListTail,
        Layout::StructField(0),
        Layout::StructField(FieldDestination::STRUCT_FIELD_LIMIT - 1),
        Layout::MapValue(0),
        Layout::MapValue(FieldDestination::MAP_SLOT_LIMIT - 1),
    ] {
        let dest = FieldDestination::new(cell, layout);
        let again = FieldDestination::from_word(dest.word());
        assert_eq!(again, dest);
        assert_eq!(again.cell_addr(), cell);
        assert_eq!(again.layout(), layout);
    }
}

#[test]
fn a_destination_moved_to_another_cell_keeps_its_layout() {
    let dest = FieldDestination::new(0x1000 as *mut u8, Layout::StructField(3));
    let moved = dest.rebased(0x2000 as *mut u8);
    assert_eq!(moved.cell_addr(), 0x2000 as *mut u8);
    assert_eq!(moved.layout(), Layout::StructField(3));
}

#[test]
fn each_layout_names_the_kind_of_cell_it_lives_in() {
    assert_eq!(Layout::ListTail.cell_kind(), ValueKind::LIST);
    assert_eq!(Layout::StructField(0).cell_kind(), ValueKind::STRUCT);
    assert_eq!(Layout::MapValue(0).cell_kind(), ValueKind::MAP);
}

#[test]
fn a_list_hole_closes_with_a_list_and_keeps_the_head_kind_and_the_shared_mark() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let (cell, dest) = heap.alloc_open_list_cell(AnyValue::int(7));
    assert!(heap.destination_is_open(dest));
    let cons = unsafe { &mut *(cell.list_addr().unwrap() as *mut ListCons) };
    cons.mark_aliased();
    let rest = list_ref(heap.alloc_list_cons_slot(AnyValue::int(8), crate::any_value::EMPTY_LIST));
    heap.fill_destination(dest, rest);
    assert!(!heap.destination_is_open(dest));
    assert_eq!(cons.head_value(), AnyValue::int(7));
    assert!(cons.aliased(), "closing a hole does not drop the shared mark");
    assert!(matches!(cons.tail(), ListTail::Proper(next) if next != 0));
}

#[test]
fn a_list_hole_closes_with_the_empty_list() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let (cell, dest) = heap.alloc_open_list_cell(AnyValue::int(7));
    heap.fill_destination(dest, AnyValue::empty_list());
    let cons = unsafe { &*(cell.list_addr().unwrap() as *const ListCons) };
    assert_eq!(cons.tail(), ListTail::Proper(0));
}

#[test]
fn a_list_hole_closes_with_a_value_that_is_not_a_list_by_placing_its_terminator() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let (cell, dest) = heap.alloc_open_list_cell(AnyValue::int(7));
    heap.fill_destination(dest, AnyValue::int(9));
    let cons = unsafe { &*(cell.list_addr().unwrap() as *const ListCons) };
    assert!(matches!(cons.tail(), ListTail::Terminator(_)));
    assert_eq!(unsafe { cons.tail().value() }, AnyValue::int(9));
}

#[test]
fn a_struct_field_hole_closes_with_a_scalar_and_with_a_heap_value() {
    let (mut heap, pair) = heap_with_pair();
    let (object, dest) = pair_with_open_second(&mut heap, pair);
    assert!(heap.destination_is_open(dest));
    heap.fill_destination(dest, AnyValue::int(5));
    assert!(!heap.destination_is_open(dest));
    assert_eq!(heap.read_field_slot(object, 8), AnyValue::int(5));

    let (object, dest) = pair_with_open_second(&mut heap, pair);
    let list = list_ref(heap.alloc_list_cons_slot(AnyValue::int(1), crate::any_value::EMPTY_LIST));
    heap.fill_destination(dest, list);
    assert_eq!(heap.read_field_slot(object, 8), list);
    let cons = unsafe { &*(list.heap_addr().unwrap() as *const ListCons) };
    assert!(
        cons.aliased(),
        "a list a struct holds is shared, as any stored field is"
    );
}

#[test]
fn a_map_value_hole_closes_and_leaves_the_key_and_its_kind_alone() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let (node, dest) = map_with_open_value(&mut heap);
    assert!(heap.destination_is_open(dest));
    heap.fill_destination(dest, AnyValue::atom(4));
    assert!(!heap.destination_is_open(dest));
    assert_eq!(unsafe { map_entry(node, 0) }, (AnyValue::int(1), AnyValue::atom(4)));
}

#[test]
fn a_map_value_hole_closes_with_a_heap_value() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let (node, dest) = map_with_open_value(&mut heap);
    let list = list_ref(heap.alloc_list_cons_slot(AnyValue::int(1), crate::any_value::EMPTY_LIST));
    heap.fill_destination(dest, list);
    assert_eq!(unsafe { map_entry(node, 0) }.1, list);
}

#[test]
#[should_panic(expected = "heap value ref: NullAddress")]
fn a_struct_field_that_is_open_is_not_a_value_to_read() {
    let (mut heap, pair) = heap_with_pair();
    let (object, _) = pair_with_open_second(&mut heap, pair);
    let _ = heap.read_field_slot(object, 8);
}

#[test]
#[should_panic(expected = "heap value ref: NullAddress")]
fn a_map_entry_whose_value_is_open_is_not_a_value_to_read() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let (node, _) = map_with_open_value(&mut heap);
    let _ = unsafe { map_entry(node, 0) };
}

#[test]
#[should_panic(expected = "heap value ref: NullAddress")]
fn a_tuple_with_an_open_field_is_refused_by_compare() {
    let (mut heap, pair) = heap_with_pair();
    let (open, _) = pair_with_open_second(&mut heap, pair);
    let (other, _) = pair_with_open_second(&mut heap, pair);
    let schemas = heap.schemas.borrow();
    TermComparator::new(&heap.node, &schemas).compare(
        AnyValue::heap_ptr(open, ValueKind::STRUCT),
        AnyValue::heap_ptr(other, ValueKind::STRUCT),
        NumericMode::Strict,
    );
}

#[test]
#[should_panic(expected = "heap value ref: NullAddress")]
fn a_tuple_with_an_open_field_is_refused_by_hash() {
    let (mut heap, pair) = heap_with_pair();
    let (object, _) = pair_with_open_second(&mut heap, pair);
    let schemas = heap.schemas.borrow();
    TermHasher::new(&heap.node, &schemas).hash(AnyValue::heap_ptr(object, ValueKind::STRUCT));
}

#[test]
#[should_panic(expected = "heap value ref: NullAddress")]
fn a_tuple_with_an_open_field_is_refused_by_a_send() {
    let (mut sender, pair) = heap_with_pair();
    let (object, _) = pair_with_open_second(&mut sender, pair);
    let message = AnyValueRef::from_heap_object(ValueKind::STRUCT, object).unwrap();
    let mut receiver = Heap::new(SIZE_TABLE[0], Rc::clone(&sender.schemas));
    let _ = deep_copy_any_value_ref(message, &sender.view(), &mut receiver);
}

#[test]
#[should_panic(expected = "heap value ref: NullAddress")]
fn a_map_with_an_open_value_is_refused_by_a_send() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let (node, _) = map_with_open_value(&mut sender);
    let message = AnyValueRef::from_heap_object(ValueKind::MAP, node).unwrap();
    let mut receiver = Heap::new(SIZE_TABLE[0], Rc::clone(&sender.schemas));
    let _ = deep_copy_any_value_ref(message, &sender.view(), &mut receiver);
}

#[test]
#[should_panic(expected = "a list whose tail is a hole is not a value to copy")]
fn a_list_with_an_open_tail_is_refused_by_the_send_measure() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let (cell, _) = sender.alloc_open_list_cell(AnyValue::int(7));
    let _ = measure_deep_copy(&[Stored::of_ref(cell)], &sender.view());
}

#[test]
#[should_panic(expected = "a destination is not a value")]
fn a_destination_held_by_a_closure_is_not_a_value_to_read() {
    let (mut heap, pair) = heap_with_pair();
    let (_, dest) = pair_with_open_second(&mut heap, pair);
    let bits = heap.alloc_closure_slots(crate::any_value::ClosureDenotationId::user(0), 0, 1, 0);
    let closure = closure_addr_from_tagged(bits).expect("closure");
    unsafe { crate::any_value::closure_capture_set_raw_kind(closure, 0, dest.word(), ValueKind::DESTINATION) };
    let _ = unsafe { closure_capture_value(closure, 0) };
}
