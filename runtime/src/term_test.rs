use super::*;
use crate::any_value::{
    AnyValueRef, ClosureDenotationId, EMPTY_LIST_BITS, closure_addr_from_tagged, closure_capture_set,
    map_addr_from_tagged,
};
use crate::function_denotation::FunctionDenotation;
use crate::heap::{Heap, Schema, deep_copy_slot};
use crate::procbin::{SharedBinHandle, alloc_procbin};
use crate::resource::{ResourceHandle, alloc_resource, fz_resource_destructor_noop};
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

thread_local! {
    pub(super) static COMPARISON_CALLS: Cell<usize> = const { Cell::new(0) };
}

fn heap_value(bits: u64) -> AnyValue {
    AnyValue::decode_tagged_heap_bits(bits).unwrap()
}

#[test]
fn mixed_numbers_order_exactly_before_strict_kind_ties() {
    let schemas = SchemaRegistry::new();
    let node = Node::empty();
    let comparator = TermComparator::new(&node, &schemas);
    for (integer, float, expected) in [
        (9_007_199_254_740_993, 9_007_199_254_740_992.0, Ordering::Greater),
        (-9_007_199_254_740_993, -9_007_199_254_740_992.0, Ordering::Less),
        (10, -1.0, Ordering::Greater),
        (0, 0.5, Ordering::Less),
        (0, -0.5, Ordering::Greater),
        (i64::MAX, 9_223_372_036_854_775_808.0, Ordering::Less),
        (i64::MIN, -9_223_372_036_854_777_856.0, Ordering::Greater),
    ] {
        for mode in [NumericMode::Strict, NumericMode::Widening] {
            assert_eq!(
                comparator.compare(AnyValue::int(integer), AnyValue::float(float), mode),
                expected
            );
            assert_eq!(
                comparator.compare(AnyValue::float(float), AnyValue::int(integer), mode),
                expected.reverse()
            );
        }
    }
    assert_eq!(
        comparator.compare(AnyValue::int(1), AnyValue::float(1.0), NumericMode::Strict),
        Ordering::Less
    );
    assert_eq!(
        comparator.compare(AnyValue::int(1), AnyValue::float(1.0), NumericMode::Widening),
        Ordering::Equal
    );
}

fn tuple(heap: &mut Heap, schema: u32, value: AnyValue) -> AnyValue {
    let p = heap.alloc_struct(schema);
    unsafe { heap.write_field_slot(p, 0, value) };
    AnyValue::heap_ptr(p, ValueKind::STRUCT)
}

#[test]
fn lookup_by_the_retained_dag_key_does_no_structural_walk() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let schema = schemas.borrow_mut().register(Schema::tuple_of_arity(2));
    let mut heap = Heap::new(4096, schemas);
    for depth in [10, 26] {
        let mut key = AnyValue::int(0);
        for _ in 0..depth {
            let parent = heap.alloc_struct(schema);
            unsafe {
                heap.write_field_slot(parent, 0, key);
                heap.write_field_slot(parent, 8, key);
            }
            key = AnyValue::heap_ptr(parent, ValueKind::STRUCT);
        }
        let map = heap_value(heap.alloc_map_slots(&[(key, AnyValue::int(7))]));
        let map = AnyValueRef::from_heap_object(ValueKind::MAP, map.raw() as *const u8).unwrap();
        COMPARISON_CALLS.with(|count| count.set(0));
        assert_eq!(
            heap.read_map_value_for_any_key(map, key).unwrap().unwrap().load_int(),
            Ok(7)
        );
        COMPARISON_CALLS.with(|count| {
            assert_eq!(
                count.get(),
                1,
                "depth {depth}: retained identity settles at the key root"
            );
        });
    }
}

#[test]
fn nested_map_keys_keep_exact_numeric_order_above_float_integer_precision() {
    let mut registry = SchemaRegistry::new();
    let schema = registry.register(Schema::tuple_of_arity(1));
    let registry = Rc::new(RefCell::new(registry));
    let mut heap = Heap::new(1024, Rc::clone(&registry));
    let integer_key = tuple(&mut heap, schema, AnyValue::int(9_007_199_254_740_993));
    let float_key = tuple(&mut heap, schema, AnyValue::float(9_007_199_254_740_992.0));
    let map = heap.alloc_map_slots(&[(integer_key, AnyValue::int(1)), (float_key, AnyValue::int(2))]);
    let addr = map_addr_from_tagged(map).unwrap();
    assert_eq!(unsafe { map_count(addr) }, 2);
    assert_eq!(
        unsafe { map_entry(addr, 0).1 },
        AnyValue::int(2),
        "nested keys use exact numeric order"
    );
}

#[test]
fn map_keys_keep_numeric_kinds_at_every_depth_while_values_may_widen() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let schema = schemas.borrow_mut().register(Schema::tuple_of_arity(1));
    let node = Rc::new(Node::empty());
    let mut heap = Heap::with_node(1024, Rc::clone(&schemas), Rc::clone(&node));
    let integer = AnyValue::int(1);
    let float = AnyValue::float(1.0);
    let int_tuple = tuple(&mut heap, schema, integer);
    let float_tuple = tuple(&mut heap, schema, float);
    let int_list = heap_value(heap.alloc_list_cons_slot(integer, EMPTY_LIST_BITS));
    let float_list = heap_value(heap.alloc_list_cons_slot(float, EMPTY_LIST_BITS));
    let int_map = heap_value(heap.alloc_map_slots(&[(integer, integer)]));
    let float_value_map = heap_value(heap.alloc_map_slots(&[(integer, float)]));
    let float_key_map = heap_value(heap.alloc_map_slots(&[(float, integer)]));
    let registry = schemas.borrow();
    let cmp = TermComparator::new(&node, &registry);
    for (a, b) in [
        (integer, float),
        (int_tuple, float_tuple),
        (int_list, float_list),
        (int_map, float_value_map),
    ] {
        assert_ne!(cmp.compare(a, b, NumericMode::Strict), Ordering::Equal);
        assert_eq!(cmp.compare(a, b, NumericMode::Widening), Ordering::Equal);
    }
    assert_ne!(
        cmp.compare(int_map, float_key_map, NumericMode::Widening),
        Ordering::Equal,
        "keys remain strict inside widening maps"
    );
    drop(registry);
    for (a, b) in [
        (integer, float),
        (int_tuple, float_tuple),
        (int_list, float_list),
        (int_map, float_value_map),
    ] {
        let map = heap.alloc_map_slots(&[(b, integer), (a, float)]);
        assert_eq!(unsafe { map_count(map_addr_from_tagged(map).unwrap()) }, 2);
    }
}

#[test]
fn bitstrings_compare_bits_independently_of_storage_and_padding() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let node = Rc::new(Node::empty());
    let mut heap = Heap::with_node(1024, Rc::clone(&schemas), Rc::clone(&node));
    let inline = heap.alloc_bitstring(b"a", 8);
    let shared = alloc_procbin(&mut heap, SharedBinHandle::from_bytes(b"a", 8), 0);
    let shared = AnyValue::heap_ptr(shared.as_raw(), ValueKind::PROCBIN);
    let padded = heap.alloc_bitstring(&[0b1011_1111], 3);
    let clean = heap.alloc_bitstring(&[0b1010_0000], 3);
    let lower = heap.alloc_bitstring(&[0b1000_0000], 3);
    let registry = schemas.borrow();
    let cmp = TermComparator::new(&node, &registry);
    assert_eq!(cmp.compare(inline, shared, NumericMode::Strict), Ordering::Equal);
    assert_eq!(cmp.compare(padded, clean, NumericMode::Strict), Ordering::Equal);
    assert_eq!(cmp.compare(lower, clean, NumericMode::Strict), Ordering::Less);
    drop(registry);
    let map = heap.alloc_map_slots(&[(inline, AnyValue::int(1)), (shared, AnyValue::int(2))]);
    let map = map_addr_from_tagged(map).unwrap();
    assert_eq!(unsafe { map_count(map) }, 1);
    assert_eq!(unsafe { map_entry(map, 0).1 }, AnyValue::int(2));
}

#[test]
#[should_panic(expected = "absent carrier is not a language value")]
fn absent_carrier_has_no_language_order() {
    let schemas = SchemaRegistry::new();
    let node = Node::empty();
    TermComparator::new(&node, &schemas).compare(AnyValue::null(), AnyValue::null(), NumericMode::Strict);
}

#[test]
#[should_panic(expected = "published atom must be registered")]
fn unregistered_atom_has_no_language_order() {
    TermComparator::new(&Node::empty(), &SchemaRegistry::new()).compare(
        AnyValue::atom(100),
        AnyValue::atom(100),
        NumericMode::Strict,
    );
}

#[test]
#[should_panic(expected = "unpublished map is not a language value")]
fn unfinished_map_has_no_language_order() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let node = Rc::new(Node::empty());
    let mut heap = Heap::with_node(1024, Rc::clone(&schemas), Rc::clone(&node));
    let unfinished = heap.alloc_map_destination(None, 0);
    TermComparator::new(&node, &schemas.borrow()).compare(
        heap_value(unfinished),
        heap_value(unfinished),
        NumericMode::Strict,
    );
}

#[test]
#[should_panic(expected = "internal storage schema is not a language value")]
fn identical_internal_struct_has_no_language_order() {
    let mut registry = SchemaRegistry::new();
    let mut schema = Schema::tuple_of_arity(0);
    schema.identity = crate::heap::SchemaIdentity::Internal("storage".into());
    let schema = registry.register(schema);
    let registry = Rc::new(RefCell::new(registry));
    let mut heap = Heap::new(1024, Rc::clone(&registry));
    let value = AnyValue::heap_ptr(heap.alloc_struct(schema), ValueKind::STRUCT);
    TermComparator::new(&Node::empty(), &registry.borrow()).compare(value, value, NumericMode::Strict);
}

#[test]
#[should_panic(expected = "published closure must have a source denotation")]
fn unregistered_closure_id_cannot_authorize_equality() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let node = Rc::new(Node::empty());
    let mut heap = Heap::with_node(1024, Rc::clone(&schemas), Rc::clone(&node));
    let closure = heap.alloc_closure_slots(ClosureDenotationId::user(100), 0, 0, 0);
    TermComparator::new(&node, &schemas.borrow()).compare(
        heap_value(closure),
        heap_value(closure),
        NumericMode::Strict,
    );
}

#[test]
fn typed_closure_and_resource_identity_survive_transport_without_comparison_allocations() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let node = Rc::new(Node::empty());
    let denotation = ClosureDenotationId::user(7);
    node.register_closure_denotation(
        denotation,
        Arc::new(FunctionDenotation::named(None, "capture".into(), 0)),
    );
    let mut source = Heap::with_node(1024, Rc::clone(&schemas), Rc::clone(&node));
    let mut destination = Heap::with_node(1024, Rc::clone(&schemas), Rc::clone(&node));
    let resource = alloc_resource(
        &mut source,
        ResourceHandle::new(99, fz_resource_destructor_noop),
        AnyValue::null(),
    );
    let distinct = alloc_resource(
        &mut source,
        ResourceHandle::new(99, fz_resource_destructor_noop),
        AnyValue::null(),
    );
    let resource = AnyValue::heap_ptr(resource.as_raw(), ValueKind::RESOURCE);
    let distinct = AnyValue::heap_ptr(distinct.as_raw(), ValueKind::RESOURCE);
    let a = source.alloc_closure_slots(denotation, 0, 1, 0);
    let b = source.alloc_closure_slots(denotation, 0, 1, 0);
    let changed = source.alloc_closure_slots(denotation, 0, 1, 0);
    unsafe {
        closure_capture_set(closure_addr_from_tagged(a).unwrap(), 0, resource);
        closure_capture_set(closure_addr_from_tagged(b).unwrap(), 0, resource);
        closure_capture_set(closure_addr_from_tagged(changed).unwrap(), 0, distinct);
    }
    let map = source.alloc_map_slots(&[
        (heap_value(a), AnyValue::int(1)),
        (heap_value(b), AnyValue::int(2)),
        (heap_value(changed), AnyValue::int(3)),
    ]);
    assert_eq!(unsafe { map_count(map_addr_from_tagged(map).unwrap()) }, 2);
    let copied = deep_copy_slot(heap_value(map), &source, &mut destination, &mut HashMap::new());
    let mut roots = [copied];
    destination.gc_with_extra_root_slots(&mut std::ptr::null_mut(), &mut roots);
    let before = destination.alloc_stats_snapshot();
    let registry = schemas.borrow();
    let cmp = TermComparator::new(&node, &registry);
    assert_eq!(
        cmp.compare(heap_value(map), roots[0], NumericMode::Strict),
        Ordering::Equal
    );
    assert_ne!(
        cmp.compare(resource, distinct, NumericMode::Strict),
        Ordering::Equal,
        "equal payloads do not merge generative resources"
    );
    let moved = AnyValueRef::from_heap_object(ValueKind::MAP, roots[0].raw() as *const u8).unwrap();
    assert_eq!(
        destination
            .read_map_value_for_any_key(moved, heap_value(b))
            .unwrap()
            .unwrap()
            .load_int(),
        Ok(2)
    );
    assert_eq!(
        destination.alloc_stats_snapshot(),
        before,
        "comparison and lookup borrow their terms"
    );
}

#[test]
#[should_panic(expected = "nonfinite float is not a language value")]
fn nonfinite_foreign_float_cannot_be_compared_as_a_language_term() {
    TermComparator::new(&Node::empty(), &SchemaRegistry::new()).compare(
        AnyValue::Float(f64::NAN.to_bits()),
        AnyValue::Float(f64::NAN.to_bits()),
        NumericMode::Strict,
    );
}

#[test]
fn signed_zeros_are_distinct_strict_keys_but_widening_equal() {
    let mut heap = Heap::new(1024, Rc::new(RefCell::new(SchemaRegistry::new())));
    let map = heap.alloc_map_slots(&[
        (AnyValue::float(-0.0), AnyValue::int(1)),
        (AnyValue::float(0.0), AnyValue::int(2)),
    ]);
    let map = map_addr_from_tagged(map).unwrap();
    assert_eq!(unsafe { map_count(map) }, 2);
    assert_eq!(unsafe { map_entry(map, 0).1 }, AnyValue::int(1));
    assert_eq!(unsafe { map_entry(map, 1).1 }, AnyValue::int(2));
    assert_eq!(
        TermComparator::new(&Node::empty(), &SchemaRegistry::new()).compare(
            AnyValue::float(-0.0),
            AnyValue::float(0.0),
            NumericMode::Widening,
        ),
        Ordering::Equal
    );
}
