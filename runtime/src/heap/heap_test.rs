use super::imp::{BUDGET_FLOOR, MAJOR_GROWTH_FACTOR};
use super::*;
use crate::any_value::{
    AnyValue, AnyValueRef, AnyValueRefError, AnyValueRefPacking, EMPTY_LIST, EMPTY_LIST_BITS, ListCons, ListLink,
    ListTail, STRUCT_HEADER_NAMED_MASK, STRUCT_PAYLOAD_OFFSET, SlotLayout, ValueKind, binview_addr_from_tagged,
    bitstring_bytes_ptr, bitstring_size_for_bit_len, closure_addr_from_tagged, closure_capture_set,
    closure_capture_value, closure_captured_count, closure_fn_ptr, closure_halt_kind, heap_kind_from_tagged,
    heap_object_word, heap_word_addr, list_addr_from_tagged, map_addr_from_tagged, map_count, map_entry,
    map_size_for_count, object_size, struct_addr_from_tagged, struct_is_named, struct_schema_id,
    struct_size_for_payload,
};
use crate::module_name::ModuleName;
use crate::resource::ResourceStub;
use crate::sync::Ordering;
use std::cell::RefCell;
use std::f64::consts::PI;
use std::mem::MaybeUninit;
use std::ptr::{null_mut, read, write};
use std::rc::Rc;

fn fresh_registry() -> Rc<RefCell<SchemaRegistry>> {
    Rc::new(RefCell::new(SchemaRegistry::new()))
}

#[test]
fn schema_identity_preserves_module_segments_across_display_collisions() {
    use crate::module_name::ModuleName;
    let one = ModuleName::from_segments(vec!["A.B".into()]);
    let two = ModuleName::from_segments(vec!["A".into(), "B".into()]);
    assert_eq!(one.to_string(), two.to_string());
    let mut registry = SchemaRegistry::new();
    let first = registry.register(Schema::named_struct(one, Vec::new()));
    let second = registry.register(Schema::named_struct(two, Vec::new()));
    assert_ne!(first, second, "rendering cannot merge distinct source identities");
}

#[test]
#[should_panic(expected = "map is already published")]
fn published_map_cannot_reenter_mutable_construction() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let map = heap.alloc_map_slots(&[(AnyValue::int(1), AnyValue::int(2))]);
    let _ = heap.map_destination_freeze(map);
}

#[test]
fn map_publication_shares_list_keys_and_values() {
    for construction in 0..3 {
        let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
        let key = heap.alloc_list_cons_slot(AnyValue::int(1), EMPTY_LIST);
        let value = heap.alloc_list_cons_slot(AnyValue::int(2), EMPTY_LIST);
        match construction {
            0 => {
                heap.alloc_map_slots(&[(heap_root(key), heap_root(value))]);
            }
            1 => {
                let empty = heap.alloc_map_slots(&[]);
                let empty =
                    AnyValueRef::from_heap_object(ValueKind::MAP, map_addr_from_tagged(empty).unwrap()).unwrap();
                heap.map_put_slot(empty, heap_root(key), heap_root(value));
            }
            _ => {
                let destination = heap.alloc_map_destination(1);
                unsafe {
                    heap.map_destination_put(destination, heap_root(key), heap_root(value));
                }
                heap.map_destination_freeze(destination).expect("a build publishes");
            }
        }
        for source in [key, value] {
            let cell = list_addr_from_tagged(source).expect("list source") as *const ListCons;
            assert!(
                unsafe { (*cell).aliased() },
                "construction {construction} publishes both fields"
            );
        }
    }
}

#[test]
fn map_freeze_keeps_one_allocation_and_gc_preserves_structural_lookup() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let a = heap.alloc_list_cons_slot(AnyValue::int(7), EMPTY_LIST);
    let b = heap.alloc_list_cons_slot(AnyValue::int(7), EMPTY_LIST);
    let setup = heap.node.alloc_stats();
    let dest = heap.alloc_map_destination(3);
    unsafe {
        heap.map_destination_put(dest, heap_root(a), AnyValue::int(1));
        heap.map_destination_put(dest, AnyValue::int(0), AnyValue::int(2));
        heap.map_destination_put(dest, heap_root(b), AnyValue::int(3));
    }
    assert_eq!(
        heap.map_destination_freeze(dest).expect("a build publishes").raw_word(),
        AnyValueRef::from_heap_object(ValueKind::MAP, map_addr_from_tagged(dest).unwrap())
            .unwrap()
            .raw_word(),
        "freezing compacts the unpublished allocation in place"
    );
    let allocation = heap.node.alloc_stats();
    assert_eq!(allocation.total.allocs - setup.total.allocs, 1);
    assert_eq!(allocation.total.bytes - setup.total.bytes, 64);
    assert_eq!(
        (
            allocation.map.allocs - setup.map.allocs,
            allocation.map.bytes - setup.map.bytes
        ),
        (1, 64),
        "the one destination allocation belongs to Map"
    );
    assert_eq!(allocation.other.allocs, setup.other.allocs);
    let mut roots = [heap_ref(dest)];
    heap.collect_stats(&mut roots);
    let fresh = heap.alloc_list_cons_slot(AnyValue::int(7), EMPTY_LIST);
    let map = roots[0];
    assert_eq!(unsafe { map_count(map.map_addr().unwrap()) }, 2);
    assert_eq!(heap.read_map_value(map, heap_root(fresh)).unwrap().load_int(), Ok(3));
    let before = heap.node.alloc_stats();
    assert_eq!(heap.map_view_delete(map, AnyValue::int(99)), map);
    assert_eq!(
        heap.node.alloc_stats(),
        before,
        "an absent deletion neither allocates nor copies"
    );
}

#[test]
fn tuple_display_name_cannot_alias_a_named_struct_identity() {
    let mut registry = SchemaRegistry::new();
    let named = registry.register(Schema::named_struct(
        crate::module_name::ModuleName::from_segments(vec!["Tuple2".into()]),
        ["a".into(), "b".into()],
    ));
    let tuple = registry.register(Schema::tuple_of_arity(2));
    assert_ne!(named, tuple, "a display label is not a schema denotation");
}

#[test]
fn named_struct_key_order_is_independent_of_schema_registration_order() {
    let registry = fresh_registry();
    let z = registry.borrow_mut().register(Schema::named_struct(
        crate::module_name::ModuleName::from_segments(vec!["Zed".into()]),
        ["x".into()],
    ));
    let a = registry.borrow_mut().register(Schema::named_struct(
        crate::module_name::ModuleName::from_segments(vec!["Alpha".into()]),
        ["x".into()],
    ));
    let mut heap = Heap::new(SIZE_TABLE[0], registry);
    let zp = heap.alloc_struct(z);
    let ap = heap.alloc_struct(a);
    unsafe { heap.write_field_slot(zp, 0, AnyValue::int(1)) };
    unsafe { heap.write_field_slot(ap, 0, AnyValue::int(1)) };
    let map = heap.alloc_map_slots(&[
        (AnyValue::heap_ptr(zp, ValueKind::STRUCT), AnyValue::int(0)),
        (AnyValue::heap_ptr(ap, ValueKind::STRUCT), AnyValue::int(1)),
    ]);
    let addr = map_addr_from_tagged(map).unwrap();
    assert_eq!(
        unsafe { map_entry(addr, 0).0.raw() },
        ap as u64,
        "source schema identity owns key order"
    );
}

#[test]
fn map_publication_collapses_independently_allocated_structural_keys_last_wins() {
    let registry = fresh_registry();
    let tuple_schema = registry.borrow_mut().register(Schema::tuple_of_arity(2));
    let mut heap = Heap::new(SIZE_TABLE[0], registry);
    let keys: Vec<_> = (0..3)
        .map(|_| {
            let tuple = heap.alloc_struct(tuple_schema);
            unsafe { heap.write_field_slot(tuple, 0, AnyValue::int(1)) };
            unsafe { heap.write_field_slot(tuple, 8, AnyValue::int(2)) };
            AnyValue::heap_ptr(tuple, ValueKind::STRUCT)
        })
        .collect();
    assert_ne!(keys[0].raw(), keys[1].raw());
    let slots = heap.alloc_map_slots(&[(keys[0], AnyValue::int(10)), (keys[1], AnyValue::int(20))]);
    let slots = AnyValueRef::from_heap_object(ValueKind::MAP, map_addr_from_tagged(slots).unwrap()).unwrap();
    assert_eq!(
        unsafe { map_count(slots.map_addr().unwrap()) },
        1,
        "one strict structural key must occupy one entry"
    );
    assert_eq!(heap.read_map_value(slots, keys[2]).unwrap().load_int(), Ok(20));

    let first = AnyValueRef::from_heap_object(ValueKind::STRUCT, keys[0].raw() as *const u8).unwrap();
    let second = AnyValueRef::from_heap_object(ValueKind::STRUCT, keys[1].raw() as *const u8).unwrap();
    let old_value = 10u64;
    let new_value = 20u64;
    let refs = heap
        .alloc_map_refs(&[
            (
                first,
                AnyValueRef::from_scalar_slot(ValueKind::INT, &old_value).unwrap(),
            ),
            (
                second,
                AnyValueRef::from_scalar_slot(ValueKind::INT, &new_value).unwrap(),
            ),
        ])
        .unwrap();
    assert_eq!(unsafe { map_count(refs.map_addr().unwrap()) }, 1);
    assert_eq!(heap.read_map_value(refs, keys[2]).unwrap().load_int(), Ok(20));
}

#[test]
fn closure_allocation_does_not_change_struct_schema_identity() {
    let registry = fresh_registry();
    let first_free_id = registry.borrow().len() as u32;
    let mut heap = Heap::new(SIZE_TABLE[0], Rc::clone(&registry));
    heap.alloc_closure_slots(crate::any_value::ClosureDenotationId::user(0), 1, 2, 0);
    assert_eq!(
        registry.borrow_mut().register(Schema::tuple_of_arity(2)),
        first_free_id,
        "closure capture layout must not consume a struct schema identity",
    );
}

#[test]
#[should_panic(expected = "internal continuation is not a user closure")]
fn internal_continuation_cannot_render_as_a_user_closure() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bits = heap.alloc_closure_slots(crate::any_value::ClosureDenotationId::INTERNAL, 0, 0, 0);
    crate::any_value::debug::render_value(null_mut(), heap_root(bits));
}

#[test]
fn closure_denotation_survives_cross_heap_copy_and_gc() {
    let mut source = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut destination = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bits = source.alloc_closure_slots(crate::any_value::ClosureDenotationId::user(73), 1, 1, 0);
    let closure = closure_addr_from_tagged(bits).expect("source closure");
    unsafe { closure_capture_set(closure, 0, AnyValue::int(42)) };
    let copied = deep_copy_slot(heap_root(bits), &source.view(), &mut destination);
    let mut roots = [copied.ref_word()];
    destination.collect_stats(&mut roots);
    let moved = roots[0].closure_addr().expect("copied closure");
    assert_eq!(
        unsafe { crate::any_value::closure_denotation(moved) },
        crate::any_value::ClosureDenotationId::user(73),
        "copying and moving a closure must preserve its semantic header word verbatim",
    );
    assert_eq!(unsafe { closure_capture_value(moved, 0) }, AnyValue::int(42));
}

fn heap_root(bits: u64) -> AnyValue {
    AnyValue::decode_tagged_heap_bits(bits).expect("tagged heap root")
}

fn heap_ref(bits: u64) -> AnyValueRef {
    let kind = heap_kind_from_tagged(bits).expect("tagged heap root");
    AnyValueRef::from_raw_word(bits)
        .inspect(|root| assert_eq!(root.tag(), kind))
        .expect("heap root ref")
}

fn ref_bits(value: AnyValueRef) -> u64 {
    value.heap_object_word().expect("heap root bits")
}

impl Heap {
    /// Collect and keep what the collection measured, releasing its from-space.
    pub(crate) fn collect_stats(&mut self, roots: &mut (impl Roots + ?Sized)) -> GcStats {
        let mut stats = GcStats::default();
        drop(self.collect(roots, &mut stats));
        stats
    }

    /// Collect with at most one root, given as tagged heap bits (null for no
    /// root); the slot holds the forwarded bits afterwards. The from-space is
    /// released when the returned collection is dropped.
    pub(crate) fn collect_tagged_held<'h>(&'h mut self, root: &mut *mut u8, stats: &'h mut GcStats) -> Collected<'h> {
        let mut roots: Vec<AnyValueRef> = (!root.is_null()).then(|| heap_ref(*root as u64)).into_iter().collect();
        let collected = self.collect(&mut roots, stats);
        if let Some(forwarded) = roots.first() {
            *root = ref_bits(*forwarded) as *mut u8;
        }
        collected
    }

    /// Collect with at most one root, as `collect_tagged_held`, releasing the
    /// from-space.
    pub(crate) fn collect_tagged(&mut self, root: &mut *mut u8) -> GcStats {
        let mut stats = GcStats::default();
        drop(self.collect_tagged_held(root, &mut stats));
        stats
    }
}

fn tagged_bits(value: AnyValue) -> u64 {
    value.heap_object_word().expect("tagged heap bits")
}

fn any_value(raw: u64, kind: ValueKind) -> AnyValue {
    match kind {
        ValueKind::NULL => AnyValue::null(),
        ValueKind::LIST if raw == 0 => AnyValue::empty_list(),
        ValueKind::INT => AnyValue::int(raw as i64),
        ValueKind::FLOAT => AnyValue::decode_parts(raw, kind.tag()).expect("float value"),
        ValueKind::ATOM => AnyValue::atom(raw as u32),
        kind if kind.is_heap() => AnyValue::heap_ptr(raw as *mut u8, kind),
        _ => AnyValue::decode_parts(raw, kind.tag()).expect("test value"),
    }
}

fn alloc_int_list_cons(heap: &mut Heap, head: i64, tail_bits: u64) -> u64 {
    heap.alloc_list_cons_slot(AnyValue::int(head), tail_bits)
}

fn list_ref_from_bits(bits: u64) -> AnyValueRef {
    let addr = list_addr_from_tagged(bits).expect("list addr");
    AnyValueRef::from_heap_object(ValueKind::LIST, addr).expect("list ref")
}

/// The list `bits` names, as the tail value a cell is rebuilt in front of.
fn list_value(bits: u64) -> AnyValue {
    AnyValue::from_ref(list_ref_from_bits(bits)).expect("list value")
}

/// What a link to the list `bits` answers: the next cell's address, 0 for `[]`.
fn proper(bits: u64) -> ListTail {
    ListTail::Proper(list_addr_from_tagged(bits).map_or(0, |addr| addr as u64))
}

#[test]
fn alloc_stats_record_heap_allocations_by_kind() {
    let registry = fresh_registry();
    let pair_schema = {
        let mut schemas = registry.borrow_mut();
        schemas.register(Schema::tuple_of_arity(2))
    };
    let mut h = Heap::new(SIZE_TABLE[0], registry);

    let _ = h.alloc_struct(pair_schema);
    let _ = h.alloc_list_cons_slot(AnyValue::int(1), EMPTY_LIST_BITS);
    let _ = h.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
    let _ = h.alloc_bitstring(b"abc", 24);
    let _ = h.alloc_bitstring(&[0; SHARED_BIN_THRESHOLD_BYTES + 1], 65 * 8);
    let _ = h.alloc_closure_slots(crate::any_value::ClosureDenotationId::user(0), 0, 1, 0);
    let _ = h.box_any_value_ref(AnyValue::int(42));
    let _ = h.alloc(16);

    let stats = h.node.alloc_stats();
    assert_eq!(stats.struct_.allocs, 1);
    assert_eq!(stats.list_cons.allocs, 1);
    assert_eq!(stats.map.allocs, 1);
    assert_eq!(stats.bitstring.allocs, 1);
    assert_eq!(stats.binview.allocs, 1);
    assert_eq!(stats.binref.allocs, 1, "a buffer entering the heap makes one BinRef");
    assert_eq!(stats.closure.allocs, 1);
    assert_eq!(stats.scalar_box.allocs, 1);
    assert_eq!(stats.other.allocs, 1);
    assert_eq!(stats.total.allocs, 9);
    assert_eq!(
        stats.total.bytes,
        stats.struct_.bytes
            + stats.list_cons.bytes
            + stats.map.bytes
            + stats.bitstring.bytes
            + stats.binview.bytes
            + stats.binref.bytes
            + stats.closure.bytes
            + stats.scalar_box.bytes
            + stats.other.bytes
    );
}

#[test]
fn any_value_ref_list_reads_scalar_head_and_heap_tail() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let tail_bits = h.alloc_list_cons_slot(AnyValue::atom(9), EMPTY_LIST_BITS);
    let tail_addr = list_addr_from_tagged(tail_bits).expect("tail addr");
    let list_bits = h.alloc_list_cons_slot(AnyValue::int(42), tail_bits);
    let list_addr = list_addr_from_tagged(list_bits).expect("list addr");
    let list_ref = AnyValueRef::from_heap_object(ValueKind::LIST, list_addr).expect("list ref");

    assert_eq!(h.read_list_head_ref(list_ref).unwrap().load_int(), Ok(42));
    assert_eq!(h.read_list_tail_ref(list_ref).unwrap().list_addr(), Ok(tail_addr));
    assert!(
        h.read_list_tail_ref(AnyValueRef::from_heap_object(ValueKind::LIST, tail_addr).expect("tail ref"))
            .unwrap()
            .is_empty_list()
    );
}

#[test]
fn any_value_ref_list_reads_heap_object_head() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let child_bits = h.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
    let child_addr = map_addr_from_tagged(child_bits).expect("map addr");
    let list_bits = h.alloc_list_cons_slot(AnyValue::heap_ptr(child_addr, ValueKind::MAP), EMPTY_LIST_BITS);
    let list_addr = list_addr_from_tagged(list_bits).expect("list addr");
    let list_ref = AnyValueRef::from_heap_object(ValueKind::LIST, list_addr).expect("list ref");

    assert_eq!(h.read_list_head_ref(list_ref).unwrap().map_addr(), Ok(child_addr));
}

#[test]
fn any_value_ref_map_lookup_reads_scalar_and_heap_values() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let child_atom = h.node.intern_atom("child");
    let key_atom = h.node.intern_atom("key");
    let missing_atom = h.node.intern_atom("missing");
    let child_bits = h.alloc_list_cons_slot(AnyValue::atom(child_atom), EMPTY_LIST_BITS);
    let child_addr = list_addr_from_tagged(child_bits).expect("child addr");
    let map_bits = h.alloc_map_slots(&[
        (AnyValue::int(1), AnyValue::int(10)),
        (
            AnyValue::atom(key_atom),
            AnyValue::heap_ptr(child_addr, ValueKind::LIST),
        ),
    ]);
    let map_addr = map_addr_from_tagged(map_bits).expect("map addr");
    let map_ref = AnyValueRef::from_heap_object(ValueKind::MAP, map_addr).expect("map ref");
    let scalar = h.read_map_value(map_ref, AnyValue::int(1)).expect("present int key");
    assert_eq!(scalar.load_int(), Ok(10));

    let heap_value = h
        .read_map_value(map_ref, AnyValue::atom(key_atom))
        .expect("present atom key");
    assert_eq!(heap_value.list_addr(), Ok(child_addr));

    assert_eq!(h.read_map_value(map_ref, AnyValue::atom(missing_atom)), None);
}

#[test]
fn any_value_ref_struct_reads_scalar_and_heap_fields() {
    let reg = fresh_registry();
    let schema_id = reg.borrow_mut().register(Schema::tuple_of_arity(2));
    let mut h = Heap::new(SIZE_TABLE[0], reg);
    let child_bits = h.alloc_list_cons_slot(AnyValue::atom(1), EMPTY_LIST_BITS);
    let child_addr = list_addr_from_tagged(child_bits).expect("child addr");
    let obj = h.alloc_struct(schema_id);
    unsafe { h.write_field_slot(obj, 0, AnyValue::float(2.5)) };
    unsafe { h.write_field_slot(obj, 8, AnyValue::heap_ptr(child_addr, ValueKind::LIST)) };
    let obj_ref = AnyValueRef::from_heap_object(ValueKind::STRUCT, obj).expect("struct ref");

    assert_eq!(h.read_struct_field_ref(obj_ref, 0).unwrap().load_float(), Ok(2.5));
    assert_eq!(h.read_struct_field_ref(obj_ref, 8).unwrap().list_addr(), Ok(child_addr));
}

#[test]
fn any_value_ref_closure_capture_reads_are_ported() {
    let reg = fresh_registry();
    let mut h = Heap::new(SIZE_TABLE[0], reg);
    let child_bits = h.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
    let child_addr = map_addr_from_tagged(child_bits).expect("child addr");
    let closure_bits = h.alloc_closure(
        crate::any_value::ClosureDenotationId::user(0),
        0,
        2,
        0,
        0xfeed,
        &[AnyValue::atom(7), AnyValue::heap_ptr(child_addr, ValueKind::MAP)],
    );
    let closure_addr = closure_addr_from_tagged(closure_bits).expect("closure addr");
    let closure_ref = AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure_addr).expect("closure ref");

    assert_eq!(h.read_closure_capture_ref(closure_ref, 0).unwrap().load_atom(), Ok(7));
    assert_eq!(
        h.read_closure_capture_ref(closure_ref, 1).unwrap().map_addr(),
        Ok(child_addr)
    );
}

#[test]
fn typed_list_construction_writes_scalar_head_and_heap_tail() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let tail_bits = h.alloc_list_cons_slot(AnyValue::atom(1), EMPTY_LIST_BITS);
    let tail_addr = list_addr_from_tagged(tail_bits).expect("tail addr");
    let tail_ref = AnyValueRef::from_heap_object(ValueKind::LIST, tail_addr).expect("tail ref");

    let list_ref = h.alloc_list_cons_int(42, tail_ref).expect("list ref");

    assert_eq!(h.read_list_head_ref(list_ref).unwrap().load_int(), Ok(42));
    assert_eq!(h.read_list_tail_ref(list_ref).unwrap().list_addr(), Ok(tail_addr));
}

#[test]
#[should_panic(expected = "alloc_list_cons_ref head requires a heap/sentinel ref; use the typed scalar write path")]
fn list_ref_construction_rejects_scalar_head() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let head_slot = 42u64;
    let head_ref = AnyValueRef::from_scalar_slot(ValueKind::INT, &head_slot).expect("head ref");

    let _ = h.alloc_list_cons_ref(head_ref, AnyValueRef::empty_list());
}

#[test]
fn any_value_ref_list_construction_rejects_non_list_tail() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let head_bits = h.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
    let head_addr = map_addr_from_tagged(head_bits).expect("head addr");
    let tail_slot = 2u64;
    let head_ref = AnyValueRef::from_heap_object(ValueKind::MAP, head_addr).expect("head ref");
    let tail_ref = AnyValueRef::from_scalar_slot(ValueKind::INT, &tail_slot).expect("tail ref");

    assert_eq!(
        h.alloc_list_cons_ref(head_ref, tail_ref),
        Err(AnyValueRefError::ExpectedTag {
            expected: ValueKind::LIST,
            found: ValueKind::INT
        })
    );
}

#[test]
fn any_value_ref_map_construction_and_put_write_scalar_and_heap_values() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let child_atom = h.node.intern_atom("child");
    let key_atom = h.node.intern_atom("key");
    let child_bits = h.alloc_list_cons_slot(AnyValue::atom(child_atom), EMPTY_LIST_BITS);
    let child_addr = list_addr_from_tagged(child_bits).expect("child addr");
    let child_ref = AnyValueRef::from_heap_object(ValueKind::LIST, child_addr).expect("child ref");
    let int_key_slot = 1u64;
    let int_any_value = 10u64;
    let int_key = AnyValueRef::from_scalar_slot(ValueKind::INT, &int_key_slot).expect("int key");

    let map_ref = h
        .alloc_map_refs(&[(
            int_key,
            AnyValueRef::from_scalar_slot(ValueKind::INT, &int_any_value).expect("int value"),
        )])
        .expect("map ref");
    assert_eq!(
        h.read_map_value(map_ref, AnyValue::int(1)).expect("int key").load_int(),
        Ok(10)
    );

    let map_ref = h.map_put_slot(
        map_ref,
        AnyValue::atom(key_atom),
        AnyValue::from_ref(child_ref).expect("child value"),
    );
    assert_eq!(
        h.read_map_value(map_ref, AnyValue::atom(key_atom))
            .expect("atom key")
            .list_addr(),
        Ok(child_addr)
    );

    let map_ref = h.map_put_slot(map_ref, AnyValue::int(1), AnyValue::int(11));
    assert_eq!(
        h.read_map_value(map_ref, AnyValue::int(1)).expect("int key").load_int(),
        Ok(11)
    );
}

#[test]
fn any_value_ref_struct_and_closure_writes_store_scalar_and_heap_values() {
    let reg = fresh_registry();
    let struct_schema = reg.borrow_mut().register(Schema::tuple_of_arity(2));
    let mut h = Heap::new(SIZE_TABLE[0], reg);
    let child_bits = h.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
    let child_addr = map_addr_from_tagged(child_bits).expect("child addr");
    let child_ref = AnyValueRef::from_heap_object(ValueKind::MAP, child_addr).expect("child ref");
    let scalar_ref = AnyValueRef::atom(99);

    let struct_addr = h.alloc_struct(struct_schema);
    let struct_ref = AnyValueRef::from_heap_object(ValueKind::STRUCT, struct_addr).expect("struct ref");
    let pair = SlotLayout::of(2);
    unsafe {
        h.store_struct_field(
            struct_addr,
            SlotLayout::slot_offset(0),
            pair.kind_offset(0),
            AnyValue::from_ref(scalar_ref).expect("value"),
        )
    }
    .expect("write scalar field");
    unsafe {
        h.store_struct_field(
            struct_addr,
            SlotLayout::slot_offset(1),
            pair.kind_offset(1),
            AnyValue::from_ref(child_ref).expect("value"),
        )
    }
    .expect("write heap field");
    assert_eq!(h.read_struct_field_ref(struct_ref, 0).unwrap().load_atom(), Ok(99));
    assert_eq!(
        h.read_struct_field_ref(struct_ref, 8).unwrap().map_addr(),
        Ok(child_addr)
    );

    let closure_bits = h.alloc_closure_slots(crate::any_value::ClosureDenotationId::user(0), 0, 2, 0);
    let closure_addr = closure_addr_from_tagged(closure_bits).expect("closure addr");
    let closure_ref = AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure_addr).expect("closure ref");
    unsafe {
        h.write_closure_capture_value(
            closure_ref.closure_addr().expect("closure addr"),
            0,
            AnyValue::from_ref(scalar_ref).expect("value"),
        )
    };
    unsafe {
        h.write_closure_capture_value(
            closure_ref.closure_addr().expect("closure addr"),
            1,
            AnyValue::from_ref(child_ref).expect("value"),
        )
    };
    assert_eq!(h.read_closure_capture_ref(closure_ref, 0).unwrap().load_atom(), Ok(99));
    assert_eq!(
        h.read_closure_capture_ref(closure_ref, 1).unwrap().map_addr(),
        Ok(child_addr)
    );
}

#[test]
fn any_value_ref_heap_writes_are_traced_by_gc() {
    let reg = fresh_registry();
    let struct_schema = reg.borrow_mut().register(Schema::tuple_of_arity(1));
    let mut h = Heap::new(SIZE_TABLE[0], reg);
    let key_slot = 1u64;
    let key_ref = AnyValueRef::from_scalar_slot(ValueKind::INT, &key_slot).expect("key ref");

    let child_map_bits = h.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
    let child_map_addr = map_addr_from_tagged(child_map_bits).expect("child map addr");
    let child_map_ref = AnyValueRef::from_heap_object(ValueKind::MAP, child_map_addr).expect("child map ref");
    let list_ref = h
        .alloc_list_cons_ref(child_map_ref, AnyValueRef::empty_list())
        .expect("list ref");

    let child_list_bits = h.alloc_list_cons_slot(AnyValue::atom(3), EMPTY_LIST_BITS);
    let child_list_addr = list_addr_from_tagged(child_list_bits).expect("child list addr");
    let child_list_ref = AnyValueRef::from_heap_object(ValueKind::LIST, child_list_addr).expect("child list ref");
    let map_ref = h.alloc_map_refs(&[(key_ref, child_list_ref)]).expect("map ref");

    let struct_addr = h.alloc_struct(struct_schema);
    let struct_ref = AnyValueRef::from_heap_object(ValueKind::STRUCT, struct_addr).expect("struct ref");
    let single = SlotLayout::of(1);
    unsafe {
        h.store_struct_field(
            struct_addr,
            SlotLayout::slot_offset(0),
            single.kind_offset(0),
            AnyValue::from_ref(child_list_ref).expect("value"),
        )
    }
    .expect("write struct field");

    let closure_bits = h.alloc_closure_slots(crate::any_value::ClosureDenotationId::user(0), 0, 1, 0);
    let closure_addr = closure_addr_from_tagged(closure_bits).expect("closure addr");
    let closure_ref = AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure_addr).expect("closure ref");
    unsafe {
        h.write_closure_capture_value(
            closure_ref.closure_addr().expect("closure addr"),
            0,
            AnyValue::from_ref(child_map_ref).expect("value"),
        )
    };
    let mut roots = [list_ref, map_ref, struct_ref, closure_ref];

    h.collect_stats(&mut roots);

    let [moved_list_ref, moved_map_ref, moved_struct_ref, moved_closure_ref] = roots;
    let moved_list_head = h.read_list_head_ref(moved_list_ref).unwrap().map_addr();

    let moved_map_value = h
        .read_map_value(moved_map_ref, AnyValue::from_ref(key_ref).unwrap())
        .expect("map value")
        .list_addr();

    let moved_struct_field = h.read_struct_field_ref(moved_struct_ref, 0).unwrap().list_addr();

    let moved_closure_capture = h.read_closure_capture_ref(moved_closure_ref, 0).unwrap().map_addr();

    assert_eq!(moved_list_head, moved_closure_capture);
    assert_eq!(moved_map_value, moved_struct_field);
}

#[test]
#[should_panic(expected = "one schema identity must have one layout")]
fn schema_identity_cannot_silently_replace_its_published_layout() {
    let mut registry = SchemaRegistry::new();
    let name = crate::module_name::ModuleName::from_segments(vec!["Item".into()]);
    registry.register(Schema::named_struct(name.clone(), ["value".into()]));
    registry.register(Schema::named_struct(name, ["value".into(), "extra".into()]));
}

#[test]
fn schema_registry_register_and_get() {
    let mut reg = SchemaRegistry::new();
    let first_free_id = reg.len() as u32;
    let id_a = reg.register(Schema {
        identity: SchemaIdentity::Internal("A".into()),
        size: 0,
        fields: vec![],
    });
    let id_b = reg.register(Schema {
        identity: SchemaIdentity::Internal("Pair".into()),
        size: 16,
        fields: vec![
            FieldDescriptor {
                offset: 0,
                kind: FieldKind::AnyValue,
                name: None,
            },
            FieldDescriptor {
                offset: 8,
                kind: FieldKind::AnyValue,
                name: None,
            },
        ],
    });
    assert_eq!(id_a, first_free_id);
    assert_eq!(id_b, first_free_id + 1);
    assert_eq!(reg.get(id_a).identity.display_name(), "A");
    assert_eq!(reg.get(id_b).identity.display_name(), "Pair");
}

/// Every strict inline Bitstring allocation reserves
/// at least one zero byte past its payload at offset
/// `bytes_ptr + ceil(bit_len/8)`. Mirrors the SharedBin invariant covered
/// by bits.rs::shared_bin_alloc_has_trailing_nul.
#[test]
fn alloc_bitstring_inline_has_trailing_nul() {
    let mut h = Heap::new(1024, fresh_registry());
    // Cover lengths around the 16-byte-alignment boundary so the
    // formerly-zero pad cases get exercised.
    for n in [0usize, 1, 7, 8, 9, 15, 16, 17, 24, 25] {
        let bytes: Vec<u8> = (0..n).map(|i| (i as u8) ^ 0xff).collect();
        let bit_len = (n as u64) * 8;
        let p = h.alloc_bitstring(&bytes, bit_len).heap_addr().expect("bitstring");
        unsafe {
            assert_eq!(crate::any_value::bitstring_bit_len(p), bit_len);
            assert_eq!(
                bitstring_size_for_bit_len(bit_len),
                object_size(heap_object_word(p, ValueKind::BITSTRING))
            );
            let payload = bitstring_bytes_ptr(p);
            for (i, expected) in bytes.iter().enumerate().take(n) {
                assert_eq!(*payload.add(i), *expected, "payload byte {} at len {}", i, n);
            }
            assert_eq!(*payload.add(n), 0, "trailing NUL at offset {} for payload len {}", n, n);
        }
    }
}

#[test]
fn alloc_bumps_and_tracks() {
    let mut h = Heap::new(1024, fresh_registry());
    let p = h.alloc_list_cons_slot(AnyValue::int(1), EMPTY_LIST);
    assert!(list_addr_from_tagged(p).is_some());
    assert_eq!(h.node.alloc_stats().total.allocs, 1);
    assert_eq!(h.bytes_used(), 16);
}

#[test]
fn heap_pointers_are_16_aligned() {
    let mut h = Heap::new(1024, fresh_registry());
    for _ in 0..10 {
        let p = h.alloc_list_cons_slot(AnyValue::nil_atom(), EMPTY_LIST);
        let addr = list_addr_from_tagged(p).expect("tagged list ptr");
        assert_eq!((addr as usize) & 15, 0);
    }
}

/// Bump overflow triggers a grow at the next capacity. Old block is
/// abandoned; new block holds further allocations. `bytes_used`
/// covers both. The next gc() returns both blocks to the pool.
#[test]
fn alloc_grows_to_next_capacity_on_overflow() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    // SIZE_TABLE[0] = 1024 bytes -> 64 headerless cons cells fit exactly.
    // Allocate 80 to force grow.
    let initial_block = h.block_start;
    let initial_capacity = h.block_size;
    for _ in 0..80 {
        let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), EMPTY_LIST);
    }
    assert_ne!(h.block_start, initial_block, "grow must move block_start");
    assert!(h.block_size > initial_capacity, "grow must raise the capacity");
    assert_eq!(h.block_size, next_block_capacity(initial_capacity));
    assert!(!h.young_blocks.is_empty());
    assert_eq!(h.node.alloc_stats().total.allocs, 80);
}

/// `should_gc` is a function of the heap's state: it turns true once the
/// bytes allocated reach the budget floor while nothing is live, and a collection that reclaims them turns
/// it false again with nothing cleared in between.
#[test]
fn should_gc_follows_bytes_in_use_against_the_budget_floor_and_a_collection_answers_it() {
    let cells_in_floor = 4096 / 16;
    let mut h = Heap::new(1024, fresh_registry());
    assert!(!h.should_gc());
    for _ in 0..cells_in_floor - 1 {
        let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), EMPTY_LIST);
    }
    assert!(!h.should_gc(), "one cell under the 4096-byte floor");
    let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), EMPTY_LIST);
    assert!(h.should_gc(), "256 cells at 4096 bytes reach the floor");

    let mut root: *mut u8 = null_mut();
    h.collect_tagged(&mut root);
    assert!(!h.should_gc(), "nothing was live, so nothing is due");

    for _ in 0..cells_in_floor {
        let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), EMPTY_LIST);
    }
    assert!(
        h.should_gc(),
        "enough allocation after the collection makes it due again"
    );
}

/// With a null root, Cheney recycles the arena: from-space is freed,
/// to-space is a fresh empty block, no object is kept.
#[test]
fn gc_with_null_root_recycles_arena() {
    let mut h = Heap::new(1024, fresh_registry());
    let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), EMPTY_LIST);
    let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), EMPTY_LIST);
    assert_eq!(h.node.alloc_stats().total.allocs, 2);
    let mut root: *mut u8 = null_mut();
    h.collect_tagged(&mut root);
    assert_eq!(h.gc_run_count, 1);
    assert_eq!(h.old_objects, 0, "no root → nothing copied");
    assert_eq!(h.bytes_used(), 0, "to-space is empty");
    assert!(root.is_null());
}

/// A rooted list survives Cheney: every cell is copied to to-space,
/// the root pointer is rewritten to the new head, and from-space is
/// freed. Live count matches the chain length.
#[test]
fn gc_copies_rooted_list_and_rewrites_root() {
    let mut h = Heap::new(1024, fresh_registry());
    // Build [1, 2, 3] — head ptr is n1.
    let n3 = alloc_int_list_cons(&mut h, 3, EMPTY_LIST);
    let n2 = alloc_int_list_cons(&mut h, 2, n3);
    let n1 = alloc_int_list_cons(&mut h, 1, n2);
    let mut roots = [heap_ref(n1)];
    let old_n1 = n1 as usize;
    h.collect_stats(&mut roots);
    let root_ptr = list_addr_from_tagged(ref_bits(roots[0])).unwrap();
    assert_ne!(root_ptr as usize, old_n1, "root should be rewritten to to-space");
    assert_eq!(h.old_objects, 3, "all three cells copied");
    // Walk the new list and verify integers match.
    let mut cur = root_ptr as *mut ListCons;
    let mut sum = 0i64;
    let mut count = 0;
    while !cur.is_null() {
        let cons = unsafe { &*cur };
        sum += cons.head as i64;
        count += 1;
        cur = if cons.tail_cell_addr() == 0 {
            null_mut()
        } else {
            cons.tail_cell_addr() as *mut ListCons
        };
    }
    assert_eq!(count, 3);
    assert_eq!(sum, 6);
}

#[test]
fn gc_preserves_list_alias_metadata() {
    let mut h = Heap::new(1024, fresh_registry());
    let n2 = alloc_int_list_cons(&mut h, 2, EMPTY_LIST);
    let n1 = alloc_int_list_cons(&mut h, 1, n2);
    let n2_ref = list_ref_from_bits(n2);
    h.mark_published_ref_aliased(n2_ref).expect("mark aliased");
    let mut roots = [heap_ref(n1)];
    h.collect_stats(&mut roots);

    let copied_n1 = list_addr_from_tagged(ref_bits(roots[0])).unwrap();
    let copied_n1 = unsafe { &*(copied_n1 as *const ListCons) };
    let copied_n2 = unsafe { &*(copied_n1.tail_cell_addr() as *const ListCons) };
    assert!(copied_n2.aliased());
    assert_eq!(copied_n2.head as i64, 2);
}

/// A collection keeps what is reachable, and what it keeps is old. An old cell
/// must never come to point at a value made after the collection, so a kept
/// cell answers a changed rebuild with a fresh cell even when the compiler
/// granted rewrite permission.
#[test]
fn a_list_cell_a_collection_kept_is_not_rewritten_in_place() {
    let mut h = Heap::new(1024, fresh_registry());
    let tail = alloc_int_list_cons(&mut h, 2, EMPTY_LIST);
    let source = alloc_int_list_cons(&mut h, 1, tail);
    let mut roots = [heap_ref(source)];
    h.collect_stats(&mut roots);
    let kept = roots[0];
    let before = h.node.alloc_stats().list_cons.allocs;

    let rebuilt = h
        .reuse_or_alloc_list_cons_raw_kind(kept, 1, ValueKind::INT, AnyValue::EmptyList, true)
        .expect("rebuild");

    assert_ne!(rebuilt, kept);
    assert_eq!(h.node.alloc_stats().list_cons.allocs, before + 1);
    let kept_cell = unsafe { &*(kept.list_addr().unwrap() as *const ListCons) };
    assert_ne!(kept_cell.tail_cell_addr(), 0, "the kept cell still has its tail");
}

#[test]
fn published_ref_alias_marking_marks_every_reachable_list_cons() {
    let mut h = Heap::new(1024, fresh_registry());
    let n3 = alloc_int_list_cons(&mut h, 3, EMPTY_LIST);
    let n2 = alloc_int_list_cons(&mut h, 2, n3);
    let n1 = alloc_int_list_cons(&mut h, 1, n2);

    let out = h
        .mark_published_ref_aliased(list_ref_from_bits(n1))
        .expect("mark published list");

    assert_eq!(out, list_ref_from_bits(n1));
    for bits in [n1, n2, n3] {
        let cons = unsafe { &*(list_addr_from_tagged(bits).unwrap() as *const ListCons) };
        assert!(cons.aliased(), "cons {bits:#x} should be aliased");
    }
}

#[test]
fn shared_spine_publication_visits_only_newly_protected_cells() {
    let mut heap = Heap::new(1024, fresh_registry());
    let tail = alloc_int_list_cons(&mut heap, 3, EMPTY_LIST);
    let middle = alloc_int_list_cons(&mut heap, 2, tail);
    let head = alloc_int_list_cons(&mut heap, 1, middle);

    assert_eq!(heap.share(list_ref_from_bits(middle)).unwrap(), 2);
    assert_eq!(heap.share(list_ref_from_bits(head)).unwrap(), 1);
    assert_eq!(heap.share(list_ref_from_bits(head)).unwrap(), 0);
    assert_eq!(heap.share(list_ref_from_bits(tail)).unwrap(), 0);
    for bits in [head, middle, tail] {
        let cons = unsafe { &*(list_addr_from_tagged(bits).unwrap() as *const ListCons) };
        assert!(cons.aliased());
    }
}

#[test]
fn published_ref_alias_marking_ignores_non_list_refs_and_empty_list() {
    let mut h = Heap::new(1024, fresh_registry());
    let scalar = 42u64;
    let int_ref = AnyValueRef::from_scalar_slot(ValueKind::INT, &scalar).expect("int ref");

    assert_eq!(h.mark_published_ref_aliased(int_ref).expect("mark int"), int_ref);
    assert_eq!(
        h.mark_published_ref_aliased(AnyValueRef::empty_list())
            .expect("mark empty list"),
        AnyValueRef::empty_list()
    );
}

#[test]
fn unchanged_list_retention_needs_no_rewrite_permission_even_when_published() {
    let mut heap = Heap::new(1024, fresh_registry());
    let tail = alloc_int_list_cons(&mut heap, 2, EMPTY_LIST);
    let source = alloc_int_list_cons(&mut heap, 1, tail);
    let source_ref = list_ref_from_bits(source);
    heap.mark_published_ref_aliased(source_ref).unwrap();
    let before = heap.node.alloc_stats().list_cons.allocs;
    let retained = heap
        .reuse_or_alloc_list_cons_raw_kind(source_ref, 1, ValueKind::INT, list_value(tail), false)
        .unwrap();
    assert_eq!(retained, source_ref);
    assert_eq!(heap.node.alloc_stats().list_cons.allocs, before);
}

#[test]
fn retained_unaliased_source_without_permission_allocates_for_changed_contents() {
    let mut heap = Heap::new(1024, fresh_registry());
    let source = alloc_int_list_cons(&mut heap, 1, EMPTY_LIST);
    let source_ref = list_ref_from_bits(source);
    let before = heap.node.alloc_stats().list_cons.allocs;
    let rebuilt = heap
        .reuse_or_alloc_list_cons_raw_kind(source_ref, 9, ValueKind::INT, AnyValue::EmptyList, false)
        .unwrap();
    assert_ne!(rebuilt, source_ref);
    assert_eq!(heap.node.alloc_stats().list_cons.allocs, before + 1);
    let original = unsafe { &*(source_ref.list_addr().unwrap() as *const ListCons) };
    assert_eq!(original.head, 1);
}

#[test]
fn unaliased_reuse_or_alloc_rewrites_cons_in_place() {
    let mut h = Heap::new(1024, fresh_registry());

    let old_tail = alloc_int_list_cons(&mut h, 1, EMPTY_LIST);
    let new_tail = alloc_int_list_cons(&mut h, 2, EMPTY_LIST);
    let head = alloc_int_list_cons(&mut h, 0, old_tail);
    let before = h.node.alloc_stats().list_cons.allocs;

    let out = h
        .reuse_or_alloc_list_cons_raw_kind(list_ref_from_bits(head), 7, ValueKind::ATOM, list_value(new_tail), true)
        .expect("reuse");

    assert_eq!(out, list_ref_from_bits(head));
    assert_eq!(h.node.alloc_stats().list_cons.allocs, before);
    let cons = unsafe { &*(list_addr_from_tagged(head).unwrap() as *const ListCons) };
    assert_eq!(cons.head as i64, 7);
    assert_eq!(cons.head_kind(), ValueKind::ATOM);
    assert_eq!(cons.tail(), proper(new_tail));
    assert!(!cons.aliased());
}

#[test]
fn aliased_reuse_or_alloc_allocates_fresh_cons_without_mutating_original() {
    let mut h = Heap::new(1024, fresh_registry());
    let old_tail = alloc_int_list_cons(&mut h, 1, EMPTY_LIST);
    let new_tail = alloc_int_list_cons(&mut h, 2, EMPTY_LIST);
    let head = alloc_int_list_cons(&mut h, 0, old_tail);
    let head_ref = list_ref_from_bits(head);
    h.mark_published_ref_aliased(head_ref).expect("mark aliased");
    let before = h.node.alloc_stats().list_cons.allocs;

    let out = h
        .reuse_or_alloc_list_cons_raw_kind(head_ref, 9, ValueKind::FLOAT, list_value(new_tail), true)
        .expect("fallback allocation");

    assert_ne!(out, head_ref);
    assert_eq!(h.node.alloc_stats().list_cons.allocs, before + 1);
    let original = unsafe { &*(list_addr_from_tagged(head).unwrap() as *const ListCons) };
    assert_eq!(original.head as i64, 0);
    assert_eq!(original.head_kind(), ValueKind::INT);
    assert_eq!(original.tail(), proper(old_tail));
    assert!(original.aliased());
    let fresh = unsafe { &*(out.list_addr().expect("fresh list addr") as *const ListCons) };
    assert_eq!(fresh.head as i64, 9);
    assert_eq!(fresh.head_kind(), ValueKind::FLOAT);
    assert_eq!(fresh.tail(), proper(new_tail));
    assert!(!fresh.aliased());
}

#[test]
fn published_reuse_or_alloc_allocates_fresh_cons_without_mutating_original() {
    let mut h = Heap::new(1024, fresh_registry());
    let old_tail = alloc_int_list_cons(&mut h, 1, EMPTY_LIST);
    let new_tail = alloc_int_list_cons(&mut h, 2, EMPTY_LIST);
    let head = alloc_int_list_cons(&mut h, 0, old_tail);
    let head_ref = list_ref_from_bits(head);
    h.mark_published_ref_aliased(head_ref).expect("publish");
    let before = h.node.alloc_stats().list_cons.allocs;

    let out = h
        .reuse_or_alloc_list_cons_raw_kind(head_ref, 42, ValueKind::INT, list_value(new_tail), true)
        .expect("fallback allocation");

    assert_ne!(out, head_ref);
    assert_eq!(h.node.alloc_stats().list_cons.allocs, before + 1);
    let original = unsafe { &*(list_addr_from_tagged(head).unwrap() as *const ListCons) };
    assert_eq!(original.head as i64, 0);
    assert_eq!(original.tail(), proper(old_tail));
    assert!(original.aliased());
    let fresh = unsafe { &*(out.list_addr().expect("fresh list addr") as *const ListCons) };
    assert_eq!(fresh.head as i64, 42);
    assert_eq!(fresh.head_kind(), ValueKind::INT);
    assert_eq!(fresh.tail(), proper(new_tail));
    assert!(!fresh.aliased());
}

#[test]
fn any_value_ref_root_gc_forwards_heap_ref() {
    let mut h = Heap::new(1024, fresh_registry());
    let list_bits = alloc_int_list_cons(&mut h, 1, EMPTY_LIST);
    let old_list = list_addr_from_tagged(list_bits).unwrap();
    let mut roots = [AnyValueRef::from_heap_object(ValueKind::LIST, old_list).expect("list ref")];

    let stats = h.collect_stats(&mut roots);

    let new_list = roots[0].list_addr().expect("forwarded list ref");
    assert_ne!(new_list, old_list);
    let head = unsafe { (*(new_list as *const ListCons)).head_value() };
    assert_eq!(head, AnyValue::int(1));
    assert_eq!(stats.copied_objects, 1);
    assert_eq!(stats.copied_bytes, 16);
}

#[test]
fn any_value_ref_root_gc_copies_scalar_box_without_tracing_payload() {
    let mut h = Heap::new(1024, fresh_registry());
    let decoy_bits = alloc_int_list_cons(&mut h, 99, EMPTY_LIST);
    let decoy_addr = list_addr_from_tagged(decoy_bits).unwrap();
    let scalar = h.alloc(8);
    unsafe {
        write(scalar as *mut u64, decoy_addr as u64);
    }
    let mut roots = [AnyValueRef::from_scalar_slot(ValueKind::INT, scalar as *const u64).expect("scalar root ref")];

    let stats = h.collect_stats(&mut roots);

    assert_ne!(roots[0].storage_addr(), scalar);
    assert_eq!(roots[0].load_int().unwrap(), decoy_addr as i64);
    assert_eq!(stats.copied_objects, 1);
    assert_eq!(stats.copied_bytes, 16);
}

#[test]
fn any_value_ref_root_gc_preserves_tagged_literal_scalar_ref() {
    static STATIC_INT: u64 = 42;
    let mut h = Heap::new(1024, fresh_registry());
    let original = AnyValueRef::from_scalar_slot(ValueKind::INT, &STATIC_INT)
        .expect("static scalar ref")
        .literal();
    let mut roots = [original];

    let stats = h.collect_stats(&mut roots);

    assert_eq!(roots[0], original);
    assert_eq!(roots[0].load_int().unwrap(), 42);
    assert_eq!(stats.copied_objects, 0);
}

#[test]
fn gc_stats_prove_scalar_list_head_is_copied_but_not_traced() {
    let mut h = Heap::new(1024, fresh_registry());
    let decoy_bits = alloc_int_list_cons(&mut h, 99, EMPTY_LIST);
    let decoy_addr = list_addr_from_tagged(decoy_bits).unwrap();
    let live_bits = h.alloc_list_cons_slot(any_value(decoy_addr as u64, ValueKind::INT), EMPTY_LIST);
    let mut roots = [heap_ref(live_bits)];

    let stats = h.collect_stats(&mut roots);

    assert_eq!(stats.copied_objects, 1);
    assert_eq!(stats.copied_bytes, 16);
    assert_eq!(stats.live_objects, 1);
    let moved = list_addr_from_tagged(ref_bits(roots[0])).expect("moved live list");
    let moved_head = unsafe { (*(moved as *const ListCons)).head_value() };
    assert_eq!(moved_head.kind(), ValueKind::INT);
    assert_eq!(moved_head.raw(), decoy_addr as u64);
}

#[test]
fn a_struct_collection_moves_heap_fields_and_leaves_scalar_fields() {
    let reg = fresh_registry();
    let schema_id = reg.borrow_mut().register(Schema::tuple_of_arity(2));
    let mut h = Heap::new(1024, reg);
    let decoy_bits = alloc_int_list_cons(&mut h, 1, EMPTY_LIST);
    let decoy_addr = list_addr_from_tagged(decoy_bits).unwrap();
    let child_bits = alloc_int_list_cons(&mut h, 2, EMPTY_LIST);
    let child_addr = list_addr_from_tagged(child_bits).unwrap();
    let tuple = h.alloc_struct(schema_id);
    unsafe { h.write_field_slot(tuple, 0, any_value(decoy_addr as u64, ValueKind::INT)) };
    unsafe { h.write_field_slot(tuple, 8, AnyValue::heap_ptr(child_addr, ValueKind::LIST)) };
    let mut root = heap_object_word(tuple, ValueKind::STRUCT) as *mut u8;

    let stats = h.collect_tagged(&mut root);

    assert_eq!(stats.copied_objects, 2);
    assert_eq!(h.old_objects, 2);
    let moved = struct_addr_from_tagged(root as u64).expect("moved struct");
    assert_eq!(h.read_field_slot(moved, 0).raw(), decoy_addr as u64);
    assert_ne!(h.read_field_slot(moved, 8).raw() as *mut u8, child_addr);
}

/// A tuple and a named struct on one heap, each as a root, with the bit each
/// header should carry.
fn named_and_anonymous_structs(source: &mut Heap) -> [(u64, bool); 2] {
    let reg = source.schemas.clone();
    let tuple_schema = reg.borrow_mut().register(Schema::tuple_of_arity(1));
    let record_schema = reg.borrow_mut().register(Schema::named_struct(
        ModuleName::from_segments(vec!["Point".into()]),
        ["x".to_string()],
    ));
    [(tuple_schema, false), (record_schema, true)].map(|(schema, named)| {
        let object = source.alloc_struct(schema);
        (heap_object_word(object, ValueKind::STRUCT), named)
    })
}

fn named_bit(value: AnyValueRef) -> bool {
    unsafe { struct_is_named(value.struct_addr().expect("a struct")) }
}

fn header_of(value: AnyValueRef) -> u64 {
    unsafe { read(value.struct_addr().expect("a struct") as *const u64) }
}

#[test]
fn a_struct_header_names_whether_its_schema_is_a_named_struct() {
    let mut h = Heap::new(1024, fresh_registry());
    for (bits, named) in named_and_anonymous_structs(&mut h) {
        let value = heap_ref(bits);
        assert_eq!(named_bit(value), named);
        assert_eq!(header_of(value) & STRUCT_HEADER_NAMED_MASK != 0, named);
        assert_eq!(header_of(value) & 0xf, 0, "the forwarding nibble stays clear");
    }
}

#[test]
fn a_struct_keeps_its_named_bit_through_a_collection() {
    let mut h = Heap::new(1024, fresh_registry());
    let structs = named_and_anonymous_structs(&mut h);
    let mut roots = structs.map(|(bits, _)| heap_ref(bits));
    h.collect_stats(&mut roots);
    for (moved, (_, named)) in roots.into_iter().zip(structs) {
        assert_eq!(named_bit(moved), named);
    }
}

#[test]
fn a_struct_keeps_its_named_bit_through_a_deep_copy() {
    let mut source = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut destination = Heap::new(SIZE_TABLE[0], source.schemas.clone());
    for (bits, named) in named_and_anonymous_structs(&mut source) {
        let copied = deep_copy_slot(heap_root(bits), &source.view(), &mut destination);
        assert_eq!(named_bit(copied.ref_word()), named);
    }
}

#[test]
fn a_map_and_closure_collection_moves_heap_slots_and_leaves_scalar_slots() {
    let mut h = Heap::new(1024, fresh_registry());
    let map_child_bits = alloc_int_list_cons(&mut h, 3, EMPTY_LIST);
    let map_child_addr = list_addr_from_tagged(map_child_bits).unwrap();
    let closure_child_bits = alloc_int_list_cons(&mut h, 4, EMPTY_LIST);
    let closure_child_addr = list_addr_from_tagged(closure_child_bits).unwrap();
    let map_bits = h.alloc_map_slots(&[(AnyValue::atom(7), AnyValue::heap_ptr(map_child_addr, ValueKind::LIST))]);
    let closure_bits = h.alloc_closure(
        crate::any_value::ClosureDenotationId::user(0),
        0,
        2,
        0,
        0,
        &[
            AnyValue::int(5),
            AnyValue::heap_ptr(closure_child_addr, ValueKind::LIST),
        ],
    );
    let mut roots = [heap_ref(map_bits), heap_ref(closure_bits)];

    let stats = h.collect_stats(&mut roots);

    assert_eq!(stats.copied_objects, 4);
    let moved_map = map_addr_from_tagged(ref_bits(roots[0])).unwrap();
    let moved_closure = closure_addr_from_tagged(ref_bits(roots[1])).unwrap();
    let (_, moved_map_value) = unsafe { map_entry(moved_map, 0) };
    let moved_capture = unsafe { closure_capture_value(moved_closure, 1) };
    assert_ne!(moved_map_value.raw() as *mut u8, map_child_addr);
    assert_ne!(moved_capture.raw() as *mut u8, closure_child_addr);
}

/// The one entry forwards every kind of root in one call: a closure
/// (with what it captures) and a message waiting in a mailbox.
#[test]
fn collect_forwards_a_closure_root_and_a_mailbox_root_together() {
    let mut h = Heap::new(1024, fresh_registry());
    let captured_bits = alloc_int_list_cons(&mut h, 10, EMPTY_LIST);
    let mailbox_bits = alloc_int_list_cons(&mut h, 20, EMPTY_LIST);
    let closure_bits = h.alloc_closure_slots(crate::any_value::ClosureDenotationId::user(0), 0, 1, 0);
    let old_closure = closure_addr_from_tagged(closure_bits).unwrap();
    let old_capture = list_addr_from_tagged(captured_bits).unwrap();
    let old_mailbox = list_addr_from_tagged(mailbox_bits).unwrap();
    unsafe {
        closure_capture_set(
            old_closure,
            0,
            AnyValue::decode_tagged_heap_bits(captured_bits).unwrap(),
        );
    }
    let mut roots = [heap_ref(closure_bits), heap_ref(mailbox_bits)];

    let stats = h.collect_stats(&mut roots);

    let new_closure = roots[0].closure_addr().unwrap();
    assert_ne!(new_closure, old_closure);
    let new_capture = unsafe { closure_capture_value(new_closure, 0) };
    assert_ne!(new_capture.raw() as *mut u8, old_capture);
    assert_ne!(roots[1].list_addr().unwrap(), old_mailbox);
    assert_eq!(
        stats.copied_objects, 3,
        "the closure, what it captures, and the mailbox message"
    );
}

/// Cheney drops unreachable objects: a cell allocated alongside the
/// root chain but not pointed to by it is discarded. Only the
/// chain is kept.
#[test]
fn gc_drops_unreachable_objects() {
    let mut h = Heap::new(1024, fresh_registry());
    let _orphan = alloc_int_list_cons(&mut h, 99, EMPTY_LIST);
    let kept = alloc_int_list_cons(&mut h, 7, EMPTY_LIST);
    assert_eq!(h.node.alloc_stats().total.allocs, 2);
    let mut roots = [heap_ref(kept)];
    h.collect_stats(&mut roots);
    assert_eq!(h.old_objects, 1, "orphan dropped, kept survives");
    let new_cons = list_addr_from_tagged(ref_bits(roots[0])).unwrap() as *mut ListCons;
    let head = unsafe { (*new_cons).head };
    assert_eq!(head as i64, 7);
}

#[test]
fn list_head_can_be_a_tagged_list_without_int_collision() {
    let mut h = Heap::new(1024, fresh_registry());
    let child_bits = alloc_int_list_cons(&mut h, 7, EMPTY_LIST);
    let parent_bits = h.alloc_list_cons_slot(heap_root(child_bits), EMPTY_LIST);
    let parent = list_addr_from_tagged(parent_bits).expect("parent list ptr");
    let cons = unsafe { &*(parent as *const ListCons) };
    assert_eq!(cons.head_kind(), ValueKind::LIST);
    assert_eq!(cons.head, list_addr_from_tagged(child_bits).unwrap() as u64);
}

#[test]
fn deep_copy_tagged_list_preserves_nested_list_head() {
    let mut src = Heap::new(1024, fresh_registry());
    let mut dst = Heap::new(1024, fresh_registry());
    let child_bits = alloc_int_list_cons(&mut src, 7, EMPTY_LIST);
    let parent_bits = src.alloc_list_cons_slot(heap_root(child_bits), EMPTY_LIST);

    let copied = deep_copy_slot(heap_root(parent_bits), &src.view(), &mut dst);
    let copied_parent = list_addr_from_tagged(tagged_bits(copied)).expect("copied parent list ptr");
    let parent = unsafe { &*(copied_parent as *const ListCons) };
    assert_eq!(parent.head_kind(), ValueKind::LIST);

    let copied_child = parent.head as *mut u8;
    assert_ne!(copied_child, list_addr_from_tagged(child_bits).unwrap());
    let child = unsafe { &*(copied_child as *const ListCons) };
    assert_eq!(child.head_kind(), ValueKind::INT);
    assert_eq!(child.head as i64, 7);
    assert_eq!(child.tail(), proper(EMPTY_LIST));
}

#[test]
fn deep_copy_single_boxed_list_keeps_container_publication() {
    assert_copied_boxed_list_is_published(false);
}

#[test]
fn deep_copy_duplicate_outer_box_keeps_nested_list_publication() {
    assert_copied_boxed_list_is_published(true);
}

fn assert_copied_boxed_list_is_published(duplicate: bool) {
    let registry = fresh_registry();
    let boxed = registry.borrow_mut().register(Schema::tuple_of_arity(1));
    let pair = registry.borrow_mut().register(Schema::tuple_of_arity(2));
    let mut source = Heap::new(1024, registry.clone());
    let mut destination = Heap::new(1024, registry);
    let list = alloc_int_list_cons(&mut source, 7, EMPTY_LIST);
    let inner = source.alloc_struct(boxed);
    unsafe { source.write_field_slot(inner, 0, heap_root(list)) };
    let root = if duplicate {
        let outer = source.alloc_struct(pair);
        unsafe {
            source.write_field_slot(outer, 0, AnyValue::heap_ptr(inner, ValueKind::STRUCT));
            source.write_field_slot(outer, 8, AnyValue::heap_ptr(inner, ValueKind::STRUCT));
        }
        outer
    } else {
        inner
    };
    let copied = deep_copy_slot(
        AnyValue::heap_ptr(root, ValueKind::STRUCT),
        &source.view(),
        &mut destination,
    );
    let copied_box = if duplicate {
        destination
            .read_field_slot(copied.heap_addr().unwrap(), 0)
            .heap_addr()
            .unwrap()
    } else {
        copied.heap_addr().unwrap()
    };
    let copied_list = destination.read_field_slot(copied_box, 0).heap_addr().unwrap();
    assert!(
        unsafe { &*(copied_list as *const ListCons) }.aliased(),
        "a copied container must publish its list field, even if the container itself was copied only once"
    );
}

#[test]
fn deep_copy_closure_publishes_its_list_capture() {
    let registry = fresh_registry();
    let mut source = Heap::new(1024, registry.clone());
    let mut destination = Heap::new(1024, registry);
    let list = alloc_int_list_cons(&mut source, 7, EMPTY_LIST);
    let closure = source.alloc_closure_slots(crate::any_value::ClosureDenotationId::INTERNAL, 0, 1, 0);
    let address = closure_addr_from_tagged(closure).unwrap();
    unsafe { source.write_closure_capture_value(address, 0, heap_root(list)) };
    let copied = deep_copy_slot(heap_root(closure), &source.view(), &mut destination);
    let captured = unsafe { destination.read_closure_capture_value(copied.heap_addr().unwrap(), 0) };
    assert!(
        unsafe { &*(captured.heap_addr().unwrap() as *const ListCons) }.aliased(),
        "copied public closures guard list captures before repeated invocation"
    );
}

#[test]
fn deep_copy_clears_list_alias_metadata() {
    let mut src = Heap::new(1024, fresh_registry());
    let mut dst = Heap::new(1024, fresh_registry());
    let list_bits = alloc_int_list_cons(&mut src, 7, EMPTY_LIST);
    src.mark_published_ref_aliased(list_ref_from_bits(list_bits))
        .expect("mark aliased");
    let copied = deep_copy_slot(heap_root(list_bits), &src.view(), &mut dst);
    let copied_list = list_addr_from_tagged(tagged_bits(copied)).expect("copied list ptr");
    let copied_cons = unsafe { &*(copied_list as *const ListCons) };

    assert!(!copied_cons.aliased());
    assert_eq!(copied_cons.head as i64, 7);
}

#[test]
fn deep_copy_strict_heap_kinds_dispatch_from_pointer_tags() {
    use crate::resource::{ResourceHandle, ResourceStub, alloc_resource};

    const TEST_DESTRUCTOR: u64 = 0xD7;

    let reg = fresh_registry();
    let pair_id = reg.borrow_mut().register(Schema::tuple_of_arity(2));
    let mut src = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut dst = Heap::with_node(SIZE_TABLE[0], reg, Rc::clone(&src.node));
    let keys = ["a", "b", "c", "d", "e", "f"].map(|name| src.node.intern_atom(name));

    let list_bits = alloc_int_list_cons(&mut src, 7, EMPTY_LIST);

    let struct_p = src.alloc_struct(pair_id);
    unsafe { src.write_field_slot(struct_p, 0, heap_root(list_bits)) };
    unsafe { src.write_field_slot(struct_p, 8, AnyValue::int(11)) };

    let closure_bits = src.alloc_closure(
        crate::any_value::ClosureDenotationId::user(0),
        0,
        1,
        0,
        0x1234,
        &[heap_root(list_bits)],
    );

    let bitstring_p = src.alloc_bitstring(b"abc", 24).heap_addr().expect("bitstring");

    let binview = alloc_buffer_view(
        &mut src,
        SharedBinHandle::from_bytes(&[1, 2, 3, 4]),
        32,
        StubSite::FilledBuffer,
    );

    let resource = alloc_resource(&mut src, ResourceHandle::new(0xfeed, TEST_DESTRUCTOR));

    let entries = [
        (
            AnyValue::atom(keys[0]),
            AnyValue::heap_ptr(list_addr_from_tagged(list_bits).unwrap(), ValueKind::LIST),
        ),
        (AnyValue::atom(keys[1]), AnyValue::heap_ptr(struct_p, ValueKind::STRUCT)),
        (
            AnyValue::atom(keys[2]),
            AnyValue::heap_ptr(closure_addr_from_tagged(closure_bits).unwrap(), ValueKind::CLOSURE),
        ),
        (
            AnyValue::atom(keys[3]),
            AnyValue::heap_ptr(bitstring_p, ValueKind::BITSTRING),
        ),
        (
            AnyValue::atom(keys[4]),
            AnyValue::heap_ptr(binview.as_raw(), ValueKind::BINVIEW),
        ),
        (
            AnyValue::atom(keys[5]),
            AnyValue::heap_ptr(resource.as_raw(), ValueKind::RESOURCE),
        ),
    ];
    let map_bits = src.alloc_map_slots(&entries);

    let copied = deep_copy_slot(heap_root(map_bits), &src.view(), &mut dst);
    let copied_map = map_addr_from_tagged(tagged_bits(copied)).unwrap();

    let copied_values = (0..entries.len())
        .map(|i| unsafe { map_entry(copied_map as *const u8, i).1 })
        .collect::<Vec<_>>();
    for (i, value) in copied_values.iter().enumerate() {
        assert_eq!(value.kind(), entries[i].1.kind());
        assert_ne!(value.raw(), entries[i].1.raw(), "heap entry {} moved/copied", i);
    }

    let copied_struct = copied_values[1].raw() as *mut u8;
    let copied_struct_list = dst.read_field_slot(copied_struct, 0);
    assert_eq!(copied_struct_list.kind(), ValueKind::LIST);
    assert!(!copied_struct_list.heap_addr().unwrap().is_null());

    let copied_closure = copied_values[2].raw() as *mut u8;
    let copied_capture = unsafe { closure_capture_value(copied_closure as *const u8, 0) };
    assert!(list_addr_from_tagged(tagged_bits(copied_capture)).is_some());

    let copied_resource = unsafe { ResourceStub::from_raw(copied_values[5].raw() as *mut u8) };
    assert_eq!(copied_resource.payload(), 0xfeed);
}

/// Acceptance (§6.6): spawn under load shows no per-spawn
/// malloc after warm-up. After dropping a Heap, its block goes to the
/// pool; the next Heap::new of the same capacity pulls from the
/// pool, no malloc required. Repeating spawn+drop with a fixed pool
/// occupancy proves the cache is doing its job.
#[test]
fn pool_caches_blocks_across_heap_drops() {
    pool_drain_for_test();
    assert_eq!(pool_total_cached_blocks(), 0, "test starts with empty pool");

    // Warm-up: create + drop one Heap. Drop returns the block.
    {
        let _h = Heap::new(SIZE_TABLE[0], fresh_registry());
    }
    assert_eq!(pool_total_cached_blocks(), 1, "first drop fills the pool");

    // Subsequent spawn-equivalents (Heap::new + drop) must not increase
    // the pool occupancy — they pull from the cache, return the same
    // block. The acceptance "no per-spawn malloc": occupancy stays at
    // 1 across N create+drop cycles.
    for _ in 0..50 {
        let _h = Heap::new(SIZE_TABLE[0], fresh_registry());
        assert_eq!(pool_total_cached_blocks(), 0, "alloc drained the cache");
        // _h dropped here → returns the block to the pool.
    }
    assert_eq!(pool_total_cached_blocks(), 1, "pool stayed at 1 cached block");

    pool_drain_for_test();
}

#[test]
fn size_table_first_entry_is_1k() {
    assert_eq!(SIZE_TABLE[0], 1024);
}

#[test]
fn size_table_is_monotonic_and_16_aligned() {
    for i in 1..SIZE_TABLE.len() {
        assert!(
            SIZE_TABLE[i] > SIZE_TABLE[i - 1],
            "non-monotonic at {}: {} <= {}",
            i,
            SIZE_TABLE[i],
            SIZE_TABLE[i - 1]
        );
        assert_eq!(SIZE_TABLE[i] % 16, 0, "entry {} ({}) not 16-aligned", i, SIZE_TABLE[i]);
    }
}

#[test]
fn size_table_tail_is_geometric_ish() {
    // Tail entries grow ~×1.2 (after the Fibonacci low end). Sample
    // index 20 → 21: ratio in [1.18, 1.23].
    let ratio = SIZE_TABLE[21] as f64 / SIZE_TABLE[20] as f64;
    assert!(
        ratio > 1.18 && ratio < 1.23,
        "tail ratio out of expected range: {}",
        ratio
    );
}

#[test]
fn pick_block_capacity_is_the_smallest_table_entry_that_fits() {
    assert_eq!(pick_block_capacity(1024), SIZE_TABLE[0]);
    assert_eq!(pick_block_capacity(1025), SIZE_TABLE[1]);
    assert_eq!(pick_block_capacity(SIZE_TABLE[5]), SIZE_TABLE[5]);
    assert_eq!(pick_block_capacity(SIZE_TABLE[5] + 1), SIZE_TABLE[6]);
    assert_eq!(pick_block_capacity(TABLE_CEILING), TABLE_CEILING);
}

#[test]
fn pick_block_capacity_below_the_table_is_the_request_rounded_to_16() {
    assert_eq!(pick_block_capacity(16), 16);
    assert_eq!(pick_block_capacity(17), 32);
    assert_eq!(pick_block_capacity(1000), 1008);
    assert_eq!(pick_block_capacity(SIZE_TABLE[0] - 1), SIZE_TABLE[0]);
    assert_eq!(pick_block_capacity(0), 16, "a block is at least one 16-byte slot");
}

#[test]
fn a_heap_built_with_a_small_capacity_still_has_a_tip_at_the_first_table_entry() {
    for capacity in [16, 64, 1008] {
        let h = Heap::new(capacity, fresh_registry());
        assert_eq!(h.block_size, SIZE_TABLE[0], "capacity {capacity}");
    }
}

#[test]
fn pick_block_capacity_past_the_table_is_the_request_rounded_to_16() {
    assert_eq!(pick_block_capacity(TABLE_CEILING + 1), TABLE_CEILING + 16);
    assert_eq!(pick_block_capacity(TABLE_CEILING + 16), TABLE_CEILING + 16);
    assert_eq!(pick_block_capacity(TABLE_CEILING * 10 + 3), TABLE_CEILING * 10 + 16);
}

#[test]
fn next_block_capacity_climbs_the_table_then_stays_at_its_last_entry() {
    assert_eq!(next_block_capacity(SIZE_TABLE[0]), SIZE_TABLE[1]);
    assert_eq!(next_block_capacity(SIZE_TABLE[0] + 1), SIZE_TABLE[1]);
    assert_eq!(next_block_capacity(TABLE_CEILING - 1), TABLE_CEILING);
    assert_eq!(next_block_capacity(TABLE_CEILING), TABLE_CEILING);
    assert_eq!(next_block_capacity(TABLE_CEILING * 10), TABLE_CEILING);
}

#[test]
fn pick_tip_capacity_is_pick_block_capacity_clamped_to_the_last_table_entry() {
    assert_eq!(pick_tip_capacity(1), pick_block_capacity(1));
    assert_eq!(pick_tip_capacity(SIZE_TABLE[5] + 1), SIZE_TABLE[6]);
    assert_eq!(pick_tip_capacity(TABLE_CEILING), TABLE_CEILING);
    assert_eq!(pick_tip_capacity(TABLE_CEILING + 1), TABLE_CEILING);
    assert_eq!(pick_tip_capacity(TABLE_CEILING * 10 + 3), TABLE_CEILING);
}

/// Grow a list until its cells hold more than `bytes`, without collecting.
fn grow_list_past(h: &mut Heap, bytes: usize) -> u64 {
    let mut head = EMPTY_LIST;
    let mut i = 0;
    while h.bytes_used() <= bytes {
        head = alloc_int_list_cons(h, i, head);
        i += 1;
    }
    head
}

/// Survivors larger than the size table's last entry are copied into a chain
/// of table-max blocks when the to-space guess has reached that entry, so every
/// to-space block is one the pool recycles.
#[test]
fn survivors_past_the_table_are_copied_into_table_max_blocks() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let head = grow_list_past(&mut h, 2 * TABLE_CEILING);
    let mut roots = [heap_ref(head)];
    h.collect_stats(&mut roots);

    let stats = h.collect_stats(&mut roots);

    assert_eq!(stats.generation, Generation::Major);
    assert_eq!(stats.to_space_guess_bytes as usize, TABLE_CEILING);
    assert!(stats.copied_bytes as usize > 2 * TABLE_CEILING);
    assert!(
        h.old_blocks.iter().all(|block| SIZE_TABLE.contains(&block.capacity)),
        "every to-space block is a table entry"
    );
    let chain = h
        .old_blocks
        .iter()
        .filter(|block| block.capacity == TABLE_CEILING)
        .count();
    assert!(
        chain >= 3,
        "the copy filled a chain of table-max blocks, not one exact block"
    );
    assert_eq!(stats.blocks_after as usize, h.old_blocks.len());
}

/// The table-max blocks collections filled return to the pool when a major
/// collection releases them, and the tip the next collection installs is one
/// of them.
#[test]
fn table_max_blocks_return_to_the_pool_and_a_later_tip_reuses_them() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut head = grow_list_past(&mut h, 2 * TABLE_CEILING);
    let mut roots = [heap_ref(head)];
    h.collect_stats(&mut roots);
    h.collect_stats(&mut roots);
    head = roots[0].raw_word();
    let mut i = 0;
    while h.young_bytes() <= h.old_after_last_major {
        head = alloc_int_list_cons(&mut h, i, head);
        i += 1;
    }
    let mut roots = [heap_ref(head)];
    assert_eq!(h.collect_stats(&mut roots).generation, Generation::Minor);
    let chain: Vec<*mut u8> = h
        .old_blocks
        .iter()
        .filter(|block| block.capacity == TABLE_CEILING)
        .map(|block| block.start)
        .collect();
    assert!(chain.len() >= 6, "both collections left table-max blocks old");
    let held: Vec<*mut u8> = h
        .old_blocks
        .iter()
        .chain(&h.young_blocks)
        .map(|block| block.start)
        .chain([h.block_start])
        .collect();

    let stats = h.collect_stats(&mut roots);

    assert_eq!(stats.generation, Generation::Major, "the chain is in the from-space");
    assert!(
        pool_footprint().idle_bytes >= chain.len() * TABLE_CEILING,
        "the released table-max blocks rest in the pool"
    );
    h.collect_stats(&mut roots);
    assert_eq!(h.block_size, TABLE_CEILING, "the tip is a table-max block");
    assert!(
        held.contains(&h.block_start),
        "the fresh tip is a block the heap held before the collection released them"
    );
}

/// Under increasing load, each round's list replaces the last. A major
/// collection leaves exactly the live bytes. A minor collection leaves the live
/// bytes plus old data that has died since, and that is bounded: old data
/// reaching `MAJOR_GROWTH_FACTOR` times what the last major collection left
/// makes the next collection major.
#[test]
fn the_heaps_blocks_hold_the_live_bytes_and_a_bounded_amount_of_dead_old_data() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut seen = Vec::new();
    for power in 6..=12 {
        let len = 1usize << power; // 64, 128, ..., 4096 cells
        let mut tail = EMPTY_LIST;
        for i in 0..len {
            tail = alloc_int_list_cons(&mut h, i as i64, tail);
        }
        let old_before = h.live_baseline;
        let dead_old_allowed = MAJOR_GROWTH_FACTOR * h.old_after_last_major.max(SIZE_TABLE[0] / 2);
        let mut roots = [heap_ref(tail)];
        let stats = h.collect_stats(&mut roots);
        let live_bytes = len * 16;
        match stats.generation {
            Generation::Major => {
                assert_eq!(
                    h.bytes_used(),
                    live_bytes,
                    "a major collection leaves exactly the live bytes"
                );
            }
            Generation::Minor => {
                assert_eq!(
                    h.bytes_used(),
                    old_before + live_bytes,
                    "a minor collection adds its survivors"
                );
                assert!(
                    old_before <= dead_old_allowed,
                    "dead old data {old_before} is within the bound {dead_old_allowed}"
                );
            }
        }
        assert_eq!(
            h.live_baseline,
            h.bytes_used(),
            "everything held after a collection is old"
        );
        assert_eq!(stats.live_bytes, h.live_baseline as u64);
        assert_eq!(stats.blocks_after, h.old_blocks.len() as u64);
        let capacity: usize = h.old_blocks.iter().map(|block| block.capacity).sum();
        assert!(
            capacity >= h.bytes_used(),
            "capacity {capacity} holds the bytes kept {}",
            h.bytes_used()
        );
        seen.push(stats.generation);
    }
    assert!(seen.contains(&Generation::Minor) && seen.contains(&Generation::Major));
}

/// A heap holding more than the largest pooled block still allocates its
/// young data in a pooled block and collects after filling one, so a large
/// live set does not make each collection obtain and return a large block.
#[test]
fn a_large_heaps_young_generation_is_one_pooled_block() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut tail = EMPTY_LIST;
    for i in 0..(TABLE_CEILING / 16 * 2) {
        tail = alloc_int_list_cons(&mut h, i as i64, tail);
    }
    let mut roots = [heap_ref(tail)];
    h.collect_stats(&mut roots);
    assert!(h.live_baseline > TABLE_CEILING);
    assert_eq!(h.block_size, TABLE_CEILING, "the fresh tip is the largest pooled block");
    assert!(!h.should_gc());
    for i in 0..(TABLE_CEILING / 16) {
        alloc_int_list_cons(&mut h, i as i64, EMPTY_LIST);
    }
    assert!(
        h.should_gc(),
        "a collection is due once the pooled block's worth is allocated"
    );
}

/// To-space starts as a tip sized by a guess, the last live bytes. When the
/// live bytes outgrow the guess, the copy fills the tip, parks it, and
/// continues in the next capacity up, exactly as allocation does.
#[test]
fn a_copy_larger_than_the_guessed_tip_parks_to_space_blocks() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    assert_eq!(h.live_baseline, 0, "no collection yet: the guess is the smallest tip");
    let len = SIZE_TABLE[0] / 16 * 4;
    let mut tail = EMPTY_LIST;
    for i in 0..len {
        tail = alloc_int_list_cons(&mut h, i as i64, tail);
    }
    let mut roots = [heap_ref(tail)];

    let stats = h.collect_stats(&mut roots);

    assert!(h.old_blocks.len() > 1, "the copy overflowed its guessed tip");
    assert_eq!(stats.blocks_after, h.old_blocks.len() as u64);
    assert_eq!(stats.live_bytes, (len * 16) as u64);
    assert_eq!(
        h.bytes_used(),
        len * 16,
        "tip and parked to-blocks hold every copied byte"
    );
    assert_eq!(h.old_objects as usize, len);
    let mut cursor = roots[0];
    let mut seen = 0;
    while !cursor.is_empty_list() {
        assert!(
            h.contains_heap_addr(cursor.storage_addr()),
            "every cell is in a heap block"
        );
        cursor = h.read_list_tail_ref(cursor).expect("tail");
        seen += 1;
    }
    assert_eq!(seen, len);
}

/// A collection's survivors are the next collection's guess for the tip, so
/// a steady live set of N bytes collects into a single block.
#[test]
fn a_steady_live_set_collects_into_one_block() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut tail = EMPTY_LIST;
    for i in 0..(SIZE_TABLE[0] / 16 * 4) {
        tail = alloc_int_list_cons(&mut h, i as i64, tail);
    }
    let mut roots = [heap_ref(tail)];
    h.collect_stats(&mut roots);
    let stats = h.collect_stats(&mut roots);
    assert_eq!(stats.blocks_after, 1, "the guess now holds the live bytes");
    assert!(h.young_blocks.is_empty());
}

/// live_baseline is the bytes the collection copied.
#[test]
fn a_collection_sets_the_live_baseline_to_the_bytes_it_copied() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    assert_eq!(h.live_baseline, 0, "zero before first gc");
    let n3 = alloc_int_list_cons(&mut h, 3, EMPTY_LIST);
    let n2 = alloc_int_list_cons(&mut h, 2, n3);
    let n1 = alloc_int_list_cons(&mut h, 1, n2);
    let mut roots = [heap_ref(n1)];
    let stats = h.collect_stats(&mut roots);
    assert_eq!(h.live_baseline, 3 * 16, "three cons cells = 48 bytes");
    assert_eq!(stats.copied_bytes, 3 * 16);

    h.collect_stats(&mut roots);
    assert_eq!(h.live_baseline, 3 * 16, "live bytes unchanged");
    assert_eq!(
        h.block_size, BUDGET_FLOOR,
        "a tiny live set keeps a tip of the budget floor"
    );
}

#[test]
fn allocation_pressure_marks_gc_without_spending_reductions() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());

    let _ = h.alloc(BUDGET_FLOOR);

    assert!(h.should_gc(), "allocation pressure should request boundary GC");
}

/// Large struct (200-byte payload, well past the old 64-byte cap)
/// allocates without panic; grow promotes to a larger capacity as needed.
#[test]
fn alloc_large_struct_succeeds_and_grows_capacity() {
    let reg = fresh_registry();
    // Build a schema whose payload is 200 bytes of typed value fields.
    let n_fields = 200 / 8; // 25 any values
    let mut fields = Vec::with_capacity(n_fields);
    for i in 0..n_fields {
        fields.push(FieldDescriptor {
            offset: (i * 8) as u32,
            kind: FieldKind::AnyValue,
            name: None,
        });
    }
    let id = reg.borrow_mut().register(Schema {
        identity: SchemaIdentity::Internal("Big".into()),
        size: (n_fields * 8) as u32,
        fields,
    });
    let mut h = Heap::new(SIZE_TABLE[0], reg);
    let p = h.alloc_struct(id);
    unsafe {
        assert_eq!(struct_schema_id(p), id);
        // total = 8 + 200 = 208, rounded to 208.
        assert_eq!(struct_size_for_payload(200), 208);
    }
}

#[test]
fn struct_layout_size_correct() {
    let reg = fresh_registry();
    let id = reg.borrow_mut().register(Schema::tuple_of_arity(3));
    let mut h = Heap::new(SIZE_TABLE[0], reg);
    let before = h.bytes_used();

    let p = h.alloc_struct(id);

    assert_eq!(Schema::tuple_of_arity(3).allocation_payload_size(), 32);
    assert_eq!(h.bytes_used() - before, 48);
    unsafe {
        assert_eq!(struct_schema_id(p), id);
        assert_eq!(
            read(p as *const u64) & 0xF,
            0,
            "a live struct header leaves the low nibble clear"
        );
    }
}

#[test]
fn struct_field_read_at_new_offset() {
    let reg = fresh_registry();
    let id = reg.borrow_mut().register(Schema::tuple_of_arity(2));
    let mut h = Heap::new(SIZE_TABLE[0], reg);
    let p = h.alloc_struct(id);

    unsafe { h.write_field_slot(p, 0, AnyValue::int(11)) };
    unsafe { h.write_field_slot(p, 8, AnyValue::int(22)) };

    unsafe {
        assert_eq!(read(p.add(8) as *const u64), 11);
        assert_eq!(read(p.add(16) as *const u64), 22);
        assert_eq!(read(p.add(24) as *const u8), ValueKind::INT.tag());
        assert_eq!(read(p.add(25) as *const u8), ValueKind::INT.tag());
    }
    assert_eq!(h.read_field_slot(p, 0), AnyValue::int(11));
    assert_eq!(h.read_field_slot(p, 8), AnyValue::int(22));
}

#[test]
fn struct_forwarding_marker_through_gc() {
    let reg = fresh_registry();
    let id = reg.borrow_mut().register(Schema::tuple_of_arity(1));
    let mut h = Heap::new(SIZE_TABLE[0], reg);
    let p = h.alloc_struct(id);
    let old_addr = p;
    unsafe { h.write_field_slot(p, 0, AnyValue::int(9)) };
    let mut root = heap_object_word(p, ValueKind::STRUCT) as *mut u8;

    h.collect_tagged(&mut root);

    let new_p = struct_addr_from_tagged(root as u64).expect("forwarded root");
    assert_ne!(new_p as *const u8, old_addr);
    assert_eq!(h.read_field_slot(new_p, 0), AnyValue::int(9));
    assert_eq!(forwarded_target(old_addr, ValueKind::STRUCT), Some(new_p));
}

/// Map with 5 entries exercises both alloc and the Cheney trace path
/// (Map walks each entry's typed children).
#[test]
fn alloc_large_map_round_trips_through_gc() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let entries: Vec<(AnyValue, AnyValue)> = (0..5)
        .map(|i| {
            (
                any_value(i as u64, ValueKind::INT),
                any_value((i * 10) as u64, ValueKind::INT),
            )
        })
        .collect();
    let bits = h.alloc_map_slots(&entries);
    let mut roots = [heap_ref(bits)];
    h.collect_stats(&mut roots);
    assert_eq!(h.old_objects, 1, "map survives GC");
    let new_p = map_addr_from_tagged(ref_bits(roots[0])).unwrap();
    unsafe {
        let count = map_count(new_p as *const u8);
        assert_eq!(count, 5);
    }
}

#[test]
fn map_layout_size_correct() {
    for count in [0usize, 1, 2, 3, 7, 8, 9] {
        let entries: Vec<(AnyValue, AnyValue)> = (0..count)
            .map(|i| {
                (
                    any_value(i as u64, ValueKind::INT),
                    any_value((i + 10) as u64, ValueKind::INT),
                )
            })
            .collect();
        let mut h = Heap::new(1024, fresh_registry());
        let bits = h.alloc_map_slots(&entries);
        assert_eq!(object_size(bits), map_size_for_count(count));
    }
}

#[test]
fn closure_layout_zero_captures() {
    let mut h = Heap::new(1024, fresh_registry());
    let bits = h.alloc_closure(
        crate::any_value::ClosureDenotationId::user(0),
        42,
        0,
        2,
        0xfeed_beef,
        &[],
    );
    assert_eq!(heap_kind_from_tagged(bits), Some(ValueKind::CLOSURE));
    assert_eq!(object_size(bits), 16);
    let p = closure_addr_from_tagged(bits).unwrap();
    assert_eq!(unsafe { closure_captured_count(p) }, 0);
    assert_eq!(unsafe { closure_halt_kind(p) }, 2);
    assert_eq!(unsafe { closure_fn_ptr(p) }, 0xfeed_beef);
}

#[test]
fn closure_layout_n_captures() {
    let mut h = Heap::new(1024, fresh_registry());
    let captures = [AnyValue::int(10), AnyValue::int(20)];
    let bits = h.alloc_closure(
        crate::any_value::ClosureDenotationId::user(0),
        7,
        captures.len(),
        1,
        0x1234,
        &captures,
    );
    assert_eq!(object_size(bits), 48);
    let p = closure_addr_from_tagged(bits).unwrap();
    assert_eq!(unsafe { closure_captured_count(p) }, 2);
    for (i, expected) in captures.iter().enumerate() {
        let got = unsafe { closure_capture_value(p, i) };
        assert_eq!(got, *expected);
    }
}

#[test]
fn closure_forwarding_marker() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bits = h.alloc_closure(crate::any_value::ClosureDenotationId::user(0), 12, 0, 0, 0x7777, &[]);
    let old = closure_addr_from_tagged(bits).unwrap();
    let mut root = bits as *mut u8;
    h.collect_tagged(&mut root);
    let new_bits = root as u64;
    let new_p = closure_addr_from_tagged(new_bits).unwrap();
    assert_ne!(old, new_p);
    assert_eq!(unsafe { closure_captured_count(new_p) }, 0);
    assert_eq!(unsafe { closure_fn_ptr(new_p as *const u8) }, 0x7777);
    assert_eq!(forwarded_target(old, ValueKind::CLOSURE), Some(new_p));
}

/// A zero-capture closure on its own read-only page, the way the compiled
/// program's static closures sit: outside every heap, and a write to it faults.
struct ReadOnlyClosure {
    page: *mut u8,
}

impl ReadOnlyClosure {
    const PAGE_BYTES: usize = 4096;

    fn new() -> Self {
        unsafe {
            let page = libc::mmap(
                null_mut(),
                Self::PAGE_BYTES,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_ANON | libc::MAP_PRIVATE,
                -1,
                0,
            ) as *mut u8;
            assert_ne!(page as *mut libc::c_void, libc::MAP_FAILED);
            crate::any_value::closure_header_write(
                page,
                crate::any_value::closure_header_word(crate::any_value::ClosureDenotationId::user(5), 0, 0, 1),
            );
            write(page.add(8) as *mut u64, 0x5757);
            assert_eq!(libc::mprotect(page.cast(), Self::PAGE_BYTES, libc::PROT_READ), 0);
            Self { page }
        }
    }

    /// The closure as compiled code names it: a literal.
    fn value(&self) -> AnyValue {
        AnyValue::HeapRef(
            AnyValueRef::from_heap_object(ValueKind::CLOSURE, self.page)
                .expect("static closure ref")
                .literal(),
        )
    }
}

impl Drop for ReadOnlyClosure {
    fn drop(&mut self) {
        unsafe { libc::munmap(self.page.cast(), Self::PAGE_BYTES) };
    }
}

#[test]
fn strict_heap_decoder_accepts_static_closure_pointer() {
    let closure = ReadOnlyClosure::new();
    let bits = heap_object_word(closure.page as *const u8, ValueKind::CLOSURE);

    let value = heap_root(bits);

    assert_eq!(value.kind(), ValueKind::CLOSURE);
    assert_eq!(value.raw(), closure.page as u64);
}

#[test]
fn collection_leaves_a_read_only_static_closure_in_place() {
    let closure = ReadOnlyClosure::new();
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let holder = heap.alloc_closure_slots(crate::any_value::ClosureDenotationId::user(73), 1, 1, 0);
    unsafe { closure_capture_set(closure_addr_from_tagged(holder).expect("holder"), 0, closure.value()) };
    let mut roots = [heap_ref(holder), closure.value().ref_word()];

    heap.collect_stats(&mut roots);

    let moved = roots[0].closure_addr().expect("moved holder");
    assert_eq!(
        unsafe { closure_capture_value(moved, 0) },
        closure.value(),
        "a reference held by a moved object still names the static closure"
    );
    assert_eq!(roots[1].closure_addr(), Ok(closure.page), "a root is left as it was");
}

#[test]
fn deep_copy_leaves_a_read_only_static_closure_in_place() {
    let closure = ReadOnlyClosure::new();
    let mut source = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut destination = Heap::new(SIZE_TABLE[0], fresh_registry());
    let holder = source.alloc_closure_slots(crate::any_value::ClosureDenotationId::user(73), 1, 1, 0);
    unsafe { closure_capture_set(closure_addr_from_tagged(holder).expect("holder"), 0, closure.value()) };

    let copied = deep_copy_slot(heap_root(holder), &source.view(), &mut destination);

    let copy = copied.ref_word().closure_addr().expect("copied holder");
    assert_eq!(unsafe { closure_capture_value(copy, 0) }, closure.value());
    let alone = deep_copy_slot(closure.value(), &source.view(), &mut destination);
    assert_eq!(
        alone,
        closure.value(),
        "a static closure sent on its own is passed by pointer"
    );
}

#[test]
fn map_packed_tags_round_trip() {
    let cases = [1usize, 2, 3, 7, 8, 9];
    for count in cases {
        let mut h = Heap::new(1024, fresh_registry());
        let entries: Vec<(AnyValue, AnyValue)> = (0..count)
            .map(|i| {
                let key = if i % 2 == 0 {
                    AnyValue::atom(h.node.intern_atom(&format!("key_{i}")))
                } else {
                    AnyValue::int(i as i64)
                };
                let value_kind = if i % 3 == 0 { ValueKind::FLOAT } else { ValueKind::INT };
                (key, any_value((100 + i) as u64, value_kind))
            })
            .collect();
        let bits = h.alloc_map_slots(&entries);
        let p = map_addr_from_tagged(bits).unwrap();
        // The SET of entries round-trips, not their positions. A map is a
        // sorted array and `alloc_map_slots` sorts, so where an
        // entry lands is the map's business; what this test is about is that
        // the packed key/value KIND tags survive the write and read back as the
        // same values.
        assert_eq!(unsafe { map_count(p) }, entries.len());
        for i in 0..entries.len() {
            assert!(entries.contains(&unsafe { map_entry(p, i) }), "entry {i} of {count}");
        }
    }
}

#[test]
fn map_float_value_is_unboxed_raw_bits() {
    let mut h = Heap::new(1024, fresh_registry());
    let f = PI;
    let bits = h.alloc_map_slots(&[(any_value(0, ValueKind::ATOM), any_value(f.to_bits(), ValueKind::FLOAT))]);
    let p = map_addr_from_tagged(bits).unwrap();
    let (_, value) = unsafe { map_entry(p, 0) };
    assert_eq!(value.kind(), ValueKind::FLOAT);
    assert_eq!(value.raw(), f.to_bits());
    assert_eq!(
        h.node.alloc_stats().total.allocs,
        1,
        "map allocation should not box the float"
    );
}

#[test]
fn map_int_value_stores_full_i64_range() {
    let mut h = Heap::new(1024, fresh_registry());
    let value = i64::MIN;
    let bits = h.alloc_map_slots(&[(any_value(1, ValueKind::ATOM), any_value(value as u64, ValueKind::INT))]);
    let p = map_addr_from_tagged(bits).unwrap();
    let (_, got) = unsafe { map_entry(p, 0) };
    assert_eq!(got.kind(), ValueKind::INT);
    assert_eq!(got.raw() as i64, value);
}

#[test]
fn deep_copy_tagged_map_preserves_nested_list_value() {
    let mut src = Heap::new(1024, fresh_registry());
    let mut dst = Heap::new(1024, fresh_registry());
    let child_bits = alloc_int_list_cons(&mut src, 7, EMPTY_LIST);
    let child_ptr = list_addr_from_tagged(child_bits).unwrap();
    let map_bits = src.alloc_map_slots(&[(
        any_value(1, ValueKind::ATOM),
        AnyValue::heap_ptr(child_ptr, ValueKind::LIST),
    )]);
    let copied = deep_copy_slot(heap_root(map_bits), &src.view(), &mut dst);
    let copied_map = map_addr_from_tagged(tagged_bits(copied)).unwrap();
    let (_, value) = unsafe { map_entry(copied_map as *const u8, 0) };
    assert_eq!(value.kind(), ValueKind::LIST);
    assert_ne!(value.raw() as *mut u8, child_ptr);
    let copied_list = unsafe { &*(value.raw() as *const ListCons) };
    assert_eq!(copied_list.head_kind(), ValueKind::INT);
    assert_eq!(copied_list.head as i64, 7);
}

#[test]
fn gc_map_count_twelve_does_not_collide_with_forwarding_tag() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let entries: Vec<(AnyValue, AnyValue)> = (0..12)
        .map(|i| {
            (
                any_value(i as u64, ValueKind::INT),
                any_value((i * 2) as u64, ValueKind::INT),
            )
        })
        .collect();
    let bits = h.alloc_map_slots(&entries);
    let old = map_addr_from_tagged(bits).unwrap();
    let mut roots = [heap_ref(bits)];
    h.collect_stats(&mut roots);
    let new_p = map_addr_from_tagged(ref_bits(roots[0])).unwrap();
    assert_ne!(new_p, old);
    assert_eq!(unsafe { map_count(new_p as *const u8) }, 12);
}

/// Acceptance: ≥10 GC cycles with the same small live working set
/// keep the arena bounded. Block size may grow once to fit per-cycle
/// garbage but does not increase without bound; no abandoned blocks
/// remain post-GC; the kept objects stay at the rooted chain length.
/// (§6.4 acceptance.)
#[test]
fn gc_keeps_arena_bounded_across_many_cycles() {
    let mut h = Heap::new(1024, fresh_registry());
    // Rooted [1, 2, 3] — the live working set across every cycle.
    let n3 = alloc_int_list_cons(&mut h, 3, EMPTY_LIST);
    let n2 = alloc_int_list_cons(&mut h, 2, n3);
    let n1 = alloc_int_list_cons(&mut h, 1, n2);
    let mut roots = [heap_ref(n1)];
    for _ in 0..15 {
        // Per-cycle garbage that overflows the 1 KiB initial block,
        // forcing grow → abandon → reclaim at next gc().
        for _ in 0..100 {
            let _ = h.alloc_list_cons_slot(AnyValue::nil_atom(), EMPTY_LIST);
        }
        h.collect_stats(&mut roots);
        // Post-gc invariants.
        assert_eq!(h.old_objects, 3, "rooted chain survives");
        assert_eq!(h.young_blocks.len(), 0, "abandoned blocks reclaimed");
    }
    // After the working-set-fits-in-block point, block_size stays put.
    // Generous upper bound: 32× initial guards against runaway growth.
    assert!(
        h.block_size <= 1024 * 32,
        "block_size grew unboundedly: {}",
        h.block_size
    );
}

/// Cycle (a.0 = b, b.0 = a) doesn't loop the collector: forwarding
/// pointers in from-space short-circuit revisits.
#[test]
fn gc_handles_cycle_via_forwarding() {
    let reg = fresh_registry();
    let pair_id = reg.borrow_mut().register(Schema {
        identity: SchemaIdentity::Internal("Pair".into()),
        size: 16,
        fields: vec![
            FieldDescriptor {
                offset: 0,
                kind: FieldKind::AnyValue,
                name: None,
            },
            FieldDescriptor {
                offset: 8,
                kind: FieldKind::AnyValue,
                name: None,
            },
        ],
    });
    let mut h = Heap::new(1024, reg);
    let a = h.alloc_struct(pair_id);
    let b = h.alloc_struct(pair_id);
    unsafe { h.write_field_slot(a, 0, AnyValue::heap_ptr(b, ValueKind::STRUCT)) };
    unsafe { h.write_field_slot(a, 8, AnyValue::nil_atom()) };
    unsafe { h.write_field_slot(b, 0, AnyValue::heap_ptr(a, ValueKind::STRUCT)) };
    unsafe { h.write_field_slot(b, 8, AnyValue::nil_atom()) };
    let mut root = heap_object_word(a as *const u8, ValueKind::STRUCT) as *mut u8;
    h.collect_tagged(&mut root);
    assert_eq!(h.old_objects, 2);
}

// ===== BinView + intrusive off-heap chain + post-Cheney sweep =================

use crate::bits::{
    BINREF_BYTES, BINVIEW_BYTES, Bin, BinRef, BinView, SHARED_BIN_BYTES, SharedBinHandle, alloc_buffer_view,
};
use crate::heap::StubSite;

fn shared_refs(handle: &SharedBinHandle) -> usize {
    unsafe { (*handle.as_raw()).refcount.load(Ordering::Relaxed) }
}

/// Walk an off-heap chain from `head` and return the contained tagged pointers
/// in chain order (head → tail).
fn chain_from(head: u64) -> Vec<u64> {
    let mut out = Vec::new();
    let mut cur_bits = head;
    while cur_bits != 0 {
        let addr = heap_word_addr(cur_bits);
        let next = match heap_kind_from_tagged(cur_bits) {
            Some(ValueKind::BINREF) => unsafe { BinRef::from_raw(addr).off_heap_next() },
            Some(ValueKind::RESOURCE) => unsafe { ResourceStub::from_raw(addr).off_heap_next() },
            kind => panic!("unexpected off-heap kind {kind:?}"),
        };
        out.push(cur_bits);
        cur_bits = next;
    }
    out
}

/// The young BinRefs: those allocated since the last collection.
fn off_heap_chain(h: &Heap) -> Vec<u64> {
    chain_from(h.off_heap_head)
}

/// The old BinRefs: those a collection kept.
fn off_heap_old_chain(h: &Heap) -> Vec<u64> {
    chain_from(h.off_heap_old_head)
}

/// A fresh buffer allocates a `BINREF_BYTES` BinRef, which goes onto the chain,
/// and a `BINVIEW_BYTES` view of it, which does not.
#[test]
fn a_fresh_buffer_puts_its_binref_on_the_chain_and_its_view_on_none() {
    let witness = SharedBinHandle::from_bytes(&[1, 2, 3, 4]);
    {
        let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
        let pb = alloc_buffer_view(
            &mut h,
            witness.clone(),
            witness.bytes_len() as u64 * 8,
            StubSite::FilledBuffer,
        );
        let tagged = heap_object_word(pb.as_raw() as *const u8, ValueKind::BINVIEW);
        assert_eq!(heap_kind_from_tagged(tagged), Some(ValueKind::BINVIEW));
        assert_eq!(object_size(tagged), BINVIEW_BYTES);
        assert_eq!(object_size(pb.binref().word()), BINREF_BYTES);
        assert_eq!(
            off_heap_chain(&h),
            vec![pb.binref().word()],
            "only the BinRef is on the chain"
        );
        assert_eq!(
            shared_refs(&witness),
            2,
            "the buffer has one heap reference, the BinRef's"
        );
    }
    assert_eq!(shared_refs(&witness), 1, "heap drop removes its exact owned edge");
}

/// A rooted view survives Cheney, and its BinRef is copied with it and relinked
/// onto the old chain.
#[test]
fn a_rooted_view_carries_its_binref_through_gc() {
    let witness = SharedBinHandle::from_bytes(&[0xaa; 8]);
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let pb = alloc_buffer_view(
        &mut h,
        witness.clone(),
        witness.bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    );
    let shared_p = pb.shared_raw();
    let from_pb = pb.as_raw();
    let mut root = heap_object_word(from_pb as *const u8, ValueKind::BINVIEW) as *mut u8;
    assert_eq!(shared_refs(&witness), 2);
    h.collect_tagged(&mut root);
    let new_pb = binview_addr_from_tagged(root as u64).unwrap();
    assert_ne!(new_pb, from_pb, "BinView should have moved to to-space");
    assert_eq!(off_heap_chain(&h), vec![], "the young chain is empty");
    let pb_to = unsafe { BinView::from_raw(new_pb) };
    assert_eq!(
        off_heap_old_chain(&h),
        vec![pb_to.binref().word()],
        "the view's BinRef is on the old chain"
    );
    assert_eq!(shared_refs(&witness), 2, "GC preserves the same heap-owned edge");
    assert_eq!(pb_to.shared_raw(), shared_p);
    drop(h);
    assert_eq!(shared_refs(&witness), 1);
}

/// An unrooted view dies, so its BinRef is unreached and the sweep releases the
/// SharedBin.
#[test]
fn an_unrooted_view_lets_the_sweep_release_its_shared_bin() {
    let witness = SharedBinHandle::from_bytes(&[0x55; 16]);
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let _ = alloc_buffer_view(
        &mut h,
        witness.clone(),
        witness.bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    );
    assert_eq!(shared_refs(&witness), 2);
    let mut root: *mut u8 = null_mut();
    h.collect_tagged(&mut root);
    assert_eq!(h.off_heap_head, 0, "the dead BinRef is swept from the chain");
    assert_eq!(shared_refs(&witness), 1, "sweep removes its exact owned edge");
}

/// A binary's block (header, bytes, NUL) is in use while a handle or a BinRef holds it, and leaves
/// the count when the sweep drops the last reference.
#[test]
fn a_binarys_bytes_are_in_use_until_its_stub_dies_at_a_collection() {
    let mut h = Heap::new(BUDGET_FLOOR, fresh_registry());
    let before = pool_footprint().in_use_bytes;
    let witness = SharedBinHandle::from_bytes(&[0x55; 4096]);
    let buffer_bytes = SHARED_BIN_BYTES + 4096 + 1;
    assert_eq!(pool_footprint().in_use_bytes, before + buffer_bytes);
    let _ = alloc_buffer_view(
        &mut h,
        witness.clone(),
        witness.bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    );
    drop(witness);
    assert_eq!(
        pool_footprint().in_use_bytes,
        before + buffer_bytes,
        "the BinRef still holds the buffer"
    );
    let mut root: *mut u8 = null_mut();
    h.collect_tagged(&mut root);
    assert_eq!(pool_footprint().in_use_bytes, before, "the sweep freed the buffer");
}

/// Mixed live/dead BinRefs: sweep must read the next link from
/// from-space while reading the survivor's shared_ptr from to-space.
#[test]
fn the_binref_chain_is_intact_through_gc_partial_survival() {
    let witnesses = [1, 2, 3].map(|value| SharedBinHandle::from_bytes(&[value]));
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let _dead_tail = alloc_buffer_view(
        &mut h,
        witnesses[0].clone(),
        witnesses[0].bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    );
    let live = alloc_buffer_view(
        &mut h,
        witnesses[1].clone(),
        witnesses[1].bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    );
    let _dead_head = alloc_buffer_view(
        &mut h,
        witnesses[2].clone(),
        witnesses[2].bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    );
    let live_from = live.as_raw();
    let live_shared = live.shared_raw();
    assert_eq!(off_heap_chain(&h).len(), 3);
    assert_eq!(witnesses.each_ref().map(shared_refs), [2, 2, 2]);

    let mut root = heap_object_word(live_from as *const u8, ValueKind::BINVIEW) as *mut u8;
    h.collect_tagged(&mut root);

    let live_to = binview_addr_from_tagged(root as u64).unwrap();
    assert_ne!(live_to, live_from);
    assert_eq!(
        off_heap_old_chain(&h),
        vec![unsafe { BinView::from_raw(live_to) }.binref().word()]
    );
    assert_eq!(unsafe { BinView::from_raw(live_to).shared_raw() }, live_shared);
    assert_eq!(
        witnesses.each_ref().map(shared_refs),
        [1, 2, 1],
        "only the rooted binary keeps its heap edge"
    );
    drop(h);
    assert_eq!(witnesses.each_ref().map(shared_refs), [1, 1, 1]);
}

/// Heap::drop releases every chain entry's shared_ptr.
#[test]
fn heap_drop_releases_all_off_heap_shared_refs() {
    let witnesses = [
        SharedBinHandle::from_bytes(&[1, 2]),
        SharedBinHandle::from_bytes(&[3, 4, 5]),
    ];
    {
        let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
        for witness in &witnesses {
            alloc_buffer_view(
                &mut h,
                witness.clone(),
                witness.bytes_len() as u64 * 8,
                StubSite::FilledBuffer,
            );
        }
        assert_eq!(witnesses.each_ref().map(shared_refs), [2, 2]);
        assert_eq!(off_heap_chain(&h).len(), 2);
    }
    assert_eq!(witnesses.each_ref().map(shared_refs), [1, 1]);
}

// ===== deep_copy_slot handles BinView via retain =====================

/// Cross-heap deep_copy of a view gives the destination heap its own BinRef,
/// which retains the SharedBin.
#[test]
fn deep_copy_of_a_view_makes_a_binref_in_the_destination_that_retains() {
    let witness = SharedBinHandle::from_bytes(&[7, 8, 9, 10]);
    let mut src = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut dst = Heap::new(SIZE_TABLE[0], fresh_registry());
    let src_pb = alloc_buffer_view(
        &mut src,
        witness.clone(),
        witness.bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    );
    let shared_p = src_pb.shared_raw();
    let copied = deep_copy_slot(
        AnyValue::heap_ptr(src_pb.as_raw(), ValueKind::BINVIEW),
        &src.view(),
        &mut dst,
    );
    let dst_p = binview_addr_from_tagged(tagged_bits(copied)).unwrap();
    let dst_pb = unsafe { BinView::from_raw(dst_p) };
    assert_ne!(dst_p, src_pb.as_raw());
    assert_eq!(dst_pb.shared_raw(), shared_p);
    assert_eq!(off_heap_chain(&src).len(), 1);
    assert_eq!(off_heap_chain(&dst).len(), 1);
    assert_eq!(shared_refs(&witness), 3, "one witness plus two heap-owned edges");
    drop(dst);
    assert_eq!(shared_refs(&witness), 2);
    assert_eq!(off_heap_chain(&src).len(), 1);
    drop(src);
    assert_eq!(shared_refs(&witness), 1);
}

/// A tuple containing the same view twice deep-copies to two views, each with
/// a BinRef of its own, and each BinRef holds one reference to the buffer.
#[test]
fn deep_copy_of_one_view_twice_makes_a_binref_per_copied_view() {
    let witness = SharedBinHandle::from_bytes(&[0xab, 0xcd]);
    let reg = fresh_registry();
    let pair_id = reg.borrow_mut().register(Schema {
        identity: SchemaIdentity::Internal("Pair".into()),
        size: 16,
        fields: vec![
            FieldDescriptor {
                offset: 0,
                kind: FieldKind::AnyValue,
                name: None,
            },
            FieldDescriptor {
                offset: 8,
                kind: FieldKind::AnyValue,
                name: None,
            },
        ],
    });
    let mut src = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut dst = Heap::new(SIZE_TABLE[0], reg);
    let src_pb = alloc_buffer_view(
        &mut src,
        witness.clone(),
        witness.bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    );
    let proc_bits = heap_object_word(src_pb.as_raw() as *const u8, ValueKind::BINVIEW);
    let pair = src.alloc_struct(pair_id);
    let proc_value = heap_root(proc_bits);
    unsafe { src.write_field_slot(pair, 0, proc_value) };
    unsafe { src.write_field_slot(pair, 8, proc_value) };
    let _ = deep_copy_slot(AnyValue::heap_ptr(pair, ValueKind::STRUCT), &src.view(), &mut dst);
    assert_eq!(off_heap_chain(&dst).len(), 2, "one BinRef per copied view");
    assert_eq!(
        shared_refs(&witness),
        4,
        "one witness, the sender's edge, and one reference per copied view"
    );
    drop(dst);
    assert_eq!(shared_refs(&witness), 2);
    drop(src);
    assert_eq!(shared_refs(&witness), 1);
}

// ===== alloc_bitstring threshold + dispatch ===========================

#[test]
fn alloc_bitstring_small_stays_inline() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bytes: Vec<u8> = (0..32u8).collect();
    let p = h.alloc_bitstring(&bytes, 256).heap_addr().expect("bitstring");
    let tagged = heap_object_word(p, ValueKind::BITSTRING);
    unsafe {
        assert_eq!(heap_kind_from_tagged(tagged), Some(ValueKind::BITSTRING));
        assert_eq!(Bin::of_binary(tagged).bit_len(), 256);
        let pay = Bin::of_binary(tagged).ptr();
        for (i, expected) in bytes.iter().enumerate().take(32) {
            assert_eq!(*pay.add(i), *expected);
        }
    }
    assert_eq!(h.off_heap_head, 0);
}

#[test]
fn alloc_bitstring_large_routes_to_shared_zone() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bytes: Vec<u8> = (0..128u8).collect();
    let p = h.alloc_bitstring(&bytes, 1024).heap_addr().expect("binview");
    let witness = unsafe { SharedBinHandle::retain_from_raw(BinView::from_raw(p).shared_raw()) };
    let tagged = heap_object_word(p, ValueKind::BINVIEW);
    unsafe {
        assert_eq!(heap_kind_from_tagged(tagged), Some(ValueKind::BINVIEW));
        assert_eq!(object_size(tagged), BINVIEW_BYTES);
        assert_eq!(Bin::of_binary(tagged).bit_len(), 1024);
        let pay = Bin::of_binary(tagged).ptr();
        for (i, expected) in bytes.iter().enumerate().take(128) {
            assert_eq!(*pay.add(i), *expected);
        }
    }
    assert_eq!(off_heap_chain(&h).len(), 1);
    assert_eq!(shared_refs(&witness), 2);
    drop(h);
    assert_eq!(shared_refs(&witness), 1);
}

#[test]
fn alloc_bitstring_with_fills_an_inline_payload_in_place() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let value = h.alloc_bitstring_with(32, 256, |dest| dest.fill(MaybeUninit::new(7)));
    assert_eq!(value.kind(), ValueKind::BITSTRING);
    let tagged = heap_object_word(value.heap_addr().expect("bitstring"), ValueKind::BITSTRING);
    let payload = unsafe { std::slice::from_raw_parts(Bin::of_binary(tagged).ptr(), 33) };
    assert_eq!(&payload[..32], &[7u8; 32][..]);
    assert_eq!(payload[32], 0, "the invisible trailing NUL stays zero");
    assert_eq!(h.node.alloc_stats().shared_bin.bytes, 0);
}

#[test]
fn alloc_bitstring_with_fills_a_shared_buffer_in_place_and_counts_it_once() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let len = SHARED_BIN_THRESHOLD_BYTES + 36;
    let value = h.alloc_bitstring_with(len, (len * 8) as u64, |dest| dest.fill(MaybeUninit::new(9)));
    assert_eq!(value.kind(), ValueKind::BINVIEW);
    let tagged = heap_object_word(value.heap_addr().expect("binview"), ValueKind::BINVIEW);
    let payload = unsafe { std::slice::from_raw_parts(Bin::of_binary(tagged).ptr(), len + 1) };
    assert!(payload[..len].iter().all(|&b| b == 9));
    assert_eq!(payload[len], 0, "the invisible trailing NUL stays zero");
    let stats = h.node.alloc_stats();
    assert_eq!(stats.shared_bin.bytes, len as u64);
    assert_eq!(stats.shared_bin.allocs, 1);
    assert_eq!(
        stats.total.allocs, 2,
        "the buffer is no heap object: the view and its BinRef are"
    );
}

/// An off-heap buffer is one count at the `SharedBin` site, whether it is
/// filled or made by a concatenation, and is no part of the total: its bytes
/// are on no heap. The view and BinRef that name it are heap objects and
/// count there.
#[test]
fn an_off_heap_buffer_counts_once_at_the_shared_bin_site_and_not_in_the_total() {
    let shared_bin_sites = |h: &Heap| {
        h.node
            .alloc_site_counts()
            .into_iter()
            .filter(|site| site.kind == HeapAllocKind::SharedBin)
            .map(|site| (site.function, site.placed))
            .collect::<Vec<_>>()
    };
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let len = SHARED_BIN_THRESHOLD_BYTES + 1;
    let _ = h.alloc_bitstring_with(len, (len * 8) as u64, |dest| dest.fill(MaybeUninit::new(1)));
    assert_eq!(
        shared_bin_sites(&h),
        [(
            "runtime::alloc_shared_bin".to_owned(),
            AllocStat {
                allocs: 1,
                bytes: len as u64
            }
        )]
    );
    let filled = h.node.alloc_stats();
    assert_eq!(filled.total.allocs, filled.binview.allocs + filled.binref.allocs);

    let (left, right) = ([2u8; SHARED_BIN_THRESHOLD_BYTES], [3u8; 8]);
    let _ = unsafe {
        h.alloc_concatenation(&left, None, right.len(), |dest| {
            dest.write_copy_of_slice(&right);
        })
    };
    let total_bytes = left.len() + right.len();
    assert_eq!(
        shared_bin_sites(&h),
        [(
            "runtime::alloc_shared_bin".to_owned(),
            AllocStat {
                allocs: 2,
                bytes: (len + total_bytes * 2) as u64
            }
        )]
    );
    let stats = h.node.alloc_stats();
    assert_eq!(stats.shared_bin.allocs, 2);
    assert_eq!(stats.total.allocs, stats.binview.allocs + stats.binref.allocs);
}

/// The bytes of a binary value, whichever way it is stored.
fn binary_bytes(value: AnyValue) -> Vec<u8> {
    let word = value.ref_word().raw_word();
    unsafe { Bin::of_binary(word) }.bytes().to_vec()
}

/// The view a result above the threshold is.
fn view_of_result(value: AnyValue) -> BinView {
    unsafe { BinView::from_raw(value.heap_addr().expect("a result above the threshold is a view")) }
}

/// The right side of an append is the bytes its fill writes, once: the fill
/// gets exactly `right_len` bytes, whether the result is built inline, written
/// into the left side's buffer, or written into a new buffer with room.
#[test]
fn an_append_fills_exactly_the_right_side_once_on_every_path() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut fills = 0;
    let mut append = |h: &mut Heap, left: &[u8], view: Option<BinView>, right: &[u8]| {
        let appended = unsafe {
            h.alloc_concatenation(left, view, right.len(), |dest| {
                assert_eq!(
                    dest.len(),
                    right.len(),
                    "the fill gets the right side's bytes and no more"
                );
                fills += 1;
                dest.write_copy_of_slice(right);
            })
        };
        let mut expected = left.to_vec();
        expected.extend_from_slice(right);
        assert_eq!(binary_bytes(appended), expected);
        appended
    };

    let inline = append(&mut h, b"ten bytes!", None, b"+five");
    assert!(
        inline.heap_addr().is_some() && binview_addr_from_tagged(inline.ref_word().raw_word()).is_none(),
        "a small result is inline"
    );

    let left = [7u8; SHARED_BIN_THRESHOLD_BYTES];
    let grown = append(&mut h, &left, None, b"abc");
    let grown_view = view_of_result(grown);
    let longer = append(&mut h, &binary_bytes(grown), Some(grown_view), b"de");
    assert_eq!(
        view_of_result(longer).shared_raw(),
        grown_view.shared_raw(),
        "a right side that fits is written into the left side's buffer"
    );
    assert_eq!(
        grown_view.bytes_len(),
        left.len() + 3,
        "the left side keeps its own length"
    );

    let room = unsafe { &*grown_view.shared_raw() }.spare();
    let overflow = vec![9u8; room + 1];
    let moved = append(&mut h, &binary_bytes(longer), Some(view_of_result(longer)), &overflow);
    assert_ne!(
        view_of_result(moved).shared_raw(),
        grown_view.shared_raw(),
        "a right side that does not fit goes to a new buffer"
    );
    assert_eq!(fills, 4, "each append writes its right side once");
}

/// A fill may read the left side it follows: appending a binary to itself
/// copies from bytes that stay where they are, in a buffer that extends in
/// place.
#[test]
fn an_append_fill_may_read_the_left_side() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let left: Vec<u8> = (0..100u8).collect();
    let first = unsafe { h.alloc_concatenation(&left, None, 0, |_| {}) };
    let first_view = view_of_result(first);
    let doubled = unsafe {
        let source = std::slice::from_raw_parts(first_view.bytes_ptr(), first_view.bytes_len());
        h.alloc_concatenation(source, Some(first_view), source.len(), |dest| {
            dest.write_copy_of_slice(source);
        })
    };
    let expected: Vec<u8> = left.iter().chain(left.iter()).copied().collect();
    assert_eq!(binary_bytes(doubled), expected);
    assert_eq!(binary_bytes(first), left, "the value appended to is unchanged");
}

/// Full spawn-and-share scenario at the heap layer.
#[test]
fn shared_heap_acceptance_spawn_and_share() {
    const N: usize = 4;
    let payload: Vec<u8> = (0..128u8).collect();
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bs_in_sender = sender.alloc_bitstring(&payload, 1024).heap_addr().expect("binview");
    let witness = unsafe { SharedBinHandle::retain_from_raw(BinView::from_raw(bs_in_sender).shared_raw()) };
    assert_eq!(shared_refs(&witness), 2);

    let mut receivers: Vec<Heap> = (0..N).map(|_| Heap::new(SIZE_TABLE[0], fresh_registry())).collect();
    let sender_bits = heap_object_word(bs_in_sender as *const u8, ValueKind::BINVIEW);
    let mut receiver_roots: Vec<u64> = Vec::with_capacity(N);
    for r in receivers.iter_mut() {
        let copied = deep_copy_slot(heap_root(sender_bits), &sender.view(), r);
        receiver_roots.push(tagged_bits(copied));
    }
    assert_eq!(
        shared_refs(&witness),
        2 + N,
        "the witness and sender keep one edge each"
    );

    for (r, root_ptr) in receivers.iter_mut().zip(receiver_roots.iter_mut()) {
        let mut root_u8 = *root_ptr as *mut u8;
        r.collect_tagged(&mut root_u8);
        *root_ptr = root_u8 as u64;
        let chain = off_heap_old_chain(r);
        assert_eq!(chain.len(), 1);
        let view = unsafe { BinView::from_raw(crate::any_value::heap_addr_from_tagged(*root_ptr).expect("view root")) };
        assert_eq!(chain[0], view.binref().word(), "the chain holds the view's BinRef");
    }
    assert_eq!(shared_refs(&witness), 2 + N, "moving stubs preserve their shared edges");

    for root_ptr in &receiver_roots {
        unsafe {
            assert_eq!(Bin::of_binary(*root_ptr).bit_len(), 1024);
            let bp = Bin::of_binary(*root_ptr).ptr();
            for (i, expected) in payload.iter().enumerate() {
                assert_eq!(*bp.add(i), *expected);
            }
        }
    }

    let _ = receiver_roots;
    drop(receivers);
    assert_eq!(shared_refs(&witness), 2, "all receiver edges are released");

    drop(sender);
    assert_eq!(shared_refs(&witness), 1, "the sender releases its edge too");
}

// ===== blocks above the size table =====================================

/// The last table entry: anything larger than this is outside the pool.
const TABLE_CEILING: usize = SIZE_TABLE[SIZE_TABLE.len() - 1];

/// A struct schema whose object is larger than every table entry, so the heap
/// must give it an exact block.
fn above_table_schema(reg: &Rc<RefCell<SchemaRegistry>>) -> u32 {
    let n_fields = (TABLE_CEILING + 256) / 8;
    let fields = (0..n_fields)
        .map(|i| FieldDescriptor {
            offset: (i * 8) as u32,
            kind: FieldKind::AnyValue,
            name: None,
        })
        .collect();
    reg.borrow_mut().register(Schema {
        identity: SchemaIdentity::Internal("Big".into()),
        size: (n_fields * 8) as u32,
        fields,
    })
}

fn struct_root(p: *mut u8) -> *mut u8 {
    heap_object_word(p as *const u8, ValueKind::STRUCT) as *mut u8
}

/// An object larger than the table's last entry takes a block of exactly its
/// size, parked beside the tip, and that block is outside the pool: the pool's
/// outstanding count is the same before and after.
#[test]
fn an_object_above_the_table_allocates_into_an_exact_unpooled_block() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let pooled_before = pool_outstanding_blocks();
    let want = TABLE_CEILING + 8;

    let p = h.alloc(want);

    assert!(!p.is_null());
    assert_eq!(h.block_size, SIZE_TABLE[0], "the tip did not move");
    assert_eq!(h.bytes_remaining_in_block(), SIZE_TABLE[0]);
    let parked = h.young_blocks.last().expect("the huge object's block is parked");
    assert_eq!(parked.start, p);
    assert_eq!(
        parked.capacity,
        TABLE_CEILING + 16,
        "capacity is the size rounded to 16"
    );
    assert_eq!(
        parked.fill(),
        TABLE_CEILING + 16,
        "the block holds the object and nothing else"
    );
    assert_eq!(h.young_blocks.len(), 1);
    assert_eq!(
        pool_outstanding_blocks(),
        pooled_before,
        "an exact block never touches the pool"
    );
    assert!(h.bytes_used() >= TABLE_CEILING + 16);
}

/// A huge object is parked alone and the tip keeps serving small allocations:
/// the tip's capacity does not move and the small object lands in it.
#[test]
fn a_huge_object_parks_and_the_next_small_allocation_lands_in_the_unmoved_tip() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let (tip_start, tip_capacity) = (h.block_start, h.block_size);
    let huge = next_block_capacity(tip_capacity) + 16;

    let big = h.alloc(huge);
    let small = h.alloc(16);

    assert_eq!(h.block_size, tip_capacity, "the tip's capacity did not move");
    assert_eq!(h.block_start, tip_start);
    assert_eq!(small, tip_start, "the small object is the tip's first");
    assert_eq!(h.bump_top, unsafe { tip_start.add(16) });
    assert_eq!(h.young_blocks.len(), 1);
    assert_eq!(h.young_blocks[0].start, big);
    assert_eq!(h.young_blocks[0].capacity, pick_block_capacity(huge));
    assert_eq!(h.node.alloc_stats().total.allocs, 2);
}

/// An allocation that exactly fills the capacity one step up is not huge: the
/// tip is parked and climbs a step as before.
#[test]
fn an_allocation_within_one_step_of_the_tip_still_climbs_the_tip() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let (tip_start, tip_capacity) = (h.block_start, h.block_size);
    let step = next_block_capacity(tip_capacity);
    h.alloc(tip_capacity);

    let p = h.alloc(step);

    assert_eq!(h.block_size, step, "the tip climbed one step");
    assert_eq!(h.block_start, p);
    assert_eq!(h.young_blocks.len(), 1);
    assert_eq!(h.young_blocks[0].start, tip_start, "the old tip is what was parked");
    assert_eq!(h.young_blocks[0].capacity, tip_capacity);
}

/// A live huge object parked beside the tip is copied by a collection and its
/// exact block goes back to the system allocator.
#[test]
fn a_collection_copies_a_parked_huge_object_and_releases_its_block() {
    let reg = fresh_registry();
    let id = above_table_schema(&reg);
    let mut h = Heap::new(SIZE_TABLE[0], reg);
    let big = h.alloc_struct(id);
    assert_eq!(h.young_blocks.len(), 1, "the huge object is parked");
    let mut root = struct_root(big);

    let mut stats = GcStats::default();
    let collected = h.collect_tagged_held(&mut root, &mut stats);
    let released = collected.heap().collected_blocks().blocks_released();
    drop(collected);

    let moved = struct_addr_from_tagged(root as u64).expect("root is still a struct");
    assert_ne!(moved, big);
    assert!(h.contains_heap_addr(moved));
    assert!(!h.contains_heap_addr(big), "the parked exact block was released");
    assert_eq!(h.old_blocks.len(), 1, "the copy is parked alone in a block of its own");
    assert_eq!(stats.copied_objects, 1);
    assert_eq!(stats.blocks_after, 1, "the copy's block");
    assert_eq!(released, 2, "the tip and the parked block");
}

/// A gift window sizes its one block to the measured bytes, so a huge
/// allocation inside it is a disagreement between measure and copy.
#[test]
#[should_panic(expected = "huge object was allocated inside a gift window")]
fn a_huge_allocation_inside_a_gift_window_is_refused() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    h.begin_gift(SIZE_TABLE[0]);
    h.alloc(SIZE_TABLE[0]);
    h.alloc(next_block_capacity(SIZE_TABLE[0]) + 16);
}

/// A rooted object above the table is copied like any other: it moves, it
/// lands alone in its own block, and the root follows it.
#[test]
fn a_rooted_object_above_the_table_survives_a_collection_by_being_copied() {
    let reg = fresh_registry();
    let id = above_table_schema(&reg);
    let mut h = Heap::new(SIZE_TABLE[0], reg);
    let big = h.alloc_struct(id);
    let size = TABLE_CEILING + 256 + 8;
    let mut root = struct_root(big);

    let stats = h.collect_tagged(&mut root);

    let moved = struct_addr_from_tagged(root as u64).expect("root is still a struct");
    assert_ne!(moved, big, "the object was copied, not marked in place");
    assert!(h.contains_heap_addr(moved));
    assert!(!h.contains_heap_addr(big), "its old block went back");
    assert_eq!(stats.copied_objects, 1);
    assert_eq!(stats.live_objects, 1);
    assert_eq!(
        stats.live_bytes, h.live_baseline as u64,
        "live bytes are the bytes in the heap's blocks"
    );
    assert!(stats.live_bytes as usize >= size);
}

/// An unrooted object above the table is reclaimed by the collection that
/// finds it dead, and the heap sheds the capacity it needed on the next one.
#[test]
fn an_unrooted_object_above_the_table_is_freed_by_a_collection() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let pooled_before = pool_outstanding_blocks();
    let p = h.alloc(TABLE_CEILING + 16);
    let mut root: *mut u8 = null_mut();

    let stats = h.collect_tagged(&mut root);

    assert!(!h.contains_heap_addr(p), "the exact block was released");
    assert!(h.young_blocks.is_empty());
    assert_eq!(stats.live_bytes, 0);
    assert_eq!(stats.live_objects, 0);
    assert_eq!(
        pool_outstanding_blocks(),
        pooled_before,
        "the old tip went back to the pool and the fresh tip took its place"
    );

    h.collect_tagged(&mut root);
    assert_eq!(
        h.block_size, BUDGET_FLOOR,
        "with nothing live the heap is back to a tip of the budget floor"
    );
}

/// An object above the table that holds an edge to a small object carries it
/// through the collection: the child is copied and the field follows it.
#[test]
fn an_object_above_the_table_keeps_its_small_children_alive() {
    let reg = fresh_registry();
    let id = above_table_schema(&reg);
    let mut h = Heap::new(SIZE_TABLE[0], reg);
    let cons = alloc_int_list_cons(&mut h, 7, EMPTY_LIST);
    let big = h.alloc_struct(id);
    unsafe { h.write_field_slot(big, 0, heap_root(cons)) };
    let mut root = struct_root(big);

    h.collect_tagged(&mut root);

    let moved = struct_addr_from_tagged(root as u64).expect("struct root");
    let child = h.read_field_slot(moved, 0);
    assert_eq!(child.kind(), ValueKind::LIST);
    assert!(h.contains_heap_addr(child.raw() as *mut u8));
    let cons = unsafe { &*(child.raw() as *const ListCons) };
    assert_eq!(cons.head_kind(), ValueKind::INT);
    assert_eq!(cons.head as i64, 7);
}

/// Two objects above the table, one reaching the other, both survive; a third
/// that nothing reaches does not.
#[test]
fn objects_above_the_table_are_kept_by_reachability_alone() {
    let reg = fresh_registry();
    let id = above_table_schema(&reg);
    let mut h = Heap::new(SIZE_TABLE[0], reg);
    let head = h.alloc_struct(id);
    let tail = h.alloc_struct(id);
    let _dead = h.alloc_struct(id);
    unsafe { h.write_field_slot(head, 0, AnyValue::heap_ptr(tail, ValueKind::STRUCT)) };
    let mut root = struct_root(head);

    let stats = h.collect_tagged(&mut root);

    assert_eq!(
        stats.copied_objects, 2,
        "head and tail were copied; the unreached one was not"
    );
    assert_eq!(stats.live_objects, 2);
    let moved = struct_addr_from_tagged(root as u64).expect("struct root");
    let moved_tail = h.read_field_slot(moved, 0);
    assert_eq!(moved_tail.kind(), ValueKind::STRUCT);
    assert!(h.contains_heap_addr(moved_tail.raw() as *mut u8));
}

/// Dropping a heap that holds exact blocks returns them to the allocator and
/// leaves the pool's accounting exact.
#[test]
fn dropping_a_heap_with_an_object_above_the_table_releases_everything() {
    let pooled_before = pool_outstanding_blocks();
    {
        let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
        let _ = h.alloc(TABLE_CEILING + 16);
        let _ = h.alloc(TABLE_CEILING + 16);
        assert_eq!(
            pool_outstanding_blocks(),
            pooled_before + 1,
            "only the first pooled block is counted"
        );
    }
    assert_eq!(pool_outstanding_blocks(), pooled_before);
}

#[test]
fn binview_round_trips_through_bitstring_dispatchers() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bytes: Vec<u8> = (0..100u8).collect();
    let p = h.alloc_bitstring(&bytes, 800).heap_addr().expect("binview");
    let tagged = heap_object_word(p, ValueKind::BINVIEW);
    let bl = unsafe { Bin::of_binary(tagged).bit_len() };
    let bp = unsafe { Bin::of_binary(tagged).ptr() };
    assert_eq!(bl, 800);
    let recovered: Vec<u8> = (0..100).map(|i| unsafe { *bp.add(i) }).collect();
    assert_eq!(recovered, bytes);
}

/// A receiver that has grafted many small gifts holds a block per gift. A
/// collection forwards every gifted object and leaves every tagged literal
/// where it is, reading one bit per pointer rather than searching the chain.
#[test]
fn many_grafted_gifts_collect_with_every_survivor_forwarded_and_every_literal_left_in_place() {
    const GIFTS: usize = 64;
    let closure = ReadOnlyClosure::new();
    let registry = fresh_registry();
    let mut sender = Heap::new(SIZE_TABLE[0], registry.clone());
    let mut receiver = Heap::new(SIZE_TABLE[0], registry);
    let mut roots = Vec::new();
    for _ in 0..GIFTS {
        let holder = sender.alloc_closure_slots(crate::any_value::ClosureDenotationId::user(73), 1, 1, 0);
        unsafe { closure_capture_set(closure_addr_from_tagged(holder).expect("holder"), 0, closure.value()) };
        let (segment, copied) = crate::sched::gift_copy(&mut sender, &[heap_ref(holder)]);
        receiver.graft(segment);
        roots.push(copied[0]);
    }
    let gifted: Vec<*mut u8> = roots
        .iter()
        .map(|root| root.closure_addr().expect("gifted closure"))
        .collect();
    roots.push(closure.value().ref_word());

    receiver.collect_stats(&mut roots);

    for (root, before) in roots[..GIFTS].iter().zip(&gifted) {
        let moved = root.closure_addr().expect("forwarded closure");
        assert_ne!(moved, *before, "a gifted survivor is forwarded");
        assert!(receiver.contains_heap_addr(moved));
        assert_eq!(
            unsafe { closure_capture_value(moved, 0) },
            closure.value(),
            "the literal it captures is still the tagged static closure"
        );
    }
    assert!(roots[GIFTS].is_literal());
    assert_eq!(
        roots[GIFTS].closure_addr(),
        Ok(closure.page),
        "a literal root is left in place"
    );
}

/// A scalar field's ref points into the struct's own payload, so it is
/// read-only data exactly when the struct is.
#[test]
fn a_scalar_field_read_from_a_tagged_literal_is_tagged() {
    let registry = fresh_registry();
    let pair = registry.borrow_mut().register(Schema::tuple_of_arity(2));
    let mut h = Heap::new(SIZE_TABLE[0], registry);
    let obj = h.alloc_struct(pair);
    unsafe { h.write_field_slot(obj, 0, AnyValue::int(7)) };
    let plain = AnyValueRef::from_heap_object(ValueKind::STRUCT, obj).expect("struct ref");

    let from_heap = h.read_struct_field_ref(plain, 0).expect("heap field");
    let from_literal = h.read_struct_field_ref(plain.literal(), 0).expect("literal field");

    assert!(!from_heap.is_literal(), "a field of a heap struct is heap data");
    assert!(from_literal.is_literal(), "a field of a literal struct is literal data");
    assert_eq!(from_literal.load_int().unwrap(), 7);
}

/// A heap child stored in a literal parent keeps the bit its payload word
/// carries; the parent being literal does not tag it.
#[test]
fn a_literal_child_read_from_a_struct_keeps_its_stored_tag() {
    let closure = ReadOnlyClosure::new();
    let registry = fresh_registry();
    let pair = registry.borrow_mut().register(Schema::tuple_of_arity(2));
    let mut h = Heap::new(SIZE_TABLE[0], registry);
    let obj = h.alloc_struct(pair);
    unsafe { h.write_field_slot(obj, 0, closure.value()) };
    let parent = AnyValueRef::from_heap_object(ValueKind::STRUCT, obj).expect("struct ref");

    let child = h.read_struct_field_ref(parent, 0).expect("child");

    assert!(child.is_literal());
    assert_eq!(child.closure_addr(), Ok(closure.page));
}

/// The debug cross-check makes a literal that lost its tag loud: its address
/// lies outside from-space while an untagged pointer must lie inside.
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "an untagged heap pointer")]
fn a_literal_that_lost_its_tag_faults_the_collection() {
    let closure = ReadOnlyClosure::new();
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut roots = [AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure.page).expect("untagged ref")];

    h.collect_stats(&mut roots);
}

/// A map holding a static closure and a static struct survives a collection
/// with both left in place. The struct stands in for a compiled literal: it
/// lives outside the collected heap and its references carry the bit.
#[test]
fn a_map_holding_a_literal_closure_and_a_literal_struct_survives_a_collection_with_both_in_place() {
    let closure = ReadOnlyClosure::new();
    let registry = fresh_registry();
    let pair = registry.borrow_mut().register(Schema::tuple_of_arity(2));
    let mut elsewhere = Heap::new(SIZE_TABLE[0], registry.clone());
    let built = elsewhere.alloc_struct(pair);
    // A literal sits outside every heap block, as a compiled program's static
    // does: the struct is copied out of the heap that built it.
    let struct_bytes = struct_size_for_payload(Schema::tuple_of_arity(2).allocation_payload_size());
    let mut static_storage = vec![0u128; struct_bytes / 16];
    let static_struct = static_storage.as_mut_ptr() as *mut u8;
    unsafe { std::ptr::copy_nonoverlapping(built, static_struct, struct_bytes) };
    let literal_struct = AnyValue::HeapRef(
        AnyValueRef::from_heap_object(ValueKind::STRUCT, static_struct)
            .expect("struct ref")
            .literal(),
    );
    let mut h = Heap::new(SIZE_TABLE[0], registry);
    let (k1, k2) = (h.node.intern_atom("closure"), h.node.intern_atom("struct"));
    let map = h.alloc_map_slots(&[
        (AnyValue::atom(k1), closure.value()),
        (AnyValue::atom(k2), literal_struct),
    ]);
    let mut roots = [heap_ref(map)];

    h.collect_stats(&mut roots);

    let moved = roots[0].map_addr().expect("moved map");
    assert!(h.contains_heap_addr(moved), "the map itself was forwarded");
    let mut held = |key: u32| h.read_map_value(roots[0], AnyValue::atom(key)).expect("entry");
    assert!(held(k1).is_literal());
    assert_eq!(
        held(k1).closure_addr(),
        Ok(closure.page),
        "the static closure stays in place"
    );
    assert!(held(k2).is_literal());
    assert_eq!(
        held(k2).struct_addr(),
        Ok(static_struct),
        "the static struct stays in place"
    );
}

/// A struct's fields sit where `SlotLayout` says for every schema the
/// language can build: compiled code places a field by the layout alone,
/// the runtime by the schema, and the two must agree.
#[test]
fn a_slot_layout_places_fields_where_the_schema_does() {
    let named = |fields: usize| {
        Schema::named_struct(
            ModuleName::from_segments(vec!["Rec".to_string()]),
            (0..fields).map(|index| format!("f{index}")),
        )
    };
    for fields in 0..20 {
        for schema in [Schema::tuple_of_arity(fields), named(fields)] {
            let layout = SlotLayout::of(fields);
            assert_eq!(layout.payload_size(), schema.allocation_payload_size());
            for (index, (field, kind_offset)) in schema.any_value_fields_with_kind_offsets().enumerate() {
                assert_eq!(
                    SlotLayout::slot_offset(index),
                    STRUCT_PAYLOAD_OFFSET + field.offset as usize
                );
                assert_eq!(layout.kind_offset(index), STRUCT_PAYLOAD_OFFSET + kind_offset as usize);
            }
        }
    }
}

/// An unwritten struct is complete once each field is stored: nothing reads
/// the bytes the allocation left alone. The payload is dirtied first so a
/// store that skipped a byte would show.
#[test]
fn an_unwritten_struct_reads_back_exactly_what_was_stored() {
    let reg = fresh_registry();
    let schema = reg.borrow_mut().register(Schema::tuple_of_arity(3));
    let mut h = Heap::new(SIZE_TABLE[0], reg);
    let layout = SlotLayout::of(3);
    let list = alloc_int_list_cons(&mut h, 7, EMPTY_LIST_BITS);
    let int_slot = 41u64;
    let values = [
        AnyValueRef::from_scalar_slot(ValueKind::INT, &int_slot).unwrap(),
        list_ref_from_bits(list),
        AnyValueRef::empty_list(),
    ];
    let header = h.schemas.borrow().struct_header(schema);
    let object = h.alloc_struct_unwritten(header, layout.size());
    unsafe { std::ptr::write_bytes(object.add(STRUCT_PAYLOAD_OFFSET), 0xFF, layout.payload_size()) };
    for (index, value) in values.into_iter().enumerate() {
        unsafe {
            h.store_struct_field(
                object,
                SlotLayout::slot_offset(index),
                layout.kind_offset(index),
                AnyValue::from_ref(value).expect("value"),
            )
        }
        .expect("store");
    }

    assert_eq!(h.read_field_slot(object, 0), AnyValue::int(41));
    assert_eq!(
        h.read_field_slot(object, 8),
        AnyValue::from_ref(list_ref_from_bits(list)).unwrap()
    );
    assert_eq!(h.read_field_slot(object, 16), AnyValue::EmptyList);
    assert_eq!(
        h.share(list_ref_from_bits(list)).unwrap(),
        0,
        "the store shared the list the struct now holds"
    );
}

/// A copy is the same struct in a new object: every slot and kind byte comes
/// across, a list it holds is shared with the original, and writing the copy
/// leaves the original alone.
#[test]
fn a_struct_copy_holds_every_field_and_leaves_the_original_alone() {
    let reg = fresh_registry();
    let schema = reg.borrow_mut().register(Schema::tuple_of_arity(3));
    let mut h = Heap::new(SIZE_TABLE[0], reg);
    let list = alloc_int_list_cons(&mut h, 7, EMPTY_LIST_BITS);
    let held = AnyValue::from_ref(list_ref_from_bits(list)).unwrap();
    let original = h.alloc_struct(schema);
    unsafe {
        h.write_field_slot(original, 0, AnyValue::int(41));
        h.write_field_slot(original, 8, held);
        h.write_field_slot(original, 16, AnyValue::EmptyList);
    }

    let copy = unsafe { h.copy_struct(original, SlotLayout::of(3)) };
    assert_ne!(copy, original);
    assert_eq!(unsafe { struct_schema_id(copy) }, schema);
    assert_eq!(h.read_field_slot(copy, 0), AnyValue::int(41));
    assert_eq!(h.read_field_slot(copy, 8), held);
    assert_eq!(h.read_field_slot(copy, 16), AnyValue::EmptyList);
    assert_eq!(
        h.share(list_ref_from_bits(list)).unwrap(),
        0,
        "the copy shared the list both structs now hold"
    );

    unsafe { h.write_field_slot(copy, 0, AnyValue::atom(3)) };
    assert_eq!(h.read_field_slot(copy, 0), AnyValue::atom(3));
    assert_eq!(h.read_field_slot(original, 0), AnyValue::int(41));
}

/// A map literal whose keys the compiler has already put in key order needs
/// no sort: publishing it in place leaves the same bytes a sorted build of
/// the same entries does.
#[test]
fn a_destination_filled_in_key_order_publishes_the_bytes_a_sorted_one_does() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let [a, b, c] = ["a", "b", "c"].map(|name| AnyValue::atom(h.node.intern_atom(name)));
    let list = heap_root(h.alloc_list_cons_slot(AnyValue::int(7), EMPTY_LIST));
    let entries = [(a, AnyValue::int(1)), (b, list), (c, AnyValue::float(2.5))];

    let sorted = h.alloc_map_destination(3);
    for (key, value) in [entries[2], entries[0], entries[1]] {
        unsafe { h.map_destination_put(sorted, key, value) };
    }
    let sorted = h.map_destination_freeze(sorted).expect("a build publishes");

    let ordered = h.alloc_map_destination(3);
    for (key, value) in entries {
        unsafe { h.map_destination_put(ordered, key, value) };
    }
    let ordered = h.map_destination_publish(ordered);

    let bytes = |map: AnyValueRef| unsafe {
        std::slice::from_raw_parts(map.map_addr().expect("map").cast_const(), map_size_for_count(3))
    };
    assert_eq!(bytes(ordered), bytes(sorted));
}

#[test]
fn a_destination_with_a_repeated_key_publishes_the_map_its_last_values_make() {
    // A literal whose keys arrive at run time can repeat one, so its
    // destination holds more entries than the map it publishes: the entries
    // are sorted and merged where they stand and moved down to the smaller
    // layout, giving the bytes a map built from the same entries has.
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let [a, b, c] = ["a", "b", "c"].map(|name| AnyValue::atom(h.node.intern_atom(name)));
    let puts = [
        (c, AnyValue::int(3)),
        (a, AnyValue::int(1)),
        (c, AnyValue::float(2.5)),
        (b, AnyValue::int(2)),
    ];

    let built = h.alloc_map_destination(puts.len());
    for (key, value) in puts {
        unsafe { h.map_destination_put(built, key, value) };
    }
    let built = h.map_destination_freeze(built).expect("a build publishes");
    let built = built.map_addr().expect("map");
    let expected = map_addr_from_tagged(h.alloc_map_slots(&puts)).expect("map");

    let bytes = |map: *mut u8| unsafe { std::slice::from_raw_parts(map.cast_const(), map_size_for_count(3)) };
    assert_eq!(
        bytes(built),
        bytes(expected),
        "one entry per key, in key order, the last value kept"
    );
}

#[test]
fn map_publication_orders_keys_and_keeps_the_last_value_of_a_repeated_key_at_every_size() {
    // Lists shorter than, equal to and longer than the stack buffer all give
    // the same map: keys ascending, one entry per key, the last value kept.
    for distinct in [
        0usize,
        1,
        5,
        imp::MAP_STACK_ENTRIES - 1,
        imp::MAP_STACK_ENTRIES,
        imp::MAP_STACK_ENTRIES + 7,
    ] {
        let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
        let mut entries: Vec<(AnyValue, AnyValue)> = (0..distinct as i64)
            .rev()
            .map(|key| (AnyValue::int(key), AnyValue::int(key * 10)))
            .collect();
        if distinct > 0 {
            entries.push((AnyValue::int(0), AnyValue::int(-1)));
        }
        let map = heap.alloc_map_slots(&entries);
        let layout = MapLayout::Entries(map_addr_from_tagged(map).expect("a map"));
        let published = heap.map_view_entries(layout);
        let expected: Vec<(AnyValue, AnyValue)> = (0..distinct as i64)
            .map(|key| (AnyValue::int(key), AnyValue::int(if key == 0 { -1 } else { key * 10 })))
            .collect();
        assert_eq!(published, expected, "{distinct} distinct keys");
    }
}

#[test]
fn boxing_an_atom_allocates_nothing_and_the_ref_carries_its_id() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let before = h.node.alloc_stats();

    let atom = h.box_any_value_ref(AnyValue::atom(1234));

    let after = h.node.alloc_stats();
    assert_eq!(after.scalar_box.allocs, before.scalar_box.allocs);
    assert_eq!(after.total.allocs, before.total.allocs);
    assert_eq!(atom, AnyValueRef::atom(1234));
    assert_eq!(atom.load_atom(), Ok(1234));
}

#[test]
fn an_atom_ref_is_a_root_the_collector_leaves_as_it_is() {
    let mut h = Heap::new(1024, fresh_registry());
    let original = AnyValueRef::atom(77);
    let mut roots = [original];

    let stats = h.collect_stats(&mut roots);

    assert_eq!(roots[0], original);
    assert_eq!(roots[0].load_atom(), Ok(77));
    assert_eq!(stats.copied_objects, 0);
    assert_eq!(stats.copied_bytes, 0);
}

#[test]
fn an_atom_read_from_a_list_head_is_the_atom_stored() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bits = h.alloc_list_cons_slot(AnyValue::atom(9), EMPTY_LIST_BITS);
    let list = AnyValueRef::from_heap_object(ValueKind::LIST, list_addr_from_tagged(bits).expect("list addr"))
        .expect("list ref");

    assert_eq!(list_head_ref(list), Ok(AnyValueRef::atom(9)));
}

#[test]
fn an_atom_read_from_a_map_key_or_value_is_the_atom_stored() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let key_atom = h.node.intern_atom("key");
    let value_atom = h.node.intern_atom("value");
    let bits = h.alloc_map_slots(&[(AnyValue::atom(key_atom), AnyValue::atom(value_atom))]);
    let map =
        AnyValueRef::from_heap_object(ValueKind::MAP, map_addr_from_tagged(bits).expect("map addr")).expect("map ref");

    let (key, value) = unsafe { super::ref_io::map_entry_refs(map.map_addr().expect("map addr"), 0) };

    assert_eq!(key, AnyValueRef::atom(key_atom));
    assert_eq!(value, AnyValueRef::atom(value_atom));
    assert_eq!(
        h.read_map_value(map, AnyValue::atom(key_atom)),
        Some(AnyValueRef::atom(value_atom))
    );
}

#[test]
fn an_atom_read_from_a_struct_field_or_closure_capture_is_the_atom_stored() {
    let reg = fresh_registry();
    let schema = reg.borrow_mut().register(Schema::tuple_of_arity(1));
    let mut h = Heap::new(SIZE_TABLE[0], reg);

    let struct_addr = h.alloc_struct(schema);
    let struct_ref = AnyValueRef::from_heap_object(ValueKind::STRUCT, struct_addr).expect("struct ref");
    let layout = SlotLayout::of(1);
    unsafe {
        h.store_struct_field(
            struct_addr,
            SlotLayout::slot_offset(0),
            layout.kind_offset(0),
            AnyValue::from_ref(AnyValueRef::atom(21)).expect("value"),
        )
    }
    .expect("write atom field");
    assert_eq!(h.read_struct_field_ref(struct_ref, 0), Ok(AnyValueRef::atom(21)));

    let closure_bits = h.alloc_closure_slots(crate::any_value::ClosureDenotationId::user(0), 0, 1, 0);
    let closure = AnyValueRef::from_heap_object(
        ValueKind::CLOSURE,
        closure_addr_from_tagged(closure_bits).expect("closure addr"),
    )
    .expect("closure ref");
    unsafe {
        h.write_closure_capture_value(
            closure.closure_addr().expect("closure addr"),
            0,
            AnyValue::from_ref(AnyValueRef::atom(22)).expect("value"),
        )
    };
    assert_eq!(h.read_closure_capture_ref(closure, 0), Ok(AnyValueRef::atom(22)));
}

#[test]
fn an_atom_read_from_a_literal_struct_names_no_literal() {
    let reg = fresh_registry();
    let schema = reg.borrow_mut().register(Schema::tuple_of_arity(1));
    let mut h = Heap::new(SIZE_TABLE[0], reg);
    let struct_addr = h.alloc_struct(schema);
    let literal = AnyValueRef::from_heap_object(ValueKind::STRUCT, struct_addr)
        .expect("struct ref")
        .literal();
    unsafe {
        h.store_struct_field(
            struct_addr,
            SlotLayout::slot_offset(0),
            SlotLayout::of(1).kind_offset(0),
            AnyValue::from_ref(AnyValueRef::atom(5)).expect("value"),
        )
    }
    .expect("write atom field");

    let field = h.read_struct_field_ref(literal, 0).expect("field");

    assert!(!field.is_literal());
    assert_eq!(field, AnyValueRef::atom(5));
}

#[test]
fn boxing_a_pid_allocates_nothing_and_the_ref_round_trips_its_word() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let before = h.node.alloc_stats();

    let pid = h.box_any_value_ref(AnyValue::Opaque(ValueKind::PID, 0x1_0007));

    let after = h.node.alloc_stats();
    assert_eq!(after.scalar_box.allocs, before.scalar_box.allocs);
    assert_eq!(after.total.allocs, before.total.allocs);
    assert_eq!(pid.tag(), ValueKind::PID);
    assert_eq!(pid.load_opaque_word(ValueKind::PID), Ok(0x1_0007));
    assert_eq!(
        pid.raw_word() & AnyValueRefPacking::current().address_mask(),
        0x1_0007,
        "the pid sits in the address field and names no object"
    );
    assert_eq!(AnyValue::from_ref(pid), Ok(AnyValue::Opaque(ValueKind::PID, 0x1_0007)));
}

#[test]
fn boxing_a_reference_still_allocates_one_scalar_box() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let before = h.node.alloc_stats();

    let reference = h.box_any_value_ref(AnyValue::Opaque(ValueKind::REF, (3 << 32) | 9));

    assert_eq!(h.node.alloc_stats().scalar_box.allocs, before.scalar_box.allocs + 1);
    assert_eq!(reference.load_opaque_word(ValueKind::REF), Ok((3 << 32) | 9));
}

#[test]
fn a_pid_ref_is_a_root_the_collector_leaves_as_it_is() {
    let mut h = Heap::new(1024, fresh_registry());
    let original = h.box_any_value_ref(AnyValue::Opaque(ValueKind::PID, 77));
    let mut roots = [original];

    let stats = h.collect_stats(&mut roots);

    assert_eq!(roots[0], original);
    assert_eq!(roots[0].load_opaque_word(ValueKind::PID), Ok(77));
    assert_eq!(stats.copied_objects, 0);
    assert_eq!(stats.copied_bytes, 0);
}

#[test]
fn a_pid_read_from_a_list_head_map_value_struct_field_or_capture_is_the_pid_stored() {
    let reg = fresh_registry();
    let schema = reg.borrow_mut().register(Schema::tuple_of_arity(1));
    let mut h = Heap::new(SIZE_TABLE[0], reg);
    let pid_value = AnyValue::Opaque(ValueKind::PID, 21);
    let pid = h.box_any_value_ref(pid_value);

    let list_bits = h.alloc_list_cons_slot(pid_value, EMPTY_LIST_BITS);
    let list = AnyValueRef::from_heap_object(ValueKind::LIST, list_addr_from_tagged(list_bits).expect("list addr"))
        .expect("list ref");
    assert_eq!(list_head_ref(list), Ok(pid));

    let key = h.node.intern_atom("pid");
    let map_bits = h.alloc_map_slots(&[(AnyValue::atom(key), pid_value)]);
    let map = AnyValueRef::from_heap_object(ValueKind::MAP, map_addr_from_tagged(map_bits).expect("map addr"))
        .expect("map ref");
    assert_eq!(h.read_map_value(map, AnyValue::atom(key)), Some(pid));

    let struct_addr = h.alloc_struct(schema);
    let struct_ref = AnyValueRef::from_heap_object(ValueKind::STRUCT, struct_addr).expect("struct ref");
    unsafe {
        h.store_struct_field(
            struct_addr,
            SlotLayout::slot_offset(0),
            SlotLayout::of(1).kind_offset(0),
            AnyValue::from_ref(pid).expect("value"),
        )
    }
    .expect("write pid field");
    assert_eq!(h.read_struct_field_ref(struct_ref, 0), Ok(pid));
    assert_eq!(
        h.read_struct_field_ref(struct_ref.literal(), 0)
            .map(AnyValueRef::is_literal),
        Ok(false),
        "a pid read from a literal struct names no literal"
    );

    let closure_bits = h.alloc_closure_slots(crate::any_value::ClosureDenotationId::user(0), 0, 1, 0);
    let closure = AnyValueRef::from_heap_object(
        ValueKind::CLOSURE,
        closure_addr_from_tagged(closure_bits).expect("closure addr"),
    )
    .expect("closure ref");
    unsafe {
        h.write_closure_capture_value(
            closure.closure_addr().expect("closure addr"),
            0,
            AnyValue::from_ref(pid).expect("value"),
        )
    };
    assert_eq!(h.read_closure_capture_ref(closure, 0), Ok(pid));
}

#[test]
fn a_pid_in_a_struct_field_survives_a_collection() {
    let reg = fresh_registry();
    let schema = reg.borrow_mut().register(Schema::tuple_of_arity(1));
    let mut h = Heap::new(1024, reg);
    let pid = h.box_any_value_ref(AnyValue::Opaque(ValueKind::PID, 21));
    let struct_addr = h.alloc_struct(schema);
    unsafe {
        h.store_struct_field(
            struct_addr,
            SlotLayout::slot_offset(0),
            SlotLayout::of(1).kind_offset(0),
            AnyValue::from_ref(pid).expect("value"),
        )
    }
    .expect("write pid field");
    let mut roots = [AnyValueRef::from_heap_object(ValueKind::STRUCT, struct_addr).expect("struct ref")];

    h.collect_stats(&mut roots);

    assert_eq!(h.read_struct_field_ref(roots[0], 0), Ok(pid));
}

#[test]
fn inline_alloc_layout_names_the_fields_a_placement_updates() {
    let heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let base = (&heap as *const Heap).addr();
    let at = |field: usize| field - base;
    let layout = INLINE_ALLOC_LAYOUT;
    assert_eq!(layout.block_start, at((&heap.block_start as *const *mut u8).addr()));
    assert_eq!(layout.bump_top, at((&heap.bump_top as *const *mut u8).addr()));
    assert_eq!(layout.block_end, at((&heap.block_end as *const *mut u8).addr()));
}

/// Prepend `cells` fresh cells to `tail`, collect with the list as the only
/// root, and return the new head with the collection's stats.
fn grow_list_and_collect(h: &mut Heap, tail: u64, cells: usize) -> (u64, GcStats) {
    let mut head = tail;
    for i in 0..cells {
        head = alloc_int_list_cons(h, i as i64, head);
    }
    let mut roots = [heap_ref(head)];
    let stats = h.collect_stats(&mut roots);
    (roots[0].raw_word(), stats)
}

/// A minor collection's to-space is sized by what minor collections copy. A
/// major's copy is the whole live set, and the minor after it keeps only a few
/// young cells: its to-space is the smallest class, not the major's.
#[test]
fn a_minor_after_a_major_gets_a_to_space_of_its_own_copys_class() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut list = EMPTY_LIST;
    let major_copy = loop {
        let (next, stats) = grow_list_and_collect(&mut h, list, 40);
        list = next;
        if stats.generation == Generation::Major {
            break stats.copied_bytes as usize;
        }
    };
    assert!(
        pick_block_capacity(major_copy) > SIZE_TABLE[0],
        "the major's copy is larger than the smallest class"
    );

    let (_, stats) = grow_list_and_collect(&mut h, list, 1);

    assert_eq!(stats.generation, Generation::Minor);
    let to_space = h.old_blocks.last().expect("the minor's survivors are in a block");
    assert_eq!(to_space.capacity, SIZE_TABLE[0]);
}

/// A copy that outgrows its to-space block takes an overflow block sized for
/// the overflow, not one a growth step above the whole block: the room the
/// copy leaves unused in old blocks stays within one smallest class.
fn assert_overflow_leaves_at_most_one_step_unused(stats: &GcStats, h: &Heap, guess: usize, step: usize) {
    assert!(
        stats.copied_bytes as usize > guess,
        "the copy outgrew its to-space guess of {guess}"
    );
    assert_eq!(stats.to_space_guess_bytes as usize, guess);
    let to_space_capacity = h.collected_blocks().to_space_capacity_bytes();
    let unused = to_space_capacity - stats.copied_bytes;
    assert!(
        unused <= step as u64,
        "{unused} bytes of the to-space are unused, more than the overflow step"
    );
    assert_eq!(
        to_space_capacity as usize,
        guess + step,
        "one overflow block of the step's class follows the guess block"
    );
    assert!(h.old_blocks.iter().any(|block| block.capacity == step));
}

#[test]
fn a_major_that_outgrows_its_guess_overflows_into_a_block_of_the_overflow_step() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut list = EMPTY_LIST;
    loop {
        let raw_guess = h.live_baseline.max(SIZE_TABLE[0]);
        let guess = pick_tip_capacity(raw_guess);
        let step = if raw_guess >= TABLE_CEILING {
            TABLE_CEILING
        } else {
            SIZE_TABLE[0]
        };
        let (next, stats) = grow_list_and_collect(&mut h, list, 8);
        list = next;
        if stats.generation == Generation::Major && stats.copied_bytes as usize > guess {
            assert_overflow_leaves_at_most_one_step_unused(&stats, &h, guess, step);
            assert_eq!(stats.blocks_after, 2);
            return;
        }
    }
}

#[test]
fn a_minor_that_outgrows_its_guess_overflows_into_a_smallest_class_block() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    // A heap with nothing old collects minor; its guess is the smallest class.
    let (_, stats) = grow_list_and_collect(&mut h, EMPTY_LIST, SIZE_TABLE[0] / 16 + 8);

    assert_eq!(stats.generation, Generation::Minor);
    assert_overflow_leaves_at_most_one_step_unused(&stats, &h, SIZE_TABLE[0], SIZE_TABLE[0]);
    assert_eq!(stats.blocks_after, 2);
}

/// A full tip is left behind for a fresh one a step up, and the answer is the
/// first address of that fresh tip with `size` taken from it. The allocation
/// is not counted: whoever asked for room counts it.
#[test]
fn room_beyond_a_full_tip_answers_the_start_of_a_fresh_tip() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let (tip_start, tip_capacity) = (h.block_start, h.block_size);
    h.alloc(tip_capacity);
    let counted = h.node.alloc_stats();

    let p = h.room(32);

    assert_eq!(
        h.block_size,
        next_block_capacity(tip_capacity),
        "the tip climbed a step"
    );
    assert_eq!(p, h.block_start, "the object starts the fresh tip");
    assert_eq!(h.bump_top, unsafe { p.add(32) }, "the tip is advanced past the object");
    assert_eq!(h.young_blocks.len(), 1);
    assert_eq!(h.young_blocks[0].start, tip_start, "the full tip is what was parked");
    assert_eq!(h.node.alloc_stats(), counted, "room does not count the allocation");
}

/// An object too large for any tip one step up is parked alone, and the tip
/// the compiled code was bumping stays where it was.
#[test]
fn room_for_a_huge_object_parks_it_alone_and_leaves_the_tip() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let (tip_start, tip_capacity) = (h.block_start, h.block_size);
    h.alloc(tip_capacity);
    let (top, counted) = (h.bump_top, h.node.alloc_stats());
    let huge = next_block_capacity(tip_capacity) + 16;

    let p = h.room(huge);

    assert_eq!(h.block_start, tip_start, "the tip did not move");
    assert_eq!(h.bump_top, top);
    assert_eq!(h.young_blocks.len(), 1);
    assert_eq!(h.young_blocks[0].start, p, "the parked block starts with the object");
    assert_eq!(h.young_blocks[0].capacity, pick_block_capacity(huge));
    assert_eq!(h.node.alloc_stats(), counted, "room does not count the allocation");
}

/// Two references a holder keeps in its own fields, which it hands to the
/// collection one after the other.
struct TwoHeldRefs {
    first: AnyValueRef,
    second: AnyValueRef,
}

impl Roots for TwoHeldRefs {
    fn forward_into(&mut self, forwarder: &mut RootForwarder<'_, '_>) {
        forwarder.forward(&mut self.first);
        forwarder.forward(&mut self.second);
    }
}

/// The holder's own fields hold the forwarded values afterwards: the
/// collection builds no list of roots and copies none back.
#[test]
fn a_collection_forwards_each_root_where_its_holder_keeps_it() {
    let mut h = Heap::new(1024, fresh_registry());
    let first = alloc_int_list_cons(&mut h, 1, EMPTY_LIST);
    let second = alloc_int_list_cons(&mut h, 2, EMPTY_LIST);
    let (first_before, second_before) = (
        list_addr_from_tagged(first).unwrap(),
        list_addr_from_tagged(second).unwrap(),
    );
    let mut held = TwoHeldRefs {
        first: AnyValueRef::from_heap_object(ValueKind::LIST, first_before).expect("list ref"),
        second: AnyValueRef::from_heap_object(ValueKind::LIST, second_before).expect("list ref"),
    };

    let stats = h.collect_stats(&mut held);

    let head_of = |root: AnyValueRef| unsafe { (*(root.list_addr().unwrap() as *const ListCons)).head_value() };
    assert_ne!(held.first.list_addr().unwrap(), first_before, "the first moved");
    assert_ne!(held.second.list_addr().unwrap(), second_before, "the second moved");
    assert_eq!(head_of(held.first), AnyValue::int(1));
    assert_eq!(head_of(held.second), AnyValue::int(2));
    assert_eq!(stats.copied_objects, 2);
}

/// A heap that has collected keeps the buffers a collection needs, so the next
/// one starts from the capacity the last one grew to instead of from nothing.
#[test]
fn the_worklist_and_the_block_lists_keep_their_capacity_across_collections() {
    let mut h = Heap::new(1024, fresh_registry());
    let mut list = EMPTY_LIST;
    for i in 0..4000 {
        list = alloc_int_list_cons(&mut h, i, list);
    }
    assert!(h.young_blocks.len() >= 3, "the allocation climbed through several tips");
    let mut root = list as *mut u8;

    h.collect_tagged(&mut root);

    let worklist = h.worklist.capacity();
    let (young, from) = (h.young_blocks.capacity(), h.from_blocks.capacity());
    assert!(worklist >= 4000, "the worklist grew to hold every copied cell");
    assert!(h.worklist.is_empty(), "and was cleared, not freed");
    assert!(from >= 4, "the from-space list grew to hold the young blocks");
    assert!(h.from_blocks.is_empty(), "the from-space was released");

    let mut list = root as u64;
    for i in 0..4000 {
        list = alloc_int_list_cons(&mut h, i, list);
    }
    root = list as *mut u8;
    h.collect_tagged(&mut root);

    assert!(
        h.worklist.capacity() >= worklist,
        "the worklist keeps its largest capacity"
    );
    assert!(
        h.young_blocks.capacity() >= from,
        "the list that held the first from-space holds the next collection's overflow blocks"
    );
    assert!(h.from_blocks.capacity() >= young.min(from));
    assert!(
        h.young_blocks.capacity() > 0 && h.from_blocks.capacity() > 0,
        "neither list is freed"
    );
}

/// A source of `len` distinct-ish bytes sliced at `start_bit` for `bit_len`
/// bits. Returns the slice's bits, kind, and the views the slice made, read
/// from the collection that follows it, which counts each view under the site
/// that made it.
fn slice_of_fresh_source(len: usize, start_bit: u64, bit_len: u64) -> (Vec<u8>, ValueKind, StubCounts) {
    let bytes: Vec<u8> = (0..len).map(|i| (i * 7 + 3) as u8).collect();
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let source = heap.alloc_bitstring(&bytes, len as u64 * 8);
    let mut roots = [source.ref_word()];
    heap.collect_stats(&mut roots);
    let slice = unsafe { heap.slice(roots[0].raw_word(), start_bit, bit_len) };
    let mut roots = [roots[0], slice.ref_word()];
    let stats = heap.collect_stats(&mut roots);
    let slice = roots[1];
    let bits = unsafe { crate::bits::Bin::of_binary(slice.raw_word()) };
    assert_eq!(bits.bit_len(), bit_len);
    let bits_bytes = unsafe { std::slice::from_raw_parts(bits.ptr(), bit_len.div_ceil(8) as usize) }.to_vec();
    (bits_bytes, slice.tag(), stats.stubs_made)
}

fn window_made() -> StubCounts {
    let mut counts = StubCounts::default();
    counts.record(StubSite::WindowOfBuffer);
    counts
}

/// A field that is the whole source is the source itself, under the same word.
#[test]
fn slicing_the_whole_binary_answers_the_binary() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    for len in [10usize, 200] {
        let source = heap.alloc_bitstring(&vec![5u8; len], len as u64 * 8);
        let word = source.ref_word().raw_word();
        let whole = unsafe { heap.slice(word, 0, len as u64 * 8) };
        assert_eq!(
            whole.ref_word().raw_word(),
            word,
            "a {len}-byte source is its own whole"
        );
    }
}

/// A byte-aligned window over the threshold shares the source's buffer: it is
/// a view, and the bytes are the source's bytes.
#[test]
fn an_aligned_window_over_the_threshold_is_a_view_of_the_source() {
    let source: Vec<u8> = (0..200).map(|i| (i * 7 + 3) as u8).collect();
    let (bytes, kind, made) = slice_of_fresh_source(200, 10 * 8, 100 * 8);
    assert_eq!(kind, ValueKind::BINVIEW);
    assert_eq!(made, window_made());
    assert_eq!(bytes, &source[10..110]);
}

/// A window of exactly the threshold is cheaper copied than viewed, and does
/// not keep the source's buffer alive.
#[test]
fn an_aligned_window_of_the_threshold_is_a_copy() {
    let source: Vec<u8> = (0..200).map(|i| (i * 7 + 3) as u8).collect();
    let (bytes, kind, made) = slice_of_fresh_source(200, 10 * 8, SHARED_BIN_THRESHOLD_BYTES as u64 * 8);
    assert_eq!(kind, ValueKind::BITSTRING);
    assert_eq!(made, StubCounts::default(), "a copy makes no view");
    assert_eq!(bytes, &source[10..10 + SHARED_BIN_THRESHOLD_BYTES]);
}

/// A window that does not start and end on byte boundaries cannot be a view,
/// whatever its size: it is a copy of exactly its bits.
#[test]
fn an_unaligned_window_is_a_copy_of_its_bits() {
    let source: Vec<u8> = (0..200).map(|i| (i * 7 + 3) as u8).collect();
    let (bytes, kind, made) = slice_of_fresh_source(200, 3, 100 * 8);
    assert_eq!(
        kind,
        ValueKind::BINVIEW,
        "a copy over the threshold lands in a shared buffer"
    );
    assert_eq!(made, {
        let mut counts = StubCounts::default();
        counts.record(StubSite::FilledBuffer);
        counts
    });
    let expected: Vec<u8> = (0..100).map(|i| (source[i] << 3) | (source[i + 1] >> 5)).collect();
    assert_eq!(bytes, expected);
}

/// A slice of a small inline source is a copy, however it is aligned.
#[test]
fn a_slice_of_a_small_source_is_a_copy() {
    let source: Vec<u8> = (0..20).map(|i| (i * 7 + 3) as u8).collect();
    let (bytes, kind, made) = slice_of_fresh_source(20, 4 * 8, 10 * 8);
    assert_eq!(kind, ValueKind::BITSTRING);
    assert_eq!(made, StubCounts::default());
    assert_eq!(bytes, &source[4..14]);
}

/// The collection counts nothing per object: what it reports as copied is read
/// from the blocks it filled, and those blocks hold exactly the survivors.
#[test]
fn the_reported_copy_is_the_fill_of_the_blocks_the_collection_filled() {
    let mut h = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut list = EMPTY_LIST;
    let mut collections = 0;
    let mut overflowed = false;
    while collections < 12 {
        let (next, stats) = grow_list_and_collect(&mut h, list, 300);
        list = next;
        collections += 1;
        let filled = &h.old_blocks[h.retired_from..];
        overflowed |= filled.len() > 1;
        assert_eq!(
            stats.copied_bytes as usize,
            filled.iter().map(Block::fill).sum::<usize>(),
            "{:?} collection {collections}: copied bytes are the fill of the blocks it filled",
            stats.generation
        );
        assert_eq!(
            stats.copied_bytes,
            stats.copied_objects * 16,
            "a list cell is one 16-byte object"
        );
    }
    assert!(overflowed, "some collection copied into more than one block");
}

/// Intent: consing onto a value that is not a list places the value in a
/// terminator cell and nothing else: two list cells, and no box for the
/// scalar.
#[test]
fn an_int_tail_costs_two_list_cells_and_no_scalar_box() {
    let mut h = Heap::new(1024, fresh_registry());
    let before = h.node.alloc_stats();

    let cell = h.alloc_list_cons_any(AnyValue::int(1), AnyValue::int(2));

    let stats = h.node.alloc_stats();
    assert_eq!(
        stats.list_cons.allocs - before.list_cons.allocs,
        2,
        "the cell and its terminator cell"
    );
    assert_eq!(
        stats.scalar_box.allocs - before.scalar_box.allocs,
        0,
        "the int is stored in the cell, not boxed"
    );
    assert_eq!(
        stats.total.allocs - before.total.allocs,
        2,
        "no other object was placed"
    );
    let tail = h.read_list_tail_ref(cell).expect("a tail");
    assert_eq!(tail.tag(), ValueKind::INT);
    assert_eq!(tail.load_int(), Ok(2));
}

/// Intent: the terminator is read where a tail is read, whatever its kind.
#[test]
fn the_tail_of_an_improper_cell_is_the_terminator_value() {
    let mut h = Heap::new(1024, fresh_registry());
    let cell = h.alloc_list_cons_any(AnyValue::int(1), AnyValue::atom(7));
    let tail = h.read_list_tail_ref(cell).expect("a tail");
    assert_eq!(tail.tag(), ValueKind::ATOM);
    assert_eq!(tail.load_atom(), Ok(7));
}

/// Intent: a hole is reserved for the destination that fills it, so reading
/// its tail fails loudly rather than answering `[]` or garbage.
#[test]
#[should_panic(expected = "hole")]
fn reading_the_tail_of_a_hole_is_refused() {
    let mut h = Heap::new(1024, fresh_registry());
    let bits = alloc_int_list_cons(&mut h, 1, EMPTY_LIST);
    let addr = list_addr_from_tagged(bits).expect("list addr") as *mut ListCons;
    unsafe { *addr = ListCons::with_link(1, ListLink::hole(ValueKind::INT)) };
    let _ = h.read_list_tail_ref(list_ref_from_bits(bits));
}
