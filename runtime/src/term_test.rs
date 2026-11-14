use super::*;
use crate::any_value::{
    AnyValueRef, ClosureDenotationId, EMPTY_LIST_BITS, closure_addr_from_tagged, closure_capture_set,
    map_addr_from_tagged,
};
use crate::function_denotation::FunctionDenotation;
use crate::heap::AddressMap;
use crate::heap::{Heap, Schema, deep_copy_slot};
use crate::module_name::ModuleName;
use crate::procbin::{SharedBinHandle, alloc_procbin};
use crate::resource::{ResourceHandle, alloc_resource, fz_resource_destructor_noop};
use std::cell::{Cell, RefCell};
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
        AnyValue::atom(101),
        NumericMode::Strict,
    );
}

/// Intent: an atom is equal to itself by id alone, so an id the table has
/// never heard of still answers for itself, though it has no place in the order.
#[test]
fn an_atom_equals_itself_without_a_name() {
    let cmp_schemas = SchemaRegistry::new();
    let node = Node::empty();
    let cmp = TermComparator::new(&node, &cmp_schemas);
    for mode in [NumericMode::Strict, NumericMode::Widening] {
        assert_eq!(
            cmp.compare(AnyValue::atom(100), AnyValue::atom(100), mode),
            Ordering::Equal
        );
        assert!(cmp.equal(AnyValue::atom(100), AnyValue::atom(100), mode));
        assert!(!cmp.equal(AnyValue::atom(100), AnyValue::atom(101), mode));
    }
}

#[test]
#[should_panic(expected = "unpublished map is not a language value")]
fn unfinished_map_has_no_language_order() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let node = Rc::new(Node::empty());
    let mut heap = Heap::with_node(1024, Rc::clone(&schemas), Rc::clone(&node));
    let unfinished = heap.alloc_map_destination(0);
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
    let copied = deep_copy_slot(
        heap_value(map),
        &source.view(),
        &mut destination,
        &mut AddressMap::default(),
    );
    let mut roots = [copied.ref_word()];
    destination.collect(&mut roots);
    let moved = AnyValue::decode_tagged_heap_bits(roots[0].heap_object_word().unwrap()).unwrap();
    let before = destination.alloc_stats_snapshot();
    let registry = schemas.borrow();
    let cmp = TermComparator::new(&node, &registry);
    assert_eq!(
        cmp.compare(heap_value(map), moved, NumericMode::Strict),
        Ordering::Equal
    );
    assert_ne!(
        cmp.compare(resource, distinct, NumericMode::Strict),
        Ordering::Equal,
        "equal payloads do not merge generative resources"
    );
    let moved = roots[0];
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

/// Intent: a pid and a reference stand where Erlang puts them: a reference
/// above every number and atom and below a function, a pid above a function
/// and below a tuple; within a kind, words order by value.
#[test]
fn a_reference_and_a_pid_sort_between_atoms_and_tuples() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let node = Rc::new(Node::empty());
    let mut heap = Heap::with_node(1024, Rc::clone(&schemas), Rc::clone(&node));
    let denotation = ClosureDenotationId::user(7);
    node.register_closure_denotation(
        denotation,
        Arc::new(FunctionDenotation::named(None, "capture".into(), 0)),
    );
    let closure_bits = heap.alloc_closure_slots(denotation, 0, 0, 0);
    let schema = schemas.borrow_mut().register(Schema::tuple_of_arity(1));
    let tuple = tuple(&mut heap, schema, AnyValue::int(1));
    let registry = schemas.borrow();
    let cmp = TermComparator::new(&node, &registry);
    let ascending = [
        AnyValue::float(1.5),
        AnyValue::int(i64::MAX),
        AnyValue::atom(0),
        AnyValue::Opaque(ValueKind::REF, 1),
        AnyValue::Opaque(ValueKind::REF, 2),
        heap_value(closure_bits),
        AnyValue::Opaque(ValueKind::PID, 1),
        AnyValue::Opaque(ValueKind::PID, 2),
        tuple,
    ];
    for (i, lower) in ascending.iter().enumerate() {
        for higher in &ascending[i + 1..] {
            assert_eq!(
                cmp.compare(*lower, *higher, NumericMode::Strict),
                Ordering::Less,
                "{lower:?} sorts below {higher:?}"
            );
            assert_eq!(cmp.compare(*higher, *lower, NumericMode::Strict), Ordering::Greater);
        }
    }
    assert_eq!(
        cmp.compare(
            AnyValue::Opaque(ValueKind::PID, 7),
            AnyValue::Opaque(ValueKind::PID, 7),
            NumericMode::Strict
        ),
        Ordering::Equal
    );
    assert_ne!(
        cmp.compare(
            AnyValue::Opaque(ValueKind::PID, 7),
            AnyValue::int(7),
            NumericMode::Strict
        ),
        Ordering::Equal,
        "a pid is not the integer with the same word"
    );
}

/// Intent: equality is the same question as comparison asked for less; each
/// of the early exits must leave `equal` answering exactly `compare == Equal`.
fn equal_matches_compare(cmp: &TermComparator, a: AnyValue, b: AnyValue, mode: NumericMode) {
    let want = cmp.compare(a, b, mode) == Ordering::Equal;
    assert_eq!(cmp.equal(a, b, mode), want, "{a:?} vs {b:?}");
}

struct Xorshift(u64);

impl Xorshift {
    fn below(&mut self, bound: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % bound as u64) as usize
    }
}

struct Pool {
    heap: Heap,
    node: Rc<Node>,
    schemas: Rc<RefCell<SchemaRegistry>>,
    values: Vec<AnyValue>,
}

impl Pool {
    fn new() -> Self {
        let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
        let node = Rc::new(Node::empty());
        let heap = Heap::with_node(1 << 16, Rc::clone(&schemas), Rc::clone(&node));
        Self {
            heap,
            node,
            schemas,
            values: Vec::new(),
        }
    }

    fn atom(&self, name: &str) -> AnyValue {
        AnyValue::atom(self.node.intern_atom(name))
    }

    fn add_scalars(&mut self) {
        self.values.extend((-3..3).map(AnyValue::int));
        self.values.extend([0.0, -0.0, 1.0, 1.5, -2.0].map(AnyValue::float));
        self.values.extend([i64::MAX, 9_007_199_254_740_993].map(AnyValue::int));
        self.values.push(AnyValue::float(9_007_199_254_740_992.0));
        for name in ["a", "b", "ab", "ba", "", "zz"] {
            self.values.push(self.atom(name));
        }
        let opaque = [
            (ValueKind::PID, 1),
            (ValueKind::PID, 2),
            (ValueKind::REF, 1),
            (ValueKind::REF, 2),
        ];
        self.values
            .extend(opaque.map(|(kind, word)| AnyValue::Opaque(kind, word)));
        self.values.push(AnyValue::EmptyList);
    }

    /// Binaries of every representation over a few contents: inline, whole
    /// ProcBin, ProcBin viewed from an offset, whole bytes and partial
    /// trailing bytes whose padding bits differ.
    fn add_bitstrings(&mut self) {
        let contents: [&[u8]; 4] = [b"", b"a", b"abc", b"0123456789abcdefghijklmnopqrstuvwxyz0123"];
        for bytes in contents {
            let bits = 8 * bytes.len() as u64;
            self.values.push(self.heap.alloc_bitstring(bytes, bits));
            let shared = alloc_procbin(&mut self.heap, SharedBinHandle::from_bytes(bytes, bits), 0);
            self.values
                .push(AnyValue::heap_ptr(shared.as_raw(), ValueKind::PROCBIN));
        }
        let framed = SharedBinHandle::from_bytes(b"xxabc", 40);
        let view = alloc_procbin(&mut self.heap, framed, 2);
        self.values.push(AnyValue::heap_ptr(view.as_raw(), ValueKind::PROCBIN));
        for (bytes, bits) in [(0b1011_1111u8, 3), (0b1010_0000, 3), (0b1000_0000, 3), (0b1010_0000, 4)] {
            self.values.push(self.heap.alloc_bitstring(&[bytes], bits));
            let shared = alloc_procbin(&mut self.heap, SharedBinHandle::from_bytes(&[bytes], bits), 0);
            self.values
                .push(AnyValue::heap_ptr(shared.as_raw(), ValueKind::PROCBIN));
        }
        self.values.push(self.heap.alloc_bitstring(&[0xff, 0b1010_0000], 11));
    }

    fn add_containers(&mut self) {
        let pair = self.schemas.borrow_mut().register(Schema::tuple_of_arity(2));
        for (x, y) in [(1.0, 2.0), (1.0, 2.0), (3.0, 4.0)] {
            let pair_value = self.pair(pair, AnyValue::float(x), AnyValue::float(y));
            self.values.push(pair_value);
            let pair_value = self.pair(pair, AnyValue::int(x as i64), AnyValue::int(y as i64));
            self.values.push(pair_value);
        }
        for head in [AnyValue::int(1), AnyValue::float(1.0), AnyValue::int(2)] {
            self.values
                .push(heap_value(self.heap.alloc_list_cons_slot(head, EMPTY_LIST_BITS)));
        }
        for (key, value) in [(1, 1), (1, 2), (2, 1)] {
            let entries = [(AnyValue::int(key), AnyValue::int(value))];
            self.values.push(heap_value(self.heap.alloc_map_slots(&entries)));
            let widened = [(AnyValue::int(key), AnyValue::float(value as f64))];
            self.values.push(heap_value(self.heap.alloc_map_slots(&widened)));
            let float_key = [(AnyValue::float(key as f64), AnyValue::int(value))];
            self.values.push(heap_value(self.heap.alloc_map_slots(&float_key)));
        }
    }

    fn pair(&mut self, schema: u32, first: AnyValue, second: AnyValue) -> AnyValue {
        let object = self.heap.alloc_struct(schema);
        unsafe {
            self.heap.write_field_slot(object, 0, first);
            self.heap.write_field_slot(object, 8, second);
        }
        AnyValue::heap_ptr(object, ValueKind::STRUCT)
    }

    /// Each named struct beside the entries map that holds the same fields
    /// and its module under `__struct__`: the two are one term.
    fn add_structs_and_their_maps(&mut self) {
        let module = ModuleName::from_segments(vec!["Pt".to_string()]);
        let schema = self
            .schemas
            .borrow_mut()
            .register(Schema::named_struct(module, ["x".to_string(), "y".to_string()]));
        for (x, y) in [(1, 2), (1, 2), (3, 4)] {
            let pair_value = self.pair(schema, AnyValue::int(x), AnyValue::int(y));
            self.values.push(pair_value);
            let entries = [
                (self.atom("__struct__"), self.atom("Elixir.Pt")),
                (self.atom("x"), AnyValue::int(x)),
                (self.atom("y"), AnyValue::int(y)),
            ];
            self.values.push(heap_value(self.heap.alloc_map_slots(&entries)));
        }
    }

    /// Closures of one denotation, equal when their environments are.
    fn add_closures(&mut self) {
        let denotation = ClosureDenotationId::user(7);
        self.node.register_closure_denotation(
            denotation,
            Arc::new(FunctionDenotation::named(None, "capture".into(), 1)),
        );
        for captured in [1, 1, 2] {
            let bits = self.heap.alloc_closure_slots(denotation, 0, 1, 0);
            unsafe { closure_capture_set(closure_addr_from_tagged(bits).unwrap(), 0, AnyValue::int(captured)) };
            self.values.push(heap_value(bits));
        }
    }

    fn mixed() -> Self {
        let mut pool = Self::new();
        pool.add_scalars();
        pool.add_bitstrings();
        pool.add_containers();
        pool.add_structs_and_their_maps();
        pool.add_closures();
        pool
    }
}

/// Intent: over a pool that mixes every kind of term, every pair in both
/// numeric modes, `equal` is exactly `compare == Equal`, and the pool holds
/// enough equal pairs that the property is not met by answering false.
#[test]
fn equal_agrees_with_compare_over_mixed_terms_in_both_modes() {
    let pool = Pool::mixed();
    let registry = pool.schemas.borrow();
    let cmp = TermComparator::new(&pool.node, &registry);
    let mut rng = Xorshift(0x9e37_79b9_7f4a_7c15);
    for mode in [NumericMode::Strict, NumericMode::Widening] {
        let mut equal_pairs = 0;
        for _ in 0..200_000 {
            let a = pool.values[rng.below(pool.values.len())];
            let b = pool.values[rng.below(pool.values.len())];
            equal_matches_compare(&cmp, a, b, mode);
            equal_pairs += usize::from(cmp.equal(a, b, mode));
        }
        assert!(equal_pairs > 1_000, "only {equal_pairs} equal pairs");
    }
    for mode in [NumericMode::Strict, NumericMode::Widening] {
        for a in &pool.values {
            for b in &pool.values {
                equal_matches_compare(&cmp, *a, *b, mode);
            }
        }
    }
}

/// Intent: the integer fast path never decides an integer against a float,
/// which widening equates and strictness separates.
#[test]
fn an_integer_and_a_float_are_equal_only_when_widening() {
    let cmp_schemas = SchemaRegistry::new();
    let node = Node::empty();
    let cmp = TermComparator::new(&node, &cmp_schemas);
    let (one, one_float) = (AnyValue::int(1), AnyValue::float(1.0));
    assert!(cmp.equal(one, one_float, NumericMode::Widening));
    assert!(cmp.equal(one_float, one, NumericMode::Widening));
    assert!(!cmp.equal(one, one_float, NumericMode::Strict));
    assert!(!cmp.equal(one_float, one, NumericMode::Strict));
    assert!(!cmp.equal(AnyValue::int(2), one_float, NumericMode::Widening));
    assert!(cmp.equal(AnyValue::float(0.0), AnyValue::float(-0.0), NumericMode::Widening));
    assert!(!cmp.equal(AnyValue::float(0.0), AnyValue::float(-0.0), NumericMode::Strict));
}

/// Intent: two integers compare as integers, so values a float cannot tell
/// apart still order exactly.
#[test]
fn two_integers_compare_exactly_beyond_float_precision() {
    let cmp_schemas = SchemaRegistry::new();
    let node = Node::empty();
    let cmp = TermComparator::new(&node, &cmp_schemas);
    let (low, high) = (
        AnyValue::int(9_007_199_254_740_992),
        AnyValue::int(9_007_199_254_740_993),
    );
    for mode in [NumericMode::Strict, NumericMode::Widening] {
        assert_eq!(cmp.compare(low, high, mode), Ordering::Less);
        assert_eq!(cmp.compare(high, low, mode), Ordering::Greater);
        assert_eq!(cmp.compare(high, high, mode), Ordering::Equal);
        assert!(!cmp.equal(low, high, mode));
    }
}

/// Intent: binaries are equal by their bits, not their bytes: the same bytes
/// at different bit lengths differ, and padding past the last bit is ignored,
/// in whatever representation each side is stored.
#[test]
fn binaries_are_equal_by_bit_length_then_bits() {
    let mut pool = Pool::new();
    let whole = pool.heap.alloc_bitstring(&[0b1010_0000], 8);
    let three = pool.heap.alloc_bitstring(&[0b1010_0000], 3);
    let three_padded = pool.heap.alloc_bitstring(&[0b1011_1111], 3);
    let three_shared = alloc_procbin(&mut pool.heap, SharedBinHandle::from_bytes(&[0b1010_1010], 3), 0);
    let three_shared = AnyValue::heap_ptr(three_shared.as_raw(), ValueKind::PROCBIN);
    let different_third_bit = pool.heap.alloc_bitstring(&[0b1000_0000], 3);
    let framed = alloc_procbin(&mut pool.heap, SharedBinHandle::from_bytes(b"xab", 24), 1);
    let framed = AnyValue::heap_ptr(framed.as_raw(), ValueKind::PROCBIN);
    let ab = pool.heap.alloc_bitstring(b"ab", 16);
    let registry = pool.schemas.borrow();
    let cmp = TermComparator::new(&pool.node, &registry);
    for mode in [NumericMode::Strict, NumericMode::Widening] {
        assert!(!cmp.equal(whole, three, mode), "same byte, different bit length");
        assert!(
            cmp.equal(three, three_padded, mode),
            "padding bits are not part of the value"
        );
        assert!(cmp.equal(three, three_shared, mode), "storage does not matter");
        assert!(!cmp.equal(three, different_third_bit, mode));
        assert!(
            cmp.equal(framed, ab, mode),
            "a view from an offset is the bytes it shows"
        );
        assert_eq!(cmp.compare(whole, three, mode), Ordering::Greater);
    }
}

/// Intent: terms of different kinds are never equal, and a kind that only
/// shares a payload word with another does not become equal to it.
#[test]
fn terms_of_different_kinds_are_not_equal() {
    let mut pool = Pool::new();
    let atom = pool.atom("a");
    let binary = pool.heap.alloc_bitstring(b"a", 8);
    let registry = pool.schemas.borrow();
    let cmp = TermComparator::new(&pool.node, &registry);
    for mode in [NumericMode::Strict, NumericMode::Widening] {
        let kinds = [
            AnyValue::int(7),
            atom,
            binary,
            AnyValue::EmptyList,
            AnyValue::Opaque(ValueKind::PID, 7),
            AnyValue::Opaque(ValueKind::REF, 7),
        ];
        for (i, a) in kinds.iter().enumerate() {
            for b in &kinds[i + 1..] {
                assert!(!cmp.equal(*a, *b, mode), "{a:?} vs {b:?}");
                assert!(!cmp.equal(*b, *a, mode), "{b:?} vs {a:?}");
            }
        }
    }
}
