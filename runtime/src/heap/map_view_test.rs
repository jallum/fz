use super::*;
use crate::any_value::{struct_field_kind_slot, struct_field_raw_slot};
use crate::heap::{NamedSchema, Schema, SchemaRegistry};
use crate::module_name::ModuleName;
use crate::process::Node;
use crate::term::TermComparator;
use std::cell::RefCell;
use std::rc::Rc;

struct Fixture {
    heap: Heap,
    node: Rc<Node>,
    point: u32,
}

/// A heap with `%Pt{x, y}` registered.
fn fixture() -> Fixture {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let node = Rc::new(Node::empty());
    let heap = Heap::with_node(4096, Rc::clone(&schemas), Rc::clone(&node));
    let point = heap.register_schema(Schema::named_struct(
        ModuleName::from_segments(vec!["Pt".to_string()]),
        ["x".to_string(), "y".to_string()],
    ));
    Fixture { heap, node, point }
}

impl Fixture {
    fn atom(&self, name: &str) -> AnyValue {
        AnyValue::atom(self.node.intern_atom(name))
    }

    fn point(&mut self, x: i64, y: i64) -> AnyValueRef {
        let object = self.heap.alloc_struct(self.point);
        unsafe {
            self.heap.write_field_slot(object, 0, AnyValue::int(x));
            self.heap.write_field_slot(object, 8, AnyValue::int(y));
        }
        AnyValueRef::from_heap_object(ValueKind::STRUCT, object).expect("struct ref")
    }

    /// The entries layout map `%{name: value, ...}`.
    fn plain(&mut self, entries: &[(&str, i64)]) -> AnyValueRef {
        let entries: Vec<_> = entries
            .iter()
            .map(|(name, value)| (self.atom(name), AnyValue::int(*value)))
            .collect();
        let bits = self.heap.alloc_map_slots(&entries);
        let addr = map_addr_from_tagged(bits).expect("published map");
        AnyValueRef::from_heap_object(ValueKind::MAP, addr).expect("map ref")
    }

    fn entries(&self, map: AnyValueRef) -> Vec<(AnyValue, AnyValue)> {
        let layout = self.heap.expect_map_layout(map, "test");
        self.heap.map_view_entries(layout)
    }

    fn point_entries(&self, x: i64, y: i64) -> Vec<(AnyValue, AnyValue)> {
        vec![
            (self.atom("__struct__"), self.atom("Elixir.Pt")),
            (self.atom("x"), AnyValue::int(x)),
            (self.atom("y"), AnyValue::int(y)),
        ]
    }
}

fn is_struct_layout(layout: Option<MapLayout>) -> bool {
    matches!(layout, Some(MapLayout::Struct { .. }))
}

fn is_entries_layout(layout: Option<MapLayout>) -> bool {
    matches!(layout, Some(MapLayout::Entries(_)))
}

#[test]
fn a_struct_reads_as_a_map_of_its_fields_and_module() {
    let mut f = fixture();
    let p = f.point(1, 2);
    let layout = f.heap.map_layout(p);
    assert!(is_struct_layout(layout), "a named struct keeps its own layout");
    let layout = layout.unwrap();
    assert_eq!(f.heap.map_view_count(layout), 3, "two fields and __struct__");
    assert_eq!(f.entries(p), f.point_entries(1, 2), "keys come in map key order");

    let x = f.atom("x");
    let module_key = f.atom("__struct__");
    let absent = f.atom("z");
    assert_eq!(f.heap.map_view_get(layout, x).map(|v| v.load_int()), Some(Ok(1)));
    let module = f.heap.map_view_get(layout, module_key).expect("__struct__ is a key");
    assert_eq!(AnyValue::from_ref(module).unwrap(), f.atom("Elixir.Pt"));
    assert!(f.heap.map_view_get(layout, absent).is_none());
    assert!(f.heap.map_view_has_key(layout, module_key));
    assert!(
        !f.heap.map_view_has_key(layout, AnyValue::int(0)),
        "only atoms name struct keys"
    );
}

#[test]
fn a_tuple_is_not_a_map() {
    let mut f = fixture();
    let pair = f.heap.register_schema(Schema::tuple_of_arity(2));
    let object = f.heap.alloc_struct(pair);
    unsafe {
        f.heap.write_field_slot(object, 0, AnyValue::int(1));
        f.heap.write_field_slot(object, 8, AnyValue::int(2));
    }
    let tuple = AnyValueRef::from_heap_object(ValueKind::STRUCT, object).unwrap();
    assert_eq!(f.heap.map_layout(tuple), None);
}

#[test]
fn putting_a_field_keeps_the_struct_and_a_new_key_leaves_it() {
    let mut f = fixture();
    let p = f.point(1, 2);
    let layout = f.heap.map_layout(p).unwrap();
    let x = f.atom("x");
    let replaced = f.heap.map_view_put(layout, x, AnyValue::int(9));
    assert!(is_struct_layout(f.heap.map_layout(replaced)));
    assert_eq!(f.entries(replaced), f.point_entries(9, 2));
    assert_eq!(f.entries(p), f.point_entries(1, 2), "the original is untouched");

    let z = f.atom("z");
    let grown = f.heap.map_view_put(layout, z, AnyValue::int(0));
    assert!(
        is_entries_layout(f.heap.map_layout(grown)),
        "a key outside the schema leaves it"
    );
    let mut expected = f.point_entries(1, 2);
    expected.push((z, AnyValue::int(0)));
    assert_eq!(f.entries(grown), expected, "__struct__ stays an ordinary key");
}

#[test]
fn deleting_a_key_leaves_the_struct_and_deleting_an_absent_key_changes_nothing() {
    let mut f = fixture();
    let p = f.point(1, 2);
    let x = f.atom("x");
    let shrunk = f.heap.map_view_delete(p, x);
    assert!(is_entries_layout(f.heap.map_layout(shrunk)));
    let expected = vec![
        (f.atom("__struct__"), f.atom("Elixir.Pt")),
        (f.atom("y"), AnyValue::int(2)),
    ];
    assert_eq!(f.entries(shrunk), expected);

    let absent = f.atom("w");
    let same = f.heap.map_view_delete(p, absent);
    assert_eq!(same.raw_word(), p.raw_word());
}

#[test]
fn an_update_of_a_struct_field_freezes_into_the_struct() {
    let mut f = fixture();
    let p = f.point(1, 2);
    let dest = f.heap.alloc_map_update(p);
    let y = f.atom("y");
    let dest = unsafe { f.heap.map_destination_put(dest, y, AnyValue::int(5)) };
    let updated = f.heap.map_destination_freeze(dest).expect("every key is present");
    assert!(is_struct_layout(f.heap.map_layout(updated)));
    assert_eq!(f.entries(updated), f.point_entries(1, 5));
    assert_eq!(f.entries(p), f.point_entries(1, 2), "the original is untouched");
}

#[test]
fn an_update_naming_a_missing_key_makes_no_map() {
    let mut f = fixture();
    let p = f.point(1, 2);
    let plain = f.plain(&[("x", 1)]);
    let x = f.atom("x");
    let z = f.atom("z");
    for base in [p, plain] {
        let dest = f.heap.alloc_map_update(base);
        let dest = unsafe { f.heap.map_destination_put(dest, z, AnyValue::int(0)) };
        let dest = unsafe { f.heap.map_destination_put(dest, x, AnyValue::int(9)) };
        assert!(
            f.heap.map_destination_freeze(dest).is_none(),
            "a miss anywhere in the update answers no map"
        );
    }
}

/// A struct is the struct its module says. Naming the module it already has
/// changes nothing; naming another leaves a map that holds the new module as
/// an ordinary key, however many fields were replaced before or after.
#[test]
fn an_update_of_the_module_keeps_the_struct_only_when_the_module_is_its_own() {
    let mut f = fixture();
    let p = f.point(1, 2);
    let module_key = f.atom("__struct__");
    let x = f.atom("x");
    let y = f.atom("y");

    let own = f.atom("Elixir.Pt");
    let dest = f.heap.alloc_map_update(p);
    let dest = unsafe { f.heap.map_destination_put(dest, module_key, own) };
    let dest = unsafe { f.heap.map_destination_put(dest, x, AnyValue::int(3)) };
    let same = f.heap.map_destination_freeze(dest).expect("every key is present");
    assert!(is_struct_layout(f.heap.map_layout(same)));
    assert_eq!(f.entries(same), f.point_entries(3, 2));

    let other = f.atom("Elixir.Far");
    let dest = f.heap.alloc_map_update(p);
    let dest = unsafe { f.heap.map_destination_put(dest, x, AnyValue::int(3)) };
    let dest = unsafe { f.heap.map_destination_put(dest, module_key, other) };
    let dest = unsafe { f.heap.map_destination_put(dest, y, AnyValue::int(4)) };
    let moved = f.heap.map_destination_freeze(dest).expect("every key is present");
    assert!(is_entries_layout(f.heap.map_layout(moved)));
    assert_eq!(
        f.entries(moved),
        vec![(module_key, other), (x, AnyValue::int(3)), (y, AnyValue::int(4))]
    );
    assert_eq!(f.entries(p), f.point_entries(1, 2), "the original is untouched");
}

#[test]
fn a_nested_struct_answers_its_whole_module_name() {
    let mut f = fixture();
    let nested = f.heap.register_schema(Schema::named_struct(
        ModuleName::from_segments(vec!["Geo".to_string(), "Pt".to_string()]),
        ["lat".to_string()],
    ));
    let object = AnyValueRef::from_heap_object(ValueKind::STRUCT, f.heap.alloc_struct(nested)).unwrap();
    let layout = f.heap.map_layout(object).unwrap();
    let module_key = f.atom("__struct__");
    let module = f.heap.map_view_get(layout, module_key).expect("__struct__ is a key");
    assert_eq!(AnyValue::from_ref(module).unwrap(), f.atom("Elixir.Geo.Pt"));
}

/// A scalar field's ref points into the struct's own payload, so a field read
/// from a literal struct as a map names read-only data, as a direct field
/// read does.
#[test]
fn a_scalar_value_read_from_a_literal_struct_as_a_map_is_literal() {
    let mut f = fixture();
    let point = f.point(1, 2);
    let y = f.atom("y");

    let from_heap = {
        let layout = f.heap.expect_map_layout(point, "test");
        f.heap.map_view_get(layout, y).expect("y")
    };
    let from_literal = {
        let layout = f.heap.expect_map_layout(point.literal(), "test");
        f.heap.map_view_get(layout, y).expect("y")
    };

    assert!(!from_heap.is_literal(), "a field of a heap struct is heap data");
    assert!(from_literal.is_literal(), "a field of a literal struct is literal data");
    assert_eq!(from_literal.load_int().unwrap(), 2);
}

/// A value the types call a `Pt` may be in either layout. Only a value in
/// `Pt`'s struct layout has its fields in `Pt`'s slots; one that has grown a
/// key, a plain map and another struct do not.
#[test]
fn only_a_struct_in_its_own_layout_has_that_structs_slots() {
    let mut f = fixture();
    let pt = ModuleName::from_segments(vec!["Pt".to_string()]);
    let other = ModuleName::from_segments(vec!["Other".to_string()]);
    let point = f.point(1, 2);
    assert!(f.heap.has_struct_layout_of(point, &pt));
    assert!(!f.heap.has_struct_layout_of(point, &other));

    let layout = f.heap.expect_map_layout(point, "test");
    let z = f.atom("z");
    let grown = f.heap.map_view_put(layout, z, AnyValue::int(3));
    assert!(!f.heap.has_struct_layout_of(grown, &pt));

    let plain = f.plain(&[("x", 1), ("y", 2)]);
    assert!(!f.heap.has_struct_layout_of(plain, &pt));
}

/// A protocol asks a map which module it names. A struct names its own in
/// either layout; a map with no atom under `__struct__` names none; an atom
/// no struct was declared for names a module with no schema.
#[test]
fn a_map_names_the_module_under_its_struct_key_in_either_layout() {
    let mut f = fixture();
    let point = f.point(1, 2);
    assert_eq!(f.heap.named_schema(point), NamedSchema::Schema(f.point));

    let layout = f.heap.expect_map_layout(point, "test");
    let z = f.atom("z");
    let grown = f.heap.map_view_put(layout, z, AnyValue::int(3));
    assert_eq!(grown.tag(), ValueKind::MAP);
    assert_eq!(f.heap.named_schema(grown), NamedSchema::Schema(f.point));

    let plain = f.plain(&[("x", 1), ("y", 2)]);
    assert_eq!(f.heap.named_schema(plain), NamedSchema::None);

    let counted = f.plain(&[("__struct__", 7)]);
    assert_eq!(
        f.heap.named_schema(counted),
        NamedSchema::None,
        "only an atom names a module"
    );

    let undeclared = [(f.atom("__struct__"), f.atom("Elixir.Nowhere"))];
    let bits = f.heap.alloc_map_slots(&undeclared);
    let addr = map_addr_from_tagged(bits).expect("published map");
    let undeclared = AnyValueRef::from_heap_object(ValueKind::MAP, addr).expect("map ref");
    assert_eq!(f.heap.named_schema(undeclared), NamedSchema::Undeclared);
}

impl Fixture {
    fn order(&self, a: AnyValueRef, b: AnyValueRef) -> std::cmp::Ordering {
        let schemas = self.heap.schemas.borrow();
        let value = |object: AnyValueRef| AnyValue::heap_ptr(object.storage_addr(), object.tag());
        TermComparator::new(&self.node, &schemas).key_order_of(value(a), value(b))
    }

    fn entries_map(&mut self, entries: &[(AnyValue, AnyValue)]) -> AnyValueRef {
        let bits = self.heap.alloc_map_slots(entries);
        let addr = map_addr_from_tagged(bits).expect("published map");
        AnyValueRef::from_heap_object(ValueKind::MAP, addr).expect("map ref")
    }

    fn tuple(&mut self, values: &[i64]) -> AnyValueRef {
        let schema = self.heap.register_schema(Schema::tuple_of_arity(values.len()));
        let object = self.heap.alloc_struct(schema);
        for (index, value) in values.iter().enumerate() {
            unsafe {
                self.heap
                    .write_field_slot(object, (index * 8) as u32, AnyValue::int(*value))
            };
        }
        AnyValueRef::from_heap_object(ValueKind::STRUCT, object).expect("tuple ref")
    }
}

/// Equality is a question about a map's keys and values. A struct and the
/// entries map holding the same module and fields are the same term, in
/// either order of asking.
#[test]
fn a_struct_equals_the_entries_map_that_holds_its_module_and_fields() {
    use std::cmp::Ordering;
    let mut f = fixture();
    let p = f.point(1, 2);
    let spelled = f.point_entries(1, 2);
    let spelled = f.entries_map(&spelled);
    assert_eq!(f.order(p, spelled), Ordering::Equal);
    assert_eq!(f.order(spelled, p), Ordering::Equal);

    let other = f.point_entries(1, 3);
    let other = f.entries_map(&other);
    assert_eq!(f.order(p, other), Ordering::Less, "the y values decide");
    assert_eq!(f.order(other, p), Ordering::Greater);
}

/// A struct takes a map's place in the term order: after every tuple, and
/// among maps by size, then keys, then values in key order.
#[test]
fn a_struct_orders_as_the_map_it_is() {
    use std::cmp::Ordering;
    let mut f = fixture();
    let p = f.point(1, 2);

    let wide_tuple = f.tuple(&[9, 9, 9, 9, 9]);
    assert_eq!(f.order(wide_tuple, p), Ordering::Less, "a tuple is before any map");
    assert_eq!(f.order(p, wide_tuple), Ordering::Greater);

    let smaller = f.plain(&[("x", 9), ("y", 9)]);
    assert_eq!(f.order(smaller, p), Ordering::Less, "two keys are before three");

    let same_size = f.plain(&[("a", 0), ("x", 1), ("y", 2)]);
    assert_eq!(
        f.order(p, same_size),
        Ordering::Less,
        "at one size the keys decide, and __struct__ is before a"
    );

    let layout = f.heap.expect_map_layout(p, "test");
    let z = f.atom("z");
    let grown = f.heap.map_view_put(layout, z, AnyValue::int(3));
    assert_eq!(f.order(p, grown), Ordering::Less);
}

/// Two structs of one size and one set of keys differ first by the module
/// under `__struct__`, the least of their keys, and then by their fields in
/// key order, whatever order the struct declares them in.
#[test]
fn two_structs_order_by_module_and_then_by_fields_in_key_order() {
    use std::cmp::Ordering;
    let mut f = fixture();
    let other = f.heap.register_schema(Schema::named_struct(
        ModuleName::from_segments(vec!["Qt".to_string()]),
        ["y".to_string(), "x".to_string()],
    ));
    let q = |f: &mut Fixture, x: i64, y: i64| {
        let object = f.heap.alloc_struct(other);
        unsafe {
            f.heap.write_field_slot(object, 0, AnyValue::int(y));
            f.heap.write_field_slot(object, 8, AnyValue::int(x));
        }
        AnyValueRef::from_heap_object(ValueKind::STRUCT, object).expect("struct ref")
    };
    let p = f.point(5, 5);
    let low = q(&mut f, 0, 0);
    assert_eq!(
        f.order(p, low),
        Ordering::Less,
        "Pt is before Qt whatever the fields hold"
    );

    let x_first = q(&mut f, 1, 9);
    let y_first = q(&mut f, 2, 0);
    assert_eq!(
        f.order(x_first, y_first),
        Ordering::Less,
        "x is compared before y though y is declared first"
    );
}

/// A map prints as a struct when it holds exactly what the struct it names
/// declares: the module and every field, and no other key. The fields are
/// answered in the order the struct declares them.
#[test]
fn an_entries_map_spells_a_struct_when_its_keys_are_exactly_the_structs() {
    let mut f = fixture();
    let spelled = f.point_entries(1, 2);
    let spelled = f.entries_map(&spelled);
    let (module, fields) = f.heap.entries_spelling_a_struct(spelled).expect("spells Pt");
    assert_eq!(module, ModuleName::from_segments(vec!["Pt".to_string()]));
    assert_eq!(
        fields,
        vec![("x".to_string(), AnyValue::int(1)), ("y".to_string(), AnyValue::int(2))]
    );

    let mut grown = f.point_entries(1, 2);
    grown.push((f.atom("z"), AnyValue::int(3)));
    let grown = f.entries_map(&grown);
    assert_eq!(f.heap.entries_spelling_a_struct(grown), None, "a key the struct lacks");

    let fewer = [
        (f.atom("__struct__"), f.atom("Elixir.Pt")),
        (f.atom("x"), AnyValue::int(1)),
    ];
    let fewer = f.entries_map(&fewer);
    assert_eq!(f.heap.entries_spelling_a_struct(fewer), None, "a field is missing");

    let renamed = [
        (f.atom("__struct__"), f.atom("Elixir.Pt")),
        (f.atom("x"), AnyValue::int(1)),
        (f.atom("z"), AnyValue::int(2)),
    ];
    let renamed = f.entries_map(&renamed);
    assert_eq!(
        f.heap.entries_spelling_a_struct(renamed),
        None,
        "the right number of keys, one of them not a field"
    );

    let undeclared = [(f.atom("__struct__"), f.atom("Elixir.Nowhere"))];
    let undeclared = f.entries_map(&undeclared);
    assert_eq!(f.heap.entries_spelling_a_struct(undeclared), None);

    let plain = f.plain(&[("x", 1), ("y", 2)]);
    assert_eq!(f.heap.entries_spelling_a_struct(plain), None);
}

/// A flat map's stored form: its header, kind bytes, keys and values, up to
/// its last value word. The allocation is rounded up to 16 bytes, and the
/// alignment pad past the last value is never written, so it is not part of
/// the form.
fn stored_bytes(map: AnyValueRef) -> Vec<u8> {
    let addr = map.map_addr().expect("a map") as *const u8;
    let count = unsafe { map_count(addr) };
    let len = crate::any_value::map_values_offset(count) + count * 8;
    unsafe { std::slice::from_raw_parts(addr, len) }.to_vec()
}

/// Intent: a flat map has one stored form. A map reached by adding a key,
/// by replacing a value or by removing a key is byte for byte the map a
/// bulk build of the same entries makes, at every size that changes how
/// many kind bytes pad the header and at every slot.
#[test]
fn a_put_a_replace_and_a_delete_store_what_a_bulk_build_stores() {
    let mut f = fixture();
    let name = |i: usize| format!("k{i:02}");
    for count in [1usize, 2, 7, 8, 9, 16, 17, 31] {
        let names: Vec<String> = (0..count + 1).map(name).collect();
        let all: Vec<(&str, i64)> = names.iter().map(|n| (n.as_str(), 1)).collect();
        for slot in 0..=count {
            let without: Vec<_> = all.iter().copied().enumerate().filter(|(i, _)| *i != slot).collect();
            let without: Vec<(&str, i64)> = without.into_iter().map(|(_, entry)| entry).collect();
            let (key, built, smaller) = (f.atom(all[slot].0), f.plain(&all), f.plain(&without));

            let layout = f.heap.expect_map_layout(smaller, "test");
            let put = f.heap.map_view_put(layout, key, AnyValue::int(1));
            assert_eq!(
                stored_bytes(put),
                stored_bytes(built),
                "put of slot {slot} into {count}"
            );

            let deleted = f.heap.map_view_delete(built, key);
            assert_eq!(
                stored_bytes(deleted),
                stored_bytes(smaller),
                "delete of slot {slot} from {}",
                count + 1
            );

            let mut replaced_entries = all.clone();
            replaced_entries[slot].1 = 2;
            let expected = f.plain(&replaced_entries);
            let layout = f.heap.expect_map_layout(built, "test");
            let replaced = f.heap.map_view_put(layout, key, AnyValue::int(2));
            assert_eq!(
                stored_bytes(replaced),
                stored_bytes(expected),
                "replace of slot {slot} in {}",
                count + 1
            );
        }
    }
}

/// Intent: removing a key a flat map lacks answers the map itself, and
/// allocates nothing.
#[test]
fn deleting_an_absent_key_from_a_flat_map_allocates_nothing() {
    let mut f = fixture();
    let map = f.plain(&[("a", 1), ("b", 2)]);
    let absent = f.atom("c");
    let before = f.heap.node.alloc_stats().total.allocs;
    assert_eq!(f.heap.map_view_delete(map, absent), map);
    assert_eq!(f.heap.node.alloc_stats().total.allocs, before);
}

/// Intent: removing a present key from a flat map makes exactly one object,
/// the new map.
#[test]
fn deleting_a_present_key_from_a_flat_map_allocates_only_the_new_map() {
    let mut f = fixture();
    let map = f.plain(&[("a", 1), ("b", 2), ("c", 3)]);
    let key = f.atom("b");
    let before = f.heap.node.alloc_stats().total.allocs;
    let smaller = f.heap.map_view_delete(map, key);
    assert_eq!(f.heap.node.alloc_stats().total.allocs, before + 1);
    let expected = f.plain(&[("a", 1), ("c", 3)]);
    assert_eq!(stored_bytes(smaller), stored_bytes(expected));
}

impl Fixture {
    /// Each element of `list` as the word and kind its cell holds, front to back.
    fn elements(&self, list: AnyValueRef) -> Vec<(u64, ValueKind)> {
        let mut elements = Vec::new();
        let mut addr = list
            .list_addr()
            .ok()
            .filter(|addr| !addr.is_null())
            .map(|addr| addr as u64);
        while let Some(cell_addr) = addr {
            let cell = unsafe { &*(cell_addr as *const crate::any_value::ListCons) };
            elements.push((cell.head, cell.head_kind()));
            addr = Some(cell.tail_cell_addr()).filter(|addr| *addr != 0);
        }
        elements
    }

    /// The two fields of the `{key, value}` tuple at `word`, each as a word and a kind.
    fn pair_fields(&self, word: u64) -> [(u64, ValueKind); 2] {
        let object = word as *const u8;
        let schema = self.heap.schemas.borrow();
        let tuple = schema.get(unsafe { struct_schema_id(object) });
        assert_eq!(
            tuple.identity,
            crate::heap::schema::SchemaIdentity::Tuple(2),
            "each pair is a 2-tuple"
        );
        [0, 8].map(|offset| unsafe {
            let kind = *struct_field_kind_slot(object, tuple.value_field_kind_offset(offset));
            (
                *struct_field_raw_slot(object, offset),
                ValueKind::new(kind).expect("field kind"),
            )
        })
    }

    /// The map listed by each part, held to the entries the map numbers: the
    /// same words and kinds in the same order, nothing decoded and nothing
    /// boxed.
    fn assert_lists_its_entries(&mut self, map: AnyValueRef) {
        let entries: Vec<_> = self.entries(map);
        let word_kind = |value: AnyValue| (value.raw(), value.kind());
        let keys = self.heap.map_list(map, MapPart::Keys);
        assert_eq!(
            self.elements(keys),
            entries.iter().map(|e| word_kind(e.0)).collect::<Vec<_>>()
        );
        let values = self.heap.map_list(map, MapPart::Values);
        assert_eq!(
            self.elements(values),
            entries.iter().map(|e| word_kind(e.1)).collect::<Vec<_>>()
        );
        let pairs = self.heap.map_list(map, MapPart::Pairs);
        let pairs = self.elements(pairs);
        assert!(
            pairs.iter().all(|&(_, kind)| kind == ValueKind::STRUCT),
            "each pair is a tuple"
        );
        let fields: Vec<_> = pairs.iter().map(|&(word, _)| self.pair_fields(word)).collect();
        assert_eq!(
            fields,
            entries
                .iter()
                .map(|e| [word_kind(e.0), word_kind(e.1)])
                .collect::<Vec<_>>()
        );
    }
}

/// `Map.keys`, `Map.values` and `Map.to_list` read a map once, front to back,
/// in the order the map numbers its entries: an empty map, a flat map, the
/// flat limit, and tries one and several levels deep.
#[test]
fn a_map_is_listed_by_its_keys_values_or_pairs_in_the_order_it_numbers_its_entries() {
    let mut f = fixture();
    for count in [0i64, 3, 32, 33, 1000, 40_000] {
        let entries: Vec<_> = (0..count)
            .map(|i| (i * 7919) % count.max(1))
            .map(|i| (AnyValue::int(i), AnyValue::int(i * 10)))
            .collect();
        let map = f.entries_map(&entries);
        f.assert_lists_its_entries(map);
    }
}

/// Keys whose hashes are equal sit together in a collision node, and the
/// walk lists them where the map numbers them.
#[test]
fn a_trie_with_collision_nodes_is_listed_in_the_order_it_numbers_its_entries() {
    let mut f = fixture();
    let mut hashed: Vec<(u64, (AnyValue, AnyValue))> = (0..200i64)
        .map(|i| {
            (
                ((i % 4) as u64) << 62 | (i % 20) as u64,
                (AnyValue::int(i), AnyValue::int(i * 10)),
            )
        })
        .collect();
    let bits = f.heap.alloc_trie_hashed(&mut hashed);
    let map =
        AnyValueRef::from_heap_object(ValueKind::MAP, map_addr_from_tagged(bits).expect("trie")).expect("map ref");
    f.assert_lists_its_entries(map);
}

/// A struct is listed as the map it is: `__struct__` and its fields.
#[test]
fn a_struct_is_listed_with_its_module_and_its_fields() {
    let mut f = fixture();
    let point = f.point(1, 2);
    f.assert_lists_its_entries(point);
}

/// A map's mixed keys and its heap values cross into the list as the words
/// the map stores: an atom as its id, and a list value as the same list,
/// shared rather than copied.
#[test]
fn a_heap_value_is_listed_as_the_same_object_the_map_holds() {
    let mut f = fixture();
    let inner = f.heap.alloc_list_cons_any(AnyValue::int(7), AnyValue::EmptyList);
    let entries = vec![
        (f.atom("held"), AnyValue::from_ref(inner).expect("list value")),
        (AnyValue::int(-1), f.atom("ok")),
        (AnyValue::float(1.5), AnyValue::int(3)),
    ];
    let map = f.entries_map(&entries);
    f.assert_lists_its_entries(map);
    let values = f.heap.map_list(map, MapPart::Values);
    let held = f
        .elements(values)
        .into_iter()
        .find(|&(_, kind)| kind == ValueKind::LIST)
        .expect("the list value is listed");
    assert_eq!(
        held.0,
        inner.storage_raw().expect("list word"),
        "the same list, not a copy"
    );
}

/// A list is placed in runs of cells side by side, and each run is counted
/// as the cells and pairs it holds: listing a map of 40,000 entries counts
/// 40,000 cells, and for its pairs 40,000 tuples as well, as if each had been
/// placed alone.
#[test]
fn a_listed_map_counts_each_cell_and_pair_it_places() {
    let mut f = fixture();
    let entries: Vec<_> = (0..40_000i64).map(|i| (AnyValue::int(i), AnyValue::int(i))).collect();
    let map = f.entries_map(&entries);

    let before = f.heap.node.alloc_stats();
    f.heap.map_list(map, MapPart::Keys);
    let after = f.heap.node.alloc_stats();
    assert_eq!(
        (
            after.list_cons.allocs - before.list_cons.allocs,
            after.list_cons.bytes - before.list_cons.bytes
        ),
        (40_000, 40_000 * 16),
        "one 16-byte cell per key"
    );
    assert_eq!(after.struct_, before.struct_, "a list of keys places no tuple");

    let before = after;
    f.heap.map_list(map, MapPart::Pairs);
    let after = f.heap.node.alloc_stats();
    assert_eq!(
        after.list_cons.allocs - before.list_cons.allocs,
        40_000,
        "one cell per pair"
    );
    assert_eq!(
        (
            after.struct_.allocs - before.struct_.allocs,
            after.struct_.bytes - before.struct_.bytes
        ),
        (40_000, 40_000 * 32),
        "one 32-byte tuple per pair"
    );
    assert_eq!(
        after.total.allocs - before.total.allocs,
        80_000,
        "the total counts both"
    );
}
