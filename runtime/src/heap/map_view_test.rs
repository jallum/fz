use super::*;
use crate::heap::{Schema, SchemaRegistry};
use crate::module_name::ModuleName;
use crate::process::Node;
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

    fn entries(&self, map: AnyValueRef) -> Vec<(AnyValue, AnyValue)> {
        let layout = self.heap.expect_map_layout(map, "test");
        self.heap.map_view_entries(layout)
    }

    /// `struct_of_entries` over the entries layout map holding `entries`.
    fn struct_of_entries(&mut self, entries: &[(AnyValue, AnyValue)]) -> Option<AnyValueRef> {
        let bits = self.heap.alloc_map_slots(entries);
        let addr = map_addr_from_tagged(bits).expect("published map");
        self.heap.struct_of_entries(addr)
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
    unsafe { f.heap.map_destination_put(dest, y, AnyValue::int(5)) };
    let updated = f.heap.map_destination_freeze(dest).expect("every key is present");
    assert!(is_struct_layout(f.heap.map_layout(updated)));
    assert_eq!(f.entries(updated), f.point_entries(1, 5));
}

#[test]
fn an_update_naming_a_missing_key_makes_no_map() {
    let mut f = fixture();
    let p = f.point(1, 2);
    let dest = f.heap.alloc_map_update(p);
    let x = f.atom("x");
    let z = f.atom("z");
    unsafe {
        f.heap.map_destination_put(dest, z, AnyValue::int(0));
        f.heap.map_destination_put(dest, x, AnyValue::int(9));
    }
    assert!(
        f.heap.map_destination_freeze(dest).is_none(),
        "a miss anywhere in the update answers no map"
    );
}

#[test]
fn entries_whose_keys_are_a_structs_come_back_as_that_struct() {
    let mut f = fixture();
    let exact = f.point_entries(3, 4);
    let object = f.struct_of_entries(&exact).expect("the keys are exactly Pt's");
    assert!(is_struct_layout(f.heap.map_layout(object)));
    assert_eq!(f.entries(object), exact);

    let mut extra = f.point_entries(3, 4);
    extra.push((f.atom("z"), AnyValue::int(0)));
    assert!(f.struct_of_entries(&extra).is_none(), "an extra key is not Pt");
    let unknown = vec![(f.atom("__struct__"), f.atom("Elixir.Nope"))];
    assert!(
        f.struct_of_entries(&unknown).is_none(),
        "an unregistered module is no struct"
    );
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
