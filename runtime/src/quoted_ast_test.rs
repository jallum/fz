use super::*;
use crate::any_value::{AnyValue, AnyValueRef, SlotLayout, ValueKind};
use crate::heap::{Schema, SchemaRegistry};
use crate::module_name::ModuleName;
use std::cell::RefCell;
use std::rc::Rc;

struct Terms {
    heap: Heap,
}

fn terms() -> Terms {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    Terms {
        heap: Heap::new(4096, schemas),
    }
}

impl Terms {
    fn value(term: AnyValueRef) -> AnyValue {
        AnyValue::from_ref(term).expect("term has a value")
    }

    fn int(&mut self, n: i64) -> AnyValueRef {
        self.heap.box_any_value_ref(AnyValue::int(n))
    }

    fn binary(&mut self, bytes: &[u8]) -> AnyValueRef {
        let bits = self.heap.alloc_bitstring(bytes, (bytes.len() * 8) as u64);
        self.heap.box_any_value_ref(bits)
    }

    fn atom(&self, id: u32) -> AnyValueRef {
        AnyValueRef::atom(id)
    }

    fn pid(&self) -> AnyValueRef {
        AnyValueRef::pid(7).expect("pid ref")
    }

    fn reference(&mut self) -> AnyValueRef {
        self.heap.box_any_value_ref(AnyValue::Opaque(ValueKind::REF, 9))
    }

    fn closure(&mut self) -> AnyValueRef {
        let bits = self
            .heap
            .alloc_closure(crate::any_value::ClosureDenotationId::user(0), 0, 0, 0, 0xfeed, &[]);
        let addr = crate::any_value::closure_addr_from_tagged(bits).expect("closure addr");
        AnyValueRef::from_heap_object(ValueKind::CLOSURE, addr).expect("closure ref")
    }

    fn map(&mut self) -> AnyValueRef {
        let bits = self.heap.alloc_map_slots(&[(AnyValue::atom(1), AnyValue::int(2))]);
        let addr = crate::any_value::map_addr_from_tagged(bits).expect("map addr");
        AnyValueRef::from_heap_object(ValueKind::MAP, addr).expect("map ref")
    }

    fn list(&mut self, items: &[AnyValueRef]) -> AnyValueRef {
        self.improper(items, AnyValueRef::empty_list())
    }

    /// `[items... | tail]`
    fn improper(&mut self, items: &[AnyValueRef], tail: AnyValueRef) -> AnyValueRef {
        let mut list = Self::value(tail);
        for item in items.iter().rev() {
            let cell = self.heap.alloc_list_cons_any(Self::value(*item), list);
            list = Self::value(cell);
        }
        match list {
            AnyValue::EmptyList => AnyValueRef::empty_list(),
            other => self.heap.box_any_value_ref(other),
        }
    }

    fn tuple(&mut self, fields: &[AnyValueRef]) -> AnyValueRef {
        let schema = self.heap.register_schema(Schema::tuple_of_arity(fields.len()));
        self.struct_of(schema, fields)
    }

    fn struct_of(&mut self, schema: u32, fields: &[AnyValueRef]) -> AnyValueRef {
        let object = self.heap.alloc_struct(schema);
        let layout = SlotLayout::of(fields.len());
        for (index, field) in fields.iter().enumerate() {
            unsafe {
                self.heap
                    .store_struct_field(
                        object,
                        SlotLayout::slot_offset(index),
                        layout.kind_offset(index),
                        Self::value(*field),
                    )
                    .expect("field stored")
            };
        }
        AnyValueRef::from_heap_object(ValueKind::STRUCT, object).expect("struct ref")
    }

    fn call_node(&mut self, call: AnyValueRef, meta: AnyValueRef, args: AnyValueRef) -> AnyValueRef {
        self.tuple(&[call, meta, args])
    }

    fn accepts(&self, term: AnyValueRef) -> bool {
        shallow_valid_ast(&self.heap, term)
    }
}

/// Atoms, numbers, pids, funs and the empty list stand for themselves in
/// quoted code; Elixir's `is_atom/is_number/is_pid/is_function` clauses.
#[test]
fn a_literal_a_pid_and_a_fun_are_quoted_code() {
    let mut t = terms();
    let one = t.int(1);
    let pid = t.pid();
    let fun = t.closure();
    assert!(t.accepts(t.atom(3)));
    assert!(t.accepts(one));
    assert!(t.accepts(pid));
    assert!(t.accepts(fun));
    assert!(t.accepts(AnyValueRef::empty_list()));
}

/// A binary is quoted code: a string literal stands for itself, as
/// `is_binary` in Elixir's `shallow_valid_elem`.
#[test]
fn a_binary_is_quoted_code() {
    let mut t = terms();
    let text = t.binary(b"text");
    assert!(t.accepts(text));
    let in_list = t.list(&[text]);
    assert!(t.accepts(in_list));
}

/// A reference and a map are not quoted code: no clause of
/// `shallow_valid_ast` accepts them.
#[test]
fn a_reference_and_a_map_are_not_quoted_code() {
    let mut t = terms();
    let reference = t.reference();
    let map = t.map();
    assert!(!t.accepts(reference));
    assert!(!t.accepts(map));
}

/// `shallow_valid_ast([H | T])` walks the spine, so an improper list fails.
#[test]
fn a_list_must_be_proper() {
    let mut t = terms();
    let (one, two, three) = (t.int(1), t.int(2), t.int(3));
    let proper = t.list(&[one, two, three]);
    let improper = t.improper(&[one], two);
    assert!(t.accepts(proper));
    assert!(!t.accepts(improper));
}

/// The elements of a list are checked at the top level only: a list inside
/// a list is accepted without being read, so `[[1 | 2]]` passes.
#[test]
fn a_list_inside_a_list_is_not_read() {
    let mut t = terms();
    let (one, two) = (t.int(1), t.int(2));
    let inner = t.improper(&[one], two);
    let outer = t.list(&[inner]);
    assert!(t.accepts(outer));
}

/// An element of a list that is not itself valid fails the list.
#[test]
fn a_list_element_must_be_valid() {
    let mut t = terms();
    let one = t.int(1);
    let map = t.map();
    let bad = t.list(&[one, map]);
    assert!(!t.accepts(bad));
}

/// A two-tuple is a pair whose parts are both valid.
#[test]
fn a_pair_of_valid_parts_is_quoted_code() {
    let mut t = terms();
    let one = t.int(1);
    let ok = t.atom(3);
    let pair = t.tuple(&[ok, one]);
    assert!(t.accepts(pair));
    let map = t.map();
    let bad = t.tuple(&[ok, map]);
    assert!(!t.accepts(bad));
}

/// A three-tuple is a call node: `{call, meta, args}` with a list meta and
/// a list or atom args. `{1, 2, 3}` is not one.
#[test]
fn a_three_tuple_must_be_a_call_node() {
    let mut t = terms();
    let (one, two, three) = (t.int(1), t.int(2), t.int(3));
    let f = t.atom(4);
    let nil = AnyValueRef::empty_list();
    let args = t.list(&[one]);
    let call = t.call_node(f, nil, args);
    assert!(t.accepts(call));

    let variable = t.call_node(f, nil, t.atom(5));
    assert!(t.accepts(variable), "a variable's args is its context atom");

    let numbers = t.tuple(&[one, two, three]);
    assert!(!t.accepts(numbers));

    let meta_not_list = t.call_node(f, one, args);
    assert!(!t.accepts(meta_not_list));
}

/// A call whose head is not an atom is a remote or anonymous call; its head
/// is itself checked, and only with list args.
#[test]
fn a_call_node_whose_head_is_code_takes_list_args() {
    let mut t = terms();
    let f = t.atom(4);
    let nil = AnyValueRef::empty_list();
    let one = t.int(1);
    let args = t.list(&[one]);
    let head = t.call_node(f, nil, args);
    let nested = t.call_node(head, nil, args);
    assert!(t.accepts(nested));

    let map = t.map();
    let bad_head = t.call_node(map, nil, args);
    assert!(!t.accepts(bad_head));

    let atom_args = t.call_node(head, nil, t.atom(5));
    assert!(!t.accepts(atom_args));
}

/// Tuples of any other arity are not quoted code.
#[test]
fn a_tuple_of_another_arity_is_not_quoted_code() {
    let mut t = terms();
    let one = t.int(1);
    let four = t.tuple(&[one, one, one, one]);
    let one_tuple = t.tuple(&[one]);
    assert!(!t.accepts(four));
    assert!(!t.accepts(one_tuple));
}

/// A struct shares the tuple's heap tag but is a map in Elixir, so a
/// two-field and a three-field struct are not quoted code.
#[test]
fn a_struct_is_not_quoted_code() {
    let mut t = terms();
    let one = t.int(1);
    let pair_name = ModuleName::from_segments(vec!["Pair".to_string()]);
    let triple_name = ModuleName::from_segments(vec!["Triple".to_string()]);
    let pair = t
        .heap
        .register_schema(Schema::named_struct(pair_name, ["a".to_string(), "b".to_string()]));
    let triple = t.heap.register_schema(Schema::named_struct(
        triple_name,
        ["a".to_string(), "b".to_string(), "c".to_string()],
    ));
    let pair = t.struct_of(pair, &[one, one]);
    let triple = t.struct_of(
        triple,
        &[t.atom(4), AnyValueRef::empty_list(), AnyValueRef::empty_list()],
    );
    assert!(!t.accepts(pair));
    assert!(!t.accepts(triple));
}
