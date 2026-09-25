//! Which arities the other-structs axis takes, asked of the predicate alone.
//!
//! The axis is the one place a door used to derive its own answer instead of
//! reading the predicate's, and no source program can reach the difference: the
//! projection only ever turns the axis on together with a tuple axis that
//! already admits every arity. So the discriminating case is built by hand
//! here, at the layer every door reads.
//!
//! The rest of what a predicate answers is asked in the module's own `tests`,
//! whose helpers these reuse.

use self::tests::{atom, ints, tuple_of};
use super::*;

/// One exact arity-3 shape whose middle position is a 2-tuple. Arity 2 is a
/// question this test asks INSIDE a value and never of a whole one, so it is
/// not among the arities the tuple axis names.
fn nested_pair_in_a_triple() -> RuntimeTypePredicate {
    let mut predicate = tuple_of(vec![vec![atom("ok"), tuple_of(vec![vec![ints(), ints()]]), ints()]]);
    predicate.allow_other_structs = true;
    predicate
}

/// Naming is a TOP-LEVEL reading, so a whole 2-tuple belongs to the
/// other-structs axis even though the test asks about 2-tuples at depth.
///
/// This is the distinction a door loses by reading its own registered tuple
/// schemas: a schema is registered per arity at every depth
/// (`tuple_arities_at_every_depth`), so the nested 2 would exclude a top-level
/// 2-tuple that the axis admits.
#[test]
fn the_other_structs_axis_admits_an_arity_only_a_nested_position_names() {
    let admitted = nested_pair_in_a_triple().other_struct_arities();
    assert!(
        admitted.contains(&2),
        "arity 2 is named only by a nested position, so the tuple axis does not speak for a whole 2-tuple"
    );
    assert!(
        !admitted.contains(&3),
        "arity 3 is the tuple axis' own, and the two axes cover each unnamed struct exactly once"
    );
}

/// The whole-value reading agrees with the axis: a nested arity is one the
/// other-structs axis admits, so no shape of the tuple axis may refuse it.
#[test]
fn a_whole_tuple_of_a_nested_arity_is_never_refused_on_its_shape() {
    let predicate = nested_pair_in_a_triple();
    assert!(matches!(predicate.tuple_positions(2), TuplePositions::Always));
    assert!(matches!(predicate.tuple_positions(3), TuplePositions::AnyOf(_)));
}

#[cfg(test)]
mod value_membership_tests {
    use super::super::surface_membership::SurfaceMembershipCensus;
    use super::super::*;
    use crate::compiler2::World;
    use fz_runtime::any_value::AnyValueRef;

    /// A fake heap: cons cells and tuples addressed by synthetic words the
    /// reader closures resolve, so no value is ever dereferenced except a
    /// tuple's schema id, which the runtime's own `struct_schema_id` reads off
    /// the pointer.
    struct FakeHeap {
        cells: Vec<(RuntimeAnyValue, RuntimeAnyValue)>,
        tuples: Vec<(Box<u32>, Vec<RuntimeAnyValue>)>,
        module: Module,
    }

    impl FakeHeap {
        fn new(atoms: &[&str]) -> Self {
            let module = Module {
                atom_names: atoms.iter().map(|name| (*name).to_string()).collect(),
                ..Module::default()
            };
            Self {
                cells: Vec::new(),
                tuples: Vec::new(),
                module,
            }
        }

        fn atom(&self, name: &str) -> RuntimeAnyValue {
            let id = self
                .module
                .atom_names
                .iter()
                .position(|candidate| candidate == name)
                .expect("the fake heap must intern every atom a test names");
            RuntimeAnyValue::Atom(id as u32)
        }

        /// Cell `index` lives at the synthetic word `(index + 1) * 8`, which is
        /// never dereferenced and is never null, so it is never the empty list.
        fn cons(&mut self, head: RuntimeAnyValue, tail: RuntimeAnyValue) -> RuntimeAnyValue {
            self.cells.push((head, tail));
            Self::cell_ref(self.cells.len() - 1)
        }

        fn cell_ref(index: usize) -> RuntimeAnyValue {
            let addr = ((index + 1) * 8) as *const u8;
            RuntimeAnyValue::HeapRef(AnyValueRef::from_heap_object(ValueKind::LIST, addr).expect("a list ref"))
        }

        /// A proper list, built right to left.
        fn list(&mut self, elements: &[RuntimeAnyValue]) -> RuntimeAnyValue {
            let mut list = RuntimeAnyValue::EmptyList;
            for element in elements.iter().rev() {
                list = self.cons(*element, list);
            }
            list
        }

        /// A cons cell whose tail is itself: a spine no heap the runtime builds
        /// can hold, and the only way to ask whether the walk's termination is a
        /// fact of the code.
        fn cycle(&mut self, head: RuntimeAnyValue) -> RuntimeAnyValue {
            let cell = self.cons(head, RuntimeAnyValue::EmptyList);
            let index = self.cells.len() - 1;
            self.cells[index].1 = cell;
            cell
        }

        /// Its schema id is a real `u32` behind a `Box`, because
        /// `struct_schema_id` reads it off the value itself.
        fn tuple(&mut self, schema: u32, fields: Vec<RuntimeAnyValue>) -> RuntimeAnyValue {
            let boxed = Box::new(schema);
            let addr = (&*boxed) as *const u32 as *const u8;
            self.tuples.push((boxed, fields));
            RuntimeAnyValue::HeapRef(AnyValueRef::from_heap_object(ValueKind::STRUCT, addr).expect("a struct ref"))
        }

        fn cell_of(&self, value: RuntimeAnyValue) -> Option<&(RuntimeAnyValue, RuntimeAnyValue)> {
            let RuntimeAnyValue::HeapRef(value_ref) = value else {
                return None;
            };
            if value_ref.tag() != ValueKind::LIST || value_ref.is_empty_list() {
                return None;
            }
            let index = (value_ref.storage_addr() as usize) / 8;
            self.cells.get(index - 1)
        }

        fn fields_of(&self, value: RuntimeAnyValue) -> Option<&Vec<RuntimeAnyValue>> {
            let addr = value.heap_addr()?;
            self.tuples
                .iter()
                .find(|(schema, _)| (&**schema) as *const u32 as *mut u8 == addr)
                .map(|(_, fields)| fields)
        }
    }

    /// How many escapes the production tripwire reports for one value, asked
    /// the way the interpreter asks it: answer the test, and observe what it
    /// admitted. `arities` registers the schema id of each tuple arity the test
    /// names, which is the runtime's own numbering the interpreter hands in.
    fn escapes(
        heap: &FakeHeap,
        predicate: &RuntimeTypePredicate,
        value: RuntimeAnyValue,
        arities: &[(usize, u32)],
    ) -> usize {
        let tuple_schema_ids = arities.iter().copied().collect::<HashMap<_, _>>();
        let named_schema_ids = HashMap::new();
        let callables = |_: u64| None;
        let fields =
            |value: RuntimeAnyValue, index: usize| heap.fields_of(value).and_then(|fields| fields.get(index)).copied();
        let list_head = |value: RuntimeAnyValue| heap.cell_of(value).map(|(head, _)| *head);
        let list_tail = |value: RuntimeAnyValue| heap.cell_of(value).map(|(_, tail)| *tail);
        let reader = RuntimeValueReader {
            module: &heap.module,
            tuple_schema_ids: &tuple_schema_ids,
            named_schema_ids: &named_schema_ids,
            callables: &callables,
            fields: &fields,
            list_head: &list_head,
            list_tail: &list_tail,
        };
        let census = SurfaceMembershipCensus::install();
        if matches_runtime_type_predicate(predicate, &reader, value) {
            surface_membership::observe(predicate, &reader, value);
        }
        census.escapes()
    }

    fn list_test(shapes: FiniteSet<ListShape>, heads: Vec<RuntimeTypePredicate>) -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.lists = ListShapes::exact(shapes, heads);
        predicate
    }

    fn any_shape() -> FiniteSet<ListShape> {
        FiniteSet::finite([ListShape::Empty, ListShape::NonEmpty])
    }

    fn ints() -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.ints = FiniteSet::any();
        predicate
    }

    fn atom_test(name: &str) -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.atoms = FiniteSet::lit(name.to_string());
        predicate
    }

    /// The two readings agree on a list the clause actually names: every
    /// element answers the one element question, so there is nothing to report.
    #[test]
    fn a_list_whose_every_element_answers_the_head_question_is_inside_the_surface() {
        let mut heap = FakeHeap::new(&["ok"]);
        let value = heap.list(&[RuntimeAnyValue::Int(1), RuntimeAnyValue::Int(2)]);
        assert_eq!(escapes(&heap, &list_test(any_shape(), vec![ints()]), value, &[]), 0);
    }

    /// THE ACCEPTANCE RESIDUE, which is the whole point of the instrument: the
    /// head admits, the TAIL does not, and only the `Full` reading can say so.
    #[test]
    fn a_list_whose_tail_leaves_the_head_question_is_outside_the_surface() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let value = heap.list(&[RuntimeAnyValue::Int(1), ok]);
        assert_eq!(escapes(&heap, &list_test(any_shape(), vec![ints()]), value, &[]), 1);
    }

    /// PER-CLAUSE HOMOGENEITY, not a union of heads. `[int] | [:ok]` names two
    /// list types and `[1, :ok]` is neither, so reading the clauses' heads as
    /// one set would admit it and lose the correlation the clauses keep.
    #[test]
    fn a_mixed_list_belongs_to_no_clause_of_a_union_of_homogeneous_list_clauses() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let value = heap.list(&[RuntimeAnyValue::Int(1), ok]);
        let two_clauses = list_test(any_shape(), vec![ints(), atom_test("ok")]);
        assert_eq!(escapes(&heap, &two_clauses, value, &[]), 1);
    }

    /// The same list under ONE clause whose ELEMENT type is that union is
    /// inside, because a clause is one homogeneous element type and this one
    /// names both. The false escape the per-clause reading must not produce.
    #[test]
    fn a_mixed_list_belongs_to_one_clause_whose_element_type_is_that_union() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let value = heap.list(&[RuntimeAnyValue::Int(1), ok]);
        let mut element = ints();
        element.atoms = FiniteSet::lit("ok".to_string());
        assert_eq!(escapes(&heap, &list_test(any_shape(), vec![element]), value, &[]), 0);
    }

    /// The walk composes: an element that is itself a list is asked under
    /// `Full` too, so `[[1], [:ok]]` leaves `[[int]]` one level in.
    #[test]
    fn an_element_that_is_itself_a_list_is_asked_the_same_way() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let inner_ints = heap.list(&[RuntimeAnyValue::Int(1)]);
        let inner_atoms = heap.list(&[ok]);
        let value = heap.list(&[inner_ints, inner_atoms]);
        let list_of_int_lists = list_test(any_shape(), vec![list_test(any_shape(), vec![ints()])]);
        assert_eq!(escapes(&heap, &list_of_int_lists, value, &[]), 1);
    }

    /// `[]` carries nothing for a body to misread, which is the `[]` exception
    /// stated on the value side: no reading can refuse it.
    #[test]
    fn the_empty_list_carries_no_element_to_refuse() {
        let heap = FakeHeap::new(&["ok"]);
        assert_eq!(
            escapes(
                &heap,
                &list_test(any_shape(), vec![ints()]),
                RuntimeAnyValue::EmptyList,
                &[]
            ),
            0
        );
    }

    /// An axis that asks no head has no `Full` content, so it reports nothing:
    /// honest inertness for exactly the clauses fz-kdt.146's degrade rule could
    /// not shape, rather than a guess about elements nobody projected.
    #[test]
    fn a_list_axis_that_asks_no_head_reports_nothing_rather_than_guessing() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let value = heap.list(&[RuntimeAnyValue::Int(1), ok]);
        let mut shape_only = RuntimeTypePredicate::none();
        shape_only.lists = ListShapes::shape_only(any_shape());
        assert_eq!(escapes(&heap, &shape_only, value, &[]), 0);
    }

    /// A list held in a TUPLE position is walked through that position, because
    /// the scope is threaded through `matches_tuple_shape` already.
    #[test]
    fn a_list_held_in_a_tuple_position_is_walked_through_that_position() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let payload = heap.list(&[RuntimeAnyValue::Int(1), ok]);
        let tag = heap.atom("ok");
        let value = heap.tuple(7, vec![tag, payload]);
        let mut predicate = RuntimeTypePredicate::none();
        predicate.tuples = TupleShapes::exact(vec![vec![atom_test("ok"), list_test(any_shape(), vec![ints()])]]);
        assert_eq!(escapes(&heap, &predicate, value, &[(2, 7)]), 1);
    }

    /// An element question that admits everything refuses nothing, however
    /// heterogeneous the spine: the surface named all of it.
    #[test]
    fn an_element_question_that_admits_everything_refuses_nothing() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let value = heap.list(&[RuntimeAnyValue::Int(1), ok]);
        let element = RuntimeTypePredicate::any();
        assert_eq!(escapes(&heap, &list_test(any_shape(), vec![element]), value, &[]), 0);
    }

    /// A COFINITE head set is "every atom but these", and the walk reads it the
    /// way the head load does -- admitting what it does not exclude, refusing
    /// what it does.
    #[test]
    fn a_cofinite_element_question_refuses_exactly_what_it_excludes() {
        let mut heap = FakeHeap::new(&["ok", "err", "other"]);
        let other = heap.atom("other");
        let err = heap.atom("err");
        let mut element = RuntimeTypePredicate::none();
        element.atoms = FiniteSet {
            values: ["ok".to_string()].into_iter().collect(),
            cofinite: true,
        };
        let admitted = heap.list(&[other, err]);
        assert_eq!(
            escapes(&heap, &list_test(any_shape(), vec![element.clone()]), admitted, &[]),
            0,
        );
        let ok = heap.atom("ok");
        let excluded = heap.list(&[other, ok]);
        assert_eq!(
            escapes(&heap, &list_test(any_shape(), vec![element]), excluded, &[]),
            1,
            "the excluded atom is an element outside the clause, wherever in the spine it sits",
        );
    }

    /// A content-blind element axis (maps, binaries) is decided by kind alone,
    /// so it reads the same under both scopes and a list of them never reports.
    #[test]
    fn a_content_blind_element_axis_reads_the_same_under_both_scopes() {
        let mut heap = FakeHeap::new(&["ok"]);
        let map = RuntimeAnyValue::HeapRef(
            AnyValueRef::from_heap_object(ValueKind::MAP, 0x1000 as *const u8).expect("a map ref"),
        );
        let value = heap.list(&[map, map]);
        let mut element = RuntimeTypePredicate::none();
        element.maps = true;
        assert_eq!(escapes(&heap, &list_test(any_shape(), vec![element]), value, &[]), 0);
    }

    #[test]
    fn real_struct_predicates_distinguish_foo_alone_from_plain_map_unions_and_complements() {
        let mut world = World::new();
        let foo_name = ModuleName::from_segments(vec!["Pkg".into(), "Foo".into()]);
        let foo = world.reference_module(foo_name.clone());
        let int = world.types_mut().int();
        let foo_value = world.struct_value_ty(foo, &["value".to_string()], &[int]);
        let foo_envelope = world.types_mut().runtime_type_test_envelope(foo_value);
        let any = world.types_mut().any();
        let not_foo = world.types_mut().difference(any, foo_envelope);
        let raw_not_foo = world.types_mut().difference(any, foo_value);
        let map_top = world.types_mut().map_top();
        let foo_or_map = world.types_mut().union(foo_value, map_top);
        let foo_predicate = world.types().runtime_type_predicate(&foo_value);
        let not_foo_predicate = world.types().runtime_type_predicate(&not_foo);
        let raw_not_foo_predicate = world.types().runtime_type_predicate(&raw_not_foo);
        let foo_or_map_predicate = world.types().runtime_type_predicate(&foo_or_map);

        let mut heap = FakeHeap::new(&[]);
        heap.module
            .struct_schemas
            .insert(foo_name.clone(), vec!["value".to_string()]);
        let map = RuntimeAnyValue::HeapRef(
            AnyValueRef::from_heap_object(ValueKind::MAP, 0x1000 as *const u8).expect("a map ref"),
        );
        let struct_value = heap.tuple(7, vec![RuntimeAnyValue::Int(1)]);
        let tuple_schema_ids = HashMap::new();
        let named_schema_ids = HashMap::from([(foo_name, 7)]);
        let callables = |_: u64| None;
        let fields =
            |value: RuntimeAnyValue, index: usize| heap.fields_of(value).and_then(|fields| fields.get(index)).copied();
        let list_head = |_: RuntimeAnyValue| None;
        let list_tail = |_: RuntimeAnyValue| None;
        let reader = RuntimeValueReader {
            module: &heap.module,
            tuple_schema_ids: &tuple_schema_ids,
            named_schema_ids: &named_schema_ids,
            callables: &callables,
            fields: &fields,
            list_head: &list_head,
            list_tail: &list_tail,
        };
        assert!(matches_runtime_type_predicate(&foo_predicate, &reader, struct_value));
        assert!(!matches_runtime_type_predicate(&foo_predicate, &reader, map));
        assert!(
            !matches_runtime_type_predicate(&not_foo_predicate, &reader, struct_value),
            "the real complement of Foo must reject a registered Foo value"
        );
        assert!(matches_runtime_type_predicate(&not_foo_predicate, &reader, map));
        assert!(
            matches_runtime_type_predicate(&raw_not_foo_predicate, &reader, struct_value),
            "a raw shaped subtraction must preserve the Foo residue whose fields runtime tests cannot inspect"
        );
        assert!(matches_runtime_type_predicate(
            &not_foo_predicate,
            &reader,
            RuntimeAnyValue::Int(1)
        ));
        assert!(matches_runtime_type_predicate(
            &foo_or_map_predicate,
            &reader,
            struct_value
        ));
        assert!(matches_runtime_type_predicate(&foo_or_map_predicate, &reader, map));
    }

    /// An IMPROPER list's tail is not an element: the walk stops there rather
    /// than judging a value the list type never described.
    #[test]
    fn an_improper_tail_is_not_an_element_and_ends_the_walk() {
        let mut heap = FakeHeap::new(&["ok"]);
        let improper = heap.cons(RuntimeAnyValue::Int(1), RuntimeAnyValue::Int(2));
        assert_eq!(escapes(&heap, &list_test(any_shape(), vec![ints()]), improper, &[]), 0);
        let ok = heap.atom("ok");
        let atom_tailed = heap.cons(RuntimeAnyValue::Int(1), ok);
        assert_eq!(
            escapes(&heap, &list_test(any_shape(), vec![ints()]), atom_tailed, &[]),
            0,
            "an atom tail is not an element either",
        );
    }

    /// What the representation declines to show, the instrument does not judge:
    /// a cons cell the reader cannot open ends the walk silently, exactly as an
    /// unreadable head ends the `Lowered` reading.
    #[test]
    fn a_head_the_representation_declines_to_show_is_not_judged() {
        let heap = FakeHeap::new(&["ok"]);
        let orphan = RuntimeAnyValue::HeapRef(
            AnyValueRef::from_heap_object(ValueKind::LIST, 0x9000 as *const u8).expect("a list ref"),
        );
        assert_eq!(escapes(&heap, &list_test(any_shape(), vec![ints()]), orphan, &[]), 0);
    }

    /// A CALLABLE element is decided by the construction word the backend
    /// minted it with, which no scope changes: a closure the question names is
    /// never a false escape, and one it does not name is refused by BOTH
    /// readings, so it is never an escape either.
    #[test]
    fn a_callable_element_is_decided_by_its_construction_under_both_scopes() {
        let mut heap = FakeHeap::new(&["ok"]);
        // A real closure object: word 0 is the header, word 1 the code word.
        let object: Box<[u64; 2]> = Box::new([0, 66]);
        let addr = (&*object) as *const [u64; 2] as *const u8;
        let closure =
            RuntimeAnyValue::HeapRef(AnyValueRef::from_heap_object(ValueKind::CLOSURE, addr).expect("a closure ref"));
        let value = heap.list(&[closure, closure]);

        let shape = CallableShape {
            target: ClosureTarget(66),
            captures: vec![list_test(any_shape(), vec![ints()])],
        };
        let mut element = RuntimeTypePredicate::none();
        element.callables = CallableShapes::exact(vec![shape.clone()]);
        let tuple_schema_ids = HashMap::new();
        let named_schema_ids = HashMap::new();
        let callables = move |code: u64| (code == 66).then(|| shape.clone());
        let fields =
            |value: RuntimeAnyValue, index: usize| heap.fields_of(value).and_then(|fields| fields.get(index)).copied();
        let list_head = |value: RuntimeAnyValue| heap.cell_of(value).map(|(head, _)| *head);
        let list_tail = |value: RuntimeAnyValue| heap.cell_of(value).map(|(_, tail)| *tail);
        let reader = RuntimeValueReader {
            module: &heap.module,
            tuple_schema_ids: &tuple_schema_ids,
            named_schema_ids: &named_schema_ids,
            callables: &callables,
            fields: &fields,
            list_head: &list_head,
            list_tail: &list_tail,
        };
        let predicate = list_test(any_shape(), vec![element]);
        let census = SurfaceMembershipCensus::install();
        assert!(
            matches_runtime_type_predicate(&predicate, &reader, value),
            "the construction these closures carry is the one the element question names",
        );
        surface_membership::observe(&predicate, &reader, value);
        assert_eq!(
            census.escapes(),
            0,
            "a capture question is answered off the construction word, not off the value's contents, \
             so it reads the same under both scopes",
        );
    }

    /// Termination is a fact of the walk, not of the heap it reads: a spine
    /// that never ends is abandoned at [`ELEMENT_WALK_LIMIT`] and reported as
    /// inside, because a report that can hang the program it instruments is
    /// worse than a report that stops.
    #[test]
    fn a_spine_that_never_ends_is_abandoned_at_the_walk_limit() {
        let mut heap = FakeHeap::new(&["ok"]);
        let value = heap.cycle(RuntimeAnyValue::Int(1));
        assert_eq!(escapes(&heap, &list_test(any_shape(), vec![ints()]), value, &[]), 0);
        let ok = heap.atom("ok");
        let atoms_forever = heap.cycle(ok);
        assert_eq!(
            escapes(&heap, &list_test(any_shape(), vec![ints()]), atoms_forever, &[]),
            0,
            "and a cycle the question refuses at its first element is refused, not walked",
        );
    }

    /// A `[]`-only clause beside a cons clause puts no head question of its
    /// own, so the cons clause's is the only element question and the empty
    /// list is still inside.
    #[test]
    fn an_empty_list_clause_beside_a_cons_clause_asks_only_the_cons_clauses_question() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let test = list_test(any_shape(), vec![ints()]);
        assert_eq!(escapes(&heap, &test, RuntimeAnyValue::EmptyList, &[]), 0);
        let ints_only = heap.list(&[RuntimeAnyValue::Int(1), RuntimeAnyValue::Int(2)]);
        assert_eq!(escapes(&heap, &test, ints_only, &[]), 0);
        let mixed = heap.list(&[RuntimeAnyValue::Int(1), ok]);
        assert_eq!(escapes(&heap, &test, mixed, &[]), 1);
    }

    /// Three levels: a tuple holding a list of tuples whose own position is a
    /// list. The refusal is four loads deep and the walk must still find it.
    #[test]
    fn a_tuple_inside_a_list_inside_a_tuple_is_walked_to_the_bottom() {
        let mut heap = FakeHeap::new(&["ok", "err"]);
        let ok = heap.atom("ok");
        let err = heap.atom("err");
        let good_inner = heap.list(&[RuntimeAnyValue::Int(2)]);
        let bad_inner = heap.list(&[err]);
        let good = heap.tuple(7, vec![RuntimeAnyValue::Int(1), good_inner]);
        let bad = heap.tuple(7, vec![RuntimeAnyValue::Int(1), bad_inner]);
        let spine = heap.list(&[good, bad]);
        let outer = heap.tuple(7, vec![ok, spine]);

        let mut inner_tuple = RuntimeTypePredicate::none();
        inner_tuple.tuples = TupleShapes::exact(vec![vec![ints(), list_test(any_shape(), vec![ints()])]]);
        let mut predicate = RuntimeTypePredicate::none();
        predicate.tuples = TupleShapes::exact(vec![vec![atom_test("ok"), list_test(any_shape(), vec![inner_tuple])]]);
        assert_eq!(escapes(&heap, &predicate, outer, &[(2, 7)]), 1);
    }

    /// A clause that would admit a LATER element does not rescue an earlier
    /// one: per-clause homogeneity is order-blind.
    #[test]
    fn a_clause_that_admits_a_later_element_does_not_rescue_an_earlier_one() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let two_clauses = list_test(any_shape(), vec![ints(), atom_test("ok")]);
        let atom_first = heap.list(&[ok, RuntimeAnyValue::Int(1)]);
        assert_eq!(escapes(&heap, &two_clauses, atom_first, &[]), 1);
        let all_atoms = heap.list(&[ok, ok]);
        assert_eq!(escapes(&heap, &two_clauses, all_atoms, &[]), 0);
    }

    /// A callable element minted from a construction the clause does not name
    /// is outside it, wherever in the spine it sits.
    #[test]
    fn a_callable_element_from_a_construction_the_clause_never_named_is_outside_it() {
        let mut heap = FakeHeap::new(&["ok"]);
        let named: Box<[u64; 2]> = Box::new([0, 66]);
        let other: Box<[u64; 2]> = Box::new([0, 67]);
        let closure = |object: &[u64; 2]| {
            RuntimeAnyValue::HeapRef(
                AnyValueRef::from_heap_object(ValueKind::CLOSURE, object as *const [u64; 2] as *const u8)
                    .expect("a closure ref"),
            )
        };
        let value = heap.list(&[closure(&named), closure(&other)]);

        let shape = CallableShape {
            target: ClosureTarget(66),
            captures: Vec::new(),
        };
        let mut element = RuntimeTypePredicate::none();
        element.callables = CallableShapes::exact(vec![shape.clone()]);
        let predicate = list_test(any_shape(), vec![element]);

        let tuple_schema_ids = HashMap::new();
        let named_schema_ids = HashMap::new();
        let callables = move |code: u64| {
            (code == 66).then(|| shape.clone()).or_else(|| {
                (code == 67).then(|| CallableShape {
                    target: ClosureTarget(67),
                    captures: Vec::new(),
                })
            })
        };
        let fields =
            |value: RuntimeAnyValue, index: usize| heap.fields_of(value).and_then(|fields| fields.get(index)).copied();
        let list_head = |value: RuntimeAnyValue| heap.cell_of(value).map(|(head, _)| *head);
        let list_tail = |value: RuntimeAnyValue| heap.cell_of(value).map(|(_, tail)| *tail);
        let reader = RuntimeValueReader {
            module: &heap.module,
            tuple_schema_ids: &tuple_schema_ids,
            named_schema_ids: &named_schema_ids,
            callables: &callables,
            fields: &fields,
            list_head: &list_head,
            list_tail: &list_tail,
        };
        let census = SurfaceMembershipCensus::install();
        assert!(matches_runtime_type_predicate(&predicate, &reader, value));
        surface_membership::observe(&predicate, &reader, value);
        assert_eq!(census.escapes(), 1);
    }

    /// An improper tail DEEP in the spine still ends the walk, and a refusal
    /// before it is still found.
    #[test]
    fn an_improper_tail_deeper_in_the_spine_ends_the_walk_where_it_sits() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let test = list_test(any_shape(), vec![ints()]);
        let improper = heap.cons(RuntimeAnyValue::Int(1), RuntimeAnyValue::Int(2));
        let deep = heap.cons(RuntimeAnyValue::Int(0), improper);
        assert_eq!(escapes(&heap, &test, deep, &[]), 0);
        let refused_then_improper = {
            let tail = heap.cons(ok, RuntimeAnyValue::Int(2));
            heap.cons(RuntimeAnyValue::Int(0), tail)
        };
        assert_eq!(escapes(&heap, &test, refused_then_improper, &[]), 1);
    }

    /// A nested clause that admits only NON-EMPTY lists refuses an empty
    /// element, which no head load can see.
    #[test]
    fn an_empty_inner_list_leaves_an_element_clause_that_admits_only_cons_cells() {
        let mut heap = FakeHeap::new(&["ok"]);
        let inner = heap.list(&[RuntimeAnyValue::Int(1)]);
        let value = heap.list(&[inner, RuntimeAnyValue::EmptyList]);
        let non_empty_ints = list_test(FiniteSet::lit(ListShape::NonEmpty), vec![ints()]);
        assert_eq!(
            escapes(&heap, &list_test(any_shape(), vec![non_empty_ints]), value, &[]),
            1
        );
    }

    /// THE WALK LIMIT IS A FALSE NEGATIVE, and this pins where it starts: a
    /// refusal at the last index the walk reaches is reported, and the same
    /// refusal one element further out is not.
    #[test]
    fn the_walk_limit_is_where_a_refusal_stops_being_reported() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let test = list_test(any_shape(), vec![ints()]);

        let mut elements = vec![RuntimeAnyValue::Int(1); ELEMENT_WALK_LIMIT - 1];
        elements.push(ok);
        let at_the_last_judged_index = heap.list(&elements);
        assert_eq!(escapes(&heap, &test, at_the_last_judged_index, &[]), 1);

        let mut elements = vec![RuntimeAnyValue::Int(1); ELEMENT_WALK_LIMIT];
        elements.push(ok);
        let one_past_it = heap.list(&elements);
        assert_eq!(
            escapes(&heap, &test, one_past_it, &[]),
            0,
            "past the limit the walk reports nothing, which is a MISSED escape, not a clean list",
        );
    }
}

#[cfg(test)]
mod tests {
    use super::super::*;

    /// Widen this test to admit everything on `axis` and nothing more.
    ///
    /// This is the table read the other way: a field no axis names would be
    /// left at `none()` by the fold below, and `any()` would not come out.
    fn widen_to_top_on(predicate: &mut RuntimeTypePredicate, axis: RuntimeTestAxis) {
        match axis {
            RuntimeTestAxis::Ints => predicate.ints = FiniteSet::any(),
            RuntimeTestAxis::Floats => predicate.floats = FiniteSet::any(),
            RuntimeTestAxis::Atoms => predicate.atoms = FiniteSet::any(),
            RuntimeTestAxis::Lists => predicate.lists = ListShapes::any(),
            RuntimeTestAxis::Tuples => predicate.tuples = TupleShapes::any(),
            RuntimeTestAxis::NamedStructs => predicate.named_structs = FiniteSet::any(),
            RuntimeTestAxis::OtherStructs => predicate.allow_other_structs = true,
            RuntimeTestAxis::Maps => predicate.maps = true,
            RuntimeTestAxis::Binaries => predicate.binaries = true,
            RuntimeTestAxis::Callables => predicate.callables = CallableShapes::any(),
            RuntimeTestAxis::Resources => predicate.resources = true,
        }
    }

    /// A test that admits exactly the floats, for use as a capture question.
    fn floats() -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.floats = FiniteSet::any();
        predicate
    }

    fn construction(target: u32, captures: Vec<RuntimeTypePredicate>) -> CallableShape {
        CallableShape {
            target: ClosureTarget(target),
            captures,
        }
    }

    pub(super) fn tuple_of(shapes: Vec<Vec<RuntimeTypePredicate>>) -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.tuples = TupleShapes::exact(shapes);
        predicate
    }

    /// The decomposition a lowering reads off a tuple whose fields it holds.
    ///
    /// A lowering that already has the positions in hand cannot ask a schema id
    /// anything, so it asks the predicate instead: refuse outright, admit
    /// outright, or match one of these shapes.
    #[test]
    fn tuple_positions_answers_for_a_value_that_is_a_tuple_of_that_arity() {
        let tagged = tuple_of(vec![
            vec![atom("cont"), ints()],
            vec![atom("halt"), ints()],
            vec![ints()],
        ]);
        assert!(matches!(tagged.tuple_positions(3), TuplePositions::Never));
        let TuplePositions::AnyOf(pairs) = tagged.tuple_positions(2) else {
            panic!("an exact axis names the shapes of an arity it admits");
        };
        assert_eq!(pairs.len(), 2, "only the shapes of that arity are candidates");
        assert!(pairs.iter().all(|shape| shape.len() == 2));
        let TuplePositions::AnyOf(singles) = tagged.tuple_positions(1) else {
            panic!("the one-field shape is its own candidate set");
        };
        assert_eq!(singles.len(), 1);

        let mut arity_only = RuntimeTypePredicate::none();
        arity_only.tuples = TupleShapes::arity_only(FiniteSet::lit(2));
        assert!(
            matches!(arity_only.tuple_positions(2), TuplePositions::Always),
            "an inexact axis says nothing about the payloads, so every 2-tuple passes"
        );
        assert!(matches!(arity_only.tuple_positions(3), TuplePositions::Never));

        let mut cofinite = RuntimeTypePredicate::none();
        cofinite.tuples = TupleShapes::arity_only(FiniteSet::cofinite([2]));
        assert!(
            matches!(cofinite.tuple_positions(2), TuplePositions::Never),
            "a cofinite arity set names the arities it refuses"
        );
        assert!(matches!(cofinite.tuple_positions(3), TuplePositions::Always));

        assert!(matches!(
            RuntimeTypePredicate::none().tuple_positions(2),
            TuplePositions::Never
        ));
        assert!(matches!(
            RuntimeTypePredicate::any().tuple_positions(2),
            TuplePositions::Always
        ));
    }

    /// The other-structs axis admits whatever the tuple axis does not name.
    ///
    /// So a test carrying it cannot refuse a tuple on its shape: the value is
    /// admitted by that axis instead, and a lowering deciding per position has
    /// to say so rather than answer from the shapes alone.
    #[test]
    fn tuple_positions_admits_every_arity_the_other_structs_axis_covers() {
        let mut pairs = tuple_of(vec![vec![atom("cont"), ints()]]);
        pairs.allow_other_structs = true;
        assert!(
            matches!(pairs.tuple_positions(2), TuplePositions::AnyOf(_)),
            "an arity the tuple axis names is still decided by its shapes"
        );
        assert!(
            matches!(pairs.tuple_positions(3), TuplePositions::Always),
            "an arity it does not name is admitted by the other-structs axis"
        );
    }

    /// ADMISSION IS CONTAINMENT, NEVER OVERLAP (fz-kdt.167).
    ///
    /// A construction's capture types are the annotation its mint stamped, and
    /// the LAYOUT the capture was stored in is the construction's, not the
    /// value's. So a wrapper closed over `int | float` stores a boxed word,
    /// and a body compiled for an `int` capture reads a raw int out of that
    /// slot -- which is why the union construction must be refused by the
    /// narrow test even though the two overlap. Only a test naming a capture
    /// question the construction's own is INSIDE may admit it.
    #[test]
    fn a_union_capture_construction_is_admitted_only_by_a_test_that_contains_it() {
        let mut int_or_float = ints();
        int_or_float.floats = FiniteSet::any();
        let minted = construction(66, vec![int_or_float.clone()]);

        let narrow = CallableShapes::exact(vec![construction(66, vec![ints()])]);
        assert!(
            narrow.targets().values.contains(&ClosureTarget(66)),
            "the two do name one function, so nothing but the captures can separate them",
        );
        assert!(
            !narrow.admits(&minted),
            "a construction over `int | float` stored a boxed capture; a body whose capture \
             lane is a raw int must not receive it",
        );

        let equal = CallableShapes::exact(vec![construction(66, vec![int_or_float.clone()])]);
        assert!(equal.admits(&minted), "the construction's own shape admits it");

        let mut wider = int_or_float;
        wider.atoms = FiniteSet::any();
        let wide = CallableShapes::exact(vec![construction(66, vec![wider])]);
        assert!(wide.admits(&minted), "and so does any shape that contains it");

        let other_function = CallableShapes::exact(vec![construction(68, vec![ints()])]);
        assert!(
            !other_function.admits(&minted),
            "a different function is a different word"
        );
    }

    /// The callable axis is PER POSITION: it separates exactly as far as its
    /// capture questions do, and erases exactly where they erase.
    ///
    /// Two constructions of one function over disjoint capture types are a
    /// real separation -- a seat may put either first. Two over capture types
    /// that meet only through what a capture's own test cannot see past are
    /// not, and the seat owes them the surface-coverage check (fz-kdt.131).
    #[test]
    fn the_callable_axis_erases_exactly_where_its_captures_do() {
        let over_int = CallableShapes::exact(vec![construction(66, vec![ints()])]);
        let over_float = CallableShapes::exact(vec![construction(66, vec![floats()])]);
        let mut both = RuntimeTypePredicate::none();
        both.callables = over_int;
        let mut other = RuntimeTypePredicate::none();
        other.callables = over_float;
        assert!(
            !both.overlaps(&other),
            "int and float captures are disjoint, so no construction passes both tests",
        );
        assert!(
            !both.overlaps_on_an_erasing_axis(&other),
            "and a disjoint capture position is a separation the seat may rely on",
        );

        let int_list = cons_of(vec![ints()]);
        let int_or_atom_list = cons_of(vec![{
            let mut heads = ints();
            heads.atoms = FiniteSet::any();
            heads
        }]);
        let mut over_int_list = RuntimeTypePredicate::none();
        over_int_list.callables = CallableShapes::exact(vec![construction(66, vec![int_list])]);
        let mut over_wider_list = RuntimeTypePredicate::none();
        over_wider_list.callables = CallableShapes::exact(vec![construction(66, vec![int_or_atom_list])]);
        assert!(
            over_int_list.overlaps(&over_wider_list),
            "`[int]` and `[int | :ok]` admit the same cons cells at the head",
        );
        assert!(
            over_int_list.overlaps_on_an_erasing_axis(&over_wider_list),
            "and they disagree only about a tail no test reads, so the callable axis must \
             report the erasure through the capture rather than claim a separation",
        );

        let coarse = RuntimeTypePredicate {
            callables: CallableShapes::any(),
            ..RuntimeTypePredicate::none()
        };
        assert!(
            coarse.overlaps_on_an_erasing_axis(&both),
            "and an unconstrained callable axis claims no capture separation",
        );
    }

    /// The invariant behind fz-kdt.119 item 6: the axis table is the whole
    /// lattice, so nothing a predicate carries can escape the classification
    /// `overlaps_on_an_erasing_axis` and the three lowerings are written
    /// against.
    #[test]
    fn the_axis_table_names_every_axis_a_predicate_carries() {
        let mut built = RuntimeTypePredicate::none();
        for axis in RuntimeTestAxis::ALL {
            widen_to_top_on(&mut built, axis);
        }
        assert_eq!(
            built,
            RuntimeTypePredicate::any(),
            "an axis the table does not name would leave its field at none() here; \
             add it to RuntimeTestAxis::ALL and to every lowering's match",
        );
    }

    /// Every axis is reachable by some runtime value: a test the runtime can
    /// never be asked is not a test, and a value that reaches no axis is one
    /// no arm can claim.
    #[test]
    fn every_axis_is_reached_by_some_runtime_value_kind() {
        let mut reached = BTreeSet::new();
        for kind in [
            ValueKind::LIST,
            ValueKind::MAP,
            ValueKind::BITSTRING,
            ValueKind::CLOSURE,
            ValueKind::RESOURCE,
            ValueKind::STRUCT,
        ] {
            // A heap value's axes are a function of its tag alone, which is
            // what `of_value` reads; the address is never dereferenced here.
            let axes = axes_for_tag(kind);
            reached.extend(axes.iter().copied());
        }
        reached.extend(RuntimeTestAxis::of_value(RuntimeAnyValue::Int(0)).iter().copied());
        reached.extend(RuntimeTestAxis::of_value(RuntimeAnyValue::Float(0)).iter().copied());
        reached.extend(RuntimeTestAxis::of_value(RuntimeAnyValue::Atom(0)).iter().copied());
        reached.extend(RuntimeTestAxis::of_value(RuntimeAnyValue::EmptyList).iter().copied());
        assert_eq!(
            reached,
            RuntimeTestAxis::ALL.into_iter().collect::<BTreeSet<_>>(),
            "an axis no value kind reaches is a question the runtime is never asked",
        );
    }

    fn axes_for_tag(kind: ValueKind) -> &'static [RuntimeTestAxis] {
        match kind {
            ValueKind::LIST => &[RuntimeTestAxis::Lists],
            ValueKind::MAP => &[RuntimeTestAxis::Maps],
            ValueKind::BITSTRING => &[RuntimeTestAxis::Binaries],
            ValueKind::CLOSURE => &[RuntimeTestAxis::Callables],
            ValueKind::RESOURCE => &[RuntimeTestAxis::Resources],
            ValueKind::STRUCT => &[
                RuntimeTestAxis::Tuples,
                RuntimeTestAxis::NamedStructs,
                RuntimeTestAxis::OtherStructs,
            ],
            _ => &[],
        }
    }

    /// The classification and the relation it feeds must agree: an axis is
    /// erasing exactly when two tests saturating it overlap erasingly.
    #[test]
    fn the_precision_table_is_what_overlaps_on_an_erasing_axis_reports() {
        for axis in RuntimeTestAxis::ALL {
            let mut saturated = RuntimeTypePredicate::none();
            widen_to_top_on(&mut saturated, axis);
            let erases = saturated.overlaps_on_an_erasing_axis(&saturated);
            match axis.precision() {
                AxisPrecision::Separating => assert!(!erases, "{axis:?} is classified separating but reports erasing"),
                // A saturated per-position axis is its own coarse reading --
                // every arity, every element -- so it erases. The per-position
                // shapes and the head questions are what make it separate, and
                // those are the neighbouring tests' business.
                AxisPrecision::Erasing | AxisPrecision::PerPosition => {
                    assert!(erases, "{axis:?} is classified erasing but reports separating")
                }
            }
        }
    }

    fn tuple(shapes: Vec<Vec<RuntimeTypePredicate>>) -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.tuples = TupleShapes::exact(shapes);
        predicate
    }

    pub(super) fn atom(name: &str) -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.atoms = FiniteSet::lit(name.to_string());
        predicate
    }

    pub(super) fn ints() -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.ints = FiniteSet::any();
        predicate
    }

    fn list_of_anything() -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.lists = ListShapes::any();
        predicate
    }

    /// A cons-only test whose head asks `heads`.
    fn cons_of(heads: Vec<RuntimeTypePredicate>) -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.lists = ListShapes::exact(FiniteSet::lit(ListShape::NonEmpty), heads);
        predicate
    }

    /// THE ONE-SIDED-FILTER LAW, stated as a property (fz-kdt.107 step 3).
    ///
    /// A head load rejects exactly and accepts erasingly, so DISJOINT heads
    /// are the only claimable separation and any overlap at all erases. The
    /// second half is the one that was refuted by measurement: reading
    /// "the heads differ" as separation seats `[int]` ahead of `[int | :ok]`,
    /// and `[1, :ok]` then reaches a body that reads every element as an int.
    #[test]
    fn list_heads_separate_only_where_they_are_disjoint() {
        let ints_list = cons_of(vec![ints()]);
        let atoms_list = cons_of(vec![atom("ok")]);
        let mixed_list = cons_of(vec![{
            let mut mixed = ints();
            mixed.atoms = FiniteSet::lit("ok".to_string());
            mixed
        }]);

        assert!(
            !ints_list.overlaps(&atoms_list),
            "disjoint heads are disjoint tests: no list has a first element that is both",
        );
        assert!(
            !ints_list.overlaps_on_an_erasing_axis(&atoms_list),
            "disjoint heads are the one separation a head load can claim",
        );

        assert!(
            ints_list.overlaps(&mixed_list),
            "[1, ..] passes both a [int] head test and a [int | :ok] one",
        );
        assert!(
            ints_list.overlaps_on_an_erasing_axis(&mixed_list),
            "heads that overlap at all erase: the head says nothing about the tail, so a seat \
             must fall back to surface coverage",
        );
        assert!(
            ints_list.contained_in(&mixed_list) && !mixed_list.contained_in(&ints_list),
            "and the narrower head is still the narrower test",
        );
    }

    /// THE `[]` EXCEPTION: two tests meeting only at the empty list do not
    /// erase, because `[]` is one value carrying nothing for a body to
    /// misread -- the same reason the atom axis separates.
    #[test]
    fn two_tests_meeting_only_at_the_empty_list_do_not_erase() {
        let mut empty_or_ints = RuntimeTypePredicate::none();
        empty_or_ints.lists =
            ListShapes::exact(FiniteSet::finite([ListShape::Empty, ListShape::NonEmpty]), vec![ints()]);
        let mut empty_or_atoms = RuntimeTypePredicate::none();
        empty_or_atoms.lists = ListShapes::exact(
            FiniteSet::finite([ListShape::Empty, ListShape::NonEmpty]),
            vec![atom("ok")],
        );
        assert!(
            empty_or_ints.overlaps(&empty_or_atoms),
            "both admit [], so one value passes both tests",
        );
        assert!(
            !empty_or_ints.overlaps_on_an_erasing_axis(&empty_or_atoms),
            "meeting at [] is not a blind meeting: the value carries nothing either body reads",
        );
    }

    /// A head the projection could not name is a head the seat may not read as
    /// separation: the shape-only reading erases against everything that
    /// admits a cons cell.
    #[test]
    fn a_head_blind_list_axis_erases_against_every_cons_test() {
        let blind = list_of_anything();
        let ints_list = cons_of(vec![ints()]);
        assert!(
            blind.overlaps_on_an_erasing_axis(&ints_list),
            "what the projection declines to ask, a seat may not claim as separation",
        );
        assert!(
            ints_list.contained_in(&blind) && !blind.contained_in(&ints_list),
            "the shape-only reading is the over-approximation, so it contains the exact one",
        );
    }

    /// fz-kdt.145, the constructive invariant: every arity ANY sub-predicate
    /// can reach is reported, so every lowering registers a schema for it.
    ///
    /// The prototype of the list axis reported tuple arities through tuple
    /// positions only. An arity reachable solely through a list HEAD went
    /// unregistered, the interpreter's head test rejected the tuple it could
    /// not name, and the JIT -- which registers from the same walk but reads
    /// schema ids the native driver had already minted -- said yes: three
    /// interpreter-only parity breaks from one missing recursion. The walk is
    /// now one exhaustive match over the axis table
    /// (`RuntimeTypePredicate::sub_predicates_on`), so the next nested axis
    /// cannot repeat it without failing to compile.
    #[test]
    fn every_arity_a_sub_predicate_can_reach_is_reported_for_registration() {
        let triple = tuple(vec![vec![ints(), ints(), ints()]]);
        let through_a_head = cons_of(vec![triple]);
        assert_eq!(
            through_a_head.tuple_arities_at_every_depth(),
            BTreeSet::from([3]),
            "an arity reachable only through a list head is still an arity the test asks about",
        );

        let pair_over_a_list = tuple(vec![vec![atom("ok"), through_a_head]]);
        assert_eq!(
            pair_over_a_list.tuple_arities_at_every_depth(),
            BTreeSet::from([2, 3]),
            "and the walk composes: a head inside a position inside a tuple reports every rung",
        );
    }

    /// The P1 claim in lattice terms: two annotated tagged tuples are two
    /// questions, and the seat may treat the difference as separation.
    #[test]
    fn tagged_tuples_that_differ_at_an_atom_position_are_two_questions() {
        let cont = tuple(vec![vec![atom("cont"), ints()]]);
        let halt = tuple(vec![vec![atom("halt"), ints()]]);
        assert_ne!(cont, halt, "the two tests must not be one question");
        assert!(!cont.overlaps(&halt), "no value passes both tests");
        assert!(
            !cont.overlaps_on_an_erasing_axis(&halt),
            "an atom position separates, so a seat needs no surface check here",
        );
    }

    /// fz-kdt.138 in lattice terms: a LIST position is decided like any other,
    /// so it separates exactly as far as the list axis itself does -- by shape,
    /// and by disjoint heads -- and no further.
    ///
    /// This is `dispatch_nested_list_position_separates`' claim one layer down.
    /// Every pair here used to be ONE question, because the position was
    /// excluded from the lattice and from all three lowerings alike.
    #[test]
    fn a_nested_list_position_is_a_question_like_any_other() {
        let mut empty_list = RuntimeTypePredicate::none();
        empty_list.lists = ListShapes::exact(FiniteSet::lit(ListShape::Empty), Vec::new());
        let initial = tuple(vec![vec![empty_list, ints()]]);
        let grown = tuple(vec![vec![cons_of(vec![ints()]), ints()]]);
        assert!(
            !initial.overlaps(&grown),
            "the shapes disagree about the position's SHAPE, so no tuple passes both tests",
        );
        assert!(
            !initial.overlaps_on_an_erasing_axis(&grown),
            "a position the lowerings decide is separation a seat may claim",
        );

        let of_atoms = tuple(vec![vec![cons_of(vec![atom("ok")]), ints()]]);
        assert!(
            !grown.overlaps(&of_atoms),
            "and disjoint HEADS separate the position too, one nesting level in",
        );

        let mut int_or_atom = ints();
        int_or_atom.atoms = FiniteSet::lit("ok".to_string());
        let of_either = tuple(vec![vec![cons_of(vec![int_or_atom]), ints()]]);
        assert!(
            grown.overlaps(&of_either) && grown.overlaps_on_an_erasing_axis(&of_either),
            "the one-sided-filter law holds inside a position: heads that OVERLAP still \
             erase, because the tail behind them is what neither test reads",
        );
    }

    /// Correlation survives the projection: a two-clause union is two shapes,
    /// and the cross terms neither clause names are not admitted.
    #[test]
    fn two_tuple_clauses_stay_two_shapes() {
        let mixed = tuple(vec![vec![atom("cont"), ints()], vec![atom("halt"), atom("ok")]]);
        let list_payload = tuple(vec![vec![atom("cont"), list_of_anything()]]);
        assert!(
            !mixed.overlaps(&list_payload),
            "a list position is a question, so {{:cont, [..]}} and {{:cont, int}} are two of them",
        );
        let cross_of_exact_positions = tuple(vec![vec![atom("cont"), atom("ok")]]);
        assert!(
            !mixed.overlaps(&cross_of_exact_positions),
            "{{:cont, :ok}} is a cross term neither clause names, and the shapes keep it out: \
             joining the clauses position-wise would have admitted it",
        );
    }

    /// Containment is per position, and a wider position is what widens a
    /// shape.
    #[test]
    fn a_shape_contains_another_when_every_position_does() {
        let mut cont_or_halt = RuntimeTypePredicate::none();
        cont_or_halt.atoms = FiniteSet::finite(["cont".to_string(), "halt".to_string()]);
        let wide = tuple(vec![vec![cont_or_halt, ints()]]);
        let narrow = tuple(vec![vec![atom("cont"), ints()]]);
        assert!(
            narrow.contained_in(&wide),
            "a narrower atom position is a narrower shape"
        );
        assert!(!wide.contained_in(&narrow), "and containment is not mutual");
        assert!(
            wide.overlaps(&narrow),
            "a {{:cont, 3}} passes both, so the pair is a seating question at all",
        );
        assert!(
            !wide.overlaps_on_an_erasing_axis(&narrow),
            "and every position they overlap at separates, so precision may settle the seat \
             without a surface-coverage check",
        );
    }

    /// An inexact clause degrades to the arity-only reading rather than
    /// claiming a precision the projection could not produce.
    #[test]
    fn an_inexact_tuple_axis_is_the_arity_only_reading() {
        let exact = tuple(vec![vec![atom("cont"), ints()]]);
        let arity_only = RuntimeTypePredicate::tuple_arity(2);
        assert!(exact.contained_in(&arity_only), "every shape is inside its own arity");
        assert!(
            !arity_only.contained_in(&exact),
            "and the arity admits more than the shape"
        );
        assert!(exact.overlaps(&arity_only));
        assert!(
            exact.overlaps_on_an_erasing_axis(&arity_only),
            "an arity-only test sees nothing of the payload, so it separates nothing",
        );
    }

    /// The arity reading is derived from the shapes, so the coarse callers and
    /// the precise ones can never disagree about which tuples are admitted.
    #[test]
    fn the_arity_reading_is_derived_from_the_shapes() {
        let predicate = tuple(vec![vec![atom("cont"), ints()], vec![ints(), ints(), ints()]]);
        assert_eq!(*predicate.tuples.arities(), FiniteSet::finite([2, 3]));
        assert_eq!(*RuntimeTypePredicate::none().tuples.arities(), FiniteSet::none());
        assert_eq!(*RuntimeTypePredicate::any().tuples.arities(), FiniteSet::any());
        assert_eq!(
            *RuntimeTypePredicate::tuple_arity(3).tuples.arities(),
            FiniteSet::lit(3)
        );
    }

    /// Nested arities are reported, because a nested position can only be
    /// tested where the runtime has a schema to name.
    #[test]
    fn every_nested_tuple_arity_is_reported_for_schema_registration() {
        let inner = tuple(vec![vec![ints(), ints(), ints()]]);
        let outer = tuple(vec![vec![atom("ok"), inner]]);
        assert_eq!(
            outer.tuple_arities_at_every_depth(),
            BTreeSet::from([2, 3]),
            "the inner 3-tuple's schema is what makes the nested position askable",
        );
    }
}
