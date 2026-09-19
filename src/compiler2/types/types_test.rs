use std::collections::{BTreeMap, HashMap};
use std::mem;
use std::slice;

use super::*;
use crate::compiler2::ModuleId;
use crate::dispatch_matrix::demand::DispatchDemand;
use crate::finite_set::FiniteSet;
use crate::runtime_type_predicate::{CallableShape, ListShape, ListShapes, RuntimeTypePredicate};

fn module_name(text: &str) -> ModuleName {
    ModuleName::parse_dotted(text).expect("test source module path")
}

#[test]
fn ty_is_an_integer_handle() {
    assert_eq!(mem::size_of::<Ty>(), mem::size_of::<u32>());
}

#[test]
fn factory_interns_equal_descriptors() {
    let mut t = Types::new();
    assert_eq!(t.int(), t.int());
    let a = t.int();
    let lhs = t.tuple(&[a]);
    let rhs = t.tuple(&[a]);
    assert_eq!(lhs, rhs);
}

#[test]
fn union_of_the_same_type_returns_before_it_probes_or_normalizes() {
    let mut t = Types::new();
    let int = t.int();
    let before = t.interning_work_stats();

    assert_eq!(t.union(int, int), int);
    let expected = InterningWorkStats {
        identity_shortcuts: before.identity_shortcuts + 1,
        ..before
    };
    assert_eq!(
        t.interning_work_stats(),
        expected,
        "identity union already has its canonical Ty; it must not probe or normalize a descriptor"
    );
}

#[test]
fn empty_constant_and_self_difference_return_before_the_type_boundary() {
    let mut t = Types::new();

    let before_none = t.interning_work_stats();
    let none = t.none();
    assert_eq!(
        t.interning_work_stats(),
        before_none,
        "the empty lattice constant already has its canonical Ty; asking for it must not rebuild, hash, or probe a descriptor"
    );

    let int = t.int();
    let before_difference = t.interning_work_stats();
    let before_operations = t.binary_type_operation_stats();
    assert_eq!(t.difference(int, int), none, "t \\ t is the empty type");
    assert_eq!(
        t.interning_work_stats(),
        before_difference,
        "the self-difference law already knows the empty Ty; it must not build or intern a descriptor"
    );
    assert_eq!(
        t.binary_type_operation_stats(),
        before_operations,
        "a lattice law with a known constant result must not occupy an operand-pair result entry"
    );
}

#[test]
fn fixed_type_constructors_return_before_the_type_boundary() {
    let mut t = Types::new();
    let before = t.interning_work_stats();

    let any = t.any();
    let none = t.none();
    let nil = t.nil();
    let bool_t = t.bool();
    let int = t.int();
    let int_lit = t.int_lit(42);
    let float = t.float();
    let float_lit = t.float_lit(42.0);
    let atom = t.atom();
    let empty_list = t.empty_list();
    let str_t = t.str_t();
    let map_top = t.map_top();
    let pid = t.pid();
    let reference = t.reference();
    let c_pointer = t.c_pointer();

    assert_eq!(int_lit, int, "numeric literals use their fixed kind type");
    assert_eq!(float_lit, float, "numeric literals use their fixed kind type");
    assert_ne!(any, none, "the lattice constants stay distinct");
    assert_ne!(nil, bool_t, "fixed atom types stay distinct");
    assert_ne!(atom, empty_list, "fixed value families stay distinct");
    assert_ne!(str_t, map_top, "fixed structural tops stay distinct");
    assert_ne!(pid, reference, "built-in opaque identities stay distinct");
    assert_ne!(reference, c_pointer, "built-in opaque identities stay distinct");
    assert_eq!(
        t.interning_work_stats(),
        before,
        "a fixed type is already owned by this world; its constructor must not rebuild, hash, or probe a descriptor"
    );
}

#[test]
fn canonical_empty_identity_returns_before_the_comparison_cache() {
    let mut t = Types::new();
    let none = t.none();
    let int = t.int();
    let empty_non_empty_list = t.non_empty_list(none);
    let list = t.list(int);
    assert_eq!(
        empty_non_empty_list, none,
        "a non-empty list cannot hold an empty element type"
    );

    let before = t.comparison_cache_stats();
    assert!(t.is_empty(&none));
    assert!(t.is_empty(&empty_non_empty_list));
    assert!(!t.is_empty(&int));
    assert!(!t.is_empty(&list));
    assert_eq!(
        t.comparison_cache_stats(),
        before,
        "the interning boundary gives every empty denotation the canonical bottom Ty; checking it must not hash, cache, or traverse"
    );
}

#[test]
fn empty_operand_constructors_return_before_the_type_boundary() {
    let mut t = Types::new();
    let none = t.none();
    let empty_list = t.empty_list();
    let before = t.interning_work_stats();

    assert_eq!(t.resource(none), none, "a resource cannot carry an empty payload");
    assert_eq!(
        t.non_empty_list(none),
        none,
        "a non-empty list cannot hold an empty element type"
    );
    assert_eq!(
        t.list(none),
        empty_list,
        "a list of no possible element is exactly the retained empty-list type"
    );
    assert_eq!(
        t.interning_work_stats(),
        before,
        "canonical empty operands already determine these constructors; they must not build, inspect, hash, or probe a descriptor"
    );
}

#[test]
fn canonical_bottom_binary_laws_return_before_the_operation_boundary() {
    let mut t = Types::new();
    let none = t.none();
    let int = t.int();
    let before_interning = t.interning_work_stats();
    let before_operations = t.binary_type_operation_stats();

    assert_eq!(t.union(none, int), int, "none is union's left identity");
    assert_eq!(t.union(int, none), int, "none is union's right identity");
    assert_eq!(t.intersect(none, int), none, "none absorbs intersection on the left");
    assert_eq!(t.intersect(int, none), none, "none absorbs intersection on the right");
    assert_eq!(t.difference(none, int), none, "none minus a type remains none");
    assert_eq!(t.difference(int, none), int, "subtracting none changes no type");
    assert_eq!(
        t.interning_work_stats(),
        before_interning,
        "canonical bottom already determines each result; no descriptor may reach the interner"
    );
    assert_eq!(
        t.binary_type_operation_stats(),
        before_operations,
        "canonical bottom laws must not hash operands or occupy the binary-operation table"
    );
}

#[test]
fn impossible_tuple_returns_before_the_type_boundary() {
    let mut t = Types::new();
    let int = t.int();
    let none = t.none();
    let before = t.interning_work_stats();

    assert_eq!(
        t.tuple(&[int, none, int]),
        none,
        "a product with an uninhabited coordinate is uninhabited"
    );
    assert_eq!(
        t.interning_work_stats(),
        before,
        "an interned bottom field decides tuple emptiness without hashing or normalizing a descriptor"
    );
}

#[test]
fn impossible_map_returns_before_the_type_boundary() {
    let mut t = Types::new();
    let int = t.int();
    let none = t.none();
    let before = t.interning_work_stats();

    assert_eq!(
        t.map(&[
            (MapKey::Atom("left".to_string()), int),
            (MapKey::Atom("missing".to_string()), none),
            (MapKey::Atom("right".to_string()), int),
        ]),
        none,
        "a map with an uninhabited required field is uninhabited"
    );
    assert_eq!(
        t.interning_work_stats(),
        before,
        "a final bottom map field decides emptiness without hashing or normalizing a descriptor"
    );

    let shadowed = MapKey::Atom("shadowed".to_string());
    let overwritten = t.map(&[(shadowed.clone(), none), (shadowed.clone(), int)]);
    assert_ne!(
        overwritten, none,
        "the last value for a duplicate map key remains the required field"
    );
    assert_eq!(
        t.map_field_lookup(&overwritten, &shadowed),
        Some(int),
        "the last value for a duplicate map key remains its field type"
    );
}

#[test]
fn impossible_struct_returns_before_the_type_boundary() {
    let mut t = Types::new();
    let int = t.int();
    let none = t.none();
    let before = t.interning_work_stats();

    assert_eq!(
        t.struct_map(
            ModuleId::for_test(1),
            module_name("Pkg.Impossible"),
            &[
                (MapKey::Atom("left".to_string()), int),
                (MapKey::Atom("missing".to_string()), none),
                (MapKey::Atom("right".to_string()), int),
            ],
        ),
        none,
        "a struct with an uninhabited required field is uninhabited"
    );
    assert_eq!(
        t.interning_work_stats(),
        before,
        "a final bottom struct field decides emptiness without hashing or normalizing a descriptor"
    );

    let shadowed = MapKey::Atom("shadowed".to_string());
    let overwritten = t.struct_map(
        ModuleId::for_test(2),
        module_name("Pkg.Shadowed"),
        &[(shadowed.clone(), none), (shadowed.clone(), int)],
    );
    assert_ne!(
        overwritten, none,
        "the last value for a duplicate struct field remains required"
    );
    assert_eq!(
        t.map_field_lookup(&overwritten, &shadowed),
        Some(int),
        "the last value for a duplicate struct field remains its field type"
    );
}

#[test]
fn repeating_binary_type_algebra_returns_before_it_rebuilds_a_descriptor() {
    let mut t = Types::new();
    let int = t.int();
    let atom = t.atom();

    let union = t.union(int, atom);
    let intersection = t.intersect(int, atom);
    let difference = t.difference(int, atom);
    let widened = t.refine_widen(&int, &atom);
    assert!(t.is_empty(&intersection));
    assert_eq!(difference, int);
    assert_eq!(widened, union);
    assert_eq!(
        t.binary_type_operation_stats(),
        BinaryTypeOperationStats {
            union: BinaryTypeOperationCount { hits: 1, misses: 1 },
            intersect: BinaryTypeOperationCount { hits: 0, misses: 1 },
            difference: BinaryTypeOperationCount { hits: 0, misses: 1 },
            refine_widen: BinaryTypeOperationCount { hits: 0, misses: 1 },
        },
        "the refinement reuses the union it reaches, while each first operation publishes one result"
    );

    let before_replay = t.interning_work_stats();
    assert_eq!(t.union(int, atom), union);
    assert_eq!(t.union(atom, int), union, "union is exact in either operand order");
    assert_eq!(t.intersect(int, atom), intersection);
    assert_eq!(t.difference(int, atom), difference);
    assert_eq!(t.refine_widen(&int, &atom), widened);
    assert_eq!(
        t.interning_work_stats(),
        before_replay,
        "a repeated immutable operand pair must return its remembered Ty before it rebuilds or interns a descriptor"
    );
    assert_eq!(
        t.binary_type_operation_stats(),
        BinaryTypeOperationStats {
            union: BinaryTypeOperationCount { hits: 3, misses: 1 },
            intersect: BinaryTypeOperationCount { hits: 1, misses: 1 },
            difference: BinaryTypeOperationCount { hits: 1, misses: 1 },
            refine_widen: BinaryTypeOperationCount { hits: 1, misses: 1 },
        },
        "each replay must use its operation-tagged, immutable operand result"
    );

    let before_inverse = t.interning_work_stats();
    assert_eq!(t.difference(atom, int), atom);
    assert_eq!(
        t.interning_work_stats().raw_index_probes,
        before_inverse.raw_index_probes + 1,
        "the inverse of an ordered operation must not collide with its original pair"
    );
}

#[test]
fn unchanged_map_refinement_returns_before_it_probes_or_normalizes() {
    let mut t = Types::new();
    let int = t.int();
    let key = MapKey::Atom("value".to_string());
    let map = t.map(&[(key.clone(), int)]);
    let before = t.interning_work_stats();

    assert_eq!(t.refine_map_field(&map, &key, &int), map);
    let expected = InterningWorkStats {
        identity_shortcuts: before.identity_shortcuts + 1,
        ..before
    };
    assert_eq!(
        t.interning_work_stats(),
        expected,
        "an unchanged map field already has its canonical Ty; it must not probe or normalize a descriptor"
    );
}

#[test]
fn widening_the_same_type_returns_before_it_probes_or_normalizes() {
    let mut t = Types::new();
    let int = t.int();
    let list = t.list(int);
    let before = t.interning_work_stats();

    assert_eq!(t.refine_widen(&list, &list), list);
    let expected = InterningWorkStats {
        identity_shortcuts: before.identity_shortcuts + 1,
        ..before
    };
    assert_eq!(
        t.interning_work_stats(),
        expected,
        "a self-join already has its canonical Ty; it must not probe or normalize a descriptor"
    );
}

#[test]
fn unchanged_instantiation_returns_before_it_probes_or_normalizes() {
    let mut t = Types::new();
    let int = t.int();
    let list = t.list(int);
    let concrete = t.tuple(&[list, int]);
    let unrelated = Sigma::from([(TypeVarId(99), int)]);
    let template = t.type_var(TypeVarId(0));
    let empty = Sigma::new();
    let before = t.interning_work_stats();

    assert_eq!(t.instantiate(&concrete, &unrelated), concrete);
    assert_eq!(t.instantiate(&template, &empty), template);

    let expected = InterningWorkStats {
        identity_shortcuts: before.identity_shortcuts + 2,
        ..before
    };
    assert_eq!(
        t.interning_work_stats(),
        expected,
        "an instantiation without a possible replacement must not probe or normalize a descriptor"
    );

    assert_eq!(
        t.instantiate(&template, &unrelated),
        template,
        "an unrelated substitution leaves a template semantically unchanged"
    );
    let matching = Sigma::from([(TypeVarId(0), int)]);
    assert_eq!(
        t.instantiate(&template, &matching),
        int,
        "a matching substitution still returns the canonical specialized Ty"
    );
}

#[test]
fn closure_input_erasure_leaves_unignored_inputs_unchanged() {
    let mut t = Types::new();
    let int = t.int();
    let inputs = [int];
    let before = t.interning_work_stats();

    assert_eq!(
        t.erase_transported_closure_identity_inputs(&inputs, &[DispatchDemand::Whole])
            .as_ref(),
        inputs
    );
    assert_eq!(
        t.interning_work_stats(),
        before,
        "an input-erasure mask without an ignored parameter cannot intern a value"
    );

    let literal = t.closure_lit(ClosureTarget(7), vec![], 0);
    let erased = t.erase_transported_closure_identity_inputs(&[literal], &[DispatchDemand::Ignore]);
    assert_ne!(
        erased[0], literal,
        "an ignored closure input must still erase its construction identity"
    );
}

#[test]
fn regular_component_replays_its_completed_descriptor() {
    let mut t = Types::new();
    let recursive = t.intern_regular_component(1, |nodes| vec![DescrOf::tuple_of(vec![nodes[0]])])[0];
    let inventory = t.identity_inventory();

    assert_eq!(t.intern(Descr::tuple_of(vec![recursive])), recursive);
    assert_eq!(t.identity_inventory(), inventory);
}

#[test]
fn renderers_bind_a_recursive_self_type() {
    let mut t = Types::new();
    let recursive = t.intern_regular_component(1, |nodes| {
        let mut body = DescrOf::atom_lit("start");
        body.tuples.push(Conj::pos_of(TupleSigOf { elems: vec![nodes[0]] }));
        vec![body]
    })[0];
    let labels = |_: FnId| String::new();
    let mut canon = TyCanon::new(&labels);

    assert_eq!(t.display(&recursive), "μX. :start | {X}");
    assert_eq!(canon.render(&t, recursive).as_ref(), "fp[a:start;T] μX. :start | {X}");
}

#[test]
fn renderers_name_independently_built_recursive_components_identically() {
    let mut first = Types::new();
    let first_root = first.intern_regular_component(1, |nodes| vec![recursive_tuple_body(nodes[0])])[0];

    let mut second = Types::new();
    second.atom_lit("unrelated");
    let second_root = second.intern_regular_component(1, |nodes| vec![recursive_tuple_body(nodes[0])])[0];
    let labels = |_: FnId| String::new();
    let mut first_canon = TyCanon::new(&labels);
    let mut second_canon = TyCanon::new(&labels);

    assert_eq!(first.display(&first_root), second.display(&second_root));
    assert_eq!(
        first_canon.render(&first, first_root),
        second_canon.render(&second, second_root)
    );
}

fn recursive_tuple_body(reference: ComponentRef) -> DescrOf<ComponentRef> {
    recursive_tuple_body_named("start", reference)
}

fn recursive_list_body(reference: ComponentRef) -> DescrOf<ComponentRef> {
    let mut descr = DescrOf::atom_lit("start");
    descr.lists.push(Conj::pos_of(ListSigOf::possibly_empty(reference)));
    descr
}

fn recursive_tuple_body_named(name: &str, reference: ComponentRef) -> DescrOf<ComponentRef> {
    let mut descr = DescrOf::<ComponentRef>::atom_lit(name);
    descr.tuples.push(Conj::pos_of(TupleSigOf { elems: vec![reference] }));
    descr
}

fn recursive_tuple_descr(reference: Ty) -> Descr {
    let mut descr = Descr::atom_lit("start");
    descr.tuples.push(Conj::pos_of(TupleSig { elems: vec![reference] }));
    descr
}

#[test]
fn renderers_bind_mutually_recursive_types() {
    let mut t = Types::new();
    let roots = t.intern_regular_component(2, |nodes| {
        vec![recursive_tuple_body(nodes[1]), DescrOf::list_of(nodes[0])]
    });
    let labels = |_: FnId| String::new();
    let mut canon = TyCanon::new(&labels);

    assert_eq!(t.display(&roots[0]), "μX. :start | {[X]}");
    assert_eq!(t.display(&roots[1]), "μX. [:start | {X}]");
    assert_eq!(
        canon.render(&t, roots[0]).as_ref(),
        "fp[a:start;T] μX. :start | {list(X)}"
    );
    assert_eq!(canon.render(&t, roots[1]).as_ref(), "fp[L] μX. list(:start | {X})");
}

#[test]
fn canon_distinguishes_recursive_denotations_without_ids() {
    let mut t = Types::new();
    let tuple = t.intern_regular_component(1, |nodes| vec![recursive_tuple_body(nodes[0])])[0];
    let list = t.intern_regular_component(1, |nodes| vec![recursive_list_body(nodes[0])])[0];
    let labels = |_: FnId| String::new();
    let mut canon = TyCanon::new(&labels);

    let tuple = canon.render(&t, tuple);
    let list = canon.render(&t, list);
    assert_ne!(tuple, list);
    assert!(!tuple.contains("Ty("));
    assert!(!list.contains("Ty("));
}

fn recursive_capture_body(capture: ComponentRef, result: Ty) -> DescrOf<ComponentRef> {
    let mut descr = DescrOf::unbranded();
    descr.funcs.push(Conj::pos_of(ArrowSigOf {
        args: Vec::new(),
        ret: ComponentRef::Published(result),
        lit: Some(ClosureLitOf {
            kind: CallableValueKind::Closure,
            fn_id: None,
            captures: vec![capture],
        }),
    }));
    descr
}

#[test]
fn regular_component_interns_bisimilar_unrollings_once() {
    let mut t = Types::new();
    let self_recursive = t.intern_regular_component(1, |nodes| vec![recursive_tuple_body(nodes[0])])[0];
    let inventory = t.identity_inventory();

    let mutual = t.intern_regular_component(2, |nodes| {
        vec![recursive_tuple_body(nodes[1]), recursive_tuple_body(nodes[0])]
    });

    assert_eq!(mutual, vec![self_recursive, self_recursive]);
    assert_eq!(t.identity_inventory(), inventory);
    assert_eq!(t.intern(recursive_tuple_descr(self_recursive)), self_recursive);
    let labels = |_: FnId| String::new();
    let mut canon = TyCanon::new(&labels);
    assert_eq!(t.display(&self_recursive), t.display(&mutual[0]));
    assert_eq!(canon.render(&t, self_recursive), canon.render(&t, mutual[0]));
}

#[test]
fn regular_components_follow_closure_captures() {
    let mut t = Types::new();
    let int = t.int();
    let self_recursive = t.intern_regular_component(1, |nodes| vec![recursive_capture_body(nodes[0], int)])[0];
    let inventory = t.identity_inventory();

    let mutual = t.intern_regular_component(2, |nodes| {
        vec![
            recursive_capture_body(nodes[1], int),
            recursive_capture_body(nodes[0], int),
        ]
    });

    assert_eq!(mutual, vec![self_recursive, self_recursive]);
    assert_eq!(t.identity_inventory(), inventory);
}

#[test]
fn regular_components_normalize_anonymous_closure_surfaces() {
    let mut t = Types::new();
    let int = t.int();
    let float = t.float();
    let int_surface = t.intern_regular_component(1, |nodes| vec![recursive_capture_body(nodes[0], int)])[0];
    let inventory = t.identity_inventory();

    let float_surface = t.intern_regular_component(1, |nodes| vec![recursive_capture_body(nodes[0], float)])[0];

    assert_eq!(float_surface, int_surface);
    assert_eq!(t.identity_inventory(), inventory);
}

#[test]
fn regular_components_absorb_a_recursive_tuple_clause() {
    let mut t = Types::new();
    let any = t.any();
    let direct = t.tuple(&[any]);
    let inventory = t.identity_inventory();

    let component = t.intern_regular_component(1, |nodes| {
        let mut body = DescrOf::unbranded();
        body.tuples = vec![
            Conj::pos_of(TupleSigOf { elems: vec![nodes[0]] }),
            Conj::pos_of(TupleSigOf {
                elems: vec![ComponentRef::Published(any)],
            }),
        ];
        vec![body]
    })[0];

    assert_eq!(component, direct);
    assert_eq!(t.identity_inventory(), inventory);
}

#[test]
fn regular_components_fuse_tuple_carvings_through_a_recursive_coordinate() {
    let mut t = Types::new();
    let int = t.int();
    let float = t.float();
    let numeric = t.union(int, float);
    let fused = t.intern_regular_component(1, |nodes| {
        let mut body = DescrOf::atom_lit("start");
        body.tuples = vec![Conj::pos_of(TupleSigOf {
            elems: vec![nodes[0], ComponentRef::Published(numeric)],
        })];
        vec![body]
    })[0];
    let inventory = t.identity_inventory();

    let carved = t.intern_regular_component(1, |nodes| {
        let mut body = DescrOf::atom_lit("start");
        body.tuples = vec![
            Conj::pos_of(TupleSigOf {
                elems: vec![nodes[0], ComponentRef::Published(int)],
            }),
            Conj::pos_of(TupleSigOf {
                elems: vec![nodes[0], ComponentRef::Published(float)],
            }),
        ];
        vec![body]
    })[0];

    assert_eq!(carved, fused);
    assert_eq!(t.identity_inventory(), inventory);
}

#[test]
fn regular_components_widen_tuple_carvings_through_a_recursive_coordinate() {
    let mut t = Types::new();
    let int = t.int();
    let ints = t.list(int);
    let empty = t.empty_list();
    let non_empty = t.non_empty_list(int);
    let wide = t.intern_regular_component(1, |nodes| {
        let mut body = DescrOf::atom_lit("start");
        body.tuples = vec![
            Conj::pos_of(TupleSigOf {
                elems: vec![nodes[0], ComponentRef::Published(ints), ComponentRef::Published(empty)],
            }),
            Conj::pos_of(TupleSigOf {
                elems: vec![nodes[0], ComponentRef::Published(empty), ComponentRef::Published(ints)],
            }),
        ];
        vec![body]
    })[0];
    let inventory = t.identity_inventory();

    let narrow = t.intern_regular_component(1, |nodes| {
        let mut body = DescrOf::atom_lit("start");
        body.tuples = vec![
            Conj::pos_of(TupleSigOf {
                elems: vec![nodes[0], ComponentRef::Published(ints), ComponentRef::Published(empty)],
            }),
            Conj::pos_of(TupleSigOf {
                elems: vec![
                    nodes[0],
                    ComponentRef::Published(empty),
                    ComponentRef::Published(non_empty),
                ],
            }),
        ];
        vec![body]
    })[0];

    assert_eq!(narrow, wide);
    assert_eq!(t.identity_inventory(), inventory);
}

#[test]
fn regular_components_keep_distinct_published_children() {
    let mut t = Types::new();
    let self_recursive = t.intern_regular_component(1, |nodes| vec![recursive_tuple_body(nodes[0])])[0];
    let int = t.int();

    let with_int = t.intern_regular_component(1, |nodes| {
        vec![DescrOf::tuple_of(vec![ComponentRef::Published(int), nodes[0]])]
    })[0];

    assert_ne!(self_recursive, with_int);
}

#[test]
fn regular_components_normalize_empty_list_alternatives() {
    let mut t = Types::new();
    let direct = t.intern_regular_component(1, |nodes| vec![DescrOf::list_of(nodes[0])])[0];
    let inventory = t.identity_inventory();

    let split = t.intern_regular_component(1, |nodes| {
        let mut body = DescrOf::unbranded();
        body.lists = vec![
            Conj::pos_of(ListSigOf::empty()),
            Conj::pos_of(ListSigOf::non_empty(nodes[0])),
        ];
        vec![body]
    })[0];

    assert_eq!(split, direct);
    assert_eq!(t.identity_inventory(), inventory);
}

#[test]
fn regular_components_ignore_declaration_order() {
    let mut t = Types::new();
    let forward = t.intern_regular_component(2, |nodes| {
        vec![
            recursive_tuple_body_named("left", nodes[1]),
            recursive_tuple_body_named("right", nodes[0]),
        ]
    });
    let inventory = t.identity_inventory();

    let reverse = t.intern_regular_component(2, |nodes| {
        vec![
            recursive_tuple_body_named("right", nodes[1]),
            recursive_tuple_body_named("left", nodes[0]),
        ]
    });

    assert_eq!(reverse, vec![forward[1], forward[0]]);
    assert_eq!(t.identity_inventory(), inventory);
}

#[test]
fn regular_components_ignore_declaration_order_after_refinement() {
    let mut t = Types::new();
    let variable = t.type_var(TypeVarId(91));
    let forward = t.intern_regular_component(2, |nodes| {
        vec![
            DescrOf::tuple_of(vec![nodes[1]]),
            DescrOf::tuple_of(vec![nodes[0], ComponentRef::Published(variable)]),
        ]
    });
    let inventory = t.identity_inventory();

    let reverse = t.intern_regular_component(2, |nodes| {
        vec![
            DescrOf::tuple_of(vec![nodes[1], ComponentRef::Published(variable)]),
            DescrOf::tuple_of(vec![nodes[0]]),
        ]
    });

    assert_eq!(reverse, vec![forward[1], forward[0]]);
    assert_eq!(t.identity_inventory(), inventory);
}

#[test]
fn regular_components_normalize_one_coordinate_tuple_difference() {
    let mut t = Types::new();
    let int = t.int();
    let float = t.float();
    let direct = t.intern_regular_component(1, |nodes| {
        vec![DescrOf::tuple_of(vec![nodes[0], ComponentRef::Published(int)])]
    })[0];
    let inventory = t.identity_inventory();

    let carved = t.intern_regular_component(1, |nodes| {
        let positive = TupleSigOf {
            elems: vec![nodes[0], ComponentRef::Published(int)],
        };
        let negative = TupleSigOf {
            elems: vec![nodes[0], ComponentRef::Published(float)],
        };
        let mut body = DescrOf::unbranded();
        body.tuples = vec![Conj {
            pos: vec![positive],
            neg: vec![negative],
        }];
        vec![body]
    })[0];

    assert_eq!(carved, direct);
    assert_eq!(t.identity_inventory(), inventory);
}

#[test]
fn cyclic_readers_collect_the_finite_variable_and_substitution_result() {
    let mut t = Types::new();
    let alpha = TypeVarId(97);
    let variable = t.type_var(alpha);
    let int = t.int();
    let self_recursive = t.intern_regular_component(1, |nodes| vec![DescrOf::tuple_of(vec![nodes[0]])])[0];
    let pattern = t.intern_regular_component(2, |nodes| {
        vec![
            DescrOf::tuple_of(vec![nodes[1]]),
            DescrOf::tuple_of(vec![nodes[0], ComponentRef::Published(variable)]),
        ]
    })[0];
    let witness = t.intern_regular_component(2, |nodes| {
        vec![
            DescrOf::tuple_of(vec![nodes[1]]),
            DescrOf::tuple_of(vec![nodes[0], ComponentRef::Published(int)]),
        ]
    })[0];

    assert!(!t.has_vars(&self_recursive));
    assert!(t.has_vars(&pattern));
    assert_eq!(t.free_var_ids(&pattern), [alpha].into_iter().collect());

    let mut sigma = Sigma::new();
    t.collect_instantiation_subst(&pattern, &witness, &mut sigma);
    assert_eq!(sigma, Sigma::from([(alpha, int)]));
}

#[test]
fn types_emptiness_discharges_a_negation_bearing_cycle() {
    let mut t = Types::new();
    let recursive = t.intern_regular_component(1, |nodes| {
        let sig = TupleSigOf { elems: vec![nodes[0]] };
        let mut descr = DescrOf::<ComponentRef>::unbranded();
        descr.tuples.push(Conj {
            pos: vec![sig.clone()],
            neg: vec![sig],
        });
        vec![descr]
    })[0];

    assert!(t.descr(&recursive).is_empty(t.ctx()));
}

fn regular_test_tys(t: &mut Types) -> Vec<Ty> {
    let first_self = t.intern_regular_component(1, |nodes| vec![DescrOf::tuple_of(vec![nodes[0]])])[0];
    let second_self = t.intern_regular_component(1, |nodes| vec![DescrOf::tuple_of(vec![nodes[0]])])[0];
    let mut nodes = vec![t.any(), t.int(), first_self, second_self];
    for graph in 0..27 {
        let children = [graph % 3, graph / 3 % 3, graph / 9];
        if !matches!(children, [1, 2, 0] | [2, 0, 1]) {
            continue;
        }
        nodes.extend(t.intern_regular_component(3, |component| {
            children
                .into_iter()
                .map(|child| DescrOf::tuple_of(vec![component[child]]))
                .collect()
        }));
    }
    nodes
}

#[test]
fn types_order_equals_identity_on_regular_trees() {
    let mut t = Types::new();
    let nodes = regular_test_tys(&mut t);

    for &left in &nodes {
        for &right in &nodes {
            let forward = t.cmp_ty(left, right);
            assert_eq!(
                forward == std::cmp::Ordering::Equal,
                left == right,
                "{left:?} and {right:?}"
            );
        }
    }
}

#[test]
fn types_order_is_total_on_cyclic_nodes() {
    let mut t = Types::new();
    let nodes = regular_test_tys(&mut t);

    for &left in &nodes {
        for &right in &nodes {
            assert_eq!(
                t.cmp_ty(left, right),
                t.cmp_ty(right, left).reverse(),
                "{left:?} and {right:?}"
            );
        }
    }

    for &left in &nodes {
        for &middle in &nodes {
            for &right in &nodes {
                let left_middle = t.cmp_ty(left, middle);
                let middle_right = t.cmp_ty(middle, right);
                let left_right = t.cmp_ty(left, right);
                assert!(
                    !(left_middle.is_le() && middle_right.is_le() && left_right.is_gt()),
                    "{left:?} <= {middle:?} <= {right:?}, but {left:?} > {right:?}",
                );
            }
        }
    }
}

#[test]
fn literal_callable_identity_ignores_an_instantiated_surface() {
    let mut t = Types::new();
    let literal = t.fn_ref_lit(ClosureTarget(3), 1);
    let int = t.int();
    let nil = t.nil();
    let target = ClosureTarget(3).into();
    let sigma = [(closure_var_id(target, 0), int), (closure_ret_var_id(target), nil)]
        .into_iter()
        .collect();
    let inventory = t.identity_inventory();
    let comparisons = t.comparison_cache_stats();

    let instantiated = t.instantiate(&literal, &sigma);

    assert_eq!(instantiated, literal);
    assert_eq!(t.identity_inventory(), inventory);
    assert_eq!(t.comparison_cache_stats(), comparisons);
}

fn assert_reuses_identity(types: &mut Types, expected: Ty, construction: impl FnOnce(&mut Types) -> Ty) {
    let inventory = types.identity_inventory();
    assert_eq!(construction(types), expected);
    assert_eq!(types.identity_inventory(), inventory);
}

#[test]
fn construction_order_reuses_identity_for_lists_tuples_and_literals() {
    let mut t = Types::new();
    let int = t.int();
    let empty = t.empty_list();
    let list = t.list(int);
    let joined = t.union(empty, list);
    assert_reuses_identity(&mut t, joined, |t| t.union(list, empty));

    let false_ = t.bool_lit(false);
    let true_ = t.bool_lit(true);
    let left = t.tuple(&[list, false_]);
    let right = t.tuple(&[list, true_]);
    let carved = t.union(left, right);
    let either = t.union(false_, true_);
    assert_reuses_identity(&mut t, carved, |t| t.tuple(&[list, either]));

    let any = t.any();
    let fun = t.arrow(&[], any);
    assert_reuses_identity(&mut t, fun, |t| t.arrow(&[int], any));

    let branded = t.closure_lit(ClosureTarget(3), vec![int], 1);
    let anonymous = t.erase_closure_identity(&branded);
    let merged = t.intersect(branded, anonymous);
    assert_reuses_identity(&mut t, merged, |t| t.intersect(anonymous, branded));
}

#[test]
fn structural_children_are_interned_handles() {
    let mut t = Types::new();
    let elem = t.int();
    let tuple = t.tuple(&[elem]);
    let d = t.descr(&tuple);
    assert_eq!(d.tuples[0].pos[0].elems, vec![elem]);
}

// fz-hwn.27.5 — the backend-boundary value-template predicate.
//
// `is_value_template` is the calculator's authority on "can this position hold a
// runtime value?" An activation whose input is a value template cannot become a
// backend executable: the bare-variable value has no representation and
// materializes as `Absent`, panicking on use (the fz-hwn.23 phantom).
//
// These pins establish that the cheap SYNTACTIC predicate — bare var, or tuple
// with a bare-var field — is exactly the materializability boundary, so the
// semantic `mvar` groundness (Castagna; a var is meaningful iff `t[0/α] ≠ t`) is
// NOT needed. The reason: the only types whose runtime representation depends on
// an inner variable being ground are the two the predicate catches. Everything
// else has a representation independent of its inner vars — `list(α)` is a
// pointer, `(α)->α` is one word (fz-hwn.27.12) — so those inner vars are
// representation-irrelevant, exactly as `mvar` would conclude, but decided
// syntactically without an emptiness probe.
#[test]
fn value_template_predicate_flags_unrepresentable_positions_only() {
    let mut t = Types::new();
    let a = t.type_var(TypeVarId(0));
    let b = t.type_var(TypeVarId(1));
    let int = t.int();

    // A bare variable IS the whole value: no representation → template.
    assert!(t.is_value_template(&a), "a bare variable has no runtime representation");

    // A tuple with a bare-variable field cannot be laid out → template.
    let tuple_with_var = t.tuple(&[a, int]);
    assert!(
        t.is_value_template(&tuple_with_var),
        "a tuple with a bare-variable field cannot be laid out",
    );

    // Representable values — inner vars are representation-irrelevant (this is the
    // mvar boundary, decided syntactically). These must NOT be templates, or
    // genuine polymorphic values (lists, callables) would be wrongly pruned.
    let list_of_var = t.list(a); // a list is a pointer regardless of element type
    assert!(!t.is_value_template(&list_of_var), "list(α) is a representable pointer");

    let poly_callable = t.arrow(&[a], a); // (α)->α is one word — fz-hwn.27.12
    assert!(!t.is_value_template(&poly_callable), "(α)->α is one representable word");

    let tuple_of_representable = t.tuple(&[list_of_var, int]);
    assert!(
        !t.is_value_template(&tuple_of_representable),
        "a tuple of representable fields is representable",
    );

    // Ground values are never templates.
    assert!(!t.is_value_template(&int), "a ground scalar is representable");
    let ground_tuple = t.tuple(&[int, int]);
    assert!(!t.is_value_template(&ground_tuple), "a ground tuple is representable");

    // `key_is_value_template` lifts the predicate to an activation's input vector:
    // a key is unrepresentable iff ANY input position is a template. This is the
    // shape of the real fz-hwn.23 phantom — distinct bare-var inputs `(a0, a1)`.
    assert!(
        t.key_is_value_template(&[a, b]),
        "an activation with bare-variable inputs is the fz-hwn.23 phantom",
    );
    assert!(
        !t.key_is_value_template(&[list_of_var, int]),
        "an activation of representable inputs is a real backend executable",
    );
}

#[test]
fn repeated_subtype_comparisons_are_memoized_by_type_id() {
    let mut t = Types::new();
    let int = t.atom();
    let lit = t.atom_lit("ok");

    let before = t.comparison_cache_stats();
    assert!(t.is_subtype(&lit, &int));
    let after_first = t.comparison_cache_stats();
    assert_eq!(
        after_first.misses,
        before.misses + 1,
        "the first subtype comparison should compute and cache the answer"
    );
    assert_eq!(after_first.hits, before.hits);

    assert!(t.is_subtype(&lit, &int));
    let after_second = t.comparison_cache_stats();
    assert_eq!(
        after_second.misses, after_first.misses,
        "repeating the same id comparison should not rewalk structure"
    );
    assert_eq!(
        after_second.hits,
        after_first.hits + 1,
        "repeating the same id comparison should hit the cache"
    );
    assert_eq!(
        after_second.entries, after_first.entries,
        "a cache hit should not add another entry"
    );
}

#[test]
fn runtime_type_predicate_projects_integer_kind() {
    // Numbers are presence bits: the predicate is a kind check, never a
    // value-membership set, from this pipeline. Constants are compared as
    // values by the matcher.
    let mut t = Types::new();
    let forty_two = t.int_lit(42);
    let predicate = t.runtime_type_predicate(&forty_two);
    assert_eq!(
        predicate,
        RuntimeTypePredicate {
            ints: FiniteSet::any(),
            ..RuntimeTypePredicate::none()
        }
    );
}

/// Both structural axes project their contents: a tuple's positions, and a
/// list's HEAD.
///
/// Both used to erase them. `{:cont, int}` and `{:halt, int}` were one "a
/// 2-tuple" question until fz-kdt.119 gave the tuple axis one sub-predicate
/// per position per clause; `[int]` and `[:ok]` were one "a non-empty list"
/// question until fz-kdt.107 step 3 gave the list axis one head question per
/// cons-admitting clause. In both cases the coarse reading the other callers
/// want -- arities, shapes -- is still answerable beside the fine one.
///
/// The list half is a ONE-SIDED FILTER and this states both sides of it:
/// `[:false | :true]` against `[int]` is a real separation, because a head
/// outside the question proves the whole homogeneous list outside the surface;
/// `[int]` against `[int | :ok]` is NOT, because a head inside it says nothing
/// about the tail no test reads.
#[test]
fn runtime_type_predicate_projects_tuple_positions_and_list_heads() {
    let mut t = Types::new();
    let empty_list_ty = t.empty_list();
    let empty_list = t.runtime_type_predicate(&empty_list_ty);
    assert_eq!(
        empty_list,
        RuntimeTypePredicate {
            lists: ListShapes::exact(FiniteSet::lit(ListShape::Empty), Vec::new()),
            ..RuntimeTypePredicate::none()
        },
        "[] admits no cons cell, so it puts no head question",
    );

    let int = t.int();
    let atom = t.atom();
    let int_list = t.list(int);
    let atom_list = t.list(atom);
    assert_ne!(
        t.runtime_type_predicate(&int_list),
        t.runtime_type_predicate(&atom_list),
        "a list test reads the first element, so list(int) and list(atom) are two questions",
    );

    let false_atom = t.atom_lit("false");
    let true_atom = t.atom_lit("true");
    let ok_atom = t.atom_lit("ok");
    let bools = t.union(false_atom, true_atom);
    let bool_list = t.list(bools);
    let bools_ask = t.runtime_type_predicate(&bool_list);
    let ints_ask = t.runtime_type_predicate(&int_list);
    assert!(
        !bools_ask.overlaps_on_an_erasing_axis(&ints_ask),
        "[:false | :true] and [int] have DISJOINT heads, and disjoint heads are the one \
         separation a head load can claim",
    );

    assert!(
        ints_ask.lists.is_exact() && ints_ask.lists.heads().len() == 1,
        "one head question per cons-admitting clause, which is what keeps the clauses correlated",
    );

    let ints_oks = t.union(int, ok_atom);
    let mixed_list = t.list(ints_oks);
    let mixed_ask = t.runtime_type_predicate(&mixed_list);
    assert!(
        ints_ask.overlaps_on_an_erasing_axis(&mixed_ask),
        "[int] and [int | :ok] OVERLAP at the head and differ only in a tail no test reads, \
         so a seat may not claim separation there -- claiming it seats [int] first and hands \
         [1, :ok] to a body that reads every element as an int",
    );
    assert!(
        ints_ask.contained_in(&mixed_ask) && !mixed_ask.contained_in(&ints_ask),
        "and the narrower head is still the narrower test",
    );

    let tuple_ty = t.tuple(&[int, atom]);
    let tuple = t.runtime_type_predicate(&tuple_ty);
    assert_eq!(*tuple.tuples.arities(), FiniteSet::lit(2));
    assert!(tuple.tuples.is_exact());
    assert_eq!(
        tuple.tuples.shapes(),
        [vec![t.runtime_type_predicate(&int), t.runtime_type_predicate(&atom)]],
        "each position carries its own question",
    );

    let cont = t.atom_lit("cont");
    let halt = t.atom_lit("halt");
    let binary = t.str_t();
    let cont_int = t.tuple(&[cont, int]);
    let halt_binary = t.tuple(&[halt, binary]);
    let either = t.union(cont_int, halt_binary);
    let either_predicate = t.runtime_type_predicate(&either);
    assert_eq!(
        either_predicate.tuples.shapes().len(),
        2,
        "arms that differ in their PAYLOAD as well as their tag stay two shapes: joining them \
         position-wise would admit {{:cont, binary}}, which neither arm holds",
    );
    assert!(
        !t.runtime_type_predicate(&cont_int)
            .overlaps(&t.runtime_type_predicate(&halt_binary)),
        "and the tags separate, which is the whole point",
    );
}

#[test]
fn runtime_type_predicate_projects_named_structs_and_widens_unknown_opaques() {
    let mut t = Types::new();
    let named_ty = t.nominal_protocol_target(module_name("box"));
    let named = t.runtime_type_predicate(&named_ty);
    assert_eq!(
        named,
        RuntimeTypePredicate {
            named_structs: FiniteSet::lit(module_name("box")),
            ..RuntimeTypePredicate::none()
        }
    );

    let mystery = t.opaque_of("mystery");
    let widened = t.runtime_type_predicate(&mystery);
    assert_eq!(widened.named_structs, FiniteSet::none());
    assert!(!widened.allow_other_structs);
    let mut every_non_struct = RuntimeTypePredicate::any();
    every_non_struct.named_structs = FiniteSet::none();
    every_non_struct.allow_other_structs = false;
    assert_eq!(widened, every_non_struct);
}

#[test]
fn runtime_type_predicate_preserves_typed_struct_exclusions_without_narrowing_generic_opaques() {
    use crate::compiler2::identity::ModuleId;

    let mut t = Types::new();
    let int = t.int();
    let foo = t.struct_map(
        ModuleId::GLOBAL,
        module_name("Pkg.Foo"),
        &[(MapKey::Atom("value".to_string()), int)],
    );
    let foo_envelope = t.runtime_type_test_envelope(foo);
    let any = t.any();
    let not_foo = t.difference(any, foo_envelope);
    assert_eq!(
        t.runtime_type_predicate(&not_foo).named_structs,
        FiniteSet::cofinite([module_name("Pkg.Foo")]),
        "a negative struct predicate must retain the exact typed schema exclusion"
    );
    assert_eq!(
        t.struct_modules([not_foo]),
        [ModuleId::GLOBAL].into_iter().collect(),
        "schema extraction must retain the named exclusion as an exact dependency"
    );

    let generic_opaque_complement = t.intern(Descr {
        opaques: FiniteSet::cofinite([OpaqueTag::Named("known".to_string())]),
        ..Descr::unbranded()
    });
    let generic = t.runtime_type_predicate(&generic_opaque_complement);
    let mut every_non_struct = RuntimeTypePredicate::any();
    every_non_struct.named_structs = FiniteSet::none();
    every_non_struct.allow_other_structs = false;
    assert_eq!(
        generic, every_non_struct,
        "a generic opaque widens every unrepresentable non-struct kind without overriding typed struct identity"
    );
}

#[test]
fn runtime_type_predicate_preserves_plain_maps_in_real_struct_complements_and_unions() {
    let mut world = crate::compiler2::World::new();
    let foo = world.reference_module(module_name("Pkg.Foo"));
    let int = world.types_mut().int();
    let foo_value = world.struct_value_ty(foo, &["value".to_string()], &[int]);
    let foo_envelope = world.types_mut().runtime_type_test_envelope(foo_value);
    let any = world.types_mut().any();
    let not_foo = world.types_mut().difference(any, foo_envelope);
    let not_foo_predicate = world.types().runtime_type_predicate(&not_foo);
    assert!(
        not_foo_predicate.maps,
        "the complement of a struct still admits every plain map"
    );
    assert_eq!(
        not_foo_predicate.named_structs,
        FiniteSet::cofinite([module_name("Pkg.Foo")]),
        "subtracting the observable struct envelope rejects Foo and admits every other struct"
    );

    let raw_not_foo = world.types_mut().difference(any, foo_value);
    assert_eq!(
        world.types().runtime_type_predicate(&raw_not_foo).named_structs,
        FiniteSet::any(),
        "a shaped subtraction cannot reject the whole Foo family before runtime enveloping"
    );

    let shaped_map = world.types_mut().map(&[(MapKey::Atom("value".to_string()), int)]);
    let not_shaped_map = world.types_mut().difference(any, shaped_map);
    assert!(
        world.types().runtime_type_predicate(&not_shaped_map).maps,
        "subtracting one shaped plain-map region still admits other plain maps"
    );

    let map = world.types_mut().map_top();
    let foo_or_map = world.types_mut().union(foo_value, map);
    let foo_or_map_predicate = world.types().runtime_type_predicate(&foo_or_map);
    assert!(
        foo_or_map_predicate.maps,
        "an explicit struct-or-map union admits plain maps"
    );
    assert_eq!(
        foo_or_map_predicate.named_structs,
        FiniteSet::lit(module_name("Pkg.Foo"))
    );
    assert!(
        !world.types().runtime_type_predicate(&foo_value).maps,
        "a struct's tagged record must not classify as a plain map"
    );
}

#[test]
fn typed_struct_identity_survives_the_type_algebra_even_when_display_names_match() {
    use super::sigs::StructTag;
    use crate::compiler2::identity::ModuleId;

    let mut t = Types::new();
    let left_module = ModuleId::for_test(1);
    let right_module = ModuleId::for_test(2);
    let left_name = ModuleName::from_segments(vec!["Pkg.Same".into()]);
    let right_name = ModuleName::from_segments(vec!["Pkg".into(), "Same".into()]);
    assert_eq!(left_name.dotted(), right_name.dotted());
    let left = t.struct_map(left_module, left_name.clone(), &[]);
    let right = t.struct_map(right_module, right_name.clone(), &[]);
    assert_ne!(
        left, right,
        "distinct source paths must intern as distinct struct types"
    );
    assert!(t.is_disjoint(&left, &right));
    let meet = t.intersect(left, right);
    assert!(t.is_empty(&meet));
    let union = t.union(left, right);
    assert_eq!(
        t.struct_modules([union]),
        [left_module, right_module].into_iter().collect(),
        "union and recursive schema extraction must preserve both typed identities"
    );
    let difference = t.difference(left, right);
    assert!(t.is_equivalent(&difference, &left));
    assert!(
        !t.runtime_type_predicate(&left)
            .overlaps(&t.runtime_type_predicate(&right))
    );
    assert_eq!(
        t.runtime_type_predicate(&left).named_structs,
        FiniteSet::lit(left_name.clone())
    );
    assert_eq!(
        t.runtime_type_predicate(&right).named_structs,
        FiniteSet::lit(right_name)
    );

    assert_eq!(
        StructTag {
            module: left_module,
            name: left_name.clone(),
        },
        StructTag {
            module: right_module,
            name: left_name,
        },
        "World-local interner coordinates do not define source identity"
    );
}

#[test]
fn nominal_protocol_targets_keep_typed_identity_through_the_opaque_algebra() {
    let mut t = Types::new();
    let left_name = ModuleName::from_segments(vec!["A.B".into()]);
    let right_name = ModuleName::from_segments(vec!["A".into(), "B".into()]);
    assert_eq!(left_name.dotted(), right_name.dotted());
    let left = t.nominal_protocol_target(left_name.clone());
    let right = t.nominal_protocol_target(right_name.clone());
    let ordinary = t.opaque_of("protocol-target(A.B)");
    assert!(t.is_disjoint(&left, &right));
    assert!(
        t.is_disjoint(&left, &ordinary),
        "ordinary opaque spelling cannot manufacture a protocol target"
    );
    let union = t.union(left, right);
    let remaining = t.difference(union, right);
    assert!(t.is_equivalent(&remaining, &left));
    assert_eq!(
        t.runtime_type_predicate(&union).named_structs,
        FiniteSet::finite([left_name, right_name])
    );
    assert!(
        !t.runtime_type_predicate(&left).maps,
        "nominal targets remain in the opaque axis"
    );
}

#[test]
fn runtime_type_predicate_keeps_named_struct_identity_out_of_plain_map_kind() {
    use crate::compiler2::identity::ModuleId;

    let mut t = Types::new();
    let first = t.atom_lit("first");
    let last = t.atom_lit("last");
    let step = t.atom_lit("step");
    let range_value = t.struct_map(
        ModuleId::GLOBAL,
        module_name("Range"),
        &[
            (MapKey::Atom("first".to_string()), first),
            (MapKey::Atom("last".to_string()), last),
            (MapKey::Atom("step".to_string()), step),
        ],
    );
    let range_predicate = t.runtime_type_predicate(&range_value);
    let map_top = t.map_top();
    let map_predicate = t.runtime_type_predicate(&map_top);

    assert_eq!(
        range_predicate.named_structs,
        FiniteSet::lit(module_name("Range")),
        "a struct value should keep its named runtime identity even though it also has structural field evidence",
    );
    assert!(
        !range_predicate.maps,
        "a tagged map is one nominal record leaf, not a union with a plain structural map",
    );
    assert!(
        !range_predicate.overlaps(&map_predicate),
        "protocol matching must not select the Map implementation for a Range struct value",
    );
}

#[test]
fn tagged_map_identity_and_fields_remain_atomic_through_the_algebra() {
    use crate::compiler2::identity::ModuleId;

    let mut t = Types::new();
    let int = t.int();
    let key = MapKey::Atom("value".to_string());
    let foo = t.struct_map(ModuleId::for_test(1), module_name("Pkg.Foo"), &[(key.clone(), int)]);
    let plain = t.map(&[(key.clone(), int)]);
    let joined = t.union(foo, plain);

    assert!(t.is_disjoint(&foo, &plain));
    let meet = t.intersect(foo, plain);
    assert!(t.is_empty(&meet));
    let without_plain = t.difference(joined, plain);
    assert!(t.is_equivalent(&without_plain, &foo));
    assert_eq!(t.map_field_lookup(&foo, &key), Some(int));
    let extra = MapKey::Atom("extra".to_string());
    let refined = t.refine_map_field(&foo, &extra, &int);
    assert_eq!(t.map_field_lookup(&refined, &extra), Some(int));
    assert_eq!(
        t.runtime_type_predicate(&refined).named_structs,
        FiniteSet::lit(module_name("Pkg.Foo")),
        "field refinement must preserve the record's nominal tag"
    );
    assert_eq!(
        t.struct_modules([refined]),
        [ModuleId::for_test(1)].into_iter().collect(),
        "schema extraction must read the same tag that field projection preserves"
    );
    assert_eq!(
        t.max_tuple_arity(&foo),
        0,
        "tuple storage is a derived runtime view, not a type summand"
    );

    let map_top = t.map_top();
    assert!(t.is_subtype(&plain, &map_top));
    assert!(
        t.is_disjoint(&foo, &map_top),
        "plain-map top excludes every tagged struct family"
    );
    let any = t.any();
    let non_plain = t.difference(any, map_top);
    assert!(t.is_disjoint(&non_plain, &map_top));
    assert!(
        t.is_subtype(&foo, &non_plain),
        "record-axis top still ranges over every tagged struct family"
    );
}

#[test]
fn semantic_struct_envelopes_keep_projectable_fields_and_predicate_envelopes_keep_only_identity() {
    use crate::compiler2::identity::ModuleId;

    let mut t = Types::new();
    let key = MapKey::Atom("value".to_string());
    let hit = t.atom_lit("hit");
    let var = t.type_var(TypeVarId(555));
    let fields = t.tuple(&[hit, var]);
    let record = t.struct_map(ModuleId::for_test(1), module_name("Pkg.Box"), &[(key.clone(), fields)]);
    let nested = t.tuple(&[record]);
    let semantic = t.runtime_envelope(nested);
    let semantic_record = t.tuple_field_type(&semantic, 0);
    let semantic_fields = t.map_field_lookup(&semantic_record, &key).unwrap();
    assert_eq!(t.tuple_field_type(&semantic_fields, 0), hit);
    let any = t.any();
    assert_eq!(
        t.tuple_field_type(&semantic_fields, 1),
        any,
        "unknown field evidence widens at its own position, without erasing concrete sibling fields"
    );
    let predicate = t.runtime_type_test_envelope(nested);
    let predicate_record = t.tuple_field_type(&predicate, 0);
    assert_eq!(t.map_field_lookup(&predicate_record, &key), Some(any));
    assert_eq!(
        t.runtime_type_predicate(&semantic),
        t.runtime_type_predicate(&predicate),
        "retaining semantic projection evidence does not teach the runtime type predicate a field test"
    );
    let raw_not_record = t.difference(any, record);
    let negative_semantic = t.runtime_envelope(raw_not_record);
    assert!(
        t.is_subtype(&raw_not_record, &negative_semantic),
        "unresolved negative field evidence must not exclude additional values"
    );
    let concrete = t.struct_map(ModuleId::for_test(1), module_name("Pkg.Box"), &[(key, hit)]);
    let not_concrete = t.difference(any, concrete);
    let semantic_not_concrete = t.runtime_envelope(not_concrete);
    assert!(t.is_equivalent(&not_concrete, &semantic_not_concrete));
    let negative_predicate = t.runtime_type_test_envelope(raw_not_record);
    assert!(
        t.is_subtype(&raw_not_record, &negative_predicate),
        "a field-blind predicate must retain the untestable residue of a shaped negative struct"
    );
}

#[test]
fn substitution_descends_only_through_equal_record_tags() {
    use crate::compiler2::identity::ModuleId;

    let mut t = Types::new();
    let key = MapKey::Atom("value".to_string());
    let alpha = t.type_var(TypeVarId(0));
    let int = t.int();
    let foo_pattern = t.struct_map(ModuleId::for_test(1), module_name("Pkg.Foo"), &[(key.clone(), alpha)]);
    let foo_witness = t.struct_map(ModuleId::for_test(1), module_name("Pkg.Foo"), &[(key.clone(), int)]);
    let other_witness = t.struct_map(ModuleId::for_test(2), module_name("Pkg.Bar"), &[(key, int)]);

    let mut sigma = HashMap::new();
    t.collect_instantiation_subst(&foo_pattern, &foo_witness, &mut sigma);
    assert_eq!(sigma.get(&TypeVarId(0)), Some(&int));
    let instantiated = t.instantiate(&foo_pattern, &sigma);
    assert!(t.is_equivalent(&instantiated, &foo_witness));

    let mut mismatched = HashMap::new();
    t.collect_instantiation_subst(&foo_pattern, &other_witness, &mut mismatched);
    assert!(
        mismatched.is_empty(),
        "different nominal records cannot bind each other's fields"
    );
}

/// A clause pins SEVERAL closure literals only when they name several BRANDS:
/// two literals that can name one value merge into one, intersecting their
/// captures. A value carries exactly one code brand, so the surviving clause
/// denotes nothing and interns as the bottom.
#[test]
fn a_clause_pinning_two_closure_brands_is_the_bottom() {
    let mut t = Types::new();
    let int = t.int();
    let float = t.float();
    let none = t.none();
    let over_int = t.closure_lit(ClosureTarget(66), vec![int], 1);
    let over_float = t.closure_lit(ClosureTarget(68), vec![float], 1);
    assert_eq!(
        t.intersect(over_int, over_float),
        none,
        "no value is both closure 66 and closure 68"
    );

    let any = t.any();
    let wider = t.closure_lit(ClosureTarget(66), vec![any], 1);
    let merged = t.intersect(over_int, wider);
    let clauses = t.descr(&merged).funcs.clone();
    assert_eq!(clauses.len(), 1);
    assert_eq!(
        clauses[0].pos.iter().filter(|sig| sig.lit.is_some()).count(),
        1,
        "one brand, one literal, whatever the two capture layouts said"
    );
    assert!(
        t.runtime_type_predicate(&merged).callables.is_exact(),
        "the runtime predicate receives only the surviving one-literal clause; a target-only fallback would describe an uninterned state"
    );
}

/// The predicate projection and the envelope are two roads to the same axis --
/// the plan path goes through the envelope first and projects the result -- so
/// they must decide a clause the same way or a value fails to match its own
/// arm. `runtime_type_predicate_callables` is the one place that decides;
/// `callable_identity_clauses` keeps the clause shape it decides on.
#[test]
fn the_envelope_and_the_predicate_agree_on_a_callable_clause() {
    let mut t = Types::new();
    let int = t.int();
    let surface = t.arrow(&[int], int);
    let literal = t.closure_lit(ClosureTarget(66), vec![int], 1);
    let both = t.intersect(literal, surface);

    let direct = t.runtime_type_predicate(&both).callables;
    let enveloped = t.runtime_type_test_envelope(both);
    let through_envelope = t.runtime_type_predicate(&enveloped).callables;
    assert_eq!(
        direct, through_envelope,
        "projecting a clause and projecting its envelope must reach the same callable axis",
    );
}

/// fz-kdt.127 -- WHY the erased forwarder key and the construction axis
/// compose, stated from the side that actually decides it: the KEYING rule.
///
/// `erase_transported_closure_identity_inputs` anonymises only the slots the
/// dispatch mask marks `Ignore` -- the ones no runtime test reads. A slot the
/// body dispatches on keeps its brand, so it stays shapeable and a test can
/// still name the construction, while the anonymous literal the erasure mints
/// lives only in the activation KEY, which no test is ever asked of. Nothing
/// in the projection has to arrange this; if it ever stops holding, the
/// `debug_assert!` in `callable_identity_literal` is what fires.
#[test]
fn the_forwarder_erasure_anonymises_only_the_slots_no_test_reads() {
    let mut t = Types::new();
    let int = t.int();
    let surface = t.arrow(&[int], int);
    let branded = t.closure_lit(ClosureTarget(3), vec![int], 1);
    let branded = t.intersect(branded, surface);
    let erased = t.erase_transported_closure_identity_inputs(
        &[branded, branded],
        &[DispatchDemand::Ignore, DispatchDemand::Whole],
    );
    let params = erased.as_ref();
    assert_eq!(params.len(), 2);
    assert_ne!(
        params[0], branded,
        "the ignored slot is freight: the erasure takes its brand"
    );
    assert!(
        t.display(&params[0]).contains("#?"),
        "and what it leaves there is the ANONYMOUS literal, got {}",
        t.display(&params[0])
    );
    assert_eq!(
        params[1], branded,
        "a slot the body dispatches on is untouched -- that is why an anonymous literal never \
         reaches a runtime test"
    );

    let capturing = CallableShape {
        target: ClosureTarget(3),
        captures: vec![t.runtime_type_predicate(&int)],
    };
    assert!(
        t.runtime_type_predicate(&params[1]).callables.admits(&capturing),
        "and the dispatch slot still names its construction",
    );
}

/// fz-kdt.127 -- a closure holds exactly one value per capture slot, so a
/// literal whose capture TYPE is empty denotes nothing at all.
///
/// The anonymous literal is one way to build one: it is every brand at once,
/// so it merges with a branded literal instead of staying distinct from it,
/// and the merged literal's capture is the two captures' intersection. Two
/// literals of the SAME brand at different capture types are the other way,
/// and that hole predates the anonymous literal. One law in
/// `func_clause_empty` closes both.
#[test]
fn a_closure_literal_with_an_empty_capture_is_empty() {
    let mut t = Types::new();
    let int = t.int();
    let float = t.float();
    let surface = t.arrow(&[int], int);
    let branded_int = t.closure_lit(ClosureTarget(3), vec![int], 1);
    let branded_int = t.intersect(branded_int, surface);
    let branded_float = t.closure_lit(ClosureTarget(4), vec![float], 1);
    let branded_float = t.intersect(branded_float, surface);
    let anon_int = t.erase_closure_identity(&branded_int);

    let meets_its_own_brand = t.intersect(anon_int, branded_int);
    assert_eq!(
        meets_its_own_brand, branded_int,
        "an anonymous literal is every brand at once, so meeting one leaves that one",
    );

    let meets_another_brand = t.intersect(anon_int, branded_float);
    assert!(
        t.is_empty(&meets_another_brand),
        "a closure over an int and a closure over a float are not one value: {}",
        t.display(&meets_another_brand)
    );

    let branded_int_at_float = t.closure_lit(ClosureTarget(3), vec![float], 1);
    let branded_int_at_float = t.intersect(branded_int_at_float, surface);
    let one_brand_two_captures = t.intersect(branded_int, branded_int_at_float);
    assert!(
        t.is_empty(&one_brand_two_captures),
        "and the same holds for ONE brand at two capture types -- the hole the anonymous \
         literal widened was already there: {}",
        t.display(&one_brand_two_captures)
    );
}

#[test]
fn symmetric_comparisons_share_one_cache_entry() {
    let mut t = Types::new();
    let int = t.int();
    let atom = t.atom();

    let before = t.comparison_cache_stats();
    assert!(t.is_disjoint(&int, &atom));
    let after_first = t.comparison_cache_stats();
    assert_eq!(after_first.misses, before.misses + 1);

    assert!(t.is_disjoint(&atom, &int));
    let after_second = t.comparison_cache_stats();
    assert_eq!(
        after_second.misses, after_first.misses,
        "the reversed disjointness query should reuse the symmetric comparison"
    );
    assert_eq!(after_second.hits, after_first.hits + 1);
}

#[test]
fn value_disjointness_reuses_the_symmetric_operand_pair() {
    let mut t = Types::new();
    let int = t.int();
    let atom = t.atom();

    let before = t.comparison_cache_stats();
    assert!(t.is_value_disjoint(&int, &atom));
    let after_first = t.comparison_cache_stats();
    assert_eq!(after_first.misses, before.misses + 1);

    assert!(t.is_value_disjoint(&atom, &int));
    let after_reverse = t.comparison_cache_stats();
    assert_eq!(after_reverse.misses, after_first.misses);
    assert_eq!(after_reverse.hits, after_first.hits + 1);
}

#[test]
fn comparison_cache_keys_predicates_and_order_by_operation() {
    let mut t = Types::new();
    let int = t.int();
    let atom = t.atom();

    let before = t.comparison_cache_stats();
    assert!(t.is_disjoint(&int, &atom));
    let after_predicate = t.comparison_cache_stats();
    assert_eq!(after_predicate.entries, before.entries + 1);

    let first_order = t.cmp_activation_ty(int, atom);
    let after_order = t.comparison_cache_stats();
    assert_eq!(
        after_order.entries,
        after_predicate.entries + 1,
        "the operation tag must give predicate and ordering results distinct slots in one cache",
    );
    assert_eq!(after_order.semantic_order_entries, before.semantic_order_entries + 1);

    assert_eq!(t.cmp_activation_ty(atom, int), first_order.reverse());
    let after_reverse = t.comparison_cache_stats();
    assert_eq!(after_reverse.entries, after_order.entries);
    assert_eq!(after_reverse.semantic_order_hits, after_order.semantic_order_hits + 1);
}

macro_rules! key_helper_conformance_tests {
    ($mod_name:ident, $ctor:expr) => {
        mod $mod_name {
            use super::*;

            #[test]
            fn key_var_count_counts_top_level_vars() {
                let mut t = $ctor;
                let alpha = t.type_var(TypeVarId(0));
                let beta = t.type_var(TypeVarId(1));
                let int_top = t.int();
                let mixed = t.union(int_top, beta);
                assert_eq!(t.key_var_count(&[alpha, mixed]), 2);
            }

            #[test]
            fn key_subsumes_with_binds_pure_vars() {
                let mut t = $ctor;
                let mut sigma = HashMap::new();
                let int = t.int();
                let alpha = t.type_var(TypeVarId(0));
                assert!(t.key_subsumes_with(&int, &alpha, &mut sigma));
                assert_eq!(sigma.get(&TypeVarId(0)), Some(&int));
            }

            #[test]
            fn key_list_subsumes_threads_one_substitution_across_positions() {
                let mut t = $ctor;
                let int = t.int();
                let atom = t.atom();
                let alpha = t.type_var(TypeVarId(0));
                let beta = t.type_var(TypeVarId(1));

                // Distinct template vars are instantiated by any ground pair.
                assert!(t.key_list_subsumes(&[int, atom], &[alpha, beta]));
                // A recurring template var binds once and must agree everywhere:
                // `[α, α]` is instantiated only when both positions match.
                assert!(t.key_list_subsumes(&[int, int], &[alpha, alpha]));
                assert!(
                    !t.key_list_subsumes(&[int, atom], &[alpha, alpha]),
                    "a recurring template var must not accept disagreeing positions",
                );
                // A ground template names one runtime shape — only itself instantiates it.
                assert!(t.key_list_subsumes(&[int, atom], &[int, atom]));
                assert!(!t.key_list_subsumes(&[atom, int], &[int, atom]));
                // Arity must match.
                assert!(!t.key_list_subsumes(&[int], &[alpha, beta]));
            }

            #[test]
            fn key_has_vars_distinguishes_ground_lists_from_templates() {
                let mut t = $ctor;
                let int = t.int();
                let atom = t.atom();
                let alpha = t.type_var(TypeVarId(0));
                assert!(!t.key_has_vars(&[int, atom]));
                assert!(t.key_has_vars(&[int, alpha]));
            }

            #[test]
            fn key_subsumes_with_leaves_sigma_empty_for_non_pure_var_keys() {
                let mut t = $ctor;
                let mut sigma = HashMap::new();
                let int = t.int();
                let alpha = t.type_var(TypeVarId(0));
                let int_top = t.int();
                let union_key = t.union(int_top, alpha);
                assert!(t.key_subsumes_with(&int, &union_key, &mut sigma));
                assert!(sigma.is_empty());
            }

            #[test]
            fn key_is_strictly_more_specific_recognizes_strict_subtype_keys() {
                let mut t = $ctor;
                let atom = t.atom();
                let atom_lit = t.atom_lit("ok");
                assert!(t.key_is_strictly_more_specific(slice::from_ref(&atom_lit), slice::from_ref(&atom)));
                assert!(!t.key_is_strictly_more_specific(slice::from_ref(&atom), slice::from_ref(&atom_lit)));
            }

            #[test]
            fn default_bool_lit_uses_reserved_atom_literals() {
                let mut t = $ctor;
                let true_lit = t.bool_lit(true);
                let false_lit = t.bool_lit(false);
                assert_eq!(t.as_atom_singleton(&true_lit).as_deref(), Some("true"));
                assert_eq!(t.as_atom_singleton(&false_lit).as_deref(), Some("false"));
            }

            #[test]
            fn default_cpointer_is_builtin_opaque() {
                let mut t = $ctor;
                let ptr = t.c_pointer();
                assert_eq!(
                    t.builtin_opaque_singleton(&ptr),
                    Some(crate::types::BuiltinOpaque::CPointer)
                );
                assert_eq!(t.opaque_singleton(&ptr), None);
            }

            #[test]
            fn default_is_equivalent_recognizes_mutual_subtypes() {
                let mut t = $ctor;
                let true_lit = t.bool_lit(true);
                let false_lit = t.bool_lit(false);
                let bool_union = t.union(true_lit, false_lit);
                let bool_t = t.bool();
                assert!(t.is_equivalent(&bool_union, &bool_t));
            }
        }
    };
}

macro_rules! seam_helper_conformance_tests {
    ($mod_name:ident, $ctor:expr) => {
        mod $mod_name {
            use super::*;

            #[test]
            fn list_element_type_projects_list_axis() {
                let mut t = $ctor;
                let elem = t.int();
                let list = t.list(elem.clone());
                let projected = t.list_element_type(&list);
                assert!(t.is_equivalent(&projected, &elem));
            }

            #[test]
            fn list_element_type_defaults_to_any_without_list_axis() {
                let mut t = $ctor;
                let int = t.int();
                let projected = t.list_element_type(&int);
                assert!(t.is_top(&projected));
            }

            #[test]
            fn has_list_shape_distinguishes_list_axis_from_runtime_projection_fallback() {
                let mut t = $ctor;
                let int = t.int();
                let list = t.list(int.clone());
                assert!(t.has_list_shape(&list));
                assert!(!t.has_list_shape(&int));
            }

            #[test]
            fn list_element_type_projects_empty_list_as_none() {
                let mut t = $ctor;
                let empty = t.empty_list();
                let projected = t.list_element_type(&empty);
                assert!(t.is_empty(&projected));
            }

            #[test]
            fn list_element_type_of_an_unconstrained_list_is_any() {
                // `any`'s list fragment is the unconstrained conjunction: a
                // value flowing here may be ANY cons cell, so its head is
                // `any` — never the empty type. Conflating "unconstrained"
                // with "exact empty list" manufactured `none` heads under a
                // root's earned-any inputs and dead-dropped live calls.
                let mut t = $ctor;
                let any = t.any();
                let projected = t.list_element_type(&any);
                assert!(t.is_top(&projected));
            }

            #[test]
            fn tuple_projections_fall_back_to_any() {
                let mut t = $ctor;
                let int = t.int();
                let comps = t.tuple_projections(&int, 2);
                assert_eq!(comps.len(), 2);
                assert!(comps.iter().all(|ty| t.is_top(ty)));
            }

            #[test]
            fn value_lane_repr_collapses_every_list_shape_to_one_lane() {
                // A `Value` lane is one boxed reference word: a list's
                // empty/non-empty refinement and element type do not change its
                // representation. So a clause returning a narrow `[int]` and a
                // function whose joined return is `[int] | []` must share one
                // lane, or destination-passing can't fold the result.
                let mut t = $ctor;
                let int = t.int();
                let non_empty = t.non_empty_list(int.clone()); // [int]
                let proper = t.list(int.clone()); // [int] | []
                let empty = t.empty_list(); // []
                let float = t.float();
                let float_list = t.list(float);

                let canon = t.value_lane_repr(non_empty);
                assert_eq!(t.value_lane_repr(proper), canon, "[int] and [int]|[] share a lane");
                assert_eq!(t.value_lane_repr(empty), canon, "[] shares the list lane");
                assert_eq!(t.value_lane_repr(float_list), canon, "element type does not split the lane");

                // Non-list values keep their own representation.
                assert_eq!(t.value_lane_repr(int), int, "a scalar is its own lane");
            }

            #[test]
            fn value_lane_repr_collapses_every_callable_to_one_lane() {
                // A callable value is one word — a code pointer or a closure ref —
                // regardless of signature, arity, identity, or captures. So every
                // callable shares one `Value` lane, exactly as every list does.
                // This is what keeps an opaque join of same-signature functions
                // (`add_a | add_b`) from splitting across lanes (fz-hwn.27.12).
                let mut t = $ctor;
                let int = t.int();
                let a0 = t.type_var(TypeVarId(0));
                let a1 = t.type_var(TypeVarId(1));

                let unary = t.arrow(&[int], int); // (int) -> int
                let binary = t.arrow(&[int, int], int); // (int, int) -> int
                let poly = t.arrow(&[a0, a1], a0); // (a0, a1) -> a0
                let join = t.union(unary, binary); // (int)->int | (int,int)->int

                let canon = t.value_lane_repr(unary);
                assert_eq!(t.value_lane_repr(binary), canon, "arity does not split the callable lane");
                assert_eq!(t.value_lane_repr(poly), canon, "signature/vars do not split the lane");
                assert_eq!(t.value_lane_repr(join), canon, "an opaque join shares the one callable lane");

                // A callable lane is its own class, distinct from a scalar.
                assert_ne!(canon, t.value_lane_repr(int), "callables do not share the scalar lane");
            }

            #[test]
            fn tuple_projections_project_tuple_shape() {
                let mut t = $ctor;
                let one = t.int_lit(1);
                let ok = t.atom_lit("ok");
                let tuple = t.tuple(&[one.clone(), ok.clone()]);
                let comps = t.tuple_projections(&tuple, 2);
                assert_eq!(comps, vec![one, ok]);
            }

            #[test]
            fn map_field_lookup_returns_known_field_type() {
                let mut t = $ctor;
                let forty_two = t.int_lit(42);
                let map = t.map(&[(MapKey::Atom("ok".to_string()), forty_two.clone())]);
                let field = t
                    .map_field_lookup(&map, &MapKey::Atom("ok".to_string()))
                    .expect("known field");
                assert!(t.is_equivalent(&field, &forty_two));
            }

            #[test]
            fn refine_map_field_overlays_field_type() {
                let mut t = $ctor;
                let map = t.map_top();
                let value = t.int_lit(7);
                let refined = t.refine_map_field(&map, &MapKey::Atom("n".to_string()), &value);
                let field = t
                    .map_field_lookup(&refined, &MapKey::Atom("n".to_string()))
                    .expect("refined field");
                assert!(t.is_subtype(&value, &field));
                assert!(!t.is_empty(&field));
            }

            #[test]
            fn as_map_key_recognizes_atom_singletons_only() {
                // Int keys ride the lowering as values (LoweredMapKey); the
                // lattice holds no numeric singletons to project.
                let mut t = $ctor;
                let ok = t.atom_lit("ok");
                let seven = t.int_lit(7);
                let wide = t.atom();
                assert!(matches!(
                    t.as_map_key(&ok),
                    Some(MapKey::Atom(name)) if name == "ok"
                ));
                assert!(t.as_map_key(&seven).is_none());
                assert!(t.as_map_key(&wide).is_none());
            }

        }
    };
}

macro_rules! semantic_helper_conformance_tests {
    ($mod_name:ident, $ctor:expr) => {
        mod $mod_name {
            use super::*;

            fn sigma_of<T>(bindings: impl IntoIterator<Item = (u32, T)>) -> Sigma<T> {
                bindings.into_iter().map(|(id, ty)| (TypeVarId(id), ty)).collect()
            }

            #[test]
            fn arrow_join_return_union_of_clauses() {
                let mut t = $ctor;
                let int_arg = t.int();
                let int_ret = t.int();
                let int_arrow = t.arrow(&[int_arg], int_ret);
                let str_arg = t.str_t();
                let bool_ret = t.bool();
                let bool_arrow = t.arrow(&[str_arg], bool_ret.clone());
                let callable = t.union(int_arrow, bool_arrow);
                let got = t.arrow_join_return(&callable);
                let int = t.int();
                let want = t.union(int, bool_ret);
                assert!(t.is_equivalent(&got, &want));
            }

            #[test]
            fn arrow_join_return_top_is_any() {
                let mut t = $ctor;
                let any = t.any();
                let got = t.arrow_join_return(&any);
                assert!(t.is_top(&got));
            }

            #[test]
            fn arrow_join_return_empty_is_any() {
                let mut t = $ctor;
                let int = t.int();
                let got = t.arrow_join_return(&int);
                assert!(t.is_top(&got));
            }

            #[test]
            fn value_disjoint_erases_embedded_brand_correctly() {
                // mint_brand embeds the inner's structural axes; erasing the brand
                // just clears the brands field — no external map needed.
                let mut t = $ctor;
                let str_inner = t.str_t();
                let int = t.int();
                let utf8 = t.mint_brand(str_inner, "utf8");
                let plain = t.str_t();
                // utf8 and int are structurally different runtime kinds — value-disjoint.
                assert!(t.is_value_disjoint(&utf8, &int));
                // utf8 and plain binary share the same runtime kind after erasing brands — NOT value-disjoint.
                assert!(!t.is_value_disjoint(&utf8, &plain));
            }

            #[test]
            fn has_vars_distinguishes_concrete_from_polymorphic() {
                let mut t = $ctor;
                let int = t.int();
                let any = t.any();
                let var = t.type_var(TypeVarId(0));
                assert!(!t.has_vars(&int));
                assert!(!t.has_vars(&any));
                assert!(t.has_vars(&var));
            }

            #[test]
            fn instantiate_replaces_top_level_var() {
                let mut t = $ctor;
                let pattern = t.type_var(TypeVarId(0));
                let int = t.int();
                let sigma = sigma_of([(0, int.clone())]);
                let result = t.instantiate(&pattern, &sigma);
                assert!(t.is_equivalent(&result, &int));
            }

            #[test]
            fn instantiate_is_identity_when_no_vars_match() {
                let mut t = $ctor;
                let pattern = t.type_var(TypeVarId(0));
                let int = t.int();
                let sigma = sigma_of([(1, int)]);
                let result = t.instantiate(&pattern, &sigma);
                assert!(t.is_equivalent(&result, &pattern));
            }

            #[test]
            fn instantiate_walks_into_lists() {
                let mut t = $ctor;
                let var = t.type_var(TypeVarId(0));
                let list_of_var = t.list(var);
                let int = t.int();
                let sigma = sigma_of([(0, int.clone())]);
                let result = t.instantiate(&list_of_var, &sigma);
                let list_of_int = t.list(int);
                assert!(t.is_equivalent(&result, &list_of_int));
            }

            #[test]
            fn instantiate_walks_into_tuples() {
                let mut t = $ctor;
                let alpha = t.type_var(TypeVarId(0));
                let beta = t.type_var(TypeVarId(1));
                let tuple = t.tuple(&[alpha, beta]);
                let int = t.int();
                let str_t = t.str_t();
                let sigma = sigma_of([(0, int.clone()), (1, str_t.clone())]);
                let result = t.instantiate(&tuple, &sigma);
                let expected = t.tuple(&[int, str_t]);
                assert!(t.is_equivalent(&result, &expected));
            }

            #[test]
            fn instantiate_walks_into_arrow_args_and_ret() {
                let mut t = $ctor;
                let alpha = t.type_var(TypeVarId(0));
                let beta = t.type_var(TypeVarId(1));
                let arrow = t.arrow(&[alpha], beta);
                let int = t.int();
                let bool_t = t.bool();
                let sigma = sigma_of([(0, int.clone()), (1, bool_t.clone())]);
                let result = t.instantiate(&arrow, &sigma);
                let expected = t.arrow(&[int], bool_t);
                assert!(t.is_equivalent(&result, &expected));
            }

            #[test]
            fn collect_subst_binds_top_level_var_to_witness() {
                let mut t = $ctor;
                let pattern = t.type_var(TypeVarId(0));
                let witness = t.int();
                let mut sigma = HashMap::new();
                t.collect_instantiation_subst(&pattern, &witness, &mut sigma);
                assert_eq!(sigma.len(), 1);
                assert!(t.is_equivalent(&sigma[&TypeVarId(0)], &witness));
            }

            #[test]
            fn collect_subst_is_noop_on_concrete_pattern() {
                let mut t = $ctor;
                let pattern = t.int();
                let witness = t.int();
                let mut sigma = HashMap::new();
                t.collect_instantiation_subst(&pattern, &witness, &mut sigma);
                assert!(sigma.is_empty());
            }

            #[test]
            fn collect_subst_then_instantiate_is_identity_on_concrete_args() {
                let mut t = $ctor;
                let pat_arg = t.type_var(TypeVarId(0));
                let pat_ret = t.type_var(TypeVarId(0));
                let witness = t.int();
                let mut sigma = HashMap::new();
                t.collect_instantiation_subst(&pat_arg, &witness, &mut sigma);
                let resolved_ret = t.instantiate(&pat_ret, &sigma);
                assert!(t.is_equivalent(&resolved_ret, &witness));
            }

            #[test]
            fn collect_subst_distinct_vars_bind_independently() {
                let mut t = $ctor;
                let alpha = t.type_var(TypeVarId(0));
                let beta = t.type_var(TypeVarId(1));
                let int = t.int();
                let bool_t = t.bool();
                let mut sigma = HashMap::new();
                t.collect_instantiation_subst(&alpha, &int, &mut sigma);
                t.collect_instantiation_subst(&beta, &bool_t, &mut sigma);
                assert_eq!(sigma.len(), 2);
                assert!(t.is_equivalent(&sigma[&TypeVarId(0)], &int));
                assert!(t.is_equivalent(&sigma[&TypeVarId(1)], &bool_t));
            }

            #[test]
            fn tuple_field_projection_skips_impossible_mixed_arity_conjunctions() {
                let mut t = $ctor;
                let done_tuple = {
                    let tag = t.atom_lit("done");
                    let payload = t.int();
                    t.tuple(&[tag, payload])
                };
                let halted_tuple = {
                    let tag = t.atom_lit("halted");
                    let payload = t.int();
                    t.tuple(&[tag, payload])
                };
                let suspended_tuple = {
                    let tag = t.atom_lit("suspended");
                    let payload = t.int();
                    let continuation = t.int();
                    t.tuple(&[tag, payload, continuation])
                };
                let outcomes = {
                    let two = t.union(done_tuple, halted_tuple);
                    t.union(two, suspended_tuple)
                };
                let two_tuple = {
                    let a = t.any();
                    let b = t.any();
                    t.tuple(&[a, b])
                };
                let narrowed = t.intersect(outcomes, two_tuple);
                let first = t.tuple_field_type(&narrowed, 0);
                let expected = {
                    let done = t.atom_lit("done");
                    let halted = t.atom_lit("halted");
                    t.union(done, halted)
                };
                assert!(
                    t.is_equivalent(&first, &expected),
                    "projecting a 2-tuple narrowing must ignore impossible 3-tuple conjunctions, got {}",
                    t.display(&first)
                );
            }

            #[test]
            fn refine_widen_collapses_int_literals_to_int() {
                let mut t = $ctor;
                let one = t.int_lit(1);
                let two = t.int_lit(2);
                let int = t.int();
                let w_lits = t.refine_widen(&one, &two);
                let w_lit_base = t.refine_widen(&one, &int);
                let w_base = t.refine_widen(&int, &int);
                assert!(t.is_equivalent(&w_lits, &int));
                assert!(t.is_equivalent(&w_lit_base, &int));
                assert!(t.is_equivalent(&w_base, &int));
            }

            #[test]
            fn refine_widen_keeps_mismatched_callable_identities_apart() {
                // Pairwise arrow-merging is an economy, not a law: it is
                // only valid when the two clauses describe the same callable
                // value. Distinct fn refs flowing into one slot (a case that
                // yields add_a on one arm and add_b on the other) must
                // survive as two identity-bearing clauses, or downstream
                // closure callsites become unresolvable opaque callables.
                let mut t = $ctor;
                let a = t.fn_ref_lit(ClosureTarget(11), 2);
                let b = t.fn_ref_lit(ClosureTarget(12), 2);
                let w = t.refine_widen(&a, &b);
                let union = t.union(a, b);
                assert!(
                    t.is_equivalent(&w, &union),
                    "mismatched closure lits widen to their union, got {}",
                    t.display(&w)
                );
            }

            #[test]
            fn refine_widen_collapses_float_literals_to_float() {
                let mut t = $ctor;
                let a = t.float_lit(1.0);
                let b = t.float_lit(2.0);
                let float = t.float();
                let w = t.refine_widen(&a, &b);
                assert!(t.is_equivalent(&w, &float));
            }

            #[test]
            fn refine_widen_recurses_into_list_elements() {
                let mut t = $ctor;
                let one = t.int_lit(1);
                let two = t.int_lit(2);
                let int = t.int();
                let l1 = t.list(one);
                let l2 = t.list(two);
                let lint = t.list(int);
                let w = t.refine_widen(&l1, &l2);
                assert!(t.is_equivalent(&w, &lint));
            }

            #[test]
            fn refine_widen_merges_empty_and_non_empty_list_shapes() {
                let mut t = $ctor;
                let int = t.int();
                let empty = t.empty_list();
                let non_empty = t.non_empty_list(int.clone());
                let expected = t.list(int);
                let widened = t.refine_widen(&empty, &non_empty);
                assert!(t.is_equivalent(&widened, &expected));
            }

            #[test]
            fn union_keeps_normalized_list_evidence_when_rejoined_with_empty_list() {
                let mut t = $ctor;
                let elem = t.type_var(TypeVarId(0));
                let empty = t.empty_list();
                let non_empty = t.non_empty_list(elem);
                let proper = t.union(empty.clone(), non_empty);
                let rejoined = t.union(proper.clone(), empty.clone());

                assert!(
                    t.is_equivalent(&rejoined, &proper),
                    "rejoining {} with {} lowered or widened the list evidence to {}",
                    t.display(&proper),
                    t.display(&empty),
                    t.display(&rejoined)
                );
                assert!(
                    !t.is_equivalent(&rejoined, &empty),
                    "rejoining normalized list evidence collapsed to exact empty list"
                );

                let predicate = t.runtime_type_predicate(&rejoined);
                assert_eq!(
                    *predicate.lists.shapes(),
                    FiniteSet::finite([ListShape::Empty, ListShape::NonEmpty])
                );
            }

            #[test]
            fn convergence_class_unifies_all_list_shapes_but_separates_other_families() {
                let mut t = $ctor;
                let int = t.int();
                let empty = t.empty_list();
                let nonempty = t.non_empty_list(int.clone());
                let list = t.list(int.clone());
                let empty_class = t.convergence_class(&empty);
                let nonempty_class = t.convergence_class(&nonempty);
                let list_class = t.convergence_class(&list);
                assert!(t.is_equivalent(&empty_class, &nonempty_class));
                assert!(t.is_equivalent(&nonempty_class, &list_class));
                let joined = t.union(empty, nonempty);
                let joined_class = t.convergence_class(&joined);
                assert!(
                    t.is_equivalent(&joined_class, &list_class),
                    "empty | non-empty list unions should share the recursive list convergence class"
                );

                let tagged = t.tuple(&[int.clone(), int.clone()]);
                let tagged_class = t.convergence_class(&tagged);
                assert!(!t.is_equivalent(&tagged_class, &list_class));

                let int_class = t.convergence_class(&int);
                assert!(!t.is_equivalent(&int_class, &list_class));
            }

            #[test]
            fn convergence_class_collapses_nested_list_and_callable_runtime_detail() {
                let mut t = $ctor;
                let int = t.int();
                let empty = t.empty_list();
                let nonempty = t.non_empty_list(int.clone());
                let cont = t.atom_lit("cont");
                let halt = t.atom_lit("halt");
                let callable_a = t.arrow(std::slice::from_ref(&int), cont);
                let callable_b = t.arrow(std::slice::from_ref(&int), halt);
                let tuple_a = t.tuple(&[empty, callable_a]);
                let tuple_b = t.tuple(&[nonempty, callable_b]);

                let class_a = t.convergence_class(&tuple_a);
                let class_b = t.convergence_class(&tuple_b);

                assert!(
                    t.is_equivalent(&class_a, &class_b),
                    "ignored recursive tuple slots should collapse nested list/callable detail while preserving tuple family"
                );
            }

            #[test]
            fn convergence_collapse_widens_only_non_dispatch_slots_of_the_arrow() {
                // The dispatch KEY of a recursive activation is a whole-arrow
                // collapse of its precise evidence arrow (fz-hwn.27.7): a
                // non-dispatch list slot widens to its ADDRESSED convergence
                // class so the recursive ascent settles, while dispatch slots and
                // the result are preserved exactly. Here slot 0 dispatches and
                // slot 1 does not, so slot 1's `list(int)` collapses to
                // `list(a1_e)` — a resolvable element address var at the slot's
                // structural address, not the path-blind `list(any)`
                // (fz-f98.14.10.2). Breadth is still one address per position so
                // fz-y6w termination holds.
                let mut t = $ctor;
                let int = t.int();
                let list_int = t.list(int.clone());
                let collapsed = t.convergence_collapse_inputs(
                    &[list_int.clone(), list_int.clone()],
                    &[DispatchDemand::Whole, DispatchDemand::Ignore],
                    &[],
                );

                let params = collapsed.as_ref();
                assert_eq!(t.display(&params[0]), "[int]");
                assert_eq!(t.display(&params[1]), "[a1_e]");
                assert_eq!(t.display(&int), "int");
            }

            #[test]
            fn convergence_collapse_list_shape_keeps_element_but_not_recursive_list_shape() {
                let mut t = $ctor;
                let int = t.int();
                let non_empty = t.non_empty_list(int.clone());
                let list_int = t.list(int);
                let joined_list_family = t.union(list_int, non_empty);
                let collapsed = t.convergence_collapse_inputs(
                    &[joined_list_family],
                    &[DispatchDemand::ListShape(Box::new(DispatchDemand::Whole))],
                    &[],
                );

                assert!(
                    t.is_equivalent(&collapsed[0], &list_int),
                    "recursive list-shape dispatch should converge joined list-family shape while preserving demanded element type"
                );
            }

            #[test]
            fn convergence_collapse_preserves_nested_dispatch_field_and_collapses_payload() {
                let mut t = $ctor;
                let elem = t.type_var(TypeVarId(0));
                let payload = t.list(elem);
                let tag = t.atom_lit("cont");
                let state = t.tuple(&[tag, payload]);
                let mut fields = BTreeMap::new();
                fields.insert(0, DispatchDemand::Whole);
                let collapsed = t.convergence_collapse_inputs(&[state], &[DispatchDemand::TupleFields(fields)], &[]);

                // The dispatch tag (field 0) is preserved exactly; the ignored
                // payload (field 1) collapses to its ADDRESSED class — the list
                // element addressed at `[Param(0), Field(1), Elem]`, displayed
                // `a0_1_e` — not the path-blind `list(any)` (fz-f98.14.10.2).
                let params = collapsed.as_ref();
                assert_eq!(
                    t.display(&params[0]),
                    "{:cont, [a0_1_e]}",
                    "nested dispatch demand should preserve the tag and collapse the payload to its addressed class: {}",
                    t.display(&params[0])
                );
            }

            #[test]
            fn convergence_collapse_tuple_union_arrow_roundtrips_through_address_inputs() {
                // A multi-alternative tagged union slot collapsed by the recursive
                // dispatch-key mint MUST round-trip through `address_inputs` (the
                // canonical addresser, fz-hwn.27): the collapsed arrow is already
                // canonically addressed, so re-addressing it is the identity. This
                // fails if `convergence_collapse` omits the per-variant `Variant(k)`
                // discriminator that `address_inputs` inserts when alternatives > 1
                // (fz-go4.18.3.2.1).
                let mut t = $ctor;
                let elem = t.type_var(TypeVarId(0));
                let payload = t.list(elem); // [T]
                let cont = {
                    let tag = t.atom_lit("cont");
                    t.tuple(&[tag, payload])
                };
                let halt = {
                    let tag = t.atom_lit("halt");
                    t.tuple(&[tag, payload])
                };
                let union = t.union(cont, halt); // {:cont,[T]} | {:halt,[T]}
                let mut fields = BTreeMap::new();
                fields.insert(0, DispatchDemand::Whole); // tag dispatches, payload ignored
                let collapsed = t.convergence_collapse_inputs(&[union], &[DispatchDemand::TupleFields(fields)], &[]);

                let params = collapsed.as_ref();
                let readdressed = t.address_inputs(params);
                assert_eq!(
                    readdressed, params,
                    "collapsed union slot must be canonically addressed (round-trip): {} vs {}",
                    t.display(&readdressed[0]),
                    t.display(&params[0]),
                );
            }

            #[test]
            fn evidence_collapse_only_widens_variable_non_dispatch_payloads() {
                let mut t = $ctor;
                let int = t.int();
                let concrete = t.list(int.clone());
                let var = t.type_var(TypeVarId(0));
                let variable = t.list(var);
                let collapsed = t.convergence_collapse_evidence_inputs(
                    &[concrete, variable],
                    &[DispatchDemand::Ignore, DispatchDemand::Ignore],
                );

                let any = t.any();
                let list_any = t.list(any);
                assert!(
                    t.is_equivalent(&collapsed[0], &concrete),
                    "concrete non-dispatch evidence should stay precise"
                );
                assert!(
                    t.is_equivalent(&collapsed[1], &list_any),
                    "variable non-dispatch evidence should converge to list(any)"
                );
            }

            #[test]
            fn refine_widen_recurses_into_tuple_fields() {
                let mut t = $ctor;
                let empty = t.empty_list();
                let int = t.int();
                let non_empty = t.non_empty_list(int.clone());
                let two = t.int_lit(2);
                let one = t.int_lit(1);
                let lhs = t.tuple(&[empty, two]);
                let rhs = t.tuple(&[non_empty, one]);
                let list_int = t.list(int.clone());
                let expected = t.tuple(&[list_int, int]);
                let widened = t.refine_widen(&lhs, &rhs);
                assert!(t.is_equivalent(&widened, &expected));
            }

            #[test]
            fn refine_widen_recurses_into_resource_payloads() {
                let mut t = $ctor;
                let one = t.int_lit(1);
                let two = t.int_lit(2);
                let int = t.int();
                let lhs = t.resource(one);
                let rhs = t.resource(two);
                let expected = t.resource(int);
                let widened = t.refine_widen(&lhs, &rhs);
                assert!(t.is_equivalent(&widened, &expected));
            }

            #[test]
            fn refine_widen_recurses_into_arrow_returns_and_unions_args() {
                let mut t = $ctor;
                let int = t.int();
                let float = t.float();
                let empty = t.empty_list();
                let one = t.int_lit(1);
                let lhs_ret = t.tuple(&[empty, one]);
                let lhs = t.arrow(slice::from_ref(&int), lhs_ret);
                let non_empty = t.non_empty_list(int.clone());
                let two = t.int_lit(2);
                let rhs_ret = t.tuple(&[non_empty, two]);
                let rhs = t.arrow(slice::from_ref(&float), rhs_ret);
                let union = t.union(int.clone(), float);
                let list_int = t.list(int.clone());
                let ret = t.tuple(&[list_int, int]);
                let expected = t.arrow(&[union], ret);
                let widened = t.refine_widen(&lhs, &rhs);
                assert!(t.is_equivalent(&widened, &expected));
            }

            #[test]
            fn refine_widen_recurses_into_map_fields() {
                let mut t = $ctor;
                let key = MapKey::Atom("value".to_string());
                let int = t.int();
                let empty = t.empty_list();
                let one = t.int_lit(1);
                let lhs_value = t.tuple(&[empty, one]);
                let lhs = t.map(&[(key.clone(), lhs_value)]);
                let non_empty = t.non_empty_list(int.clone());
                let two = t.int_lit(2);
                let rhs_value = t.tuple(&[non_empty, two]);
                let rhs = t.map(&[(key.clone(), rhs_value)]);
                let list_int = t.list(int.clone());
                let expected_value = t.tuple(&[list_int, int]);
                let expected = t.map(&[(key, expected_value)]);
                let widened = t.refine_widen(&lhs, &rhs);
                assert!(t.is_equivalent(&widened, &expected));
            }

            #[test]
            fn refine_widen_falls_back_to_union_for_incompatible_fields_monotonically() {
                let mut t = $ctor;
                let int = t.int();
                let empty = t.empty_list();
                let tuple = t.tuple(&[empty.clone(), int.clone()]);
                let prev = t.union(int, tuple.clone());
                let observed = tuple;
                let widened = t.refine_widen(&prev, &observed);
                assert!(t.is_subtype(&prev, &widened));
                assert!(t.is_subtype(&observed, &widened));
            }

            #[test]
            fn refine_widen_keeps_int_and_float_apart_no_number_rung() {
                let mut t = $ctor;
                let i = t.int_lit(1);
                let f = t.float_lit(2.0);
                let int = t.int();
                let float = t.float();
                let union = t.union(int, float);
                let any = t.any();
                let widened = t.refine_widen(&i, &f);
                assert!(t.is_equivalent(&widened, &union));
                assert!(!t.is_equivalent(&widened, &any));
            }

            #[test]
            fn refine_widen_any_absorbs() {
                let mut t = $ctor;
                let int = t.int();
                let any = t.any();
                let widened = t.refine_widen(&int, &any);
                assert!(t.is_equivalent(&widened, &any));
            }

            #[test]
            fn numeric_literals_in_type_position_mean_their_kind() {
                // The lattice cannot express a numeric singleton: a literal
                // constructor yields the kind itself, and no singleton is
                // ever observable. Atoms keep their singletons.
                let mut t = $ctor;
                let one = t.int_lit(1);
                let int = t.int();
                assert!(t.is_equivalent(&one, &int));
                assert_eq!(t.as_int_singleton(&one), None);
                let pi = t.float_lit(2.5);
                let float = t.float();
                assert!(t.is_equivalent(&pi, &float));
                assert_eq!(t.as_float_singleton(&pi), None);
                assert!(!t.is_singleton_lit(&one));
                let ok = t.atom_lit("ok");
                assert!(t.is_singleton_lit(&ok));
            }
        }
    };
}

macro_rules! closure_helper_conformance_tests {
    ($mod_name:ident, $ctor:expr) => {
        mod $mod_name {
            use super::*;

            /// Erasure drops the brand and callable observation while keeping
            /// capture denotations: two lambdas closed over the same thing
            /// become one key, while different capture types remain distinct.
            #[test]
            fn erase_closure_identity_drops_the_brand_and_keeps_the_captures() {
                let mut t = $ctor;
                let ten = t.int_lit(10);
                let lit = t.closure_lit(ClosureTarget(3), vec![ten], 2);
                let erased = t.erase_closure_identity(&lit);
                assert!(
                    t.closure_lit_parts(&erased).is_none(),
                    "an erased literal names no target, so nothing may call it directly"
                );
                let clauses = t
                    .callable_clauses(&erased)
                    .expect("erased closure should remain callable");
                assert_eq!(clauses.len(), 1);
                assert_eq!(clauses[0].args.len(), 2);
                assert!(clauses[0].closure.is_none());

                // A call surface cannot survive brand erasure in `Ty`: it is
                // planner evidence carried by the activation row instead.
                let int = t.int();
                let surface = t.arrow(&[int, int], int);
                let left = t.closure_lit(ClosureTarget(3), vec![int], 2);
                let left = t.intersect(left, surface);
                let left = t.erase_closure_identity(&left);
                let right = t.closure_lit(ClosureTarget(4), vec![int], 2);
                let right = t.intersect(right, surface);
                let right = t.erase_closure_identity(&right);
                assert_eq!(
                    left, right,
                    "two lambdas closed over the same type are one key: the brand is freight"
                );

                let float = t.float();
                let other = t.closure_lit(ClosureTarget(3), vec![float], 2);
                let other = t.intersect(other, surface);
                let other = t.erase_closure_identity(&other);
                assert_ne!(
                    other, left,
                    "one lambda closed over two types is two keys: the captures are meaning"
                );

                let bare = t.closure_lit(ClosureTarget(3), Vec::new(), 2);
                let bare = t.intersect(bare, surface);
                let erased_bare = t.erase_closure_identity(&bare);
                let any = t.any();
                let generic_surface = t.arrow(&[any, any], any);
                assert_eq!(
                    erased_bare, generic_surface,
                    "a capture-free literal becomes the literal-free callable top"
                );
            }

            #[test]
            fn callable_value_clauses_keep_literal_denotations_unspecialized() {
                let mut t = $ctor;
                let closure = t.fn_ref_lit(ClosureTarget(3), 1);
                let int = t.int();
                let nil = t.nil();
                let surface = t.arrow(&[int], nil);
                let refined = t.intersect(closure, surface);
                let clauses = t
                    .callable_value_clauses(&refined)
                    .expect("refined callable should expose value clauses");
                assert_eq!(clauses.len(), 1);
                let clause = &clauses[0];
                assert!(clause.closure.is_some(), "value clauses should preserve closure identity");
                assert!(
                    t.has_vars(&clause.args[0]) && t.has_vars(&clause.ret),
                    "the literal owns one generic callable denotation; exact observations live in ActivationInput"
                );
            }

            /// A literal's construction and reads retain one denotation even
            /// when a caller presents an exact arrow surface beside it.
            #[test]
            fn meeting_a_surface_and_reading_through_one_report_one_shape() {
                let mut t = $ctor;
                let closure = t.fn_ref_lit(ClosureTarget(3), 1);
                let int = t.int();
                let nil = t.nil();
                let surface = t.arrow(&[int], nil);

                let met = t.intersect(closure, surface);
                let met = t.callable_value_clauses(&met).expect("the meet stays callable");

                let beside = t.union(closure, surface);
                let read = t.callable_value_clauses(&beside).expect("the union stays callable");
                let read: Vec<_> = read.into_iter().filter(|clause| clause.closure.is_some()).collect();

                assert_eq!(met.len(), 1);
                assert_eq!(read.len(), 1, "one literal viewed through one surface is one clause");
                assert_eq!(
                    (met[0].args.clone(), met[0].ret),
                    (read[0].args.clone(), read[0].ret),
                    "the meet and the read retain the literal's one denotation",
                );
                assert!(t.has_vars(&read[0].args[0]) && t.has_vars(&read[0].ret));
            }

            #[test]
            fn refine_widen_same_fn_ref_preserves_closure_identity() {
                let mut t = $ctor;
                let one = t.int_lit(1);
                let two = t.int_lit(2);
                let nil = t.nil();
                let fn_ref = t.fn_ref_lit(ClosureTarget(3), 1);
                let one_surface = t.arrow(&[one], nil);
                let two_surface = t.arrow(&[two], nil);
                let a = t.intersect(fn_ref, one_surface);
                let b = t.intersect(fn_ref, two_surface);
                let widened = t.refine_widen(&a, &b);
                let clauses = t
                    .callable_value_clauses(&widened)
                    .expect("same-target fn-ref widen should stay callable");
                assert_eq!(clauses.len(), 1);
                let clause = &clauses[0];
                assert!(
                    clause.closure.is_some(),
                    "same-target fn-ref widen should preserve callable identity instead of erasing to an opaque surface"
                );
                assert!(
                    t.has_vars(&clause.args[0]),
                    "same-target fn-ref widening keeps the one literal denotation; observations do not enter Ty"
                );
                assert!(t.has_vars(&clause.ret));
            }

            #[test]
            fn refine_widen_same_closure_target_preserves_widened_captures() {
                let mut t = $ctor;
                let one = t.int_lit(1);
                let two = t.int_lit(2);
                let a = t.closure_lit(ClosureTarget(3), vec![one], 1);
                let b = t.closure_lit(ClosureTarget(3), vec![two], 1);
                let widened = t.refine_widen(&a, &b);
                let parts = t
                    .closure_lit_parts(&widened)
                    .expect("same-target closure widen should preserve closure identity");
                assert_eq!(parts.target, ClosureTarget(3));
                assert_eq!(parts.captures.len(), 1);
                assert!(
                    t.is_integer(&parts.captures[0]),
                    "same-target closure widen should widen captures elementwise through the preserved closure literal"
                );
            }

            #[test]
            fn closure_lit_intersect_same_fn_narrows_captures() {
                let mut t = $ctor;
                let int = t.int();
                let ten = t.int_lit(10);
                let a = t.closure_lit(ClosureTarget(3), vec![int], 1);
                let b = t.closure_lit(ClosureTarget(3), vec![ten], 1);
                let narrowed = t.intersect(a, b);
                let parts = t
                    .closure_lit_parts(&narrowed)
                    .expect("same-target closure meet should stay a singleton");
                assert_eq!(parts.target, ClosureTarget(3));
                assert_eq!(parts.captures.len(), 1);
                assert_eq!(
                    parts.captures[0], ten,
                    "same-target closure meet should narrow captures elementwise"
                );
            }

            #[test]
            fn closure_lit_intersect_different_fn_ids_is_empty() {
                let mut t = $ctor;
                let a = t.closure_lit(ClosureTarget(3), Vec::new(), 1);
                let b = t.closure_lit(ClosureTarget(4), Vec::new(), 1);
                let intersection = t.intersect(a, b);
                assert!(
                    t.is_empty(&intersection),
                    "different closure identities should have an empty meet"
                );
            }

            #[test]
            fn display_distinguishes_fn_ref_from_closure_on_same_fn_id() {
                // fz-go4.18.28.14 audit finding: `ArrowSig`'s `lit: Option<ClosureLit>`
                // is part of its `Eq`/`Hash` identity via `kind` + `fn_id` +
                // `captures` (see `ClosureLit`'s doc comment in sigs.rs), but the
                // old `format_arrow_clause` only ever rendered `lit.fn_id`,
                // discarding `kind` and `captures` entirely. A `FnRef` lit and a
                // `Closure` lit sharing one `fn_id` (`t.fn_ref_lit` and
                // `t.closure_lit` both key their `args`/`ret` template vars off the
                // same `fn_id`, so those match too) are distinct interned `Ty`s
                // that used to render to the identical string.
                let mut t = $ctor;
                let fn_ref = t.fn_ref_lit(ClosureTarget(3), 1);
                let closure = t.closure_lit(ClosureTarget(3), Vec::new(), 1);
                assert_ne!(
                    fn_ref, closure,
                    "a FnRef lit and a Closure lit on the same fn_id must intern to distinct Tys"
                );
                assert_ne!(
                    t.display(&fn_ref),
                    t.display(&closure),
                    "distinct ArrowSig identities (FnRef vs Closure on the same fn_id) must not collide on display(), \
                     got fn_ref={} closure={}",
                    t.display(&fn_ref),
                    t.display(&closure)
                );
            }

            #[test]
            fn display_distinguishes_closure_lits_by_captures_on_same_fn_id() {
                // Same audit finding, the other axis of `ClosureLit` identity:
                // two `Closure` lits on the same `fn_id` with different
                // `captures` are distinct by `ArrowSig`'s `Eq`/`Hash` (captures
                // participate elementwise), but the old renderer never looked at
                // `captures` at all, so both collapsed to the same `#{fn_id}`
                // string.
                let mut t = $ctor;
                let one = t.atom_lit("one");
                let two = t.atom_lit("two");
                let closure_a = t.closure_lit(ClosureTarget(3), vec![one], 1);
                let closure_b = t.closure_lit(ClosureTarget(3), vec![two], 1);
                assert_ne!(
                    closure_a, closure_b,
                    "closures over the same fn_id with different captures must intern to distinct Tys"
                );
                assert_ne!(
                    t.display(&closure_a),
                    t.display(&closure_b),
                    "distinct capture sets on the same fn_id must not collide on display(), \
                     got closure_a={} closure_b={}",
                    t.display(&closure_a),
                    t.display(&closure_b)
                );
            }

            #[test]
            fn display_fn_ref_lit_rendering_is_unchanged() {
                // The common, non-colliding case (a bare `FnRef` lit, which per
                // `ClosureLit`'s invariant always carries empty `captures`) keeps
                // its original `(args) -> ret#{fn_id}` rendering — the fix only
                // adds a disambiguating suffix to `Closure` lits.
                let mut t = $ctor;
                let fn_ref = t.fn_ref_lit(ClosureTarget(3), 1);
                let rendered = t.display(&fn_ref);
                assert!(
                    rendered.ends_with("#3"),
                    "FnRef lit rendering should be unchanged, plain `#{{fn_id}}` suffix, got {}",
                    rendered
                );
            }

            #[test]
            fn tuple_contract_meet_keeps_a_single_specialized_tuple_shape() {
                let mut t = $ctor;
                let any = t.any();
                let suspended_tag = t.atom_lit("suspended");
                let continuation_surface = t.arrow(&[], any);
                let captured = t.atom_lit("captured");
                let payload = t.atom_lit("payload");
                let continuation = t.closure_lit(ClosureTarget(7), vec![captured], 0);
                let observed = t.tuple(&[suspended_tag, payload, continuation]);
                let contract = t.tuple(&[suspended_tag, any, continuation_surface]);

                let refined = t.intersect(observed, contract);
                let fields = t
                    .tuple_lit_elems(&refined)
                    .expect("tuple meets should collapse to one tuple shape, not a conjunction of tuple clauses");
                assert_eq!(fields.len(), 3);

                let repeated = t.intersect(refined, contract);
                assert_eq!(
                    repeated, refined,
                    "meeting the same tuple contract again should stay stable"
                );
            }

            #[test]
            fn intersect_preserves_concrete_suspended_return_when_it_is_already_within_contract() {
                let mut t = $ctor;
                let any = t.any();
                let list_any = t.list(any);
                let cont_tag = t.atom_lit("cont");
                let halt_tag = t.atom_lit("halt");
                let suspend_tag = t.atom_lit("suspend");
                let done_tag = t.atom_lit("done");
                let halted_tag = t.atom_lit("halted");
                let suspended_tag = t.atom_lit("suspended");
                let reducer_surface = {
                    let cont = t.tuple(&[cont_tag, any]);
                    let halt = t.tuple(&[halt_tag, any]);
                    let suspend = t.tuple(&[suspend_tag, any]);
                    let states = t.union(cont, halt);
                    let states = t.union(states, suspend);
                    t.arrow(&[any, any], states)
                };
                let continuation_surface = t.arrow(&[], any);
                let continuation = {
                    let lit = t.closure_lit(ClosureTarget(7), vec![list_any, any, reducer_surface], 0);
                    t.intersect(lit, continuation_surface)
                };
                let done = t.tuple(&[done_tag, any]);
                let halted = t.tuple(&[halted_tag, any]);
                let suspended = t.tuple(&[suspended_tag, any, continuation]);
                let observed = {
                    let two = t.union(done, halted);
                    t.union(two, suspended)
                };

                let contract = {
                    let done = t.tuple(&[done_tag, any]);
                    let halted = t.tuple(&[halted_tag, any]);
                    let suspended = t.tuple(&[suspended_tag, any, continuation_surface]);
                    let two = t.union(done, halted);
                    t.union(two, suspended)
                };

                assert!(
                    t.is_subtype(&observed, &contract),
                    "the concrete suspended-return shape should already satisfy its declared contract: observed={} contract={}",
                    t.display(&observed),
                    t.display(&contract),
                );

                let refined = t.intersect(observed, contract);
                assert_eq!(
                    refined, observed,
                    "intersecting a subtype with its contract should be an identity, not a larger conjunction"
                );

                let repeated = t.intersect(refined, contract);
                assert_eq!(repeated, observed, "repeating the same contract meet should stay stable");
            }
        }
    };
}

macro_rules! impl_types_conformance_tests {
    ($key_mod:ident, $shape_mod:ident, $semantic_mod:ident, $closure_mod:ident, $ctor:expr) => {
        key_helper_conformance_tests!($key_mod, $ctor);
        seam_helper_conformance_tests!($shape_mod, $ctor);
        semantic_helper_conformance_tests!($semantic_mod, $ctor);
        closure_helper_conformance_tests!($closure_mod, $ctor);
    };
}

impl_types_conformance_tests!(
    types_key_helpers,
    types_shape_helpers,
    types_semantics,
    types_closure,
    Types::new()
);

// fz-go4.18.28.3 — tuple-clause emptiness must prune, not fan out.
//
// A tuple type minus a union of overlapping tuple negations drives
// `emptiness::phi_tuple`. Each negation below constrains exactly one coordinate
// (the others are `any`), so an unpruned phi recursion visits
// `arity ^ |negs|` leaves (4^14 here) before concluding — the shape that made
// 00277_enum_tier0_fixture burn >120s inside one `is_subtype` query. With
// empty-product and disjoint-negation pruning the same query is linear in the
// negation count. The intent captured: the ANSWERS are the emptiness semantics
// (unchanged), and the query completes in bounded time.
#[test]
fn tuple_emptiness_under_many_overlapping_negations_is_tractable() {
    let mut t = Types::new();
    let int = t.int();
    let atom = t.atom();
    let elem = t.union(int, atom);
    let any = t.any();
    let none = t.none();
    let arity = 4;
    let big = t.tuple(&vec![elem; arity]);

    let mut cover = none;
    for i in 0..14 {
        let a = t.atom_lit(&format!("a{i}"));
        let mut elems = vec![any; arity];
        elems[i % arity] = a;
        let neg = t.tuple(&elems);
        cover = t.union(cover, neg);
    }

    let start = std::time::Instant::now();
    // `{int, int, int, int}` inhabits `big` and no negation covers it: the
    // difference is non-empty, so `big` is NOT a subtype of the cover.
    assert!(
        !t.is_subtype(&big, &cover),
        "an all-int tuple escapes every single-coordinate atom negation"
    );
    // And with a top tuple added, the cover is total: the difference IS empty.
    let full = t.tuple(&vec![any; arity]);
    let cover_full = t.union(cover, full);
    assert!(
        t.is_subtype(&big, &cover_full),
        "adding the top tuple covers everything"
    );
    assert!(
        start.elapsed() < std::time::Duration::from_secs(5),
        "tuple emptiness under many negations must be tractable, took {:?}",
        start.elapsed()
    );
}

// fz-go4.24 — the tuples axis of an interned descriptor is hygienic by
// construction: the clause product dedups (`A ∨ A = A`), drops clauses that are
// empty by construction (arity mismatch, empty coordinate — a product with an
// empty factor is `∅`), and the persistence boundary absorbs subsumed clauses
// (`A ⊆ B ⇒ A ∨ B = B`). Without this, evidence-join traffic accumulates
// garbage clauses unboundedly (00277 interned a 60-clause tuple DNF with 54
// provably-empty clauses) and every garbage clause doubles a `dnf_neg` factor.
mod tuple_dnf_hygiene {
    use super::*;

    /// A tuple difference whose cover differs in one coordinate is still one
    /// rectangle. Keeping the negated cover as a separate clause makes the
    /// same set intern apart from its direct coordinate-difference form.
    #[test]
    fn tuple_difference_normalizes_a_single_coordinate_cover() {
        let mut t = Types::new();
        let any = t.any();
        let false_ = t.bool_lit(false);
        let true_ = t.bool_lit(true);
        let boolean = t.union(false_, true_);

        let all_booleans = t.tuple(&[any, boolean]);
        let false_booleans = t.tuple(&[any, false_]);
        let through_difference = t.difference(all_booleans, false_booleans);
        let direct = t.tuple(&[any, true_]);

        assert_eq!(
            through_difference, direct,
            "the interning boundary must give equivalent tuple forms one identity"
        );
    }

    /// The clause product of two overlapping tuple unions yields the same
    /// merged clause from symmetric pairs; idempotence collapses them and
    /// absorption drops the clause the wider survivors already contain.
    #[test]
    fn intersect_product_dedups_and_absorbs() {
        let mut t = Types::new();
        let int = t.int();
        let any = t.any();
        let str_t = t.str_t();
        let float = t.float();

        let x = t.tuple(&[int, any]);
        let y = t.tuple(&[any, int]);
        let ss = t.tuple(&[str_t, str_t]);
        let ff = t.tuple(&[float, float]);

        let a = {
            let xy = t.union(x, y);
            t.union(xy, ss)
        };
        let b = {
            let yx = t.union(y, x);
            t.union(yx, ff)
        };
        let meet = t.intersect(a, b);

        // Product pairs: X∧Y = Y∧X = {int,int} (duplicate, and subsumed by
        // both survivors), X∧X = {int,any}, Y∧Y = {any,int}; every pair
        // involving {str,str} or {float,float} has an empty coordinate.
        let d = t.descr(&meet);
        assert_eq!(
            d.tuples.len(),
            2,
            "expected exactly the two live clauses {{int,any}} and {{any,int}}, got {}",
            t.display(&meet)
        );
        let expected = t.union(x, y);
        assert!(t.is_equivalent(&meet, &expected), "hygiene must not change the set");
    }

    /// Tuples of different arity are disjoint products: their conjunction is
    /// `∅` by construction and must not persist as a multi-pos clause.
    #[test]
    fn arity_mismatched_tuple_intersection_persists_no_clause() {
        let mut t = Types::new();
        let int = t.int();
        let one = t.tuple(&[int]);
        let two = t.tuple(&[int, int]);
        let meet = t.intersect(one, two);
        assert!(t.descr(&meet).tuples.is_empty(), "∅ must persist no tuple clause");
        assert!(t.is_empty(&meet));

        // A mixed-arity union intersect keeps exactly the matching arity.
        let three = t.tuple(&[int, int, int]);
        let a = t.union(one, two);
        let b = t.union(two, three);
        let meet = t.intersect(a, b);
        assert_eq!(t.descr(&meet).tuples.len(), 1);
        assert!(t.is_equivalent(&meet, &two));
    }

    /// `∏Aᵢ ∩ ∏Bᵢ = ∏(Aᵢ∩Bᵢ)`: one empty coordinate empties the product, so
    /// the merged clause is dropped instead of persisting provably-empty.
    #[test]
    fn empty_coordinate_tuple_intersection_persists_no_clause() {
        let mut t = Types::new();
        let int = t.int();
        let str_t = t.str_t();
        let a = t.tuple(&[int, int]);
        let b = t.tuple(&[str_t, int]);
        let meet = t.intersect(a, b);
        assert!(t.descr(&meet).tuples.is_empty(), "∅ must persist no tuple clause");
        assert!(t.is_empty(&meet));
    }

    /// Absorption at union: `A ⊆ B ⇒ A ∨ B = B`. Near-duplicate evidence-join
    /// clauses collapse instead of accumulating across fixpoint iterations.
    #[test]
    fn union_absorbs_subsumed_tuple_clauses() {
        let mut t = Types::new();
        let int = t.int();
        let str_t = t.str_t();
        let any = t.any();
        let narrow = t.tuple(&[int, int]);
        let wide_elem = t.union(int, str_t);
        let wide = t.tuple(&[wide_elem, any]);

        let joined = t.union(narrow, wide);
        assert_eq!(t.descr(&joined).tuples.len(), 1, "narrow ⊆ wide ⇒ narrow ∨ wide = wide");
        assert!(t.is_equivalent(&joined, &wide));

        // Symmetric order: the wider clause survives regardless of position.
        let joined = t.union(wide, narrow);
        assert_eq!(t.descr(&joined).tuples.len(), 1);
        assert!(t.is_equivalent(&joined, &wide));
    }
}

/// `A ∨ ∅ = A`, on every axis the DNF kernel carries.
mod empty_clause_hygiene {
    use super::*;

    /// One axis's witnesses: an alternative the subtrahend covers, one it does
    /// not, the subtrahend, and the reader for that axis's clause list.
    struct AxisCase {
        axis: &'static str,
        covered: Ty,
        survivor: Ty,
        cover: Ty,
        clause_count: fn(&Descr) -> usize,
    }

    /// A difference carves the axis it is taken on into one clause per
    /// alternative of the minuend. An alternative the subtrahend COVERS —
    /// covers without being spelled the same, so no `P ∧ ¬P` collapse
    /// applies — denotes nothing. Every axis drops that clause before an
    /// identity is assigned, so the difference persists as its survivor and
    /// nothing beside it.
    #[test]
    fn an_empty_clause_is_dropped_on_every_axis() {
        let mut t = Types::new();
        let int = t.int();
        let bin = t.str_t();
        let float = t.float();
        let wide = t.union(int, bin);
        let key = MapKey::Atom("k".to_string());

        let cases = [
            AxisCase {
                axis: "tuples",
                covered: t.tuple(&[int]),
                survivor: t.tuple(&[float]),
                cover: t.tuple(&[wide]),
                clause_count: |d| d.tuples.len(),
            },
            AxisCase {
                axis: "lists",
                covered: t.non_empty_list(int),
                survivor: t.non_empty_list(float),
                cover: t.non_empty_list(wide),
                clause_count: |d| d.lists.len(),
            },
            AxisCase {
                axis: "resources",
                covered: t.resource(int),
                survivor: t.resource(float),
                cover: t.resource(wide),
                clause_count: |d| d.resources.len(),
            },
            AxisCase {
                axis: "funcs",
                covered: t.closure_lit(ClosureTarget(66), vec![int], 1),
                survivor: t.closure_lit(ClosureTarget(68), vec![float], 1),
                cover: t.closure_lit(ClosureTarget(66), vec![wide], 1),
                clause_count: |d| d.funcs.len(),
            },
            AxisCase {
                axis: "maps",
                covered: t.map(&[(key.clone(), int)]),
                survivor: t.map(&[(key.clone(), float)]),
                cover: t.map(&[(key, wide)]),
                clause_count: |d| d.maps.len(),
            },
        ];

        for case in cases {
            let carved = t.union(case.covered, case.survivor);
            let rest = t.difference(carved, case.cover);
            assert_eq!(
                (case.clause_count)(t.descr(&rest)),
                1,
                "{}: the covered alternative must not persist as an empty clause",
                case.axis
            );
            assert!(
                t.is_equivalent(&rest, &case.survivor),
                "{}: and the survivor is the whole answer",
                case.axis
            );
        }
    }
}

// fz-go4.25 — list-clause emptiness: exact-empty evidence must survive the
// positive elem fold.
//
// A list clause's positive fold tracks the element type of the NONEMPTY
// fragment of the intersection. An exact-empty sig (`elem: None`) admits no
// nonempty lists, so once one is folded the nonempty fragment is proven void
// — a later `elem: Some(_)` sig must not resurrect it. The old fold's single
// `Option<Descr>` cell used `None` for both "no evidence yet" and "fragment
// proven empty" (the unknown-is-not-none conflation), so
// `[exact_empty, list(int)]` folded to `Some(int)` and the clause
// `pos=[exact_empty, list(int)], neg=[list(atom)]` — which denotes ∅, since
// the positive intersection is exactly `{[]}` and `list(atom)` covers `[]` —
// was judged non-empty. Conservative direction only, but it poisons
// subtype/disjoint answers built on it.
//
// The tests drive the clause shapes through the public Ty algebra:
// `difference` uses the raw descriptor ops, so double negation stacks two
// positive sigs into one clause without the MergeSig collapse that
// `Types::intersect` applies.
mod list_clause_emptiness_matrix {
    use super::*;

    /// `pos=[p1, p2]` as ONE list clause: `p1 ∩ ¬¬p2` — the raw descriptor
    /// intersection concatenates positive sigs instead of merging them.
    fn stacked_pos(t: &mut Types, p1: Ty, p2: Ty) -> Ty {
        let any = t.any();
        let not_p2 = t.difference(any, p2);
        t.difference(p1, not_p2)
    }

    #[test]
    fn exact_empty_then_elem_sig_keeps_empty_evidence() {
        let mut t = Types::new();
        let int = t.int();
        let atom = t.atom();
        let e = t.empty_list();
        let li = t.list(int);
        let la = t.list(atom);

        // pos=[exact_empty, list(int)] denotes exactly {[]}: non-empty…
        let mixed = stacked_pos(&mut t, e, li);
        assert!(!t.is_empty(&mixed), "[] ∩ list(int) = {{[]}} is inhabited");
        // …and {[]} ⊆ list(atom) (which allows []), so the difference is ∅.
        let bad = t.difference(mixed, la);
        assert!(
            t.is_empty(&bad),
            "([] ∩ list(int)) \\ list(atom) = {{[]}} \\ list(atom) = ∅"
        );
        assert!(
            t.is_subtype(&mixed, &la),
            "[] ∩ list(int) = {{[]}} is a subtype of list(atom)"
        );
    }

    #[test]
    fn elem_sig_then_exact_empty_keeps_empty_evidence() {
        // Same clause, opposite fold order — pins the (inhabited, exact-empty)
        // arm as well as the (empty-evidence, elem) arm.
        let mut t = Types::new();
        let int = t.int();
        let atom = t.atom();
        let e = t.empty_list();
        let li = t.list(int);
        let la = t.list(atom);

        let mixed = stacked_pos(&mut t, li, e);
        assert!(!t.is_empty(&mixed), "list(int) ∩ [] = {{[]}} is inhabited");
        let bad = t.difference(mixed, la);
        assert!(
            t.is_empty(&bad),
            "(list(int) ∩ []) \\ list(atom) = {{[]}} \\ list(atom) = ∅"
        );
    }

    #[test]
    fn empty_list_minus_empty_list_is_empty() {
        // The audit's structurally-identical pair: P ∧ ¬P. The DNF builder's
        // hygiene drop already catches this shape; the answer is pinned here
        // so the semantic layer stays honest if that drop ever moves.
        let mut t = Types::new();
        let e = t.empty_list();
        let d = t.difference(e, e);
        assert!(t.is_empty(&d), "[] \\ [] = ∅");

        // Non-structural variant that reaches list_clause_empty: [] minus a
        // DIFFERENT sig that still covers [].
        let atom = t.atom();
        let la = t.list(atom);
        let d2 = t.difference(e, la);
        assert!(t.is_empty(&d2), "[] \\ list(atom) = ∅ (list(atom) allows [])");
    }

    // SOUNDNESS guards: the fix may only flip answers empty-ward for
    // genuinely-empty sets. These pin inhabited neighbors of the fixed cases
    // as non-empty — evidence that inhabited fragments are never dropped.
    #[test]
    fn inhabited_neighbors_stay_non_empty() {
        let mut t = Types::new();
        let int = t.int();
        let atom = t.atom();
        let e = t.empty_list();
        let li = t.list(int);
        let la = t.list(atom);
        let nea = t.non_empty_list(atom);

        // {[]} minus only the NONEMPTY atom lists keeps []: inhabited.
        let mixed = stacked_pos(&mut t, e, li);
        let keeps_nil = t.difference(mixed, nea);
        assert!(
            !t.is_empty(&keeps_nil),
            "{{[]}} \\ non_empty_list(atom) still contains []"
        );

        // list(int) \ list(atom) keeps every nonempty int list: inhabited.
        let ints_escape = t.difference(li, la);
        assert!(!t.is_empty(&ints_escape), "list(int) \\ list(atom) contains [1]");

        // And the fully-covered nonempty case still collapses: empty.
        let nei = t.non_empty_list(int);
        let covered = t.difference(nei, li);
        assert!(t.is_empty(&covered), "non_empty_list(int) \\ list(int) = ∅");
    }
}

mod smoke {
    use super::*;

    fn smoke_primitives_distinct(t: &mut Types) {
        let i = t.int();
        let f = t.float();
        let a = t.atom();
        assert!(t.is_disjoint(&i, &f), "int vs float must be disjoint");
        assert!(t.is_disjoint(&i, &a), "int vs atom must be disjoint");
        assert!(t.is_disjoint(&f, &a), "float vs atom must be disjoint");
        assert!(!t.is_disjoint(&i, &i), "int must overlap itself");
    }

    fn smoke_union_idempotent(t: &mut Types) {
        let i = t.int();
        let u = t.union(i, i);
        assert!(t.is_equivalent(&u, &i));
    }

    fn smoke_intersect_idempotent(t: &mut Types) {
        let i = t.int();
        let x = t.intersect(i, i);
        assert!(t.is_equivalent(&x, &i));
    }

    /// There is no `complement`: the lattice's primitive is `difference`,
    /// because the complement of a branded type is not representable (see
    /// `Descr::neg_structure`). Subtracting from `any` is the complement of an
    /// UNBRANDED type, which is what these smoke laws are about.
    fn complement(t: &mut Types, a: Ty) -> Ty {
        let any = t.any();
        t.difference(any, a)
    }

    fn smoke_complement_involution(t: &mut Types) {
        let i = t.int();
        let once = complement(t, i);
        let twice = complement(t, once);
        assert!(t.is_equivalent(&twice, &i));
    }

    fn smoke_de_morgan(t: &mut Types) {
        let i = t.int();
        let f = t.float();
        let u = t.union(i, f);
        let lhs = complement(t, u);
        let ni = complement(t, i);
        let nf = complement(t, f);
        let rhs = t.intersect(ni, nf);
        assert!(t.is_equivalent(&lhs, &rhs));
    }

    fn smoke_subtype_reflexive(t: &mut Types) {
        let i = t.int();
        assert!(t.is_subtype(&i, &i));
    }

    fn smoke_int_lit_in_int(t: &mut Types) {
        // A literal in type position means its kind: int_lit IS int. The
        // lattice cannot express a numeric singleton, by design.
        let i = t.int();
        let lit = t.int_lit(42);
        assert!(t.is_subtype(&lit, &i));
        assert!(t.is_subtype(&i, &lit));
    }

    fn smoke_nil_in_atom(t: &mut Types) {
        let n = t.nil();
        let a = t.atom();
        assert!(t.is_subtype(&n, &a));
    }

    fn smoke_top_bottom(t: &mut Types) {
        let top = t.any();
        let bot = t.none();
        assert!(t.is_top(&top));
        assert!(t.is_empty(&bot));
        assert!(!t.is_top(&bot));
        assert!(!t.is_empty(&top));
    }

    fn smoke_tuple_element_disjoint(t: &mut Types) {
        let i = t.int();
        let a = t.atom();
        let ti = t.tuple(&[i]);
        let ta = t.tuple(&[a]);
        assert!(t.is_disjoint(&ti, &ta));
    }

    fn smoke_arrow_contravariance(t: &mut Types) {
        let any = t.any();
        let i = t.int();
        let wide = t.arrow(&[any], i);
        let arg = i;
        let narrow = t.arrow(slice::from_ref(&arg), i);
        assert!(t.is_subtype(&wide, &narrow));
    }

    fn smoke_list_covariance(t: &mut Types) {
        let i = t.int();
        let lit = t.int_lit(42);
        let l_lit = t.list(lit);
        let l_int = t.list(i);
        assert!(t.is_subtype(&l_lit, &l_int));
        assert!(t.is_subtype(&l_lit, &l_lit));
    }

    fn smoke_core_predicates(t: &mut Types) {
        let one = t.int_lit(1);
        let int = t.int();
        let float = t.float();
        let resource = t.resource(int);
        let nil = t.nil();
        let bool_t = t.bool();
        let atom_lit = t.atom_lit("ok");
        let atom = t.atom();
        let top = t.any();
        let bot = t.none();

        assert!(t.is_integer(&one));
        assert!(t.is_integer(&int));
        assert!(!t.is_integer(&float));
        assert!(
            !t.is_integer(&resource),
            "resource(integer) must stay a boxed resource value, not collapse into the raw integer lane",
        );
        assert!(t.is_floating(&float));
        assert!(!t.is_floating(&int));
        assert!(t.is_nil(&nil));
        assert!(!t.is_nil(&top));
        assert!(t.is_bool(&bool_t));
        assert!(!t.is_bool(&atom_lit));
        assert!(t.is_atom_type(&nil));
        assert!(t.is_atom_type(&bool_t));
        assert!(t.is_atom_type(&atom));
        assert!(!t.is_atom_type(&int));
        assert!(t.is_top(&top));
        assert!(t.is_empty(&bot));
    }

    fn smoke_display_renders(t: &mut Types) {
        let i = t.int();
        let s = t.display(&i);
        assert_eq!(s, "int", "display should name the integer axis, not collapse it to any");
    }

    macro_rules! impl_smoke_suite {
        ($impl_name:ident, $ctor:expr) => {
            mod $impl_name {
                use super::*;

                #[test]
                fn primitives_distinct() {
                    smoke_primitives_distinct(&mut $ctor);
                }

                #[test]
                fn union_idempotent() {
                    smoke_union_idempotent(&mut $ctor);
                }

                #[test]
                fn intersect_idempotent() {
                    smoke_intersect_idempotent(&mut $ctor);
                }

                #[test]
                fn complement_involution() {
                    smoke_complement_involution(&mut $ctor);
                }

                #[test]
                fn de_morgan() {
                    smoke_de_morgan(&mut $ctor);
                }

                #[test]
                fn subtype_reflexive() {
                    smoke_subtype_reflexive(&mut $ctor);
                }

                #[test]
                fn int_lit_in_int() {
                    smoke_int_lit_in_int(&mut $ctor);
                }

                #[test]
                fn nil_in_atom() {
                    smoke_nil_in_atom(&mut $ctor);
                }

                #[test]
                fn top_bottom() {
                    smoke_top_bottom(&mut $ctor);
                }

                #[test]
                fn tuple_element_disjoint() {
                    smoke_tuple_element_disjoint(&mut $ctor);
                }

                #[test]
                fn arrow_contravariance() {
                    smoke_arrow_contravariance(&mut $ctor);
                }

                #[test]
                fn list_covariance() {
                    smoke_list_covariance(&mut $ctor);
                }

                #[test]
                fn core_predicates() {
                    smoke_core_predicates(&mut $ctor);
                }

                #[test]
                fn display_renders() {
                    smoke_display_renders(&mut $ctor);
                }
            }
        };
    }

    impl_smoke_suite!(types, Types::new());
}

/// fz-kdt.80 — the interned DNF carries no exact-duplicate clause on any axis.
///
/// The activation key is supposed to be a join homomorphism: keying the union
/// of two evidence rows must give the same key as keying either row, whenever
/// the key language cannot tell them apart. `erase_closure_identity` is the
/// step that makes two branded closures indistinguishable — and the union it
/// erases carries one funcs clause per brand. Erasing the brands in place
/// leaves `A ∨ A`, which interns as a DIFFERENT `Ty` than `A` unless the
/// persistence boundary collapses it.
mod erased_closure_dnf_hygiene {
    use super::*;
    use crate::compiler2::identity::{ActivationKey, FunctionId, RootId};

    /// Two closures over one declared surface, differing only in brand.
    fn branded_pair(t: &mut Types) -> (Ty, Ty) {
        let int = t.int();
        let nil = t.nil();
        let surface = t.arrow(&[int], nil);
        let left = t.closure_lit(ClosureTarget(3), vec![], 1);
        let right = t.closure_lit(ClosureTarget(4), vec![], 1);
        let left = t.intersect(left, surface);
        let right = t.intersect(right, surface);
        (left, right)
    }

    #[test]
    fn erasing_two_brands_of_one_surface_leaves_one_funcs_clause() {
        let mut t = Types::new();
        let (left, right) = branded_pair(&mut t);
        let joined = t.union(left, right);
        assert_eq!(
            t.descr(&joined).funcs.len(),
            2,
            "the brands are distinguishable before erasure, so the union keeps both clauses"
        );

        let erased = t.erase_closure_identity(&joined);
        assert_eq!(
            t.descr(&erased).funcs.len(),
            1,
            "A ∨ A = A: erasing the only distinguishing field must not leave two copies, got {}",
            t.display(&erased)
        );
        assert_eq!(
            erased,
            t.erase_closure_identity(&left),
            "and the collapsed union must be the very same interned id as either erased arm"
        );
    }

    #[test]
    fn the_activation_key_of_an_erased_union_is_the_key_of_each_arm() {
        let mut t = Types::new();
        let (left, right) = branded_pair(&mut t);
        let joined = t.union(left, right);

        let key_of = |t: &mut Types, ty: Ty| {
            let erased = t.erase_closure_identity(&ty);
            ActivationKey::from_inputs(RootId::for_test(0), FunctionId::from_coordinate(0), &[erased], t)
        };
        let left_key = key_of(&mut t, left);
        let right_key = key_of(&mut t, right);
        let joined_key = key_of(&mut t, joined);

        assert_eq!(left_key, right_key, "same surface, erased brand: one key");
        assert_eq!(
            joined_key, left_key,
            "the key must be a join homomorphism where the key language cannot see the difference"
        );
    }
}

/// fz-kdt.105 — a union's interned identity is its DENOTATION, not the order
/// its clauses arrived in.
///
/// `dnf_union` concatenates clause lists, so `A ∨ B` and `B ∨ A` reach the
/// interner as two different `Vec<Conj<_>>` and hash to two different `Descr`s.
/// Two `Ty`s for one set means the ACTIVATION KEY built from them differs too,
/// so which specializations exist becomes a function of the scheduler's arrival
/// order rather than of the program. The shape below is the one the reduce
/// bridge actually joins: `{:cont, list(int)} | {:halt, int}`.
mod union_clause_order {
    use super::*;
    use crate::compiler2::identity::{ActivationKey, FunctionId, RootId};

    fn cont_and_halt(t: &mut Types) -> (Ty, Ty) {
        let int = t.int();
        let ints = t.list(int);
        let cont = t.atom_lit("cont");
        let halt = t.atom_lit("halt");
        let cont_arm = t.tuple(&[cont, ints]);
        let halt_arm = t.tuple(&[halt, int]);
        (cont_arm, halt_arm)
    }

    #[test]
    fn a_union_interns_to_one_type_whichever_arm_arrives_first() {
        let mut t = Types::new();
        let (cont, halt) = cont_and_halt(&mut t);
        let forward = t.union(cont, halt);
        let backward = t.union(halt, cont);
        assert_eq!(
            forward,
            backward,
            "one denotation, one interned id: got {} vs {}",
            t.display(&forward),
            t.display(&backward)
        );
    }

    #[test]
    fn the_activation_key_of_a_union_does_not_depend_on_arm_order() {
        let mut t = Types::new();
        let (cont, halt) = cont_and_halt(&mut t);
        let forward = t.union(cont, halt);
        let backward = t.union(halt, cont);

        // `from_inputs` addresses its inputs, and the addresser numbers a tuple
        // union's alternatives by CLAUSE POSITION (`AddrStep::Variant`), so one
        // key for both arms is also the assertion that the variant numbering —
        // and every `a0_uK_…` var name derived from it — follows canonical
        // order rather than arrival order.
        let key_of = |t: &mut Types, ty: Ty| {
            ActivationKey::from_inputs(RootId::for_test(0), FunctionId::from_coordinate(0), &[ty], t)
        };
        let forward_key = key_of(&mut t, forward);
        let backward_key = key_of(&mut t, backward);
        assert_eq!(
            forward_key, backward_key,
            "the specialization a callee gets must be a function of the type it is passed, \
             not of which branch the scheduler ran first"
        );
    }
}

/// One tuple union has many carvings, and they are one type.
///
/// A DNF axis stores a union of rectangles, and the same set of tuples can be
/// cut into rectangles more than one way. No clause-by-clause rule sees it —
/// neither carving's clauses contain the other's — so the axis needs a rewrite
/// both carvings reach.
mod tuple_carving_fusion {
    use super::*;

    /// Two rectangles that agree on every coordinate but one are one rectangle
    /// over the union of that coordinate: `{A,C} ∨ {B,C}` is exactly
    /// `{A∨B, C}`. This is the shape a tagged-union ladder grows in, so fusing
    /// it turns width growth into depth growth.
    #[test]
    fn two_carvings_of_one_tuple_union_intern_once() {
        let mut t = Types::new();
        let int = t.int();
        let ints = t.list(int);
        let false_ = t.bool_lit(false);
        let true_ = t.bool_lit(true);

        let carved = {
            let with_false = t.tuple(&[ints, false_]);
            let with_true = t.tuple(&[ints, true_]);
            t.union(with_false, with_true)
        };
        let fused = {
            let either = t.union(false_, true_);
            t.tuple(&[ints, either])
        };
        assert_eq!(
            carved,
            fused,
            "one union of pairs, one interned id: got {} vs {}",
            t.display(&carved),
            t.display(&fused)
        );
        assert_eq!(t.descr(&carved).tuples.len(), 1, "and it is one rectangle");
    }

    /// Two carvings that differ in BOTH coordinates meet only by widening a
    /// coordinate to the axis union and keeping the step while the rectangle
    /// stays inside that union. The extra pair `{[], []}` the second carving
    /// names is already in the first carving's own first rectangle.
    #[test]
    fn two_carvings_that_overlap_differently_intern_once() {
        let mut t = Types::new();
        let int = t.int();
        let ints = t.list(int);
        let empty = t.empty_list();
        let non_empty = t.non_empty_list(int);

        let narrow = {
            let left = t.tuple(&[ints, empty]);
            let right = t.tuple(&[empty, non_empty]);
            t.union(left, right)
        };
        let wide = {
            let left = t.tuple(&[ints, empty]);
            let right = t.tuple(&[empty, ints]);
            t.union(left, right)
        };
        assert!(t.is_equivalent(&narrow, &wide), "the two carvings denote one set");
        assert_eq!(
            narrow,
            wide,
            "one denotation, one interned id: got {} vs {}",
            t.display(&narrow),
            t.display(&wide)
        );
    }
}

/// One absorber for every axis a denotation fully describes.
///
/// The callable axis is not among them; `types::axis` states why.
mod clause_absorption {
    use super::*;

    /// A clause no SINGLE sibling contains, but the two of them together do.
    /// This is what union coverage buys over pairwise containment, and it is
    /// the case a per-axis subsumption rule cannot see.
    #[test]
    fn a_clause_two_siblings_cover_between_them_is_dropped() {
        let mut t = Types::new();
        let int = t.int();
        let bin = t.str_t();
        let float = t.float();
        let int_or_bin = t.union(int, bin);

        // {int|binary, float} is inside {int, float} ∨ {binary, float} and
        // inside neither alone.
        let covered = t.tuple(&[int_or_bin, float]);
        let left = t.tuple(&[int, float]);
        let right = t.tuple(&[bin, float]);
        assert!(!t.is_subtype(&covered, &left) && !t.is_subtype(&covered, &right));

        let siblings = t.union(left, right);
        let joined = t.union(siblings, covered);
        assert_eq!(
            t.descr(&joined).tuples.len(),
            1,
            "the two siblings fuse and swallow the clause: {}",
            t.display(&joined)
        );
        assert!(t.is_equivalent(&joined, &siblings));

        // A list that admits `[]` is inside `[] ∨ non_empty_list(int)` and
        // inside neither alone.
        let empty = t.empty_list();
        let non_empty = t.non_empty_list(int);
        let whole = t.list(int);
        assert!(!t.is_subtype(&whole, &empty) && !t.is_subtype(&whole, &non_empty));
        let shapes = t.union(empty, non_empty);
        assert_eq!(shapes, whole, "the two shapes ARE the possibly-empty list");
    }

    /// An axis whose clauses between them cover it IS its top, and there is ONE
    /// spelling of that top: the contentless clause, the same one `Descr::any()`
    /// writes. A second spelling would be a second identity for one set.
    #[test]
    fn an_axis_its_clauses_cover_becomes_the_contentless_clause() {
        let mut t = Types::new();
        let any = t.any();

        let every_list = {
            let empty = t.empty_list();
            let non_empty = t.non_empty_list(any);
            t.union(empty, non_empty)
        };
        assert_eq!(every_list, t.list(any), "one set of lists, one id");
        assert!(
            t.descr(&every_list).lists.iter().all(Conj::is_top),
            "the top is the contentless clause: {:?}",
            t.descr(&every_list).lists
        );
        assert_eq!(t.display(&every_list), "[any]", "and a type a user could write");
        assert_eq!(
            t.list_element_type(&every_list),
            any,
            "a reader projecting the element still finds one"
        );

        let every_resource = t.resource(any);
        assert!(t.descr(&every_resource).resources.iter().all(Conj::is_top));
        assert_eq!(t.display(&every_resource), "resource(any)");
        assert_eq!(t.resource_payload_type(&every_resource), Some(any));

        // A single positive clause on the other two axes is never their top:
        // a positive tuple sig fixes an arity and a positive map sig fixes a
        // tag, and both are unbounded.
        let pair = t.tuple(&[any, any]);
        assert_eq!(t.descr(&pair).tuples.len(), 1);
        assert!(!t.descr(&pair).tuples[0].pos.is_empty(), "a tuple axis keeps its sig");
        let key = MapKey::Atom("k".to_string());
        let open = t.map(&[(key, any)]);
        assert!(!t.descr(&open).maps[0].pos.is_empty(), "a map axis keeps its sig");
    }

    /// One spelling means `any` stays `any`: unioning it with a type it already
    /// contains cannot mint a second identity for the whole lattice.
    #[test]
    fn any_absorbs_what_it_already_contains() {
        let mut t = Types::new();
        let any = t.any();
        let int = t.int();
        let key = MapKey::Atom("k".to_string());
        let operands = [
            t.list(any),
            t.resource(any),
            t.list(int),
            t.tuple(&[any, any]),
            t.map(&[(key, any)]),
            t.empty_list(),
            int,
        ];
        for operand in operands {
            let joined = t.union(any, operand);
            assert_eq!(
                joined,
                any,
                "any | {} minted a second identity for the whole lattice: {}",
                t.display(&operand),
                t.display(&joined)
            );
            assert!(t.descr(&joined).looks_full(), "and it must still LOOK full");
        }
    }

    /// The list top written the long way round and the list top written as a
    /// single sig are one descriptor, so they are one id.
    #[test]
    fn the_axis_top_has_one_spelling_however_it_is_built() {
        let mut t = Types::new();
        let any = t.any();

        let by_sig = t.list(any);
        let by_shapes = {
            let empty = t.empty_list();
            let non_empty = t.non_empty_list(any);
            t.union(empty, non_empty)
        };
        let by_clause = t.intern(Descr {
            lists: vec![Conj::top()],
            ..Descr::unbranded()
        });
        assert_eq!(by_sig, by_shapes);
        assert_eq!(by_sig, by_clause, "the widest sig IS the contentless clause");

        let resource_by_sig = t.resource(any);
        let resource_by_clause = t.intern(Descr {
            resources: vec![Conj::top()],
            ..Descr::unbranded()
        });
        assert_eq!(resource_by_sig, resource_by_clause);
    }

    /// `any` has more than one descriptor when a callable axis retains a
    /// literal capture layout: `f ∨ ¬f` is every callable in two clauses, so a
    /// descriptor carrying it denotes everything without LOOKING full.
    ///
    /// A structural reading of "is this element everything" would then answer
    /// no for that spelling, `[x]` would keep its sig clause while `[any]`
    /// became the contentless one, and one set of lists would take two ids and
    /// two canonical forms — a false difference from the oracle
    /// `canon_is_faithful_over_the_full_arena_of_both_target_fixtures` exists
    /// to forbid. So the question goes to `Descr::is_full`, which falls through
    /// to the calculator, and the same rule answers the resource axis.
    #[test]
    fn an_element_that_is_any_written_another_way_still_reaches_the_axis_top() {
        let mut t = Types::new();
        let any = t.any();
        let literal = t.fn_ref_lit(ClosureTarget(3), 1);
        let every_value = {
            let rest = t.difference(any, literal);
            t.union(rest, literal)
        };
        assert_ne!(
            t.descr(&every_value).funcs.len(),
            1,
            "the reproducer needs a retained literal callable axis; got {}",
            t.display(&every_value)
        );
        assert!(t.is_equivalent(&every_value, &any), "but it must still BE any");

        let labels = |_: FnId| String::new();
        let mut canon = TyCanon::new(&labels);

        let (widest, top) = (t.list(every_value), t.list(any));
        assert_eq!(
            widest,
            top,
            "one set of lists, one id: {} vs {}",
            t.display(&widest),
            t.display(&top)
        );
        assert_eq!(canon.render(&t, widest), canon.render(&t, top));

        let (widest, top) = (t.resource(every_value), t.resource(any));
        assert_eq!(widest, top, "and one set of resources: {}", t.display(&widest));
        assert_eq!(canon.render(&t, widest), canon.render(&t, top));
    }

    /// A finite union of POSITIVE-ONLY tuple or map clauses never covers its
    /// axis: a positive tuple sig fixes an arity and a positive map sig fixes a
    /// tag, and both are unbounded. A clause carrying a NEGATIVE factor is a
    /// different shape — `A ∨ ¬A` is every value of the kind, whatever `A` is —
    /// and no structural rule reads it, so the exact calculator question
    /// decides. All four axes then reach the one spelling of their top.
    #[test]
    fn a_clause_and_its_complement_are_the_whole_axis() {
        let mut t = Types::new();
        let any = t.any();
        let int = t.int();

        let every_tuple = t.intern(Descr {
            tuples: vec![Conj::top()],
            ..Descr::unbranded()
        });
        let pair = t.tuple(&[any, any]);
        let carved = t.difference(every_tuple, pair);
        let joined = t.union(carved, pair);
        assert_eq!(
            joined,
            every_tuple,
            "the pairs and everything that is not a pair are every tuple: {}",
            t.display(&joined)
        );

        let every_map = t.intern(Descr {
            maps: vec![Conj::top()],
            ..Descr::unbranded()
        });
        let open = t.map(&[(MapKey::Atom("k".to_string()), any)]);
        let carved = t.difference(every_map, open);
        let joined = t.union(carved, open);
        assert_eq!(joined, every_map, "got {}", t.display(&joined));

        let every_list = t.list(any);
        let ints = t.list(int);
        let carved = t.difference(every_list, ints);
        let joined = t.union(carved, ints);
        assert_eq!(joined, every_list, "got {}", t.display(&joined));

        let every_resource = t.resource(any);
        let int_resource = t.resource(int);
        let carved = t.difference(every_resource, int_resource);
        let joined = t.union(carved, int_resource);
        assert_eq!(joined, every_resource, "got {}", t.display(&joined));
    }

    /// Absorption rewrites a descriptor to a semantically equal one, and
    /// "equal" means equal under the relation the calculator answers with. On
    /// the resource axis that relation is narrower than reading a resource as
    /// a set of payloads: the kernel decides a resource clause carrying
    /// negatives by asking whether a SINGLE negative swallows the payload
    /// (`emptiness::resource_clause_empty`), never whether their union does.
    /// So `resource(:a|:b)` is NOT inside
    /// `resource(:a|:c) ∨ resource(:b|:c)`, and an axis rule that folded the
    /// payloads would drop it and leave a union that does not contain its own
    /// operand.
    #[test]
    fn a_resource_union_keeps_a_clause_no_single_sibling_contains() {
        let mut t = Types::new();
        let a = t.atom_lit("a");
        let b = t.atom_lit("b");
        let c = t.atom_lit("c");
        let (ab, ac, bc) = (t.union(a, b), t.union(a, c), t.union(b, c));
        let (rab, rac, rbc) = (t.resource(ab), t.resource(ac), t.resource(bc));

        let siblings = t.union(rac, rbc);
        assert!(
            !t.is_subtype(&rab, &siblings),
            "the calculator's own relation: {} is not inside {}",
            t.display(&rab),
            t.display(&siblings)
        );

        let joined = t.union(siblings, rab);
        assert_eq!(t.descr(&joined).resources.len(), 3, "got {}", t.display(&joined));
        assert!(
            t.is_subtype(&rab, &joined),
            "a union must contain the operand it was built from"
        );
    }

    /// The other half of the same rule: one sibling containing the clause
    /// alone is exactly when a resource clause is absorbed, and it still is.
    #[test]
    fn a_resource_clause_one_sibling_contains_is_dropped() {
        let mut t = Types::new();
        let a = t.atom_lit("a");
        let b = t.atom_lit("b");
        let c = t.atom_lit("c");
        let ab = t.union(a, b);
        let abc = t.union(ab, c);
        let (rab, rabc) = (t.resource(ab), t.resource(abc));

        let joined = t.union(rab, rabc);
        assert_eq!(joined, rabc, "got {}", t.display(&joined));
    }

    /// And the axis top follows the same relation. `resource(int)` and
    /// `resource(not int)` partition the payloads between them, but under the
    /// kernel's containment their union is not every resource, so the axis
    /// does not saturate and keeps both clauses.
    #[test]
    fn two_resource_clauses_that_partition_the_payload_are_not_every_resource() {
        let mut t = Types::new();
        let any = t.any();
        let int = t.int();
        let not_int = t.difference(any, int);
        let split = {
            let lhs = t.resource(int);
            let rhs = t.resource(not_int);
            t.union(lhs, rhs)
        };
        assert_eq!(t.descr(&split).resources.len(), 2, "got {}", t.display(&split));

        let every_resource = t.resource(any);
        assert!(
            !t.is_subtype(&every_resource, &split),
            "the calculator says the split is not every resource, so the axis must not say it is"
        );
    }
}

/// A clause is its factor SET: `A ∧ B` and `B ∧ A` are one clause.
///
/// `Conj::pos` grows as the clause product walks its operands, so an
/// intersection whose factors cannot merge into one signature records them in
/// arrival order. Two arrivals then reach the interner as two different
/// `Vec<Conj<_>>`, hash to two different `Descr`s, and are handed two `Ty`s for
/// one set of values — the same schedule dependence clause order carries, one
/// level down.
mod clause_factor_order {
    use super::*;

    /// Two arrows of different arity cannot merge into one signature, so their
    /// meet keeps both as factors of one clause — an overload, and inhabited.
    #[test]
    fn two_factor_orders_of_one_intersection_intern_once() {
        let mut t = Types::new();
        let int = t.int();
        let unary = t.arrow(&[int], int);
        let binary = t.arrow(&[int, int], int);

        let forward = t.intersect(unary, binary);
        let backward = t.intersect(binary, unary);

        let clauses = &t.descr(&forward).funcs;
        assert_eq!(clauses.len(), 1, "one clause");
        assert_eq!(clauses[0].pos.len(), 2, "holding both arrows as factors");
        assert_eq!(
            forward,
            backward,
            "one denotation, one interned id: got {} vs {}",
            t.display(&forward),
            t.display(&backward)
        );
    }
}

/// fz-kdt.198 — the documented brand law, as pins.
///
/// `.agent/docs/set-theoretic-types.md` states it in one line: `utf8 <:
/// binary` because a brand is a nominal REFINEMENT of its inner — the same
/// structure, with the `brands` slot narrowed — while a plain `binary` is not
/// a `utf8` because its slot is unconstrained. Every consumer of the lattice
/// inherits the direction: a `@spec` position declared `binary` must accept a
/// `utf8` argument, and a position declared `utf8` must reject a bare
/// `binary`.
mod brand_lattice_law {
    use super::*;

    fn meters(t: &mut Types) -> Ty {
        let int = t.int();
        t.mint_brand(int, "Meters")
    }

    fn feet(t: &mut Types) -> Ty {
        let int = t.int();
        t.mint_brand(int, "Feet")
    }

    fn utf8(t: &mut Types) -> Ty {
        let bin = t.str_t();
        t.mint_brand(bin, "utf8")
    }

    #[test]
    fn a_brand_is_a_subtype_of_its_inner() {
        let mut t = Types::new();
        let int = t.int();
        let meters = meters(&mut t);
        assert!(
            t.is_subtype(&meters, &int),
            "Meters refines int, so it is inside int; got Meters = {}",
            t.display(&meters)
        );
    }

    #[test]
    fn the_inner_is_not_a_subtype_of_the_brand() {
        let mut t = Types::new();
        let int = t.int();
        let meters = meters(&mut t);
        assert!(
            !t.is_subtype(&int, &meters),
            "a bare int lacks the tag, so it is NOT a Meters; got Meters = {}",
            t.display(&meters)
        );
    }

    #[test]
    fn utf8_is_a_subtype_of_binary() {
        let mut t = Types::new();
        let bin = t.str_t();
        let utf8 = utf8(&mut t);
        assert!(t.is_subtype(&utf8, &bin), "utf8 = {}", t.display(&utf8));
    }

    #[test]
    fn binary_is_not_a_subtype_of_utf8() {
        let mut t = Types::new();
        let bin = t.str_t();
        let utf8 = utf8(&mut t);
        assert!(!t.is_subtype(&bin, &utf8), "utf8 = {}", t.display(&utf8));
    }

    /// One value carries at most one brand — the language rule — so two brands
    /// over one inner are lattice-disjoint. `Positive and Even` is never,
    /// silently; there is no intersection type expression to write it with.
    #[test]
    fn two_brands_of_one_inner_are_disjoint() {
        let mut t = Types::new();
        let meters = meters(&mut t);
        let feet = feet(&mut t);
        let met = t.intersect(meters, feet);
        assert!(t.is_empty(&met), "Meters and Feet met at {}", t.display(&met));
        assert!(t.is_disjoint(&meters, &feet));
    }

    /// Subtracting a brand from its inner leaves the un-branded ints (and
    /// every OTHER brand of int) — it must not empty the inner.
    #[test]
    fn subtracting_a_brand_from_its_inner_leaves_the_inner() {
        let mut t = Types::new();
        let int = t.int();
        let meters = meters(&mut t);
        let rest = t.difference(int, meters);
        assert!(
            !t.is_empty(&rest),
            "int minus Meters must still hold a bare int; got {}",
            t.display(&rest)
        );
    }

    #[test]
    fn a_brand_is_equivalent_only_to_itself() {
        let mut t = Types::new();
        let int = t.int();
        let a = meters(&mut t);
        let b = meters(&mut t);
        assert_eq!(a, b, "one brand over one inner interns once");
        assert!(t.is_equivalent(&a, &b));
        assert!(!t.is_equivalent(&a, &int), "Meters is strictly inside int");
        let feet = feet(&mut t);
        assert!(!t.is_equivalent(&a, &feet));
    }

    /// A refinement is not a union: `Meters` denotes SOME ints, so rendering
    /// it as `int | Meters` reads as a supertype of `int`.
    #[test]
    fn a_brand_renders_as_a_refinement_not_a_union() {
        let mut t = Types::new();
        let meters = meters(&mut t);
        let shown = t.display(&meters);
        assert_eq!(shown, "Meters(int)", "a refinement wraps its inner");
    }

    /// The union of a brand and its inner is the inner: nothing is added.
    #[test]
    fn joining_a_brand_with_its_inner_is_the_inner() {
        let mut t = Types::new();
        let int = t.int();
        let meters = meters(&mut t);
        let joined = t.union(meters, int);
        assert!(
            t.is_equivalent(&joined, &int),
            "Meters | int = int; got {}",
            t.display(&joined)
        );
    }

    /// The law has to survive a structural position, because that is where a
    /// call's argument tuple meets a declared parameter tuple.
    #[test]
    fn the_law_holds_inside_a_tuple() {
        let mut t = Types::new();
        let int = t.int();
        let meters = meters(&mut t);
        let branded_pair = t.tuple(&[meters, int]);
        let plain_pair = t.tuple(&[int, int]);
        assert!(
            t.is_subtype(&branded_pair, &plain_pair),
            "{{Meters, int}} <: {{int, int}}; got {}",
            t.display(&branded_pair)
        );
        assert!(
            !t.is_subtype(&plain_pair, &branded_pair),
            "{{int, int}} is not {{Meters, int}}; got {}",
            t.display(&plain_pair)
        );
    }

    /// Typing is brand-aware; the runtime is brand-blind (fz-bsx). Both still
    /// hold with the refinement direction fixed.
    #[test]
    fn the_runtime_stays_brand_blind() {
        let mut t = Types::new();
        let bin = t.str_t();
        let int = t.int();
        let utf8 = utf8(&mut t);
        assert!(!t.is_value_disjoint(&utf8, &bin), "== between a utf8 and a binary runs");
        assert!(t.is_value_disjoint(&utf8, &int));
        assert!(
            !t.is_disjoint(&bin, &utf8),
            "typing keeps them overlapping: a utf8 IS one of the binaries"
        );
    }

    /// fz-kdt.198 / fz-kdt.192 probe X5 — the arrow matcher at a branded
    /// argument.
    ///
    /// `({int, a}) :: a` applied to `{Meters, int}` must answer `Known` with
    /// `a := int`: `Meters` is inside `int`, so the first coordinate fits and
    /// the second binds the variable. Under the refinement law the verdict
    /// follows from the lattice rather than from an overlap accident, which is
    /// what lets fz-kdt.192 replace the pattern-derived witness with the raw
    /// argument and keep this answer.
    #[test]
    fn the_arrow_matcher_admits_a_branded_coordinate_at_its_inner() {
        let mut t = Types::new();
        let int = t.int();
        let meters = t.mint_brand(int, "Meters");
        let var = t.type_var(TypeVarId(0));
        let param = t.tuple(&[int, var]);
        let arg = t.tuple(&[meters, int]);

        let outcome = t.match_arrow(&[param], &var, &HashMap::new(), &[arg]);
        let ArrowMatch::Known { result, .. } = outcome else {
            panic!("expected Known for {{Meters, int}} at ({{int, a}}) :: a, got {outcome:?}");
        };
        assert_eq!(result, int, "a := int; got {}", t.display(&result));
    }

    /// KNOWN-WRONG PIN — the one place this encoding is not exact, owned by
    /// fz-kdt.203.
    ///
    /// A descriptor holds ONE (structure, brand-slot) rectangle and `union` is
    /// the pointwise hull of both factors. That is exact whenever the operands
    /// agree on one factor (`Meters | int = int`, `Meters | Feet`), but ANY
    /// union whose operands disagree on BOTH factors releases the slot to top
    /// and loses the brand entirely. It takes only ONE brand to reach:
    /// `utf8 | nil` is the shape every optional `@spec` is written in, and it
    /// admits a bare binary. HEAD admits the same program, so this is strictly
    /// smaller than the inverted order it replaces, and it is a missed
    /// diagnostic rather than a miscompile (brands are erased before the
    /// backend). The cure is a descriptor holding a union of rectangles — the
    /// slot pushed down onto the per-axis DNF clauses — which is a data-model
    /// change, not a patch: see fz-kdt.203, where these two `is_subtype`
    /// answers flipping to `false` is the red-first signal.
    #[test]
    fn a_union_that_disagrees_on_both_factors_releases_the_brand_slot() {
        let mut t = Types::new();
        let int = t.int();
        let bin = t.str_t();
        let meters = t.mint_brand(int, "Meters");
        let utf8 = t.mint_brand(bin, "utf8");

        // ONE brand is enough: `@spec take(utf8 | nil)` accepts a bare binary.
        let nil = t.nil();
        let optional = t.union(utf8, nil);
        assert_eq!(t.display(&optional), "binary | :nil", "the slot is released to top");
        assert!(
            t.is_subtype(&bin, &optional),
            "KNOWN-WRONG (fz-kdt.203): a bare binary is inside {}",
            t.display(&optional)
        );

        // Two brands widen the same way, pairing each slot with each structure.
        let joined = t.union(meters, utf8);
        assert_eq!(
            t.display(&joined),
            "(Meters | utf8)(int | binary)",
            "the hull pairs both slots with both structures"
        );
        assert!(t.is_subtype(&meters, &joined));
        assert!(t.is_subtype(&utf8, &joined));
        assert!(!t.is_subtype(&int, &joined));
        assert!(!t.is_subtype(&bin, &joined));
        let branded_binary = t.mint_brand(bin, "Meters");
        assert!(
            t.is_subtype(&branded_binary, &joined),
            "KNOWN-WRONG (fz-kdt.203): Meters(binary) is admitted by Meters(int) | utf8(binary)"
        );
    }
}

/// fz-kdt.198 — the rectangle algebra the refinement law rests on.
///
/// A `Descr` denotes `S x B`: the kind axes it always had, times a brand slot
/// over "brand names, plus the unbranded case". The unbranded case is the
/// element every COFINITE `FiniteSet<String>` contains and no finite one
/// names, so `FiniteSet` itself needs no change and an unbranded `int` is
/// simply a top slot. These pin the algebra's laws, the two bases
/// (`Descr::none()` vs `Descr::unbranded()`), and the places precision is
/// deliberately traded for termination.
mod brand_lattice_algebra {
    use super::super::canon::TyCanon;
    use super::*;
    use crate::fz_ir::FnId;

    fn meters(t: &mut Types) -> Ty {
        let int = t.int();
        t.mint_brand(int, "Meters")
    }

    fn feet(t: &mut Types) -> Ty {
        let int = t.int();
        t.mint_brand(int, "Feet")
    }

    fn utf8(t: &mut Types) -> Ty {
        let bin = t.str_t();
        t.mint_brand(bin, "utf8")
    }

    /// The slot is a finite/cofinite set lattice and every kind axis is a set
    /// lattice, so the product distributes componentwise.
    #[test]
    fn union_distributes_over_intersect_at_the_slot() {
        let mut t = Types::new();
        let a = meters(&mut t);
        let b = feet(&mut t);
        let c = t.int();
        let bc = t.intersect(b, c);
        let lhs = t.union(a, bc);
        let ab = t.union(a, b);
        let ac = t.union(a, c);
        let rhs = t.intersect(ab, ac);
        assert!(
            t.is_equivalent(&lhs, &rhs),
            "A|(B&C) = {} but (A|B)&(A|C) = {}",
            t.display(&lhs),
            t.display(&rhs)
        );
    }

    /// Disjoint slots subtract nothing: `Meters(int) \ utf8(binary)` is the
    /// whole `Meters(int)`.
    #[test]
    fn a_brand_survives_subtracting_a_brand_over_another_inner() {
        let mut t = Types::new();
        let m = meters(&mut t);
        let u = utf8(&mut t);
        let d = t.difference(m, u);
        assert!(t.is_equivalent(&d, &m), "got {}", t.display(&d));
    }

    /// The refinement law is not a top-level special case: it survives
    /// arbitrary nesting, which is where a call's argument meets a spec.
    #[test]
    fn the_law_survives_a_map_of_a_list_of_a_tuple() {
        let mut t = Types::new();
        let int = t.int();
        let m = meters(&mut t);
        let branded_pair = t.tuple(&[m, int]);
        let plain_pair = t.tuple(&[int, int]);
        let branded_list = t.list(branded_pair);
        let plain_list = t.list(plain_pair);
        let key = MapKey::Atom("k".to_string());
        let branded_map = t.map(&[(key.clone(), branded_list)]);
        let plain_map = t.map(&[(key, plain_list)]);
        assert!(
            t.is_subtype(&branded_map, &plain_map),
            "branded {} must be inside plain {}",
            t.display(&branded_map),
            t.display(&plain_map)
        );
        assert!(
            !t.is_subtype(&plain_map, &branded_map),
            "the bare map is NOT the branded one; got {}",
            t.display(&plain_map)
        );
    }

    /// Two cofinite slots meet at a cofinite slot naming both brands, and the
    /// result still holds every unbranded int. One wrapping, not two.
    #[test]
    fn cofinite_slots_meet() {
        let mut t = Types::new();
        let int = t.int();
        let m = meters(&mut t);
        let f = feet(&mut t);
        let not_m = t.difference(int, m);
        let not_f = t.difference(int, f);
        let both = t.intersect(not_m, not_f);
        assert!(!t.is_empty(&both), "got {}", t.display(&both));
        assert_eq!(t.display(&both), "not(Feet | Meters)(int)");
        assert!(t.is_subtype(&both, &int));
        assert!(t.is_disjoint(&both, &m));
        assert!(t.is_disjoint(&both, &f));
    }

    /// A refinement of nothing is nothing; a refinement of everything is
    /// inside everything, and strictly.
    #[test]
    fn brands_on_the_two_bases() {
        let mut t = Types::new();
        let none = t.none();
        let any = t.any();
        let branded_none = t.mint_brand(none, "X");
        let branded_any = t.mint_brand(any, "X");
        assert!(t.is_empty(&branded_none), "got {}", t.display(&branded_none));
        assert!(t.is_equivalent(&branded_none, &none));
        assert!(t.is_subtype(&branded_any, &any));
        assert!(!t.is_subtype(&any, &branded_any));
    }

    /// `mint_brand` REBRANDS — it overwrites the slot, so there is no
    /// Meters-of-Feet and no nesting. One brand per value, at the constructor.
    #[test]
    fn minting_twice_rebrands_rather_than_nesting() {
        let mut t = Types::new();
        let m = meters(&mut t);
        let refeet = t.mint_brand(m, "Feet");
        let f = feet(&mut t);
        assert_eq!(refeet, f, "minting over a brand replaces the slot");
    }

    /// A brand over a UNION inner is still ONE rectangle — "an X whose
    /// structure is an int or a binary".
    #[test]
    fn minting_over_a_union_inner() {
        let mut t = Types::new();
        let int = t.int();
        let bin = t.str_t();
        let both = t.union(int, bin);
        let x = t.mint_brand(both, "X");
        assert!(t.is_subtype(&x, &both));
        assert!(!t.is_subtype(&both, &x));
        assert_eq!(t.display(&x), "X(int | binary)");
    }

    /// ONE BOTTOM. The three descriptor shapes that reach the empty set take
    /// three different routes — `Descr::none()` empties the brand slot, a meet
    /// of two disjoint kinds empties the kind axes with the slot still at top,
    /// a meet of two brands empties the slot with the kind axes inhabited —
    /// and a tuple with an empty coordinate or a non-empty list of an empty
    /// element reaches it through a structural axis. All five denote the same
    /// set, so `Types::intern` answers them with one id.
    #[test]
    fn every_bottom_interns_once() {
        let mut t = Types::new();
        let int = t.int();
        let bin = t.str_t();
        let m = meters(&mut t);
        let f = feet(&mut t);
        let none = t.none();

        let kinds_meet = t.intersect(int, bin);
        let brands_meet = t.intersect(m, f);
        let empty_coordinate = t.tuple(&[int, none]);
        let list_of_nothing = t.non_empty_list(none);

        for (spelling, bottom) in [
            ("int and binary", kinds_meet),
            ("Meters and Feet", brands_meet),
            ("{int, none}", empty_coordinate),
            ("non-empty [none]", list_of_nothing),
        ] {
            assert!(t.is_empty(&bottom), "{spelling} denotes the empty set");
            assert_eq!(bottom, none, "{spelling} must intern as the one bottom");
        }
    }

    /// The bottom is the UNION IDENTITY.
    ///
    /// A `Descr` joins its factors pointwise, and the bottom's brand slot is
    /// EMPTY. Read pointwise that slot would say "no brand at all" and erase
    /// the other operand's — `nothing | Meters(int)` would answer `int`.
    /// `union` answers on `looks_empty()` before it joins anything, so the
    /// join keeps the inhabited operand exactly.
    #[test]
    fn the_bottom_is_the_union_identity() {
        let mut t = Types::new();
        let int = t.int();
        let nil = t.nil();
        let m = meters(&mut t);
        let none = t.none();
        for inhabited in [m, nil, int] {
            let joined = t.union(none, inhabited);
            assert_eq!(
                joined,
                inhabited,
                "nothing | {} must be {} itself, not a widening of it",
                t.display(&inhabited),
                t.display(&inhabited)
            );
            let flipped = t.union(inhabited, none);
            assert_eq!(flipped, joined, "and the join commutes");
        }
        assert_eq!(t.union(none, none), none, "a join of two nothings is the nothing");
    }

    /// `Types::is_empty` and `== none()` are one question once every provably
    /// empty descriptor interns as the bottom.
    #[test]
    fn is_empty_holds_exactly_at_the_one_bottom() {
        let mut t = Types::new();
        let int = t.int();
        let bin = t.str_t();
        let m = meters(&mut t);
        let f = feet(&mut t);
        let none = t.none();
        let any = t.any();
        let nil = t.nil();
        let kinds_meet = t.intersect(int, bin);
        let brands_meet = t.intersect(m, f);
        let pair = t.tuple(&[int, m]);
        let empty_pair = t.tuple(&[int, none]);
        for ty in [none, any, nil, int, m, kinds_meet, brands_meet, pair, empty_pair] {
            assert_eq!(
                t.is_empty(&ty),
                ty == none,
                "is_empty and the bottom identity must agree on {}",
                t.display(&ty)
            );
        }
    }

    /// The canonical form answers on emptiness before it reads any axis, so a
    /// bottom renders `none` whatever descriptor reached it. One interned
    /// bottom makes that hard to break silently, and this keeps it pinned.
    #[test]
    fn the_canon_renders_the_bottom_as_none() {
        let mut t = Types::new();
        let none = t.none();
        let labels = |_: FnId| String::new();
        let mut canon = TyCanon::new(&labels);
        assert_eq!(canon.fingerprint(&t, none).as_ref(), "fp[none]");
        assert!(
            canon.render(&t, none).ends_with("none"),
            "got {}",
            canon.render(&t, none)
        );
    }

    /// Erasing the refinement must not RESURRECT an empty type. `Meters and
    /// Feet` is empty BECAUSE its slot is, so releasing the slot to top would
    /// hand `is_value_disjoint` — the live brand-blind runtime question
    /// (fz-bsx) — a fully inhabited `int`.
    #[test]
    fn erasing_a_brand_keeps_an_empty_type_empty() {
        let mut t = Types::new();
        let int = t.int();
        let m = meters(&mut t);
        let f = feet(&mut t);
        let bottom = t.intersect(m, f);
        assert!(t.is_empty(&bottom));
        assert!(
            t.is_value_disjoint(&bottom, &int),
            "an empty type shares no runtime value with int"
        );
        assert!(t.is_value_disjoint(&bottom, &bottom));
    }

    /// `diff`'s equal-structures case is SYNTACTIC. It is exact for every
    /// shape `mint_brand` builds — the constructor clones its inner — and
    /// falls back to returning the whole minuend otherwise, which is the
    /// over-approximating side. Sound, deliberately imprecise, and the reason
    /// there is no `is_equiv` call inside `diff`.
    #[test]
    fn the_equal_structures_case_is_syntactic() {
        let mut t = Types::new();
        let int = t.int();
        let bin = t.str_t();
        let carved = t.union(int, bin);
        let branded = t.mint_brand(carved, "X");
        let exact = t.difference(carved, branded);
        assert_eq!(
            t.display(&exact),
            "not(X)(int | binary)",
            "the brand's own inner subtracts exactly"
        );
        let float = t.float();
        let wider = t.union(carved, float);
        let widened = t.difference(wider, branded);
        assert_eq!(
            t.display(&widened),
            t.display(&wider),
            "a structurally different minuend gets no slot subtraction at all"
        );
    }
}

/// The interner answers from its index before it normalizes, which is sound
/// only because a descriptor's normal form is a pure function of the
/// descriptor. Storage clause order is the part of that which had to be won:
/// a closure literal orders by its `FnId` alone, so registering the owner's
/// typed origin later cannot move a clause that is already interned.
mod normal_form_is_a_function_of_the_descriptor {
    use super::*;

    fn closure_pair(t: &mut Types) -> (Ty, Ty) {
        let low = t.closure_lit(ClosureTarget(2), Vec::new(), 1);
        let high = t.closure_lit(ClosureTarget(9), Vec::new(), 1);
        (low, high)
    }

    /// The defect this rule closes: a union of two closure literals interned
    /// BEFORE either owner registered, then registered, then unioned again.
    /// Under an origin-reading storage order the second union hit the index on
    /// its stale pre-registration form while the mirror-image union minted a
    /// fresh id — two identities for one set, decided by arrival.
    #[test]
    fn registering_an_origin_does_not_move_an_interned_clause() {
        let mut t = Types::new();
        let (low, high) = closure_pair(&mut t);

        let before = t.union(low, high);
        assert_eq!(t.union(high, low), before, "the union is a set before registration");

        t.define_test_callable(ClosureTarget(9), "a", 1);
        t.define_test_callable(ClosureTarget(2), "z", 1);

        assert_eq!(
            t.union(low, high),
            before,
            "an interned union keeps its identity when an owner registers"
        );
        assert_eq!(
            t.union(high, low),
            before,
            "and the mirror-image union reaches that same identity, not a fresh one"
        );
    }

    /// The same statement read the other way: the origins decide the ACTIVATION
    /// order, and that order is free to read them because every activation
    /// surface has registered by the time it is asked. Registration must not
    /// leak into storage, and this is the relation it is allowed to reach.
    #[test]
    fn the_activation_order_still_reads_the_registered_origin() {
        for reverse in [false, true] {
            let mut t = Types::new();
            let (low, high) = closure_pair(&mut t);
            let (ordered_first, ordered_second) = if reverse { (high, low) } else { (low, high) };
            let (first_target, second_target) = if reverse {
                (ClosureTarget(9), ClosureTarget(2))
            } else {
                (ClosureTarget(2), ClosureTarget(9))
            };
            t.define_test_callable(first_target, "same", 2);
            t.define_test_callable(second_target, "same", 10);
            let arrow = |t: &mut Types, lit: Ty| {
                let int = t.int();
                let nil = t.nil();
                let sig = ArrowSig {
                    args: vec![int],
                    ret: nil,
                    lit: t.descr(&lit).as_closure_lit().cloned(),
                };
                t.intern(Descr {
                    funcs: vec![Conj::pos_of(sig)],
                    ..Descr::unbranded()
                })
            };
            let two = arrow(&mut t, ordered_first);
            let ten = arrow(&mut t, ordered_second);
            assert_eq!(
                t.cmp_activation_ty(two, ten),
                std::cmp::Ordering::Less,
                "arity 2 precedes arity 10 numerically, whichever id was minted first"
            );
        }
    }

    /// A descriptor the index already holds costs nothing but the lookup: the
    /// absorption's containment questions are the calculator's only customer at
    /// this boundary, and on a hit none of them is asked.
    ///
    /// Joining a type with itself is what hands the boundary a descriptor it
    /// already holds: `A ∨ A = A` clause by clause, so the join rebuilds the
    /// stored descriptor exactly. Rejoining `[] ∨ non_empty_list(int)` would
    /// not — that is the list normal form's input, not its output.
    #[test]
    fn re_interning_an_indexed_descriptor_asks_the_calculator_nothing() {
        let mut t = Types::new();
        let int = t.int();
        let empty = t.empty_list();
        let non_empty = t.non_empty_list(int);

        let first = t.union(empty, non_empty);
        let after_first = t.comparison_cache_stats();

        assert_eq!(t.union(first, first), first);
        assert_eq!(
            t.comparison_cache_stats(),
            after_first,
            "the second union answers from the index without re-deriving the normal form"
        );
    }

    /// The lattice constants are not derived facts. The store interns them
    /// when it is built and hands the same ids back forever, so asking for one
    /// builds no descriptor — and their exact self-laws mint nothing and ask
    /// the calculator nothing.
    #[test]
    fn the_ids_of_lattice_constants_are_held_rather_than_re_derived() {
        let mut t = Types::new();
        let any = t.any();
        let none = t.none();
        let inventory = t.identity_inventory();
        let comparisons = t.comparison_cache_stats();

        assert_eq!(t.any(), any, "the id of a constant does not move");
        assert_eq!(t.none(), none, "the id of a constant does not move");
        assert_eq!(t.union(any, any), any, "top joined with itself is top");
        assert_eq!(t.difference(any, any), none, "top minus itself is bottom");
        assert_eq!(t.identity_inventory(), inventory, "which minted no id");
        assert_eq!(t.comparison_cache_stats(), comparisons, "and re-derived no normal form");
    }
}

/// One list normal form, applied where identity is assigned.
///
/// A `ListSig` denotes `[]` (when `empty`) together with every non-empty list
/// whose elements all lie in `elem`. Two facts follow, and both are the
/// boundary's to enforce: a union is its MEMBER SET, so folding the same
/// members in any order reaches one id; and a clause is what it DENOTES, so
/// every construction route to one denotation reaches one id.
mod list_normal_form {
    use super::*;

    fn fold(t: &mut Types, members: &[Ty]) -> Ty {
        let (first, rest) = members.split_first().expect("a union needs a member");
        rest.iter().fold(*first, |acc, member| t.union(acc, *member))
    }

    fn folded_every_way(t: &mut Types, members: &[Ty]) -> Vec<(String, Ty)> {
        let mut orders: Vec<(String, Vec<Ty>)> = vec![("forward".to_string(), members.to_vec())];
        let mut reversed = members.to_vec();
        reversed.reverse();
        orders.push(("reverse".to_string(), reversed));
        for rotation in 1..members.len() {
            let mut rotated = members.to_vec();
            rotated.rotate_left(rotation);
            orders.push((format!("rotated by {rotation}"), rotated));
        }
        orders
            .into_iter()
            .map(|(name, order)| (name, fold(t, &order)))
            .collect()
    }

    /// The witness a randomized sweep found: four list members whose forward
    /// and reverse folds reached two ids. Folded forward the union-path
    /// normalizer saw `[]` last and merged nothing; folded in reverse it saw
    /// `[]` first and widened only what had already arrived.
    #[test]
    fn one_union_of_lists_interns_once_whichever_order_it_is_folded_in() {
        let mut t = Types::new();
        let binary = t.str_t();
        let nil = t.nil();
        let binaries = t.non_empty_list(binary);
        let nils = t.non_empty_list(nil);
        let empty = t.empty_list();
        let members = vec![binaries, nils, nils, empty];

        let folds = folded_every_way(&mut t, &members);
        let (_, first) = folds[0].clone();
        for (order, got) in &folds {
            assert_eq!(
                *got,
                first,
                "{order} fold is the same union: {} vs {}",
                t.display(got),
                t.display(&first)
            );
        }
    }

    /// Four routes to `list(int)`: built directly, joined from its two
    /// fragments, carved out of a wider list by a subtraction that removes
    /// nothing, met with a wider list from the side, and substituted into.
    #[test]
    fn every_route_to_a_possibly_empty_list_interns_once() {
        let mut t = Types::new();
        let int = t.int();
        let nil = t.nil();
        let binary = t.str_t();

        let direct = t.list(int);

        let empty = t.empty_list();
        let non_empty = t.non_empty_list(int);
        let joined = t.union(empty, non_empty);

        // A non-empty list over `int` is never a non-empty list over `:nil`,
        // so this subtracts nothing at all.
        let disjoint_lists = t.non_empty_list(nil);
        let carved = t.difference(direct, disjoint_lists);

        let with_binary = t.union(direct, binary);
        let with_nil = t.union(direct, nil);
        let met = t.intersect(with_binary, with_nil);

        let var = t.type_var(TypeVarId(0));
        let template = t.list(var);
        let sigma: Sigma<Ty> = [(TypeVarId(0), int)].into_iter().collect();
        let substituted = t.instantiate(&template, &sigma);

        for (route, got) in [
            ("union", joined),
            ("difference", carved),
            ("intersect", met),
            ("substitution", substituted),
        ] {
            assert_eq!(
                got,
                direct,
                "the {route} route reaches list(int) and must intern as it: {} vs {}",
                t.display(&got),
                t.display(&direct)
            );
        }
    }

    /// `list(T) ∧ ¬[]` IS `non_empty_list(T)`, so the difference route reaches
    /// the same id the constructor does.
    #[test]
    fn every_route_to_a_non_empty_list_interns_once() {
        let mut t = Types::new();
        let int = t.int();
        let direct = t.non_empty_list(int);
        let list = t.list(int);
        let empty = t.empty_list();
        let carved = t.difference(list, empty);
        assert_eq!(
            carved,
            direct,
            "list(int) without [] is non_empty_list(int): {} vs {}",
            t.display(&carved),
            t.display(&direct)
        );

        let any = t.any();
        let any_list = t.list(any);
        let every_non_empty = t.difference(any_list, empty);
        let direct_any = t.non_empty_list(any);
        assert_eq!(
            every_non_empty,
            direct_any,
            "and the same holds at the axis top: {} vs {}",
            t.display(&every_non_empty),
            t.display(&direct_any)
        );
    }

    /// The WIDEST list has one spelling too. Removing the union path's merge
    /// would leave `[] ∨ non_empty_list(any)` a two-clause axis beside the one
    /// clause `list(any)` is built as, and the top rule above would then be
    /// reached from one of them and not the other.
    #[test]
    fn the_widest_list_interns_once_whichever_fragments_build_it() {
        let mut t = Types::new();
        let any = t.any();
        let direct = t.list(any);
        let empty = t.empty_list();
        let non_empty = t.non_empty_list(any);
        let joined = t.union(empty, non_empty);
        assert_eq!(
            joined,
            direct,
            "every list is `[]` plus every non-empty list: {} vs {}",
            t.display(&joined),
            t.display(&direct)
        );
    }

    /// The union path is a plain DNF concatenation. It owns no list rule, so
    /// it cannot make the result depend on when a member arrived.
    #[test]
    fn the_union_path_owns_no_list_normalizer() {
        let mut t = Types::new();
        let int = t.int();
        let empty = t.empty_list();
        let non_empty = t.non_empty_list(int);
        let joined = {
            let cx = t.ctx();
            cx.descr(&empty).union(cx, cx.descr(&non_empty))
        };
        assert_eq!(
            joined.lists,
            vec![
                Conj::pos_of(ListSig::empty()),
                Conj::pos_of(ListSig {
                    empty: false,
                    elem: Some(int),
                }),
            ],
            "Descr::union concatenates the two clauses and leaves them alone"
        );
        let interned = t.union(empty, non_empty);
        let list = t.list(int);
        assert_eq!(interned, list, "the boundary is what merges them");
    }

    /// The one residue: a var-bearing list DIFFERENCE is one denotation with
    /// two ids.
    ///
    /// The boundary skips element arithmetic when a clause's elements carry
    /// type variables, so `non_empty_list(α) \ non_empty_list(int)` is stored
    /// as it was built rather than as the `non_empty_list(α)` it denotes. The
    /// cure is a variable-aware meet, which the kernel does not have. Until it
    /// does, `TyCanon` reads the denotation on both and gives them one
    /// canonical form, so the oracle counts this as one denotation holding two
    /// ids -- the finding -- instead of two renderings, which would hide it.
    /// Fix the meet and this test flips: the two become one id.
    #[test]
    fn a_var_bearing_list_difference_is_one_denotation_with_two_ids() {
        let mut t = Types::new();
        let int = t.int();
        let var = t.type_var(TypeVarId(0));
        let over_var = t.non_empty_list(var);
        let over_int = t.non_empty_list(int);
        let carved = t.difference(over_var, over_int);

        assert!(
            t.is_equivalent(&carved, &over_var),
            "a variable is disjoint from int, so the subtraction removes nothing: {} vs {}",
            t.display(&carved),
            t.display(&over_var)
        );
        assert_ne!(
            carved,
            over_var,
            "but the boundary stores the clause as built: {} vs {}",
            t.display(&carved),
            t.display(&over_var)
        );

        let labels = |_: FnId| String::new();
        let mut canon = TyCanon::new(&labels);
        assert_eq!(
            canon.render(&t, carved),
            canon.render(&t, over_var),
            "and the rendering reads the denotation, so the census sees one denotation, two ids"
        );
    }

    /// A seeded sweep over list-heavy unions: whatever the members, the fold
    /// order may not decide the identity.
    #[test]
    fn list_heavy_unions_intern_once_whichever_order_they_are_folded_in() {
        let mut rng = 0x5eed_1234_u64;
        let mut next = move || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng
        };
        let mut t = Types::new();
        let leaves: Vec<Ty> = {
            let int = t.int();
            let binary = t.str_t();
            let nil = t.nil();
            let ok = t.atom_lit("ok");
            let pair = t.tuple(&[int, binary]);
            vec![int, binary, nil, ok, pair]
        };

        for case in 0..400_u64 {
            let count = 2 + (next() % 4) as usize;
            let members: Vec<Ty> = (0..count)
                .map(|_| {
                    let leaf = leaves[(next() % leaves.len() as u64) as usize];
                    match next() % 5 {
                        0 => t.empty_list(),
                        1 => t.list(leaf),
                        2 => t.non_empty_list(leaf),
                        3 => {
                            let inner = t.list(leaf);
                            t.non_empty_list(inner)
                        }
                        _ => t.tuple(&[leaf, leaf]),
                    }
                })
                .collect();
            let folds = folded_every_way(&mut t, &members);
            let (_, first) = folds[0].clone();
            for (order, got) in &folds {
                assert_eq!(
                    *got,
                    first,
                    "case {case}: the {order} fold of {:?} reached a second id: {} vs {}",
                    members.iter().map(|m| t.display(m)).collect::<Vec<_>>(),
                    t.display(got),
                    t.display(&first)
                );
            }
        }
    }
}
