use super::*;
use crate::compiler2::types::descr::union_of;

/// `int | [reference]`: the body of `mu X. int | [X]` once `reference` names
/// the node itself.
fn int_or_list_of(reference: ComponentRef) -> DescrOf<ComponentRef> {
    union_of(&DescrOf::int(), &DescrOf::list_of(reference))
}

/// The same body with one more list alternative appended.
fn with_list_alternative(body: DescrOf<ComponentRef>, reference: ComponentRef) -> DescrOf<ComponentRef> {
    union_of(&body, &DescrOf::list_of(reference))
}

/// `mu X. int | [X]`, the handle every test here mentions.
fn int_list_handle(types: &mut Types) -> Ty {
    types.intern_regular_component(1, |nodes| vec![int_or_list_of(nodes[0])])[0]
}

fn child_types(types: &Types, ty: Ty) -> Vec<Ty> {
    let mut children = Vec::new();
    visit_children(types.descr(&ty), |child| children.push(child));
    children.sort_unstable();
    children.dedup();
    children
}

#[test]
fn an_empty_recursive_body_canonicalizes_to_none_before_it_receives_an_identity() {
    let mut t = Types::new();
    let atom = t.atom_lit("b");
    let before = t.identity_inventory();
    let recursive = t.intern_regular_component(1, |nodes| {
        let mut body = DescrOf::unbranded();
        body.cases[0].structure.tuples = vec![Conj {
            pos: vec![
                TupleSigOf { elems: vec![nodes[0]] },
                TupleSigOf {
                    elems: vec![ComponentRef::Published(atom)],
                },
            ],
            neg: vec![],
        }];
        vec![body]
    })[0];

    assert_eq!(
        recursive,
        t.none(),
        "X = {{X}} ∩ {{:b}} has no finite value and must not mint a regular identity"
    );
    assert_eq!(
        t.identity_inventory(),
        before,
        "local proof states never enter the interner"
    );
}

#[test]
fn pruning_an_empty_recursive_sibling_keeps_the_live_recursive_identity_canonical() {
    let mut t = Types::new();
    let atom_b = t.atom_lit("b");
    let expected = t.intern_regular_component(1, |nodes| {
        vec![union_of(&DescrOf::atom_lit("a"), &DescrOf::tuple_of(vec![nodes[0]]))]
    })[0];

    let roots = t.intern_regular_bodies(vec![
        union_of(
            &DescrOf::atom_lit("a"),
            &union_of(
                &DescrOf::tuple_of(vec![ComponentRef::local(0)]),
                &DescrOf::tuple_of(vec![ComponentRef::local(1)]),
            ),
        ),
        {
            let mut body = DescrOf::unbranded();
            body.cases[0].structure.tuples = vec![Conj {
                pos: vec![
                    TupleSigOf {
                        elems: vec![ComponentRef::local(1)],
                    },
                    TupleSigOf {
                        elems: vec![ComponentRef::Published(atom_b)],
                    },
                ],
                neg: vec![],
            }];
            body
        },
    ]);

    assert_eq!(roots[0], expected, "{{Y}} contributes no alternative once Y is empty");
    assert_eq!(roots[1], t.none(), "Y is the empty recursive branch");
    assert_eq!(
        child_types(&t, roots[0]),
        vec![roots[0]],
        "the canonical live body keeps only its own recursive child"
    );
}

#[test]
fn a_cluster_that_denotes_a_mentioned_handle_resolves_to_that_handle() {
    let mut t = Types::new();
    let handle = int_list_handle(&mut t);
    let restated = t.intern_regular_component(1, |nodes| {
        vec![with_list_alternative(
            int_or_list_of(ComponentRef::Published(handle)),
            nodes[0],
        )]
    })[0];

    assert_eq!(
        restated, handle,
        "a cluster whose only states are states of a handle it mentions is that handle"
    );
}

#[test]
fn clause_order_does_not_change_which_handle_a_cluster_resolves_to() {
    let mut t = Types::new();
    let handle = int_list_handle(&mut t);
    let restated = t.intern_regular_component(1, |nodes| {
        vec![with_list_alternative(
            int_or_list_of(nodes[0]),
            ComponentRef::Published(handle),
        )]
    })[0];

    assert_eq!(
        restated, handle,
        "the alternative that mentions the handle resolves wherever the builder wrote it"
    );
}

#[test]
fn union_with_a_cluster_that_denotes_a_handle_is_that_handle() {
    let mut t = Types::new();
    let handle = int_list_handle(&mut t);
    let restated = t.intern_regular_component(1, |nodes| {
        vec![with_list_alternative(
            int_or_list_of(ComponentRef::Published(handle)),
            nodes[0],
        )]
    })[0];

    assert_eq!(
        t.union(handle, restated),
        handle,
        "one id per denotation makes union idempotent on equal recursive types"
    );
}

#[test]
fn a_handle_mentioned_two_nodes_deep_resolves_the_whole_cluster() {
    let mut t = Types::new();
    let handle = int_list_handle(&mut t);
    let roots = t.intern_regular_component(2, |nodes| {
        vec![
            int_or_list_of(nodes[1]),
            with_list_alternative(int_or_list_of(ComponentRef::Published(handle)), nodes[0]),
        ]
    });

    assert_eq!(
        roots,
        vec![handle, handle],
        "resolution is a property of the whole refinement, not of the node that names the handle"
    );
}

#[test]
fn a_cluster_that_only_mentions_a_handle_keeps_its_own_identity() {
    let mut t = Types::new();
    let handle = int_list_handle(&mut t);
    let distinct = t.intern_regular_component(1, |nodes| {
        vec![with_list_alternative(
            union_of(
                &DescrOf::atom_lit("other"),
                &DescrOf::list_of(ComponentRef::Published(handle)),
            ),
            nodes[0],
        )]
    })[0];

    assert_ne!(
        distinct, handle,
        "a cluster that denotes something else keeps an id of its own"
    );
    assert_eq!(
        child_types(&t, distinct),
        {
            let mut expected = vec![handle, distinct];
            expected.sort_unstable();
            expected
        },
        "the new body names the handle it mentions instead of copying its states"
    );
}

/// Repeating a fixed exclusion must not leave a second spelling of the same
/// recursive child. The second subtraction is redundant:
///
/// ```text
/// X = :a | {X}
/// once  = {X} \ {:a}
/// twice = once \ {:a}
/// ```
///
/// The two result nodes are deliberately written as separate raw descriptor
/// equations, so this exercises Boolean normalization before regular
/// identities are assigned.
#[test]
fn redundant_fixed_tuple_exclusions_of_a_recursive_child_intern_once() {
    let mut types = Types::new();
    let a = types.atom_lit("a");
    let live = union_of(
        &DescrOf::atom_lit("a"),
        &DescrOf::tuple_of(vec![ComponentRef::local(0)]),
    );
    let excluded = DescrOf::tuple_of(vec![ComponentRef::Published(a)]);
    let once = DescrOf::tuple_of(vec![ComponentRef::local(0)]).diff(&excluded);
    let twice = once.diff(&excluded);
    let roots = types.intern_regular_bodies(vec![live, once, twice]);

    assert!(types.is_equivalent(&roots[1], &roots[2]));
    assert_eq!(
        roots[1], roots[2],
        "repeating the same fixed child exclusion must not mint another regular identity"
    );
}

/// A two-coordinate product exclusion has the exact factored spelling
/// `(X \\ :a) × Y | X × (Y \\ :b)`. Both `X` and `Y` recurse, so this
/// is a regular-graph Boolean operation, never an acyclic simplification.
#[test]
fn a_two_coordinate_fixed_tuple_exclusion_equals_its_factored_recursive_union() {
    let mut types = Types::new();
    let a = types.atom_lit("a");
    let b = types.atom_lit("b");
    let x = union_of(
        &DescrOf::atom_lit("a"),
        &DescrOf::tuple_of(vec![ComponentRef::local(0)]),
    );
    let y = union_of(
        &DescrOf::atom_lit("b"),
        &DescrOf::tuple_of(vec![ComponentRef::local(1)]),
    );
    let pair = DescrOf::tuple_of(vec![ComponentRef::local(0), ComponentRef::local(1)]);
    let excluded = DescrOf::tuple_of(vec![ComponentRef::Published(a), ComponentRef::Published(b)]);
    let excluded_pair = pair.diff(&excluded);
    let x_without_a = x.diff(&types.regular_published(a));
    let y_without_b = y.diff(&types.regular_published(b));
    let factored = union_of(
        &DescrOf::tuple_of(vec![ComponentRef::local(3), ComponentRef::local(1)]),
        &DescrOf::tuple_of(vec![ComponentRef::local(0), ComponentRef::local(4)]),
    );
    let roots = types.intern_regular_bodies(vec![x, y, excluded_pair, x_without_a, y_without_b, factored]);

    assert!(types.is_equivalent(&roots[2], &roots[5]));
    assert_eq!(
        roots[2], roots[5],
        "a two-coordinate fixed exclusion must share the factored union's regular identity"
    );
}

/// Public Boolean operations over regular handles must enter the regular
/// equation forest once, rather than recursively rebuilding the same pair
/// while ground tuple normalization descends through it.
#[test]
fn direct_difference_of_disjoint_recursive_types_is_the_left_handle() {
    let mut types = Types::new();
    let left = types.intern_regular_component(1, |nodes| {
        vec![union_of(&DescrOf::atom_lit("a"), &DescrOf::tuple_of(vec![nodes[0]]))]
    })[0];
    let right = types.intern_regular_component(1, |nodes| {
        vec![union_of(&DescrOf::atom_lit("b"), &DescrOf::tuple_of(vec![nodes[0]]))]
    })[0];

    let difference = types.difference(left, right);
    assert!(types.is_equivalent(&difference, &left));
    assert_eq!(
        difference, left,
        "disjoint recursive difference keeps the left identity"
    );
}

/// Neither operand subsumes the other, so the public intersection must build
/// its product graph. Its sole seed is `:b`, which makes the exact answer the
/// recursive `:b | {…}` family.
#[test]
fn direct_intersection_of_overlapping_recursive_types_is_the_shared_family() {
    let mut types = Types::new();
    let left = types.intern_regular_component(1, |nodes| {
        vec![union_of(
            &union_of(&DescrOf::atom_lit("a"), &DescrOf::atom_lit("b")),
            &DescrOf::tuple_of(vec![nodes[0]]),
        )]
    })[0];
    let right = types.intern_regular_component(1, |nodes| {
        vec![union_of(
            &union_of(&DescrOf::atom_lit("b"), &DescrOf::atom_lit("c")),
            &DescrOf::tuple_of(vec![nodes[0]]),
        )]
    })[0];
    let expected = types.intern_regular_component(1, |nodes| {
        vec![union_of(&DescrOf::atom_lit("b"), &DescrOf::tuple_of(vec![nodes[0]]))]
    })[0];

    let intersection = types.intersect(left, right);
    assert!(types.is_equivalent(&intersection, &expected));
    assert_eq!(
        intersection, expected,
        "the shared recursive seed is the one regular intersection identity"
    );
}

/// Empty-list filtering is a fixed mask on the list axis, even when the
/// element language is recursive.  Its two ordinary spellings must retain
/// the pre-existing non-empty-list identity.
#[test]
fn recursive_list_empty_and_non_empty_masks_reuse_the_non_empty_identity() {
    let mut types = Types::new();
    let element = types.intern_regular_component(1, |nodes| {
        vec![union_of(&DescrOf::atom_lit("a"), &DescrOf::tuple_of(vec![nodes[0]]))]
    })[0];
    let list = types.list(element);
    let non_empty = types.non_empty_list(element);
    let empty = types.empty_list();

    let without_empty = types.difference(list, empty);
    let with_non_empty = types.intersect(list, non_empty);

    for (actual, spelling) in [
        (without_empty, "list(X) \\ []"),
        (with_non_empty, "list(X) & non_empty_list(X)"),
    ] {
        assert!(
            types.is_equivalent(&actual, &non_empty),
            "{spelling} keeps the same recursive list language"
        );
        assert_eq!(actual, non_empty, "{spelling} must reuse non_empty_list(X)'s identity");
    }
}

/// Resource subtraction must restrict its recursive payload rather than
/// approximate the resource as a whole.  Here `X = :a | {X}`, so the exact
/// residual is `resource(X \\ :a) = resource({X})`.
#[test]
fn recursive_resource_difference_reuses_the_filtered_payload_identity() {
    let mut types = Types::new();
    let a = types.atom_lit("a");
    let x = types.intern_regular_component(1, |nodes| {
        vec![union_of(&DescrOf::atom_lit("a"), &DescrOf::tuple_of(vec![nodes[0]]))]
    })[0];
    let resource_x = types.resource(x);
    let resource_a = types.resource(a);
    let actual = types.difference(resource_x, resource_a);
    let filtered = types.difference(x, a);
    let expected = types.resource(filtered);

    assert!(types.is_equivalent(&actual, &expected));
    assert_eq!(
        actual, expected,
        "resource(X) \\ resource(:a) must be resource(X \\ :a)"
    );
}

/// The list mask must normalize through a local recursive reference, not only
/// after its child has become a published handle.  On paper:
///
/// ```text
/// X = :a | list(Y)
/// Y = X \\ []
///   = :a | non_empty_list(Y)
/// ```
///
/// The second spelling names that fixed-point graph directly. Both roots
/// must reuse its identities.
#[test]
fn a_local_recursive_list_mask_equals_its_explicit_non_empty_feedback_graph() {
    let mut types = Types::new();
    let x = union_of(&DescrOf::atom_lit("a"), &DescrOf::list_of(ComponentRef::local(1)));
    let masked_y = x.diff(&DescrOf::empty_list());
    let masked = types.intern_regular_bodies(vec![x, masked_y]);

    let explicit_x = union_of(&DescrOf::atom_lit("a"), &DescrOf::list_of(ComponentRef::local(1)));
    let explicit_y = union_of(
        &DescrOf::atom_lit("a"),
        &DescrOf::non_empty_list_of(ComponentRef::local(1)),
    );
    let explicit = types.intern_regular_bodies(vec![explicit_x, explicit_y]);

    for (actual, expected) in masked.into_iter().zip(explicit) {
        assert!(types.is_equivalent(&actual, &expected));
        assert_eq!(
            actual, expected,
            "the local list mask must share the explicit feedback identity"
        );
    }
}
