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
