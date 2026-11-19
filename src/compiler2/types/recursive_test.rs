use super::*;
use crate::compiler2::types::Types;

/// `T = nil | {int, T, T}`: a binary tree of ints.
fn tree(t: &mut Types) -> Ty {
    t.recursive(1, |t, me| {
        let (nil, int) = (t.nil(), t.int());
        let node = t.tuple(&[int, me[0], me[0]]);
        vec![t.union(nil, node)]
    })[0]
}

/// `R = :start | {int, R}`: what `build(n) = {n, build(n - 1)}` returns.
fn chain(t: &mut Types) -> Ty {
    t.recursive(1, |t, me| {
        let (start, int) = (t.atom_lit("start"), t.int());
        let link = t.tuple(&[int, me[0]]);
        vec![t.union(start, link)]
    })[0]
}

#[test]
fn a_recursive_type_names_itself_where_it_repeats() {
    let mut t = Types::new();
    let tree = tree(&mut t);
    let (int, any) = (t.int(), t.any());
    let node_shape = t.tuple(&[any, any, any]);
    let node = t.tuple(&[int, tree, tree]);
    assert_eq!(
        t.intersect(tree, node_shape),
        node,
        "a tree that is a tuple is a node whose children are trees"
    );
    assert!(!t.is_empty(&tree));
}

#[test]
fn an_equation_with_no_way_out_denotes_nothing() {
    let mut t = Types::new();
    let endless = t.recursive(1, |t, me| {
        let int = t.int();
        vec![t.tuple(&[int, me[0]])]
    })[0];
    assert_eq!(
        endless,
        t.none(),
        "a value is finite, so {{int, X}} with nothing else in X has no value"
    );
}

#[test]
fn one_meaning_has_one_id_however_it_is_written() {
    let mut t = Types::new();
    let first = tree(&mut t);
    let second = tree(&mut t);
    assert_eq!(first, second, "the same equation built twice");
    let spelled_out = t.recursive(1, |t, me| {
        let (nil, int) = (t.nil(), t.int());
        let node = t.tuple(&[int, me[0], me[0]]);
        let leaf = t.tuple(&[int, nil, nil]);
        let some = t.union(nil, leaf);
        vec![t.union(some, node)]
    })[0];
    assert_eq!(
        first, spelled_out,
        "a leaf node is already a node whose children are trees"
    );
    let twins = t.recursive(2, |t, me| {
        let (nil, int) = (t.nil(), t.int());
        let a = t.tuple(&[int, me[1], me[1]]);
        let b = t.tuple(&[int, me[0], me[0]]);
        vec![t.union(nil, a), t.union(nil, b)]
    });
    assert_eq!(twins, vec![first, first], "two names for one tree are one tree");
}

#[test]
fn a_union_that_adds_nothing_returns_the_recursive_type() {
    let mut t = Types::new();
    let tree = tree(&mut t);
    let (nil, int) = (t.nil(), t.int());
    assert_eq!(t.union(tree, nil), tree);
    let node = t.tuple(&[int, tree, tree]);
    assert_eq!(t.union(tree, node), tree, "one unfolding is already inside");
    let leaf = t.tuple(&[int, nil, nil]);
    assert_eq!(t.union(tree, leaf), tree);
    let unfolded = t.union(nil, node);
    assert_eq!(unfolded, tree, "nil | {{int, T, T}} is T");
}

#[test]
fn subtyping_follows_the_equation() {
    let mut t = Types::new();
    let tree = tree(&mut t);
    let (nil, int, any) = (t.nil(), t.int(), t.any());
    let node = t.tuple(&[int, tree, tree]);
    assert!(t.is_subtype(&node, &tree));
    let shallow = t.tuple(&[int, any, any]);
    let shallow = t.union(nil, shallow);
    assert!(
        t.is_subtype(&tree, &shallow),
        "every tree is nil or a 3-tuple led by an int"
    );
    assert!(!t.is_subtype(&shallow, &tree), "{{1, :x, :x}} is not a tree");
    let tuples = t.tuple_top();
    assert!(!t.is_subtype(&tree, &tuples), "nil is a tree");
}

#[test]
fn subtyping_between_two_recursive_types_terminates() {
    let mut t = Types::new();
    let tree = tree(&mut t);
    // Trees whose leaves all sit at an even depth.
    let even = t.recursive(2, |t, me| {
        let (nil, int) = (t.nil(), t.int());
        let even = t.tuple(&[int, me[1], me[1]]);
        let odd = t.tuple(&[int, me[0], me[0]]);
        vec![t.union(nil, even), odd]
    })[0];
    assert!(t.is_subtype(&even, &tree));
    assert!(
        !t.is_subtype(&tree, &even),
        "{{1, nil, nil}} has its leaves at depth one"
    );
    assert_eq!(t.intersect(tree, even), even);
    assert_eq!(t.union(tree, even), tree);
}

#[test]
fn a_list_can_hold_itself() {
    let mut t = Types::new();
    let nested = t.recursive(1, |t, me| {
        let int = t.int();
        let list = t.list(me[0]);
        vec![t.union(int, list)]
    })[0];
    let int = t.int();
    let one = t.list(int);
    let deeper = t.list(one);
    assert!(t.is_subtype(&deeper, &nested), "[[1]] is an int or a list of them");
    let atom = t.atom_lit("x");
    let wrong = t.list(atom);
    assert!(!t.is_subtype(&wrong, &nested));
}

#[test]
fn a_cycle_through_two_shapes_is_one_cluster() {
    let mut t = Types::new();
    let chain = chain(&mut t);
    let pair = t.recursive(2, |t, me| {
        let (start, int) = (t.atom_lit("start"), t.int());
        let a = t.tuple(&[int, me[1]]);
        let b = t.tuple(&[int, me[0]]);
        vec![t.union(start, a), t.union(start, b)]
    });
    assert_eq!(pair, vec![chain, chain]);
    let alternating = t.recursive(2, |t, me| {
        let (start, int, x) = (t.atom_lit("start"), t.int(), t.atom_lit("x"));
        let a = t.tuple(&[int, me[1]]);
        let b = t.tuple(&[x, me[0]]);
        vec![t.union(start, a), b]
    });
    assert_ne!(alternating[0], alternating[1]);
    assert!(
        !t.is_subtype(&alternating[0], &chain),
        "{{:x, ...}} is not a chain link"
    );
}

#[test]
fn a_recursive_type_is_displayed_with_its_binder() {
    let mut t = Types::new();
    let tree = tree(&mut t);
    assert_eq!(t.display(&tree), "μt. :nil | {int, t, t}");
    let int = t.int();
    let held = t.tuple(&[int, tree]);
    assert_eq!(t.display(&held), "{int, μt. :nil | {int, t, t}}");
}

#[test]
fn recursive_types_have_a_total_storage_order() {
    let mut t = Types::new();
    let tree = tree(&mut t);
    let chain = chain(&mut t);
    let forward = t.cmp_ty(tree, chain);
    assert_ne!(forward, std::cmp::Ordering::Equal);
    assert_eq!(t.cmp_ty(chain, tree), forward.reverse());
    assert_eq!(t.cmp_ty(tree, tree), std::cmp::Ordering::Equal);
}

#[test]
fn an_operation_that_meets_itself_builds_a_recursive_type() {
    let mut t = Types::new();
    let labelled = |t: &mut Types, label: &str| {
        let label = t.atom_lit(label);
        t.recursive(1, |t, me| {
            let (nil, int) = (t.nil(), t.int());
            let key = t.union(int, label);
            let node = t.tuple(&[key, me[0], me[0]]);
            vec![t.union(nil, node)]
        })[0]
    };
    let a = labelled(&mut t, "a");
    let b = labelled(&mut t, "b");
    assert!(!t.is_subtype(&a, &b) && !t.is_subtype(&b, &a));
    let both = t.intersect(a, b);
    let tree = tree(&mut t);
    assert_eq!(
        both, tree,
        "a tree keyed by ints or :a, that is also keyed by ints or :b, is keyed by ints"
    );
}
