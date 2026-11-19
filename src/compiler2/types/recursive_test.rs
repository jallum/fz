use super::*;
use crate::compiler2::types::addressed::AddrStep;
use crate::compiler2::types::{ClassReach, KeyCollapse, Sigma, Types};
use crate::dispatch_matrix::demand::DispatchDemand;

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

/// `T = nil | {label, T, T}`.
fn labelled_tree(t: &mut Types, label: Ty) -> Ty {
    t.recursive(1, |t, me| {
        let nil = t.nil();
        let node = t.tuple(&[label, me[0], me[0]]);
        vec![t.union(nil, node)]
    })[0]
}

#[test]
fn widening_literals_maps_every_unfolding() {
    let mut t = Types::new();
    let a = t.atom_lit("a");
    let tree = labelled_tree(&mut t, a);
    let atom = t.atom();
    let widened = t.recursive(1, |t, me| {
        let node = t.tuple(&[atom, me[0], me[0]]);
        vec![t.union(atom, node)]
    })[0];
    assert_eq!(t.widen_literals(&tree), widened, "every :a and every nil reads as atom");
}

#[test]
fn readings_that_change_nothing_return_the_recursive_type() {
    let mut t = Types::new();
    let tree = tree(&mut t);
    assert_eq!(t.runtime_reading(&tree), tree);
    assert_eq!(t.value_lane_repr(tree), tree);
    assert_eq!(t.structural_surface(tree), tree);
    assert_eq!(t.erase_closure_identity(&tree), tree);
    assert_eq!(t.fold_self_nested_closures(&tree), tree);
}

#[test]
fn instantiating_a_recursive_type_substitutes_every_unfolding() {
    let mut t = Types::new();
    let alpha = t.type_var(TypeVarId(7));
    let generic = labelled_tree(&mut t, alpha);
    let int = t.int();
    let mut sigma = Sigma::default();
    sigma.insert(TypeVarId(7), int);
    let tree = tree(&mut t);
    assert_eq!(t.instantiate(&generic, &sigma), tree);
}

#[test]
fn the_runtime_envelope_of_a_recursive_type_is_recursive() {
    let mut t = Types::new();
    let tree = tree(&mut t);
    assert_eq!(
        t.runtime_type_test_envelope(tree),
        tree,
        "a tree of ints is testable as it stands"
    );
    let alpha = t.type_var(TypeVarId(7));
    let generic = labelled_tree(&mut t, alpha);
    let envelope = t.runtime_envelope(generic);
    assert!(!t.has_vars(&envelope), "the envelope reads every variable away");
    assert!(
        t.is_subtype(&tree, &envelope),
        "and still holds every tree a variable could stand for"
    );
}

#[test]
fn refining_a_recursive_type_by_itself_is_itself() {
    let mut t = Types::new();
    let tree = tree(&mut t);
    let int = t.int();
    let node = t.tuple(&[int, tree, tree]);
    assert_eq!(t.refine_widen(&tree, &tree), tree);
    let refined = t.refine_widen(&node, &tree);
    assert!(t.is_subtype(&node, &refined) && t.is_subtype(&tree, &refined));
}

#[test]
fn a_variable_inside_a_recursive_type_is_addressed_at_its_first_occurrence() {
    let mut t = Types::new();
    let alpha = t.type_var(TypeVarId(7));
    let generic = labelled_tree(&mut t, alpha);
    let mut inputs = [generic, alpha];
    t.address_inputs(&mut inputs);
    let [tree, repeat] = inputs;
    let named = t.free_var_ids(&tree);
    assert_eq!(named.len(), 1, "one variable, however many unfoldings hold it");
    assert_eq!(t.free_var_ids(&repeat), named, "a repeat reuses the first address");
    assert!(t.ctx().attrs(&tree).recursive());
}

/// `V = {int, [V]}`: a node with a list of children, every one a node.
fn rose(t: &mut Types) -> Ty {
    t.recursive(1, |t, me| {
        let int = t.int();
        let children = t.list(me[0]);
        vec![t.tuple(&[int, children])]
    })[0]
}

#[test]
fn a_path_stops_at_a_recursive_type() {
    let mut t = Types::new();
    let rose = rose(&mut t);
    let int = t.int();
    let held = t.tuple(&[int, rose]);
    let path = [AddrStep::Param(0)];
    for reach in [ClassReach::Freight, ClassReach::Demanded, ClassReach::Returned] {
        let class = t.convergence_class_at(&held, &path, reach, KeyCollapse::Recursive);
        assert_eq!(class, held, "the recursive type stands whole where the path entered it");
    }
    assert_eq!(t.convergence_class(&held), held);
    let demand = DispatchDemand::TupleFields([(1, DispatchDemand::Ignore)].into_iter().collect());
    let keyed = t.convergence_collapse_evidence_inputs(&[held], &[demand]);
    assert_eq!(keyed, vec![held]);
}

#[test]
fn a_runtime_test_reads_a_recursive_type_to_its_first_back_edge() {
    let mut t = Types::new();
    let tree = tree(&mut t);
    let is_tree = t.runtime_type_predicate(&tree);
    let (nil, int, atom, any) = (t.nil(), t.int(), t.atom(), t.any());
    let cut = t.tuple(&[int, any, any]);
    let cut = t.union(nil, cut);
    assert!(
        is_tree.contained_in(&t.runtime_type_predicate(&cut)),
        "never coarser than the type a depth cut leaves behind"
    );
    let wrong_label = t.tuple(&[atom, tree, tree]);
    let is_wrong = t.runtime_type_predicate(&wrong_label);
    assert!(
        !is_wrong.overlaps(&is_tree),
        "the root is read in full: {{:x, _, _}} is no tree"
    );
    let node = t.tuple(&[int, tree, tree]);
    assert!(t.runtime_type_predicate(&node).contained_in(&is_tree));
}

#[test]
fn the_canonical_form_of_a_recursive_type_is_the_same_in_every_world() {
    let labels = |_| String::new();
    let render = |build: fn(&mut Types) -> Ty| {
        let mut t = Types::new();
        let _unrelated = chain(&mut t);
        let ty = build(&mut t);
        crate::compiler2::types::canon::TyCanon::new(&labels).render(&t, ty)
    };
    let tree_text = render(tree);
    assert_eq!(
        tree_text,
        render(|t| {
            let tree = tree(t);
            let (nil, int) = (t.nil(), t.int());
            let leaf = t.tuple(&[int, nil, nil]);
            t.union(leaf, tree)
        })
    );
    assert_ne!(tree_text, render(chain));
    assert!(tree_text.contains('μ'), "{tree_text}");
}
