use super::*;
use crate::compiler2::types::Types;

fn tuple_of(t: &mut Types, e: Ty) -> Ty {
    t.tuple(&[e])
}

fn nest(t: &mut Types, leaf: Ty, make: impl Fn(&mut Types, Ty) -> Ty, depth: usize) -> Ty {
    let mut ty = leaf;
    for _ in 0..depth {
        let wrapped = make(t, ty);
        ty = t.union(leaf, wrapped);
    }
    ty
}

#[test]
fn a_tuple_that_nests_itself_folds_at_the_slot_that_grew() {
    let mut t = Types::new();
    let int = t.int();
    let old = nest(&mut t, int, tuple_of, 1);
    let new = nest(&mut t, int, tuple_of, 2);
    let folded = t.clash_fold(old, new).expect("the second rung repeats the first");
    let nested = t.recursive(1, |t, me| {
        let wrapped = t.tuple(&[me[0]]);
        vec![t.union(int, wrapped)]
    })[0];
    assert_eq!(
        folded, nested,
        "μX. int | {{X}}: the repeated tuple is a back edge to its ancestor"
    );
    let notes = t.take_clash_folds();
    assert_eq!(notes.len(), 1, "one slot grew, so one fold is noted");
    assert_eq!(notes[0].path, vec![0], "the fold is at slot 0 of the outer tuple");
    assert_eq!(notes[0].ancestor_depth, 0, "the ancestor is the outer tuple's node");
    assert_eq!(notes[0].kind, ClashKind::Cycle);
    assert!(t.take_clash_folds().is_empty(), "the drain empties the notes");
}

#[test]
fn a_list_that_nests_itself_folds_at_the_element_that_grew() {
    let mut t = Types::new();
    let int = t.int();
    let old = nest(&mut t, int, |t, e| t.list(e), 1);
    let new = nest(&mut t, int, |t, e| t.list(e), 2);
    let folded = t.clash_fold(old, new).expect("list repeats itself");
    let nested = t.recursive(1, |t, me| {
        let wrapped = t.list(me[0]);
        vec![t.union(int, wrapped)]
    })[0];
    assert_eq!(folded, nested, "μX. int | [X]");
}

#[test]
fn a_map_that_nests_itself_folds_at_the_field_that_grew() {
    let mut t = Types::new();
    let int = t.int();
    let wrap = |t: &mut Types, e: Ty| t.map(&[(MapKey::Atom("k".to_string()), e)]);
    let old = nest(&mut t, int, wrap, 1);
    let new = nest(&mut t, int, wrap, 2);
    let folded = t.clash_fold(old, new).expect("map repeats itself");
    let nested = t.recursive(1, |t, me| {
        let wrapped = wrap(t, me[0]);
        vec![t.union(int, wrapped)]
    })[0];
    assert_eq!(folded, nested, "μX. int | %{{k: X}}");
}

#[test]
fn a_clash_no_ancestor_covers_is_not_folded_and_interns_nothing() {
    // The first rung adds `{int}` to a bare `int`: the growth is at the root,
    // where no ancestor exists to name it.
    let mut t = Types::new();
    let int = t.int();
    let rung = nest(&mut t, int, tuple_of, 1);
    let before = t.interning_work_stats().inserted;
    assert!(t.clash_fold(int, rung).is_none());
    assert_eq!(
        t.interning_work_stats().inserted,
        before,
        "a walk that does not fold interns nothing"
    );
    assert!(t.take_clash_folds().is_empty(), "a root clash notes nothing");
}

#[test]
fn a_new_head_under_a_different_head_is_ordinary_growth() {
    // [{:ok, int}] growing to [{:ok, int} | {:error, int}]: the element's new
    // head is a tuple, the only ancestor is a list, so nothing repeats.
    let mut t = Types::new();
    let (ok, err, int) = (t.atom_lit("ok"), t.atom_lit("error"), t.int());
    let ok_int = t.tuple(&[ok, int]);
    let err_int = t.tuple(&[err, int]);
    let both = t.union(ok_int, err_int);
    let (old, new) = (t.list(ok_int), t.list(both));
    let before = t.interning_work_stats().inserted;
    assert!(t.clash_fold(old, new).is_none());
    assert_eq!(t.interning_work_stats().inserted, before);
}

#[test]
fn a_node_the_ancestor_does_not_contain_joins_the_ancestor() {
    // The ancestor `int | {int}` covers the clashing node's functors, but the
    // node `int | {binary}` holds a value (`{binary}`) the ancestor never did.
    let mut t = Types::new();
    let (int, bin) = (t.int(), t.str_t());
    let old = nest(&mut t, int, tuple_of, 1);
    let inner = t.tuple(&[bin]);
    let slot = t.union(int, inner);
    let grown = t.tuple(&[slot]);
    let new = t.union(int, grown);
    let folded = t
        .clash_fold(old, new)
        .expect("the node clashes under a covering ancestor");
    let joined = t.recursive(1, |t, me| {
        let wrapped = t.tuple(&[me[0]]);
        let some = t.union(int, inner);
        vec![t.union(some, wrapped)]
    })[0];
    assert_eq!(
        folded, joined,
        "μX. int | {{binary}} | {{X}}: the ancestor takes the node's values in"
    );
    assert!(t.is_subtype(&new, &folded));
    assert_eq!(
        t.take_clash_folds()[0].kind,
        ClashKind::Replace,
        "the node holds a value the ancestor never did"
    );
}

#[test]
fn folding_is_idempotent() {
    let mut t = Types::new();
    let int = t.int();
    let old = nest(&mut t, int, tuple_of, 1);
    let new = nest(&mut t, int, tuple_of, 2);
    let folded = t.clash_fold(old, new).expect("folds");
    assert!(
        t.clash_fold(old, folded).is_none(),
        "a folded iterate repeats nothing further"
    );
    assert!(t.clash_fold(folded, folded).is_none());
}

#[test]
fn a_tagged_head_is_covered_by_the_untagged_head_of_its_arity() {
    let mut t = Types::new();
    let int = t.int();
    let tag = t.atom_lit("l");
    let any = t.any();
    let untagged = t.tuple(&[any, int]);
    let tagged = t.tuple(&[tag, int]);
    let (wide, narrow) = (Pf::of(&t, &[untagged]), Pf::of(&t, &[tagged]));
    assert!(
        wide.covers(&t, &narrow),
        "an untagged head stands for every tuple of its arity"
    );
    assert!(
        !narrow.covers(&t, &wide),
        "a tagged head does not stand for the untagged one"
    );
}

#[test]
fn two_tags_under_an_untagged_ancestor_fold() {
    // The outer pair's first slot holds `:a | {:l, :a}` and then also
    // `{:r, :a}`: a second tag of the arity the untagged outer head names.
    let mut t = Types::new();
    let int = t.int();
    let (a, l, r) = (t.atom_lit("a"), t.atom_lit("l"), t.atom_lit("r"));
    let left = t.tuple(&[l, a]);
    let right = t.tuple(&[r, a]);
    let before = t.union(a, left);
    let after = t.union(before, right);
    let pair = |t: &mut Types, first: Ty| {
        let outer = t.tuple(&[first, int]);
        t.union(a, outer)
    };
    let (old, new) = (pair(&mut t, before), pair(&mut t, after));
    let folded = t
        .clash_fold(old, new)
        .expect("the outer untagged head covers the second tag");
    let named = t.recursive(1, |t, me| {
        let outer = t.tuple(&[me[0], int]);
        let tagged = t.union(left, right);
        let some = t.union(a, tagged);
        vec![t.union(some, outer)]
    })[0];
    assert_eq!(folded, named, "the grown slot is a back edge to its ancestor");
    assert_eq!(t.take_clash_folds().len(), 1, "one slot grew, so one fold is noted");
}

/// `insert` into a binary search tree `T = μT. nil | {int, T, T}` returns a
/// non-empty tree, `R = {int, nil, nil} | {int, R, T} | {int, T, R}`, whose
/// least solution is `{int, T, T}`. A slot that holds `T` beside the finite
/// trees still has those trees to walk: only `T` itself, already a cycle, is
/// passed over.
#[test]
fn a_slot_beside_a_recursive_type_still_folds_its_own_growth() {
    let mut t = Types::new();
    let (int, nil) = (t.int(), t.atom_lit("nil"));
    let tree = t.recursive(1, |t, me| {
        let node = t.tuple(&[int, me[0], me[0]]);
        vec![t.union(nil, node)]
    })[0];
    let step = |t: &mut Types, r: Ty| {
        let leaf = t.tuple(&[int, nil, nil]);
        let left = t.tuple(&[int, r, tree]);
        let right = t.tuple(&[int, tree, r]);
        let some = t.union(leaf, left);
        t.union(some, right)
    };
    let first = t.tuple(&[int, nil, nil]);
    let mut old = step(&mut t, first);
    let mut new = step(&mut t, old);
    let mut rounds = 0;
    while let Some(folded) = t.clash_fold(old, new) {
        let joined = t.union(folded, new);
        (old, new) = (folded, step(&mut t, joined));
        rounds += 1;
        assert!(rounds < 8, "the fold settles: {}", t.display(&new));
        if t.is_subtype(&new, &old) {
            break;
        }
    }
    let answer = t.tuple(&[int, tree, tree]);
    assert!(rounds > 0, "growth beside T is folded");
    assert!(t.is_equivalent(&old, &answer), "{} is {{int, T, T}}", t.display(&old));
}

/// A parser's value is `V = int | [V]`. One iterate holds `int`, `[int]` and
/// a list of an already recursive `L = μL. [int] | [L]`; the next wraps that
/// whole iterate in a list. The list head lives only inside `L` on the old
/// side, so growth is judged on the members a walk enters, and the wrapped
/// iterate is a back edge to the root.
#[test]
fn growth_is_judged_on_the_members_the_walk_enters() {
    let mut t = Types::new();
    let int = t.int();
    let int_list = t.list(int);
    let lists = t.recursive(1, |t, me| {
        let deeper = t.list(me[0]);
        vec![t.union(int_list, deeper)]
    })[0];
    let of_lists = t.list(lists);
    let some = t.union(int, int_list);
    let old = t.union(some, of_lists);
    let new = t.list(old);
    let folded = t.clash_fold(old, new).expect("the wrapped iterate repeats the root");
    let value = t.recursive(1, |t, me| {
        let wrapped = t.list(me[0]);
        vec![t.union(int, wrapped)]
    })[0];
    assert!(
        t.is_equivalent(&folded, &value),
        "{} is μV. int | [V]",
        t.display(&folded)
    );
}
