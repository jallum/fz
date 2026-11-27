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
fn a_node_holding_a_value_the_ancestor_never_held_is_ordinary_growth() {
    // `int | {int}` growing to `int | {int | {binary}}`: the slot gains
    // `{binary}`, a value no ancestor iterate held, so nothing has come back
    // and there is nothing to close on. The iterate is left to grow; the slot
    // closes once its whole value lies inside an ancestor's.
    let mut t = Types::new();
    let (int, bin) = (t.int(), t.str_t());
    let old = nest(&mut t, int, tuple_of, 1);
    let inner = t.tuple(&[bin]);
    let slot = t.union(int, inner);
    let grown = t.tuple(&[slot]);
    let new = t.union(int, grown);
    let before = t.interning_work_stats().inserted;
    assert!(t.clash_fold(old, new).is_none());
    assert_eq!(t.interning_work_stats().inserted, before);
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
fn a_second_tag_under_an_untagged_ancestor_is_ordinary_growth() {
    // The outer pair's first slot holds `:a | {:l, :a}` and then also
    // `{:r, :a}`. The new tagged pair is no value of the outer `{_, int}` head
    // (its second element is an atom), so no ancestor value has come back.
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
    let before_work = t.interning_work_stats().inserted;
    assert!(t.clash_fold(old, new).is_none());
    assert_eq!(t.interning_work_stats().inserted, before_work);
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

/// `escape` returns `int | {r, r} | {:{}, [], [r]} | [r]` for the return `r` of
/// its previous round. A round later, `old` holds that shape around a
/// recursive type `R` (`escape` of the empty list's element) and the next
/// return wraps all of `old` in a list. The slot that gained the list holds
/// only the recursive `R` on the old side, which the walk passes over, yet the
/// list is the list `old` itself already holds: the wrapped type has come back
/// beneath itself, so it folds to a back edge to `old` instead of keeping
/// `R` beside it as a rung of a ladder.
#[test]
fn a_recursive_member_that_comes_back_beneath_its_ancestor_folds() {
    let mut t = Types::new();
    let (int, empty, brace) = (t.int(), t.empty_list(), t.atom_lit("{}"));
    let step = |t: &mut Types, r: Ty| {
        let pair = t.tuple(&[r, r]);
        let elements = t.list(r);
        let node = t.tuple(&[brace, empty, elements]);
        let some = t.union(int, pair);
        let more = t.union(some, node);
        t.union(more, elements)
    };
    let inner = t.recursive(1, |t, me| {
        let pair = t.tuple(&[me[0], me[0]]);
        let leaf = t.tuple(&[brace, empty, empty]);
        let some = t.union(int, pair);
        let more = t.union(some, leaf);
        vec![t.union(more, empty)]
    })[0];
    let old = step(&mut t, inner);
    let wrapped = t.list(old);
    let joined = t.union(old, wrapped);
    let folded = t
        .clash_fold(old, joined)
        .expect("the wrapped iterate repeats the list old holds");
    let expected = t.recursive(1, |t, me| {
        let pair = t.tuple(&[me[0], me[0]]);
        let elements = t.list(inner);
        let node = t.tuple(&[brace, empty, elements]);
        let own = t.list(me[0]);
        let some = t.union(int, pair);
        let more = t.union(some, node);
        vec![t.union(more, own)]
    })[0];
    assert!(
        t.is_equivalent(&folded, &expected),
        "{} is μt. int | {{t, t}} | {{:{{}}, [], [R]}} | [t]",
        t.display(&folded)
    );
}

#[test]
fn a_tree_insert_iterated_through_the_fold_settles_at_the_tree() {
    // The iterates of a binary-tree insert (a node rebuilt around the recursive
    // call's result on either side) close on `{int, T, T}` with `T = nil | {int, T, T}`.
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
    let answer = t.tuple(&[int, tree, tree]);
    for _ in 0..8 {
        let Some(folded) = t.clash_fold(old, new) else { break };
        let joined = t.union(folded, new);
        (old, new) = (folded, step(&mut t, joined));
        if t.is_subtype(&new, &old) {
            break;
        }
    }
    assert!(t.is_subtype(&new, &old), "the iterates settle");
    assert!(
        t.is_subtype(&old, &answer) && t.is_subtype(&answer, &old),
        "{}",
        t.display(&old)
    );
}

/// `R = μt. int | [t]` closes a slot, and the next iterate holds `R` beside a
/// list whose elements are `R` or `:ok`. That list is not inside `R`, yet it
/// has `R`'s own shape, so the slot becomes its own equation taking `R`'s body
/// in. One step covers the grown iterate and stays within the closure
/// `μt. int | [t | :ok]`; the next round re-folds what it still lacks.
#[test]
fn a_slot_holding_a_closed_member_and_a_longer_list_of_it_reopens_within_the_wider_list() {
    let mut t = Types::new();
    let (int, ok) = (t.int(), t.atom_lit("ok"));
    let member = t.recursive(1, |t, me| {
        let deeper = t.list(me[0]);
        vec![t.union(int, deeper)]
    })[0];
    let old = tuple_of(&mut t, member);
    let element = t.union(member, ok);
    let rung = t.list(element);
    let grown = t.union(member, rung);
    let new = tuple_of(&mut t, grown);
    let reopened = t.clash_fold(old, new).expect("the slot's member has been outgrown");
    let notes = t.take_clash_folds();
    assert_eq!(notes.len(), 1, "one slot is reopened");
    assert_eq!(notes[0].kind, ClashKind::Replace, "a reopened slot replaces the member");
    let wide = t.recursive(1, |t, me| {
        let element = t.union(me[0], ok);
        let deeper = t.list(element);
        vec![t.union(int, deeper)]
    })[0];
    let hand = tuple_of(&mut t, wide);
    assert!(
        t.is_subtype(&new, &reopened),
        "{} covers the iterate",
        t.display(&reopened)
    );
    assert!(
        t.is_subtype(&reopened, &hand),
        "{} stays within {{μt. int | [t | :ok]}}",
        t.display(&reopened)
    );
}

/// The slot holds `int | :a` beside the tuple rung it repeats. The rung closes
/// onto the ancestor and the `int | :a` stays beside the back edge: the head is
/// cut, not dropped, so the answer is `{μt. int | :a | {t}}`.
#[test]
fn a_value_beside_a_repeated_rung_stays_beside_the_back_edge() {
    let mut t = Types::new();
    let (int, a) = (t.int(), t.atom_lit("a"));
    let base = t.union(int, a);
    let rung = |t: &mut Types, below: Ty| {
        let slot = t.union(base, below);
        tuple_of(t, slot)
    };
    let first = tuple_of(&mut t, base);
    let second = rung(&mut t, first);
    let third = rung(&mut t, second);
    let folded = t.clash_fold(second, third).expect("the third rung repeats the second");
    let closed = t.recursive(1, |t, me| {
        let deeper = tuple_of(t, me[0]);
        vec![t.union(base, deeper)]
    })[0];
    let hand = tuple_of(&mut t, closed);
    assert!(
        t.is_subtype(&folded, &hand) && t.is_subtype(&hand, &folded),
        "{} is {{μt. int | :a | {{t}}}}",
        t.display(&folded)
    );
}

/// The element slot of `[int]` grows to `int | [int]`: the slot's old value
/// `int` is not inside the list the slot sits in, so one rung is ordinary
/// growth and nothing is folded.
#[test]
fn a_slot_whose_old_value_lies_outside_the_ancestor_is_ordinary_growth() {
    let mut t = Types::new();
    let int = t.int();
    let old = t.list(int);
    let inner = t.list(int);
    let element = t.union(int, inner);
    let new = t.list(element);
    assert!(t.clash_fold(old, new).is_none());
    assert!(t.take_clash_folds().is_empty());
}

/// The iterates `int | [int]` and `int | [[int]] | [int]` of a decoder's
/// value are proper lists all the way down; the fold is the proper-list
/// closure `μt. int | [t]`, with no terminator other than `[]`.
#[test]
fn nested_proper_lists_fold_to_the_proper_list_closure() {
    let mut t = Types::new();
    let int = t.int();
    let flat = t.list(int);
    let old = t.union(int, flat);
    let nested = t.list(flat);
    let new = t.union(old, nested);
    let folded = t.clash_fold(old, new).expect("the nested list repeats the flat one");
    let hand = t.recursive(1, |t, me| {
        let deeper = t.list(me[0]);
        vec![t.union(int, deeper)]
    })[0];
    assert!(
        t.is_subtype(&folded, &hand) && t.is_subtype(&hand, &folded),
        "{} is μt. int | [t]",
        t.display(&folded)
    );
}

/// A list that was never empty becoming possibly empty is growth by `[]` alone,
/// not a rung of a ladder: the element's old and new values are the same
/// shape, so nothing is folded and the type keeps its depth.
#[test]
fn a_slot_that_only_gains_the_empty_list_is_ordinary_growth() {
    let mut t = Types::new();
    let (int, empty) = (t.int(), t.empty_list());
    let nonempty = t.cons(int, empty);
    let possibly_empty = t.list(int);
    let old_element = t.union(int, nonempty);
    let new_element = t.union(int, possibly_empty);
    let old = t.list(old_element);
    let new = t.list(new_element);
    assert!(t.clash_fold(old, new).is_none());
    assert!(t.take_clash_folds().is_empty());
}
