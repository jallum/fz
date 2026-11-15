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
    let any = t.any();
    let old = nest(&mut t, int, tuple_of, 1);
    let new = nest(&mut t, int, tuple_of, 2);
    let folded = t.clash_fold(old, new).expect("the second rung repeats the first");
    let hollow = t.tuple(&[any]);
    assert_eq!(
        folded,
        t.union(int, hollow),
        "int | {{any}}: the repeated tuple is named by its ancestor"
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
    let any = t.any();
    let old = nest(&mut t, int, |t, e| t.list(e), 1);
    let new = nest(&mut t, int, |t, e| t.list(e), 2);
    let folded = t.clash_fold(old, new).expect("list repeats itself");
    let hollow = t.list(any);
    assert_eq!(folded, t.union(int, hollow));
}

#[test]
fn a_map_that_nests_itself_folds_at_the_field_that_grew() {
    let mut t = Types::new();
    let int = t.int();
    let any = t.any();
    let key = MapKey::Atom("k".to_string());
    let wrap = |t: &mut Types, e: Ty| t.map(&[(MapKey::Atom("k".to_string()), e)]);
    let old = nest(&mut t, int, wrap, 1);
    let new = nest(&mut t, int, wrap, 2);
    let folded = t.clash_fold(old, new).expect("map repeats itself");
    let hollow = t.map(&[(key, any)]);
    assert_eq!(folded, t.union(int, hollow));
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
fn a_node_the_ancestor_does_not_contain_is_replaced_by_any() {
    // The ancestor `int | {int}` covers the clashing node's functors, but the
    // node `int | {binary}` holds a value (`{binary}`) the ancestor never did.
    let mut t = Types::new();
    let (int, bin) = (t.int(), t.str_t());
    let old = nest(&mut t, int, tuple_of, 1);
    let inner = t.tuple(&[bin]);
    let slot = t.union(int, inner);
    let grown = t.tuple(&[slot]);
    let new = t.union(int, grown);
    let any = t.any();
    let folded = t
        .clash_fold(old, new)
        .expect("the node clashes under a covering ancestor");
    let hollow = t.tuple(&[any]);
    assert_eq!(folded, t.union(int, hollow));
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
