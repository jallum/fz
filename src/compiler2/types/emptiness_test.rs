use super::*;
use crate::compiler2::allocation_probe::allocations_during;
use crate::compiler2::types::Types;

#[test]
fn a_descriptor_already_open_on_the_path_is_assumed_empty_wherever_it_re_enters() {
    let mut t = Types::new();
    let int = t.int();
    let atom = t.atom_lit("a");
    let list = t.list(int);
    let reentered = t.descr(&list).clone();
    let unrelated = t.descr(&atom).clone();
    let pair = t.tuple(&[int, list]);
    let pair = t.descr(&pair).clone();
    let cx = t.ctx();
    assert!(!pair.is_empty(cx), "the pair is inhabited when nothing is assumed");

    let outer = Frame::open(&unrelated, InFlight::default());
    let inner = Frame::open(&reentered, InFlight::within(&outer));
    let open = InFlight::within(&inner);
    assert!(
        pair.is_empty_in(cx, open),
        "a coordinate that re-enters a descriptor in flight is assumed empty, so the product is empty"
    );
    assert!(
        open.contains(&reentered) && open.contains(&unrelated) && !open.contains(&pair),
        "a decision opens its own frame below the caller's path and leaves the caller's path as it was"
    );

    assert!(
        !pair.is_empty(cx),
        "the assumption belonged to the path that carried it and decided nothing beyond it"
    );
}

#[test]
fn an_emptiness_query_makes_no_copy_of_a_descriptor_to_remember_it_is_in_flight() {
    let mut t = Types::new();
    let int = t.int();
    let list = t.list(int);
    let inner = t.tuple(&[int, list]);
    let outer = t.tuple(&[inner, list]);
    let outer = t.descr(&outer).clone();
    let cx = t.ctx();

    let (empty, allocations) = allocations_during(|| outer.is_empty(cx));

    assert!(!empty);
    assert_eq!(
        allocations, 11,
        "only the descriptor arithmetic allocates; tracking the path in flight allocates nothing"
    );
}
