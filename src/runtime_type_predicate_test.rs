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

use super::tests::{atom, ints, tuple_of};
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
