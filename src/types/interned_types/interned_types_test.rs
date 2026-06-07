use std::mem;

use crate::types::Types;

use super::{InternedConcreteTypes, InternedTy};

#[test]
fn ty_is_an_integer_handle() {
    assert_eq!(mem::size_of::<InternedTy>(), mem::size_of::<u32>());
}

#[test]
fn factory_interns_equal_descriptors() {
    let mut t = InternedConcreteTypes::new();
    assert_eq!(t.int(), t.int());
    let a = t.int();
    let lhs = t.tuple(&[a]);
    let rhs = t.tuple(&[a]);
    assert_eq!(lhs, rhs);
}

#[test]
fn structural_children_are_interned_handles() {
    let mut t = InternedConcreteTypes::new();
    let elem = t.int();
    let tuple = t.tuple(&[elem]);
    let d = t.descr(&tuple);
    assert_eq!(d.tuples[0].pos[0].elems, vec![elem]);
}

#[test]
fn repeated_subtype_comparisons_are_memoized_by_type_id() {
    let mut t = InternedConcreteTypes::new();
    let int = t.int();
    let lit = t.int_lit(42);

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
fn symmetric_comparisons_share_one_cache_entry() {
    let mut t = InternedConcreteTypes::new();
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
