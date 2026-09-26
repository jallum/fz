use super::FiniteSet;

#[test]
fn none_and_any_are_complements() {
    assert!(FiniteSet::<i64>::none().is_none());
    assert!(FiniteSet::<i64>::any().is_any());
    assert!(!FiniteSet::<i64>::none().is_any());
    assert!(!FiniteSet::<i64>::any().is_none());
}

#[test]
fn lit_contains_only_itself() {
    let s = FiniteSet::lit(1);
    assert!(s.contains(&1));
    assert!(!s.contains(&2));
}

#[test]
fn contains_on_cofinite_excludes_listed_values() {
    let s = FiniteSet::cofinite([1, 2]);
    assert!(!s.contains(&1));
    assert!(s.contains(&3));
}

#[test]
fn union_truth_table() {
    let a = FiniteSet::finite([1, 2]);
    let b = FiniteSet::finite([2, 3]);
    assert_eq!(a.union(&b), FiniteSet::finite([1, 2, 3]));

    let a = FiniteSet::cofinite([1, 2]);
    let b = FiniteSet::finite([2, 3]);
    // cofinite {1,2} ∪ finite {2,3} = cofinite ({1,2} - {2,3}) = cofinite {1}
    assert_eq!(a.union(&b), FiniteSet::cofinite([1]));

    let a = FiniteSet::finite([1, 2]);
    let b = FiniteSet::cofinite([2, 3]);
    assert_eq!(a.union(&b), FiniteSet::cofinite([3]));

    let a = FiniteSet::cofinite([1, 2]);
    let b = FiniteSet::cofinite([2, 3]);
    assert_eq!(a.union(&b), FiniteSet::cofinite([2]));
}

#[test]
fn intersect_truth_table() {
    let a = FiniteSet::finite([1, 2]);
    let b = FiniteSet::finite([2, 3]);
    assert_eq!(a.intersect(&b), FiniteSet::finite([2]));

    let a = FiniteSet::cofinite([1, 2]);
    let b = FiniteSet::finite([2, 3]);
    assert_eq!(a.intersect(&b), FiniteSet::finite([3]));

    let a = FiniteSet::finite([1, 2]);
    let b = FiniteSet::cofinite([2, 3]);
    assert_eq!(a.intersect(&b), FiniteSet::finite([1]));

    let a = FiniteSet::cofinite([1, 2]);
    let b = FiniteSet::cofinite([2, 3]);
    assert_eq!(a.intersect(&b), FiniteSet::cofinite([1, 2, 3]));
}

#[test]
fn neg_flips_cofinite_and_keeps_values() {
    let a = FiniteSet::finite([1, 2]);
    let negated = a.neg();
    assert!(negated.cofinite);
    assert_eq!(negated.values, a.values);
    assert_eq!(negated.neg(), a);
}

#[test]
fn overlaps_matches_nonempty_intersect() {
    let cases: [(FiniteSet<i64>, FiniteSet<i64>); 4] = [
        (FiniteSet::finite([1, 2]), FiniteSet::finite([2, 3])),
        (FiniteSet::cofinite([1, 2]), FiniteSet::finite([2, 3])),
        (FiniteSet::finite([1, 2]), FiniteSet::cofinite([2, 3])),
        (FiniteSet::cofinite([1, 2]), FiniteSet::cofinite([2, 3])),
    ];
    for (a, b) in cases {
        assert_eq!(a.overlaps(&b), !a.intersect(&b).is_none(), "{a:?} vs {b:?}");
    }
}

#[test]
fn finite_elems_is_none_for_cofinite() {
    assert!(FiniteSet::cofinite([1, 2]).finite_elems().is_none());
    let elems: Vec<i64> = FiniteSet::finite([1, 2]).finite_elems().unwrap().collect();
    assert_eq!(elems, vec![1, 2]);
}

#[test]
fn finite_len_tracks_finite_only() {
    assert_eq!(FiniteSet::finite([1, 2, 3]).finite_len(), Some(3));
    assert_eq!(FiniteSet::<i64>::cofinite([1]).finite_len(), None);
}
