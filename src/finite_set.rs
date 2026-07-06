//! A finite-or-cofinite set over `T`: `cofinite=false` means "exactly these
//! values"; `cofinite=true` means "every value of `T` EXCEPT these". `(false,
//! {})` is empty; `(true, {})` is the full universe of `T`.
//!
//! Shared by the type lattice (singleton-type precision for atoms and the
//! atom-shaped nominal axes: opaques, brands, vars) and the runtime type
//! predicate (observed value-membership sets: ints, floats, atoms, list
//! shapes, tuple arities, named structs). Both call sites need exactly the
//! same finite-or-cofinite algebra, so this container serves both rather than
//! each side re-deriving its own copy of the same truth tables.

use std::collections::BTreeSet;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct FiniteSet<T> {
    pub(crate) values: BTreeSet<T>,
    pub(crate) cofinite: bool,
}

impl<T> Default for FiniteSet<T> {
    fn default() -> Self {
        Self {
            values: BTreeSet::new(),
            cofinite: false,
        }
    }
}

impl<T: Ord> FiniteSet<T> {
    pub(crate) fn none() -> Self {
        Self::default()
    }

    pub(crate) fn any() -> Self {
        Self {
            values: BTreeSet::new(),
            cofinite: true,
        }
    }

    pub(crate) fn lit(value: T) -> Self {
        Self::finite([value])
    }

    pub(crate) fn finite(values: impl IntoIterator<Item = T>) -> Self {
        Self {
            values: values.into_iter().collect(),
            cofinite: false,
        }
    }

    pub(crate) fn cofinite(values: impl IntoIterator<Item = T>) -> Self {
        Self {
            values: values.into_iter().collect(),
            cofinite: true,
        }
    }

    pub(crate) fn is_none(&self) -> bool {
        !self.cofinite && self.values.is_empty()
    }

    pub(crate) fn is_any(&self) -> bool {
        self.cofinite && self.values.is_empty()
    }

    pub(crate) fn contains(&self, value: &T) -> bool {
        self.values.contains(value) != self.cofinite
    }

    pub(crate) fn finite_len(&self) -> Option<usize> {
        (!self.cofinite).then_some(self.values.len())
    }
}

impl<T: Ord + Clone> FiniteSet<T> {
    /// The set's elements, if it is finite (not cofinite). `None` for a
    /// cofinite set — its complement is not enumerable from this side.
    pub(crate) fn finite_elems(&self) -> Option<impl Iterator<Item = T> + '_> {
        (!self.cofinite).then(|| self.values.iter().cloned())
    }

    pub(crate) fn union(&self, other: &Self) -> Self {
        match (self.cofinite, other.cofinite) {
            (false, false) => Self::finite(self.values.union(&other.values).cloned()),
            (true, false) => Self::cofinite(self.values.difference(&other.values).cloned()),
            (false, true) => Self::cofinite(other.values.difference(&self.values).cloned()),
            (true, true) => Self::cofinite(self.values.intersection(&other.values).cloned()),
        }
    }

    pub(crate) fn intersect(&self, other: &Self) -> Self {
        match (self.cofinite, other.cofinite) {
            (false, false) => Self::finite(self.values.intersection(&other.values).cloned()),
            (true, false) => Self::finite(other.values.difference(&self.values).cloned()),
            (false, true) => Self::finite(self.values.difference(&other.values).cloned()),
            (true, true) => Self::cofinite(self.values.union(&other.values).cloned()),
        }
    }

    pub(crate) fn neg(&self) -> Self {
        Self {
            values: self.values.clone(),
            cofinite: !self.cofinite,
        }
    }

    pub(crate) fn overlaps(&self, other: &Self) -> bool {
        match (self.cofinite, other.cofinite) {
            (false, false) => self.values.iter().any(|value| other.values.contains(value)),
            (false, true) => self.values.iter().any(|value| !other.values.contains(value)),
            (true, false) => other.values.iter().any(|value| !self.values.contains(value)),
            (true, true) => true,
        }
    }
}

#[cfg(test)]
mod tests {
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
}
