//! A transient min-heap whose caller supplies a stable contextual comparison.
//!
//! Items move inside the existing vector; ordering is neither identity nor
//! deduplication. The caller owns admission and may retain comparator-equal
//! distinct items. No comparison key or context snapshot is cached here.

use std::cmp::Ordering;

pub(super) struct OrderedWorklist<T> {
    values: Vec<T>,
}

impl<T> OrderedWorklist<T> {
    /// An ascending vector already satisfies the min-heap invariant.
    pub(super) fn from_sorted(values: Vec<T>) -> Self {
        Self { values }
    }

    pub(super) fn push(&mut self, value: T, mut compare: impl FnMut(&T, &T) -> Ordering) {
        let mut child = self.values.len();
        self.values.push(value);
        while child > 0 {
            let parent = (child - 1) / 2;
            if compare(&self.values[child], &self.values[parent]) != Ordering::Less {
                break;
            }
            self.values.swap(child, parent);
            child = parent;
        }
    }

    pub(super) fn pop(&mut self, mut compare: impl FnMut(&T, &T) -> Ordering) -> Option<T> {
        if self.values.is_empty() {
            return None;
        }
        let value = self.values.swap_remove(0);
        let mut parent = 0;
        loop {
            let left = parent * 2 + 1;
            if left >= self.values.len() {
                break;
            }
            let right = left + 1;
            let child =
                if right < self.values.len() && compare(&self.values[right], &self.values[left]) == Ordering::Less {
                    right
                } else {
                    left
                };
            if compare(&self.values[child], &self.values[parent]) != Ordering::Less {
                break;
            }
            self.values.swap(child, parent);
            parent = child;
        }
        Some(value)
    }

    pub(super) fn into_values(self) -> Vec<T> {
        self.values
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interleaved_admission_is_ordered_without_cloning_items_or_rebuilding_the_inventory() {
        struct Item(Box<(u32, u32)>);
        for size in [8_u32, 64, 256] {
            let mut values = Vec::with_capacity(size as usize * 2);
            for id in 0..size {
                values.push(Item(Box::new((id * 2, id))));
            }
            let storage = values.as_ptr();
            let payloads = values.iter().map(|value| (&*value.0) as *const _).collect::<Vec<_>>();
            let mut work = OrderedWorklist::from_sorted(values);
            assert_eq!(
                work.values.as_ptr(),
                storage,
                "construction moves the original allocation"
            );
            let mut comparisons = 0;
            let mut compare = |a: &Item, b: &Item| {
                comparisons += 1;
                a.0.0.cmp(&b.0.0)
            };
            let mut selected = Vec::new();
            for id in 0..size {
                let value = work.pop(&mut compare).unwrap();
                assert_eq!((&*value.0) as *const _, payloads[id as usize]);
                selected.push(value.0.0);
                work.push(Item(Box::new((id * 2 + 1, id))), &mut compare);
                selected.push(work.pop(&mut compare).unwrap().0.0);
            }
            assert_eq!(selected, (0..size * 2).collect::<Vec<_>>());
            assert_eq!(
                work.values.as_ptr(),
                storage,
                "bounded live admission needs no replacement buffer"
            );
            assert!(comparisons <= u64::from(size) * u64::from(size.ilog2() + 1) * 6);
        }
    }

    #[test]
    fn comparator_equality_does_not_discard_distinct_items() {
        let mut work = OrderedWorklist::from_sorted(Vec::new());
        for id in 0..32 {
            work.push(id, |_, _| Ordering::Equal);
        }
        let mut selected = Vec::new();
        while let Some(id) = work.pop(|_, _| Ordering::Equal) {
            selected.push(id);
        }
        selected.sort_unstable();
        assert_eq!(selected, (0..32).collect::<Vec<_>>());
    }
}
