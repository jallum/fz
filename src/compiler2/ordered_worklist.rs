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
#[path = "ordered_worklist_test.rs"]
mod ordered_worklist_test;
