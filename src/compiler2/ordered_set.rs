//! An insertion-ordered membership set.
//!
//! Iteration order is registration order, not the per-process `RandomState`
//! order a bare `HashSet` produces. compiler2 needs that in two places on the
//! same causal chain, and they are the same idea:
//!
//! - a fact's subscribers and waiters, because `enqueue_dependents` iterates
//!   them to decide which job to enqueue next;
//! - a job's published outputs, because `mark_dirty` iterates them to decide
//!   which fact changes enter `pending_changes`, and that decides which job is
//!   woken next.
//!
//! Both feed job execution order, and job execution order decides which
//! conclusion lands "first" at a keep-first merge downstream and the order
//! fresh types reach the interner — whose ids are arena positions. A hash-random
//! order in either place makes the published `BackendProgram` vary run to run
//! for the exact same input (fz-k22.28, fz-f98.19).
//!
//! The cure is order-preserving, never order-restoring: no sort, and above all
//! no after-the-fact renumbering pass. A sort needs a comparator that does not
//! depend on what is being minted, and a renumbering pass is a barrier that
//! would leave the work order nondeterministic while making only the ids look
//! stable. Keeping the order the producer already established costs nothing and
//! is correct by construction.

/// The set is its order vector. Membership is a linear scan of that order: the
/// sets compiler2 keeps are small, so scanning costs less than hashing and
/// keeping a second copy of every member.
#[derive(Debug, Clone)]
pub struct OrderedSet<T> {
    order: Vec<T>,
}

impl<T> Default for OrderedSet<T> {
    fn default() -> Self {
        Self { order: Vec::new() }
    }
}

impl<T: Eq> OrderedSet<T> {
    pub fn insert(&mut self, value: T) -> bool {
        if self.contains(&value) {
            return false;
        }
        self.order.push(value);
        true
    }

    pub fn remove(&mut self, value: &T) {
        if let Some(index) = self.order.iter().position(|existing| existing == value) {
            self.order.remove(index);
        }
    }

    pub fn contains(&self, value: &T) -> bool {
        self.order.contains(value)
    }

    pub fn is_empty(&self) -> bool {
        self.order.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.order.iter()
    }
}

impl<T: Eq> FromIterator<T> for OrderedSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut set = Self::default();
        for value in iter {
            set.insert(value);
        }
        set
    }
}

impl<T: Eq> Extend<T> for OrderedSet<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for value in iter {
            self.insert(value);
        }
    }
}

impl<'a, T> IntoIterator for &'a OrderedSet<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.order.iter()
    }
}

impl<T> IntoIterator for OrderedSet<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.order.into_iter()
    }
}

#[cfg(test)]
#[path = "ordered_set_test.rs"]
mod ordered_set_test;
