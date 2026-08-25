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

use std::collections::HashSet;
use std::hash::Hash;

#[derive(Debug, Clone)]
pub struct OrderedSet<T> {
    order: Vec<T>,
    members: HashSet<T>,
}

impl<T> Default for OrderedSet<T> {
    fn default() -> Self {
        Self {
            order: Vec::new(),
            members: HashSet::new(),
        }
    }
}

impl<T: Clone + Eq + Hash> OrderedSet<T> {
    pub fn insert(&mut self, value: T) -> bool {
        if self.members.insert(value.clone()) {
            self.order.push(value);
            return true;
        }
        false
    }

    pub fn remove(&mut self, value: &T) {
        if self.members.remove(value) {
            self.order.retain(|existing| existing != value);
        }
    }

    pub fn contains(&self, value: &T) -> bool {
        self.members.contains(value)
    }

    pub fn is_empty(&self) -> bool {
        self.order.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.order.iter()
    }
}

impl<T: Clone + Eq + Hash> FromIterator<T> for OrderedSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut set = Self::default();
        for value in iter {
            set.insert(value);
        }
        set
    }
}

impl<T: Clone + Eq + Hash> Extend<T> for OrderedSet<T> {
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

#[cfg(test)]
mod tests {
    use super::*;

    /// The whole point: iteration follows the producer's order, and a repeat
    /// insertion neither duplicates the value nor moves it. Membership order is
    /// first-registration order, so a later re-registration cannot reshuffle
    /// what an earlier one established (fz-f98.19).
    #[test]
    fn iteration_follows_first_registration_order() {
        let mut set = OrderedSet::default();
        for value in ["c", "a", "b", "a", "c"] {
            set.insert(value);
        }

        assert_eq!(
            set.iter().copied().collect::<Vec<_>>(),
            vec!["c", "a", "b"],
            "iteration is registration order, and re-registering does not move a member",
        );
    }

    #[test]
    fn removing_a_member_leaves_the_rest_in_order() {
        let mut set: OrderedSet<&str> = ["c", "a", "b"].into_iter().collect();
        set.remove(&"a");

        assert!(!set.contains(&"a"), "a removed member is gone");
        assert_eq!(
            set.iter().copied().collect::<Vec<_>>(),
            vec!["c", "b"],
            "removal closes the gap without disturbing the surviving order",
        );
    }
}
