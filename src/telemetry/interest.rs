//! The set of event-name prefixes someone listens to.
//!
//! Attaching a listener adds its prefix and detaching removes it, so the
//! answer to "does anyone listen to this event" is decided when listeners
//! change. Asking walks the segments of the event name through a trie: its cost
//! is bounded by the name's length and does not grow with the number of
//! listeners.

#[derive(Default)]
pub(super) struct Interest {
    registrations: usize,
    children: Vec<(&'static str, Interest)>,
}

impl Interest {
    pub(super) fn add(&mut self, prefix: &[&'static str]) {
        let Some((segment, rest)) = prefix.split_first() else {
            self.registrations += 1;
            return;
        };
        let position = match self.children.iter().position(|(child, _)| child == segment) {
            Some(position) => position,
            None => {
                self.children.push((segment, Interest::default()));
                self.children.len() - 1
            }
        };
        self.children[position].1.add(rest);
    }

    /// Removes one registration of `prefix`, pruning branches that no longer
    /// lead to a listener.
    pub(super) fn remove(&mut self, prefix: &[&'static str]) {
        let Some((segment, rest)) = prefix.split_first() else {
            self.registrations -= 1;
            return;
        };
        let position = self
            .children
            .iter()
            .position(|(child, _)| child == segment)
            .expect("a removed prefix was added");
        self.children[position].1.remove(rest);
        if self.children[position].1.is_empty() {
            self.children.swap_remove(position);
        }
    }

    /// Whether some added prefix is a prefix of `name`.
    pub(super) fn observes(&self, name: &[&'static str]) -> bool {
        let mut node = self;
        let mut rest = name;
        loop {
            if node.registrations > 0 {
                return true;
            }
            let Some((segment, tail)) = rest.split_first() else {
                return false;
            };
            let Some((_, child)) = node.children.iter().find(|(child, _)| child == segment) else {
                return false;
            };
            node = child;
            rest = tail;
        }
    }

    fn is_empty(&self) -> bool {
        self.registrations == 0 && self.children.is_empty()
    }
}

#[cfg(test)]
#[path = "interest_test.rs"]
mod interest_test;
