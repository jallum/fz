use std::collections::{HashMap, HashSet};
use std::hash::Hash;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FactChange<F> {
    pub key: F,
    pub old_revision: Option<u64>,
    pub new_revision: Option<u64>,
}

#[derive(Debug, Clone)]
pub struct FactReplace<F> {
    pub changed: Vec<FactChange<F>>,
    pub output_keys: HashSet<F>,
}

/// One fact: the set of jobs that currently claim it, plus a monotonic
/// counter. State facts (ModuleDefined, FunctionDefined, …) have one
/// authority job; demand facts (Activation, Executable) are held by every
/// demander and stay present until the last one drops. The counter starts at
/// 1 on first appearance and increments each time any publisher signals
/// `changed = true`. Retraction (no publishers remain) is represented as
/// `revision() = None`.
#[derive(Debug, Clone)]
struct FactSlot<J> {
    publishers: HashSet<J>,
    revision: u64,
}

impl<J> Default for FactSlot<J> {
    fn default() -> Self {
        Self {
            publishers: HashSet::new(),
            revision: 0,
        }
    }
}

impl<J> FactSlot<J> {
    fn revision(&self) -> Option<u64> {
        if self.publishers.is_empty() {
            None
        } else {
            Some(self.revision)
        }
    }
}

#[derive(Debug)]
pub struct FactTable<J, F> {
    slots: HashMap<F, FactSlot<J>>,
}

impl<J, F> Default for FactTable<J, F> {
    fn default() -> Self {
        Self { slots: HashMap::new() }
    }
}

impl<J, F> FactTable<J, F>
where
    J: Clone + Eq + Hash,
    F: Clone + Eq + Hash,
{
    pub fn new() -> Self {
        Self::default()
    }

    pub fn revision(&self, key: &F) -> Option<u64> {
        self.slots.get(key).and_then(FactSlot::revision)
    }

    /// Replaces one job's published facts. Keys the job previously published
    /// but no longer does lose that job's entry; a fact with no publishers
    /// left is retracted. The `changed` flag on each output means the job's
    /// content moved; the table increments the fact's revision only when that
    /// flag is set (or when the fact is newly appearing).
    pub fn replace_outputs(
        &mut self,
        job: &J,
        previous_output_keys: &HashSet<F>,
        outputs: Vec<(F, bool)>,
    ) -> FactReplace<F> {
        let mut new_outputs = HashMap::new();
        for (key, content_changed) in outputs {
            assert!(
                new_outputs.insert(key, content_changed).is_none(),
                "job emitted duplicate fact output for one key"
            );
        }
        let output_keys = new_outputs.keys().cloned().collect::<HashSet<_>>();
        let touched = previous_output_keys
            .iter()
            .cloned()
            .chain(output_keys.iter().cloned())
            .collect::<HashSet<_>>();

        let mut changed = Vec::new();
        for key in touched {
            let mut slot = self.slots.remove(&key).unwrap_or_default();
            let old_revision = slot.revision();

            if let Some(content_changed) = new_outputs.remove(&key) {
                let was_absent = slot.publishers.is_empty();
                slot.publishers.insert(job.clone());
                if was_absent {
                    slot.revision = 1;
                } else if content_changed {
                    slot.revision += 1;
                }
            } else {
                slot.publishers.remove(job);
            }

            let new_revision = slot.revision();
            if !slot.publishers.is_empty() {
                self.slots.insert(key.clone(), slot);
            }

            if old_revision != new_revision {
                changed.push(FactChange {
                    key,
                    old_revision,
                    new_revision,
                });
            }
        }

        FactReplace { changed, output_keys }
    }
}
