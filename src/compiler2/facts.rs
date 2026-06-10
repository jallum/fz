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

/// One fact: the revisions its publishers last published. State facts
/// (ModuleDefined, FunctionDefined, ...) have one authority job. Demand facts
/// (Activation, Executable) are published by every demander and stay present
/// until the last one retracts. The settled revision is the max over
/// publishers — the revision itself is whatever 64-bit value the fact's
/// reconcile chose; the table only stores it and propagates when it moves.
#[derive(Debug, Clone)]
struct FactSlot<J> {
    publishers: HashMap<J, u64>,
}

impl<J> Default for FactSlot<J> {
    fn default() -> Self {
        Self {
            publishers: HashMap::new(),
        }
    }
}

impl<J> FactSlot<J> {
    fn revision(&self) -> Option<u64> {
        self.publishers.values().copied().max()
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
    /// left is retracted.
    pub fn replace_outputs(
        &mut self,
        job: &J,
        previous_output_keys: &HashSet<F>,
        outputs: Vec<(F, u64)>,
    ) -> FactReplace<F> {
        let mut new_outputs = HashMap::new();
        for (key, revision) in outputs {
            assert!(
                new_outputs.insert(key, revision).is_none(),
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

            if let Some(revision) = new_outputs.remove(&key) {
                slot.publishers.insert(job.clone(), revision);
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
