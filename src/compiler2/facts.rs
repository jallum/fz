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

#[derive(Debug, Clone)]
pub struct FactSlot<J> {
    revision: Option<u64>,
    contributions: HashMap<J, u64>,
}

impl<J> Default for FactSlot<J> {
    fn default() -> Self {
        Self {
            revision: None,
            contributions: HashMap::new(),
        }
    }
}

impl<J> FactSlot<J> {
    pub fn revision(&self) -> Option<u64> {
        self.revision
    }

    pub fn contributions(&self) -> &HashMap<J, u64> {
        &self.contributions
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

    pub fn get(&self, key: &F) -> Option<u64> {
        self.slots.get(key).and_then(FactSlot::revision)
    }

    pub fn slot(&self, key: &F) -> Option<&FactSlot<J>> {
        self.slots.get(key)
    }

    pub fn replace_contributions(
        &mut self,
        job: &J,
        previous_output_keys: &HashSet<F>,
        outputs: Vec<(F, u64)>,
    ) -> FactReplace<F> {
        let mut new_outputs = HashMap::new();
        for (key, value) in outputs {
            assert!(
                new_outputs.insert(key, value).is_none(),
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
            let old_revision = slot.revision;

            if let Some(value) = new_outputs.remove(&key) {
                slot.contributions.insert(job.clone(), value);
            } else {
                slot.contributions.remove(job);
            }

            let new_revision = slot.contributions.values().copied().max();
            if let Some(revision) = new_revision {
                slot.revision = Some(revision);
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
