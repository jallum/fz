use std::collections::{HashMap, HashSet};
use std::hash::Hash;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FactReadiness {
    Current,
    Settled,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FactUse<F> {
    Current(F),
    Settled(F),
}

impl<F> FactUse<F> {
    pub fn current(fact: F) -> Self {
        Self::Current(fact)
    }

    pub fn settled(fact: F) -> Self {
        Self::Settled(fact)
    }

    pub fn fact(&self) -> &F {
        match self {
            Self::Current(fact) | Self::Settled(fact) => fact,
        }
    }

    pub fn into_fact(self) -> F {
        match self {
            Self::Current(fact) | Self::Settled(fact) => fact,
        }
    }

    pub fn readiness(&self) -> FactReadiness {
        match self {
            Self::Current(_) => FactReadiness::Current,
            Self::Settled(_) => FactReadiness::Settled,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FactChange<F> {
    pub key: F,
    pub old_revision: Option<u64>,
    pub new_revision: Option<u64>,
    pub old_settled: bool,
    pub new_settled: bool,
}

impl<F> FactChange<F> {
    pub fn content_changed(&self) -> bool {
        self.old_revision != self.new_revision
    }

    pub fn readiness_changed(&self) -> bool {
        self.old_settled != self.new_settled
    }
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
    dirty_publishers: HashSet<J>,
    revision: u64,
}

impl<J> Default for FactSlot<J> {
    fn default() -> Self {
        Self {
            publishers: HashSet::new(),
            dirty_publishers: HashSet::new(),
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

    fn is_settled(&self) -> bool {
        !self.publishers.is_empty() && self.dirty_publishers.is_empty()
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

    pub fn is_settled(&self, key: &F) -> bool {
        self.slots.get(key).is_some_and(FactSlot::is_settled)
    }

    pub fn satisfies(&self, fact_use: &FactUse<F>) -> bool {
        match fact_use {
            FactUse::Current(key) => self.revision(key).is_some(),
            FactUse::Settled(key) => self.is_settled(key),
        }
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
        outputs: Vec<F>,
        changed_keys: Vec<F>,
    ) -> FactReplace<F> {
        let mut output_keys = HashSet::new();
        for key in outputs {
            assert!(output_keys.insert(key), "job emitted duplicate fact output for one key");
        }
        let mut changed_keys_set = HashSet::new();
        for key in changed_keys {
            assert!(
                changed_keys_set.insert(key),
                "job emitted duplicate changed fact for one key"
            );
        }
        for key in &changed_keys_set {
            assert!(
                output_keys.contains(key),
                "job marked a fact changed that it does not publish"
            );
        }
        let touched = previous_output_keys
            .iter()
            .cloned()
            .chain(output_keys.iter().cloned())
            .collect::<HashSet<_>>();

        let mut changed = Vec::new();
        for key in touched {
            let mut slot = self.slots.remove(&key).unwrap_or_default();
            let old_revision = slot.revision();
            let old_settled = slot.is_settled();

            if output_keys.contains(&key) {
                let was_absent = slot.publishers.is_empty();
                slot.publishers.insert(job.clone());
                slot.dirty_publishers.remove(job);
                if was_absent {
                    slot.revision = 1;
                } else if changed_keys_set.remove(&key) {
                    slot.revision += 1;
                }
            } else {
                slot.publishers.remove(job);
                slot.dirty_publishers.remove(job);
            }

            let new_revision = slot.revision();
            let new_settled = slot.is_settled();
            if !slot.publishers.is_empty() {
                self.slots.insert(key.clone(), slot);
            }

            if old_revision != new_revision || old_settled != new_settled {
                changed.push(FactChange {
                    key,
                    old_revision,
                    new_revision,
                    old_settled,
                    new_settled,
                });
            }
        }

        FactReplace { changed, output_keys }
    }

    pub fn mark_dirty(&mut self, job: &J, output_keys: &HashSet<F>) -> Vec<FactChange<F>> {
        let mut changed = Vec::new();
        for key in output_keys {
            let Some(slot) = self.slots.get_mut(key) else {
                continue;
            };
            if !slot.publishers.contains(job) {
                continue;
            }
            let old_revision = slot.revision();
            let old_settled = slot.is_settled();
            if !slot.dirty_publishers.insert(job.clone()) {
                continue;
            }
            let new_revision = slot.revision();
            let new_settled = slot.is_settled();
            if old_revision != new_revision || old_settled != new_settled {
                changed.push(FactChange {
                    key: key.clone(),
                    old_revision,
                    new_revision,
                    old_settled,
                    new_settled,
                });
            }
        }
        changed
    }
}
