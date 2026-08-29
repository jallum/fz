use super::ordered_set::OrderedSet;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FactReadiness {
    Current,
    Settled,
}

/// The content algebra of a fact key. A **cumulative** fact's content is a
/// monotone join maintained by its store — between ground shifts it only
/// grows, so a content change is an ascent. A **replacing** fact's content
/// overwrites, so any content change can invalidate what readers derived
/// from it. This declares how content composes; it orders nothing.
pub trait ClaimShape {
    fn is_cumulative(&self) -> bool;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FactUse<F> {
    Current(F),
    Settled(F),
    SettledPresence(F),
}

impl<F> FactUse<F> {
    pub fn current(fact: F) -> Self {
        Self::Current(fact)
    }

    pub fn settled(fact: F) -> Self {
        Self::Settled(fact)
    }

    pub fn settled_presence(fact: F) -> Self {
        Self::SettledPresence(fact)
    }

    pub fn fact(&self) -> &F {
        match self {
            Self::Current(fact) | Self::Settled(fact) | Self::SettledPresence(fact) => fact,
        }
    }

    pub fn into_fact(self) -> F {
        match self {
            Self::Current(fact) | Self::Settled(fact) | Self::SettledPresence(fact) => fact,
        }
    }

    pub fn readiness(&self) -> FactReadiness {
        match self {
            Self::Current(_) => FactReadiness::Current,
            Self::Settled(_) | Self::SettledPresence(_) => FactReadiness::Settled,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FactState {
    pub revision: Option<u64>,
    pub settled: bool,
}

impl FactState {
    pub fn projected<F>(self, fact: &FactUse<F>) -> Self {
        match fact {
            FactUse::Current(_) => Self {
                revision: self.revision,
                settled: false,
            },
            FactUse::Settled(_) => self,
            FactUse::SettledPresence(_) => Self {
                revision: None,
                settled: self.settled,
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FactMovement<F> {
    pub key: F,
    pub state: FactState,
}

#[derive(Debug, Clone)]
pub struct FactReplace<F> {
    pub changed: Vec<FactChange<F>>,
    /// The keys this job now publishes, in the order the job emitted them.
    /// That order is load-bearing: it becomes the wake order downstream
    /// (fz-f98.19).
    pub output_keys: OrderedSet<F>,
}

/// One fact: the set of jobs that currently claim it, plus a monotonic
/// counter. State facts (ModuleDefined, FunctionDefined, …) have one
/// authority job; demand facts (Activation, Executable) are held by every
/// demander and stay present until the last one drops. The counter starts at
/// 1 on first appearance and increments each time any publisher signals
/// `changed = true`. Retraction (no publishers remain) is represented as
/// `revision() = None`.
///
/// Three separate questions (fz-kdt.44):
///
/// - **present** — any publisher claims it;
/// - **locally settled** — present and no publisher is queued to re-run;
/// - **settled** — locally settled AND no publisher is itself reading a fact
///   that can still move. `unfinal_publishers` is the second half: the
///   scheduler marks a publisher unfinal while any fact that publisher read is
///   not quiet, so finality is a property of the whole upstream cone rather
///   than of one hop.
///
/// A fact is **quiet** when nothing can move it: no dirty publisher and no
/// unfinal one. An absent fact is quiet — nobody is deriving it, so reading it
/// makes no reader unfinal (readers of a fact that later appears wake on its
/// first-appearance content movement instead).
#[derive(Debug, Clone)]
struct FactSlot<J> {
    publishers: HashSet<J>,
    dirty_publishers: HashSet<J>,
    unfinal_publishers: HashSet<J>,
    revision: u64,
}

impl<J> Default for FactSlot<J> {
    fn default() -> Self {
        Self {
            publishers: HashSet::new(),
            dirty_publishers: HashSet::new(),
            unfinal_publishers: HashSet::new(),
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

    fn is_locally_settled(&self) -> bool {
        !self.publishers.is_empty() && self.dirty_publishers.is_empty()
    }

    fn is_quiet(&self) -> bool {
        self.dirty_publishers.is_empty() && self.unfinal_publishers.is_empty()
    }

    fn is_settled(&self) -> bool {
        self.is_locally_settled() && self.unfinal_publishers.is_empty()
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

    /// Transitive finality: present, no publisher queued to re-run, and no
    /// publisher reading a fact that can still move. This is the ONE meaning
    /// of settled — `FactUse::Settled` projects it, telemetry renders it, and
    /// every product/job read of a settled fact asks this question.
    pub fn is_settled(&self, key: &F) -> bool {
        self.slots.get(key).is_some_and(FactSlot::is_settled)
    }

    /// Present with no publisher queued to re-run — the one-hop question.
    /// Separate from `is_settled` on purpose: local cleanliness is what the
    /// drain arbiter tests a cone's members for, and what tests assert to show
    /// the two are different questions.
    pub fn is_locally_settled(&self, key: &F) -> bool {
        self.slots.get(key).is_some_and(FactSlot::is_locally_settled)
    }

    /// Whether nothing can move this fact. Absent facts are quiet: no
    /// publisher is deriving them.
    pub fn is_quiet(&self, key: &F) -> bool {
        self.slots.get(key).is_none_or(FactSlot::is_quiet)
    }

    pub fn state(&self, key: &F) -> FactState {
        let Some(slot) = self.slots.get(key) else {
            return FactState {
                revision: None,
                settled: false,
            };
        };
        FactState {
            revision: slot.revision(),
            settled: slot.is_settled(),
        }
    }

    pub fn keys(&self) -> impl Iterator<Item = &F> {
        self.slots.keys()
    }

    pub fn satisfies(&self, fact_use: &FactUse<F>) -> bool {
        match fact_use {
            FactUse::Current(key) => self.revision(key).is_some(),
            FactUse::Settled(key) | FactUse::SettledPresence(key) => self.is_settled(key),
        }
    }

    /// Replaces one job's published facts. Keys the job previously published
    /// but no longer does lose that job's entry; a fact with no publishers
    /// left is retracted. The `changed` flag on each output means the job's
    /// content moved; the table increments the fact's revision only when that
    /// flag is set (or when the fact is newly appearing). A job may also mark
    /// one of its previous outputs as changed while retracting it if removing
    /// that contribution changes a still-present multi-publisher fact.
    pub fn replace_outputs(
        &mut self,
        job: &J,
        previous_output_keys: &OrderedSet<F>,
        outputs: Vec<F>,
        changed_keys: Vec<F>,
        publisher_unfinal: bool,
    ) -> FactReplace<F> {
        let mut output_keys = OrderedSet::default();
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
                output_keys.contains(key) || previous_output_keys.contains(key),
                "job marked a fact changed that it neither publishes nor previously owned"
            );
        }
        // Emission order first, then whatever this job used to own and no longer
        // does. Both halves are ordered, so `touched` is too — and `touched`
        // becomes the wake order (fz-f98.19).
        let touched = output_keys
            .iter()
            .cloned()
            .chain(previous_output_keys.iter().cloned())
            .collect::<OrderedSet<_>>();

        let mut changed = Vec::new();
        for key in &touched {
            let key = key.clone();
            let mut slot = self.slots.remove(&key).unwrap_or_default();
            let old_revision = slot.revision();
            let old_settled = slot.is_settled();

            if output_keys.contains(&key) {
                let was_absent = slot.publishers.is_empty();
                slot.publishers.insert(job.clone());
                slot.dirty_publishers.remove(job);
                set_membership(&mut slot.unfinal_publishers, job, publisher_unfinal);
                if was_absent {
                    slot.revision = 1;
                } else if changed_keys_set.remove(&key) {
                    slot.revision += 1;
                }
            } else {
                slot.publishers.remove(job);
                slot.dirty_publishers.remove(job);
                slot.unfinal_publishers.remove(job);
                if changed_keys_set.remove(&key) && !slot.publishers.is_empty() {
                    slot.revision += 1;
                }
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

    /// Extend one job's published facts without retracting anything. The
    /// waiting-completion arm: listed keys gain the job as publisher (revision
    /// rules identical to `replace_outputs`), unlisted keys the job previously
    /// claimed are left standing untouched. Dirtiness is NOT cleared for the
    /// listed keys — a blocked publisher is not vouching yet; the caller marks
    /// the job's full claim set dirty after extending.
    pub fn extend_outputs(
        &mut self,
        job: &J,
        outputs: Vec<F>,
        changed_keys: Vec<F>,
        publisher_unfinal: bool,
    ) -> FactReplace<F> {
        let mut output_keys = OrderedSet::default();
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

        let mut changed = Vec::new();
        for key in &output_keys {
            let mut slot = self.slots.remove(key).unwrap_or_default();
            let old_revision = slot.revision();
            let old_settled = slot.is_settled();

            let was_absent = slot.publishers.is_empty();
            slot.publishers.insert(job.clone());
            set_membership(&mut slot.unfinal_publishers, job, publisher_unfinal);
            if was_absent {
                slot.revision = 1;
            } else if changed_keys_set.remove(key) {
                slot.revision += 1;
            }

            let new_revision = slot.revision();
            let new_settled = slot.is_settled();
            self.slots.insert(key.clone(), slot);

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

        FactReplace { changed, output_keys }
    }

    /// Records whether `job` — a publisher of `key` — is itself reading a fact
    /// that can still move. Returns the settled-bit change if the projection
    /// moved. Edge-triggered: the scheduler calls this exactly when a job's own
    /// finality flips, never on every movement.
    pub fn set_publisher_unfinal(&mut self, key: &F, job: &J, unfinal: bool) -> Option<FactChange<F>> {
        let slot = self.slots.get_mut(key)?;
        if !slot.publishers.contains(job) {
            return None;
        }
        let old_settled = slot.is_settled();
        set_membership(&mut slot.unfinal_publishers, job, unfinal);
        let new_settled = slot.is_settled();
        let revision = slot.revision();
        (old_settled != new_settled).then(|| FactChange {
            key: key.clone(),
            old_revision: revision,
            new_revision: revision,
            old_settled,
            new_settled,
        })
    }

    /// Declares every publisher of `key` final. The drain arbiter's write:
    /// with nothing left to run, a locally clean cone that holds no dirty fact
    /// cannot move, so the counts that a cycle can never lower are discharged
    /// wholesale. Returns the settled-bit change if the projection moved.
    pub fn clear_unfinal_publishers(&mut self, key: &F) -> Option<FactChange<F>> {
        let slot = self.slots.get_mut(key)?;
        let old_settled = slot.is_settled();
        slot.unfinal_publishers.clear();
        let new_settled = slot.is_settled();
        let revision = slot.revision();
        (old_settled != new_settled).then(|| FactChange {
            key: key.clone(),
            old_revision: revision,
            new_revision: revision,
            old_settled,
            new_settled,
        })
    }

    pub fn mark_dirty(&mut self, job: &J, output_keys: &OrderedSet<F>) -> Vec<FactChange<F>> {
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

fn set_membership<J: Clone + Eq + Hash>(set: &mut HashSet<J>, job: &J, member: bool) {
    if member {
        set.insert(job.clone());
    } else {
        set.remove(job);
    }
}
