use super::ordered_set::OrderedSet;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FactReadiness {
    Current,
    Settled,
}

/// Which of a job's answers a claim belongs to. A job that reaches one
/// conclusion has one derivation (`DerivationId::SOLE`); a job whose body
/// answers several independent questions names one id per question, and each
/// carries its own reads, its own claims and its own finality.
///
/// The id is opaque to the engine and minted by the job: the engine never
/// interprets it, it only keeps claims that came from different reads apart.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DerivationId(pub u32);

impl DerivationId {
    /// The derivation of a job whose whole body is one answer. Every job that
    /// does not name derivations publishes under this one.
    pub const SOLE: Self = Self(0);
}

/// The ledger's publisher identity: one job's one derivation. This is what
/// claims a fact, what carries reads, and what finality is a property of.
///
/// It is deliberately NOT the agenda's identity — a job runs whole, so the
/// agenda, the `rebased` set and waits stay keyed by `J`. Splitting the two
/// identities is the point: `enqueue_dependents` wakes the JOB while dirtying
/// only the DERIVATION whose read moved.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Publisher<J> {
    pub job: J,
    pub derivation: DerivationId,
}

impl<J> Publisher<J> {
    pub fn new(job: J, derivation: DerivationId) -> Self {
        Self { job, derivation }
    }
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

/// One fact: the set of PUBLISHERS that currently claim it, plus a monotonic
/// counter. A publisher is one job's one derivation (`Publisher`), never the
/// job: a job that answers several independent questions holds one claim per
/// answer, and a claim carries the reads of the answer it came from. State
/// facts (ModuleDefined, FunctionDefined, …) have one authority publisher;
/// demand facts (Activation, Executable) are held by every demander and stay
/// present until the last one drops. The counter starts at 1 on first
/// appearance and increments each time any publisher signals `changed = true`.
/// Retraction (no publishers remain) is represented as `revision() = None`.
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
/// All three sets are keyed by the SAME publisher identity (fz-kdt.13.1).
/// That is what makes them composable: `is_settled` is one statement about one
/// derivation's claim, so a sibling derivation of the same job being dirty
/// says nothing about this fact. Per-output dirty bits sitting beside
/// per-JOB unfinality would not compose — the dirty half would be scoped to
/// the answer while the unfinal half stayed scoped to the body, and the two
/// halves of `is_settled` would then be about different things.
///
/// A fact is **quiet** when nothing can move it: no dirty publisher and no
/// unfinal one. An absent fact is quiet — nobody is deriving it, so reading it
/// makes no reader unfinal (readers of a fact that later appears wake on its
/// first-appearance content movement instead).
#[derive(Debug, Clone)]
struct FactSlot<P> {
    publishers: HashSet<P>,
    dirty_publishers: HashSet<P>,
    unfinal_publishers: HashSet<P>,
    revision: u64,
}

impl<P> Default for FactSlot<P> {
    fn default() -> Self {
        Self {
            publishers: HashSet::new(),
            dirty_publishers: HashSet::new(),
            unfinal_publishers: HashSet::new(),
            revision: 0,
        }
    }
}

impl<P> FactSlot<P> {
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
pub struct FactTable<P, F> {
    slots: HashMap<F, FactSlot<P>>,
}

impl<P, F> Default for FactTable<P, F> {
    fn default() -> Self {
        Self { slots: HashMap::new() }
    }
}

impl<P, F> FactTable<P, F>
where
    P: Clone + Eq + Hash,
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

    /// Present with no publisher queued to re-run — the one-hop question,
    /// asked of the derivations that claim this fact and of nothing else.
    /// Separate from `is_settled` on purpose: local cleanliness is what the
    /// drain arbiter tests a cone's members for, and what tests assert to show
    /// the two are different questions. A dirty sibling derivation of the same
    /// job enters this answer exactly when it also claims this key -- which,
    /// by the contract that each derivation owns its own keys, it does not;
    /// the engine does not enforce key-disjointness, the derivation authors do.
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

    /// Replaces one publisher's published facts. Keys the publisher
    /// previously published but no longer does lose its entry; a fact with no
    /// publishers left is retracted. The `changed` flag on each output means
    /// the publisher's content moved; the table increments the fact's revision
    /// only when that flag is set (or when the fact is newly appearing). A
    /// publisher may also mark one of its previous outputs as changed while
    /// retracting it if removing that contribution changes a still-present
    /// multi-publisher fact.
    pub fn replace_outputs(
        &mut self,
        publisher: &P,
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
                slot.publishers.insert(publisher.clone());
                slot.dirty_publishers.remove(publisher);
                set_membership(&mut slot.unfinal_publishers, publisher, publisher_unfinal);
                if was_absent {
                    slot.revision = 1;
                } else if changed_keys_set.remove(&key) {
                    slot.revision += 1;
                }
            } else {
                slot.publishers.remove(publisher);
                slot.dirty_publishers.remove(publisher);
                slot.unfinal_publishers.remove(publisher);
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

    /// Extend one publisher's published facts without retracting anything.
    /// The arm for a derivation that did not reach its own conclusion: listed
    /// keys gain the publisher (revision rules identical to `replace_outputs`),
    /// unlisted keys it previously claimed are left standing untouched.
    /// Dirtiness is NOT cleared for the listed keys — an unreached derivation
    /// is not vouching yet; the caller marks that derivation's full claim set
    /// dirty after extending.
    pub fn extend_outputs(
        &mut self,
        publisher: &P,
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
            slot.publishers.insert(publisher.clone());
            set_membership(&mut slot.unfinal_publishers, publisher, publisher_unfinal);
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

    /// Records whether `publisher` — a claimant of `key` — is itself reading a
    /// fact that can still move. Returns the settled-bit change if the
    /// projection moved. Edge-triggered: the scheduler calls this exactly when
    /// that derivation's own finality flips, never on every movement.
    pub fn set_publisher_unfinal(&mut self, key: &F, publisher: &P, unfinal: bool) -> Option<FactChange<F>> {
        let slot = self.slots.get_mut(key)?;
        if !slot.publishers.contains(publisher) {
            return None;
        }
        let old_settled = slot.is_settled();
        set_membership(&mut slot.unfinal_publishers, publisher, unfinal);
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
    ///
    /// The argument survives derivation granularity verbatim, because it was
    /// never about jobs: it is about the CLAIMANTS of this key. Those are the
    /// derivations named in the slot, so "nothing can move this fact" reads
    /// exactly the derivations whose answers it is, and a dirty sibling
    /// derivation — which publishes other keys — is correctly not consulted.
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

    pub fn mark_dirty(&mut self, publisher: &P, output_keys: &OrderedSet<F>) -> Vec<FactChange<F>> {
        let mut changed = Vec::new();
        for key in output_keys {
            let Some(slot) = self.slots.get_mut(key) else {
                continue;
            };
            if !slot.publishers.contains(publisher) {
                continue;
            }
            let old_revision = slot.revision();
            let old_settled = slot.is_settled();
            if !slot.dirty_publishers.insert(publisher.clone()) {
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

fn set_membership<P: Clone + Eq + Hash>(set: &mut HashSet<P>, publisher: &P, member: bool) {
    if member {
        set.insert(publisher.clone());
    } else {
        set.remove(publisher);
    }
}
