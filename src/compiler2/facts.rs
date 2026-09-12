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
    content_movement: Option<ContentMovement>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ContentMovement {
    Ascent,
    Shift,
}

impl<F> FactChange<F> {
    pub(crate) fn replacing(
        key: F,
        old_revision: Option<u64>,
        new_revision: Option<u64>,
        old_settled: bool,
        new_settled: bool,
    ) -> Self {
        let content_movement = if old_revision.unwrap_or(0) == new_revision.unwrap_or(0) {
            None
        } else if old_revision.is_none() {
            Some(ContentMovement::Ascent)
        } else {
            Some(ContentMovement::Shift)
        };
        Self {
            key,
            old_revision,
            new_revision,
            old_settled,
            new_settled,
            content_movement,
        }
    }

    /// Whether what a `Current` reader can see moved.
    ///
    /// Absent and present-at-bottom read the same, so `None` <-> `Some(0)` is
    /// not a content movement in either direction: appearing at bottom
    /// announces a publisher, and a bottom claim's retraction takes away
    /// nothing anyone could have read. Only a cumulative fact is ever minted
    /// at 0 (`appearance_revision`), so every replacing fact's appearance and
    /// retraction still moves — `Some(n > 0)` <-> `None` included.
    pub fn content_changed(&self) -> bool {
        self.content_movement.is_some()
    }

    pub(crate) fn content_movement(&self) -> Option<ContentMovement> {
        self.content_movement
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
/// counter. Each publisher is the job owning the claim and its reads. State
/// facts (ModuleDefined, FunctionDefined, …) have one authority publisher;
/// demand facts (Activation, Executable) are held by every demander and stay
/// present until the last one drops. The counter is set by
/// `appearance_revision` when the fact gains its first publisher — 1 for a
/// replacing fact, 0 for a cumulative one claimed with no content — and
/// increments each time any publisher signals `changed = true`. Retraction (no
/// publishers remain) is represented as `revision() = None`.
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
/// All three sets use the same job identity. A job's co-outputs share its
/// reads, cleanliness, and finality.
///
/// A fact is **quiet** when nothing can move it: no dirty publisher and no
/// unfinal one. An absent fact is quiet — nobody is deriving it, so reading it
/// makes no reader unfinal. A reader of the absent key wakes on the fact's
/// first CONTENT movement, which for a replacing fact is its appearance and
/// for a cumulative one is its first claim carrying evidence; if the publisher
/// that claimed the key at bottom is still deriving, the key is unquiet and
/// that reader unfinalises through the ordinary wave.
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
    F: Clone + Eq + Hash + ClaimShape,
{
    pub fn new() -> Self {
        Self::default()
    }

    pub fn revision(&self, key: &F) -> Option<u64> {
        self.slots.get(key).and_then(FactSlot::revision)
    }

    pub(crate) fn publishers(&self, key: &F) -> impl Iterator<Item = &P> {
        self.slots.get(key).into_iter().flat_map(|slot| &slot.publishers)
    }

    /// Transitive finality: present, no publisher queued to re-run, and no
    /// publisher reading a fact that can still move. This is the ONE meaning
    /// of settled — `FactUse::Settled` projects it, telemetry renders it, and
    /// every product/job read of a settled fact asks this question.
    pub fn is_settled(&self, key: &F) -> bool {
        self.slots.get(key).is_some_and(FactSlot::is_settled)
    }

    /// Present with no publisher queued to re-run — the one-hop question,
    /// asked of the jobs that claim this fact and of nothing else.
    /// Separate from `is_settled` on purpose: local cleanliness is what the
    /// drain arbiter tests before certifying a requested fact's publishers.
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
            FactUse::Settled(key) => self.is_settled(key),
        }
    }

    /// Replaces one publisher's published facts. Keys the publisher
    /// previously published but no longer does lose its entry; a fact with no
    /// publishers left is retracted. The `changed` flag on each output means
    /// the publisher's content moved; the table increments the fact's revision
    /// only when that flag is set. A newly appearing fact is minted by
    /// `appearance_revision`, which reads the flag too: an unflagged cumulative
    /// claim appears at bottom and moves nothing. A
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
        self.replace_outputs_after_run(
            publisher,
            previous_output_keys,
            outputs,
            changed_keys,
            publisher_unfinal,
            false,
        )
    }

    pub(crate) fn replace_outputs_after_run(
        &mut self,
        publisher: &P,
        previous_output_keys: &OrderedSet<F>,
        outputs: Vec<F>,
        changed_keys: Vec<F>,
        publisher_unfinal: bool,
        publisher_rebased: bool,
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
            let withdrew_publisher = !output_keys.contains(&key) && slot.publishers.contains(publisher);

            if output_keys.contains(&key) {
                let was_absent = slot.publishers.is_empty();
                let changed_listed = changed_keys_set.remove(&key);
                slot.publishers.insert(publisher.clone());
                slot.dirty_publishers.remove(publisher);
                set_membership(&mut slot.unfinal_publishers, publisher, publisher_unfinal);
                if was_absent {
                    slot.revision = appearance_revision(&key, changed_listed);
                } else if changed_listed {
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
                    content_movement: content_movement(
                        &key,
                        old_revision,
                        new_revision,
                        publisher_rebased,
                        withdrew_publisher,
                    ),
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
    /// The arm for a job that did not reach its own conclusion: listed
    /// keys gain the publisher (revision rules identical to `replace_outputs`),
    /// unlisted keys it previously claimed are left standing untouched.
    /// Dirtiness is NOT cleared for the listed keys — an unreached job
    /// is not vouching yet; the caller marks that job's full claim set
    /// dirty after extending.
    pub fn extend_outputs(
        &mut self,
        publisher: &P,
        outputs: Vec<F>,
        changed_keys: Vec<F>,
        publisher_unfinal: bool,
    ) -> FactReplace<F> {
        self.extend_outputs_after_run(publisher, outputs, changed_keys, publisher_unfinal, false)
    }

    pub(crate) fn extend_outputs_after_run(
        &mut self,
        publisher: &P,
        outputs: Vec<F>,
        changed_keys: Vec<F>,
        publisher_unfinal: bool,
        publisher_rebased: bool,
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
            let changed_listed = changed_keys_set.remove(key);
            slot.publishers.insert(publisher.clone());
            set_membership(&mut slot.unfinal_publishers, publisher, publisher_unfinal);
            if was_absent {
                slot.revision = appearance_revision(key, changed_listed);
            } else if changed_listed {
                slot.revision += 1;
            }

            let new_revision = slot.revision();
            let new_settled = slot.is_settled();
            self.slots.insert(key.clone(), slot);

            if old_revision != new_revision || old_settled != new_settled {
                changed.push(FactChange {
                    content_movement: content_movement(key, old_revision, new_revision, publisher_rebased, false),
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
    /// that job's own finality flips, never on every movement.
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
            content_movement: None,
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
                    content_movement: None,
                });
            }
        }
        changed
    }
}

fn content_movement<F: ClaimShape>(
    key: &F,
    old_revision: Option<u64>,
    new_revision: Option<u64>,
    publisher_rebased: bool,
    withdrew_publisher: bool,
) -> Option<ContentMovement> {
    if old_revision.unwrap_or(0) == new_revision.unwrap_or(0) {
        return None;
    }
    if old_revision.is_none() {
        return Some(ContentMovement::Ascent);
    }
    if new_revision.is_none() || withdrew_publisher || publisher_rebased || !key.is_cumulative() {
        return Some(ContentMovement::Shift);
    }
    Some(ContentMovement::Ascent)
}

/// The revision a fact is minted at when it first gains a publisher.
///
/// For a CUMULATIVE fact, absence and bottom are the same reading: its store
/// maintains a join, a join has a bottom, and a `Current` reader of the empty
/// join gets exactly what a reader of the absent key gets. So a first claim
/// that lists no content is PRESENCE, not content, and it is minted at
/// revision 0 -- present, at bottom, no movement to wake anyone with.
///
/// For a REPLACING fact there is no bottom to be at: whatever it says on
/// arrival is content its readers can see, so first appearance is revision 1
/// and moves.
/// PRECONDITION (asserted at the publisher): a cumulative fact's store must
/// be empty whenever its fact is absent -- revision 0 means "present at
/// bottom", and a store remnant surviving a retraction would make that a lie.
fn appearance_revision<F: ClaimShape>(key: &F, changed_listed: bool) -> u64 {
    u64::from(changed_listed || !key.is_cumulative())
}

fn set_membership<P: Clone + Eq + Hash>(set: &mut HashSet<P>, publisher: &P, member: bool) {
    if member {
        set.insert(publisher.clone());
    } else {
        set.remove(publisher);
    }
}
