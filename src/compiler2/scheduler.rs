use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;

use super::agenda::Agenda;
use super::deps::{DependencyIndex, UnresolvedWait};
use super::facts::{FactChange, FactTable, FactUse};

#[derive(Debug, Clone)]
pub struct AppliedStep<J, F> {
    pub changed: Vec<FactChange<F>>,
    pub enqueued: Vec<J>,
    pub coalesced: Vec<J>,
    pub blocked: Vec<FactUse<F>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FatalError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DriveOutcome<J, F> {
    Resolved,
    Unresolved { waits: Vec<UnresolvedWait<J, F>> },
    Fatal { job: J },
    TimedOut { jobs_ran: u64, pending_jobs: usize },
}

#[derive(Debug)]
pub struct Scheduler<J, F> {
    agenda: Agenda<J>,
    facts: FactTable<J, F>,
    deps: DependencyIndex<J, F>,
}

impl<J, F> Default for Scheduler<J, F>
where
    J: Clone + Debug + Eq + Hash,
    F: Clone + Eq + Hash,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<J, F> Scheduler<J, F>
where
    J: Clone + Debug + Eq + Hash,
    F: Clone + Eq + Hash,
{
    pub fn new() -> Self {
        Self {
            agenda: Agenda::new(),
            facts: FactTable::new(),
            deps: DependencyIndex::new(),
        }
    }

    pub fn pending_jobs(&self) -> usize {
        self.agenda.len()
    }

    pub fn facts(&self) -> &FactTable<J, F> {
        &self.facts
    }

    pub fn has_unresolved(&self) -> bool {
        self.deps.has_unresolved()
    }

    pub fn unresolved(&self) -> Vec<UnresolvedWait<J, F>> {
        self.deps.unresolved()
    }

    pub fn enqueue(&mut self, job: J) -> bool {
        self.agenda.enqueue(job)
    }

    pub fn pop(&mut self) -> Option<J> {
        self.agenda.pop()
    }

    /// Apply one job completion. The semantics bifurcate on `waits`:
    ///
    /// **Concluding** (waits empty) replaces — reads swap subscriptions,
    /// outputs replace claims (retraction-by-omission is available and final).
    ///
    /// **Waiting** (waits non-empty) extends — reads union into the standing
    /// subscriptions, listed outputs union into the standing claims, nothing
    /// retracts, and every claim the job holds is marked dirty so a blocked
    /// publisher's facts never read as settled. Pausing is not recanting.
    pub fn complete(
        &mut self,
        job: &J,
        reads: HashSet<FactUse<F>>,
        waits: HashSet<FactUse<F>>,
        outputs: Vec<F>,
        changed: Vec<F>,
        follow_up: Vec<J>,
    ) -> AppliedStep<J, F> {
        let waiting = !waits.is_empty();
        let blocked = waits.iter().cloned().collect();
        if waiting {
            self.deps.union_reads(job.clone(), reads);
        } else {
            self.deps.replace_reads(job.clone(), reads);
        }
        self.deps.replace_waits(job.clone(), waits);

        let previous_output_keys = self.deps.output_keys(job);
        let mut dirtied = Vec::new();
        let replaced = if waiting {
            let extended = self.facts.extend_outputs(job, outputs, changed);
            let mut claims = previous_output_keys;
            claims.extend(extended.output_keys.iter().cloned());
            dirtied = self.facts.mark_dirty(job, &claims);
            self.deps.replace_outputs(job.clone(), claims);
            extended
        } else {
            let concluded = self.facts.replace_outputs(job, &previous_output_keys, outputs, changed);
            self.deps.replace_outputs(job.clone(), concluded.output_keys.clone());
            concluded
        };

        let mut enqueued = Vec::new();
        let mut coalesced = Vec::new();
        let mut coalesced_seen = HashSet::new();
        let mut pending_changes = replaced.changed.clone();
        pending_changes.extend(dirtied);
        while let Some(change) = pending_changes.pop() {
            if change.content_changed() {
                self.enqueue_dependents(
                    FactUse::current(change.key.clone()),
                    &mut pending_changes,
                    &mut enqueued,
                    &mut coalesced,
                    &mut coalesced_seen,
                );
                self.enqueue_dependents(
                    FactUse::settled(change.key.clone()),
                    &mut pending_changes,
                    &mut enqueued,
                    &mut coalesced,
                    &mut coalesced_seen,
                );
            } else if change.readiness_changed() {
                self.enqueue_dependents(
                    FactUse::settled(change.key.clone()),
                    &mut pending_changes,
                    &mut enqueued,
                    &mut coalesced,
                    &mut coalesced_seen,
                );
            }
        }
        for follow_up in follow_up {
            self.enqueue_step(follow_up, &mut enqueued, &mut coalesced, &mut coalesced_seen);
        }

        AppliedStep {
            changed: replaced.changed,
            enqueued,
            coalesced,
            blocked,
        }
    }

    fn enqueue_step(&mut self, job: J, enqueued: &mut Vec<J>, coalesced: &mut Vec<J>, coalesced_seen: &mut HashSet<J>) {
        if self.agenda.enqueue(job.clone()) {
            enqueued.push(job);
        } else if coalesced_seen.insert(job.clone()) {
            coalesced.push(job);
        }
    }

    fn enqueue_dependents(
        &mut self,
        fact_use: FactUse<F>,
        pending_changes: &mut Vec<FactChange<F>>,
        enqueued: &mut Vec<J>,
        coalesced: &mut Vec<J>,
        coalesced_seen: &mut HashSet<J>,
    ) {
        let dependents = self
            .deps
            .subscribers(&fact_use)
            .into_iter()
            .chain(self.deps.waiters(&fact_use))
            .collect::<Vec<_>>();
        for job in dependents {
            let dirtied = self.facts.mark_dirty(&job, &self.deps.output_keys(&job));
            pending_changes.extend(dirtied);
            self.enqueue_step(job, enqueued, coalesced, coalesced_seen);
        }
    }
}
