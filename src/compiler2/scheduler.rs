use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;

use super::agenda::Agenda;
use super::deps::{DependencyIndex, UnresolvedWait};
use super::facts::{FactChange, FactTable, FactValue};
use super::types::Types;

#[derive(Debug, Clone)]
pub struct AppliedStep<J, F> {
    pub changed: Vec<FactChange<F>>,
    pub enqueued: Vec<J>,
    pub coalesced: Vec<J>,
    pub blocked: Vec<F>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FatalError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DriveOutcome<J, F> {
    Resolved,
    Unresolved { waits: Vec<UnresolvedWait<J, F>> },
    Fatal { job: J },
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

    pub fn complete(
        &mut self,
        types: &mut Types,
        job: J,
        reads: HashSet<F>,
        waits: HashSet<F>,
        outputs: Vec<(F, FactValue)>,
        follow_up: Vec<J>,
    ) -> AppliedStep<J, F> {
        let blocked = waits.iter().cloned().collect();
        self.deps.replace_reads(job.clone(), reads);
        self.deps.replace_waits(job.clone(), waits);

        let previous_output_keys = self.deps.output_keys(&job);
        let replaced = self
            .facts
            .replace_contributions(types, &job, &previous_output_keys, outputs);
        self.deps.replace_outputs(job.clone(), replaced.output_keys);

        let mut enqueued = Vec::new();
        let mut coalesced = Vec::new();
        let mut coalesced_seen = HashSet::new();
        for change in &replaced.changed {
            for subscriber in self.deps.subscribers(&change.key) {
                self.enqueue_step(subscriber, &mut enqueued, &mut coalesced, &mut coalesced_seen);
            }
            for waiter in self.deps.waiters(&change.key) {
                self.enqueue_step(waiter, &mut enqueued, &mut coalesced, &mut coalesced_seen);
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
}
