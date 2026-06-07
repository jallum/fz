use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;

use super::agenda::Agenda;
use super::deps::{DependencyIndex, FactPattern, UnresolvedWait};
use super::facts::{FactChange, FactTable, FactValue};

#[derive(Debug, Clone)]
pub struct AppliedStep<J, F> {
    pub changed: Vec<FactChange<F>>,
    pub enqueued: Vec<J>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FatalError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DriveOutcome<J, P> {
    Resolved,
    Unresolved { waits: Vec<UnresolvedWait<J, P>> },
    Fatal { job: J },
}

#[derive(Debug)]
pub struct Scheduler<J, F, P> {
    agenda: Agenda<J>,
    facts: FactTable<J, F>,
    deps: DependencyIndex<J, F, P>,
}

impl<J, F, P> Default for Scheduler<J, F, P>
where
    J: Clone + Debug + Eq + Hash,
    F: Clone + Eq + Hash,
    P: Clone + Eq + Hash + FactPattern<F>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<J, F, P> Scheduler<J, F, P>
where
    J: Clone + Debug + Eq + Hash,
    F: Clone + Eq + Hash,
    P: Clone + Eq + Hash + FactPattern<F>,
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

    pub fn unresolved(&self) -> Vec<UnresolvedWait<J, P>> {
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
        job: J,
        reads: HashSet<F>,
        waits: HashSet<P>,
        outputs: Vec<(F, FactValue)>,
        follow_up: Vec<J>,
    ) -> AppliedStep<J, F> {
        self.deps.replace_reads(job.clone(), reads);
        self.deps.replace_waits(job.clone(), waits);

        let previous_output_keys = self.deps.output_keys(&job);
        let replaced = self.facts.replace_contributions(&job, &previous_output_keys, outputs);
        self.deps.replace_outputs(job.clone(), replaced.output_keys);

        let mut enqueued = Vec::new();
        for change in &replaced.changed {
            for subscriber in self.deps.subscribers(&change.key) {
                if self.agenda.enqueue(subscriber.clone()) {
                    enqueued.push(subscriber);
                }
            }
            for waiter in self.deps.waiters_matching(&change.key) {
                if self.agenda.enqueue(waiter.clone()) {
                    enqueued.push(waiter);
                }
            }
        }
        for follow_up in follow_up {
            if self.agenda.enqueue(follow_up.clone()) {
                enqueued.push(follow_up);
            }
        }

        AppliedStep {
            changed: replaced.changed,
            enqueued,
        }
    }
}
