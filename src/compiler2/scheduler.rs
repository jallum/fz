use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;

use crate::diag::diagnostic::Diagnostic;
use crate::diag::driver::emit_through;
use crate::telemetry::value::opaque;
use crate::telemetry::{Metadata, Telemetry, Value};

use super::agenda::Agenda;
use super::deps::{DependencyIndex, FactPattern};
use super::facts::{FactAggregator, FactChange, FactTable};

#[derive(Debug, Clone)]
pub struct JobOutcome<J, F, P, V> {
    pub reads: HashSet<F>,
    pub waits: HashSet<P>,
    pub outputs: Vec<(F, V)>,
    pub follow_up: Vec<J>,
    pub fatal: Option<Diagnostic>,
}

impl<J, F, P, V> Default for JobOutcome<J, F, P, V> {
    fn default() -> Self {
        Self {
            reads: HashSet::new(),
            waits: HashSet::new(),
            outputs: Vec::new(),
            follow_up: Vec::new(),
            fatal: None,
        }
    }
}

impl<J, F, P, V> JobOutcome<J, F, P, V> {
    pub fn new() -> Self {
        Self::default()
    }
}

#[derive(Debug, Clone)]
pub enum StepResult<J, F> {
    Applied {
        changed: Vec<FactChange<F>>,
        enqueued: Vec<J>,
    },
    Fatal {
        job: J,
        diagnostic: Diagnostic,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DriveDone {
    pub processed_jobs: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DriveResult<J> {
    Done(DriveDone),
    Fatal { job: J },
}

#[derive(Debug)]
pub struct Scheduler<J, F, P, V, A> {
    agenda: Agenda<J>,
    facts: FactTable<J, F, V, A>,
    deps: DependencyIndex<J, F, P>,
}

impl<J, F, P, V, A> Scheduler<J, F, P, V, A>
where
    J: Clone + Debug + Eq + Hash,
    F: Clone + Eq + Hash,
    P: Clone + Eq + Hash + FactPattern<F>,
    A: FactAggregator<J, F, V>,
{
    pub fn new(aggregator: A) -> Self {
        Self {
            agenda: Agenda::new(),
            facts: FactTable::new(aggregator),
            deps: DependencyIndex::new(),
        }
    }

    pub fn agenda(&self) -> &Agenda<J> {
        &self.agenda
    }

    pub fn facts(&self) -> &FactTable<J, F, V, A> {
        &self.facts
    }

    pub fn deps(&self) -> &DependencyIndex<J, F, P> {
        &self.deps
    }

    pub fn enqueue(&mut self, job: J) -> bool {
        self.agenda.enqueue(job)
    }

    pub fn pop(&mut self) -> Option<J> {
        self.agenda.pop()
    }

    pub fn complete(&mut self, job: J, outcome: JobOutcome<J, F, P, V>, tel: &dyn Telemetry) -> StepResult<J, F> {
        if let Some(diagnostic) = outcome.fatal {
            emit_through(tel, None, std::slice::from_ref(&diagnostic));
            tel.event(
                &["fz", "compiler2", "job", "fatal"],
                Metadata::from_pairs([
                    ("job", Value::from(format!("{job:?}"))),
                    ("code", Value::from(diagnostic.code.0)),
                    ("message", Value::from(diagnostic.message.clone())),
                    ("diagnostic", opaque(&diagnostic)),
                ]),
            );
            return StepResult::Fatal { job, diagnostic };
        }

        self.deps.replace_reads(job.clone(), outcome.reads);
        self.deps.replace_waits(job.clone(), outcome.waits);

        let previous_output_keys = self.deps.output_keys(&job);
        let replaced = self
            .facts
            .replace_contributions(&job, &previous_output_keys, outcome.outputs);
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
        for follow_up in outcome.follow_up {
            if self.agenda.enqueue(follow_up.clone()) {
                enqueued.push(follow_up);
            }
        }

        StepResult::Applied {
            changed: replaced.changed,
            enqueued,
        }
    }

    pub fn drive(
        &mut self,
        tel: &dyn Telemetry,
        mut runner: impl FnMut(&Self, &J) -> JobOutcome<J, F, P, V>,
    ) -> DriveResult<J> {
        let mut processed_jobs = 0;
        while let Some(job) = self.pop() {
            processed_jobs += 1;
            let outcome = runner(self, &job);
            match self.complete(job.clone(), outcome, tel) {
                StepResult::Applied { .. } => {}
                StepResult::Fatal { .. } => return DriveResult::Fatal { job },
            }
        }
        DriveResult::Done(DriveDone { processed_jobs })
    }
}
