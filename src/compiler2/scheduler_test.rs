use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use crate::diag::diagnostic::{DiagCode, Diagnostic};
use crate::telemetry::{Capture, ConfiguredTelemetry};

use super::{
    Agenda, DependencyIndex, DriveDone, DriveResult, ExactPattern, FactAggregator, Fingerprint, JobOutcome, Scheduler,
    StepResult,
};

type TestScheduler = Scheduler<u32, &'static str, ExactPattern<&'static str>, u64, MaxU64>;

#[derive(Debug, Clone, Copy)]
struct MaxU64;

impl<J, F> FactAggregator<J, F, u64> for MaxU64
where
    J: Eq + Hash,
{
    fn aggregate(&self, _key: &F, contributions: &HashMap<J, u64>) -> Option<u64> {
        contributions.values().copied().max()
    }

    fn fingerprint(&self, _key: &F, aggregate: &u64) -> Fingerprint {
        Fingerprint::new(*aggregate)
    }
}

#[test]
fn compiler2_agenda_coalesces_and_requeues_after_pop() {
    let mut agenda = Agenda::new();

    assert!(agenda.enqueue(7));
    assert!(!agenda.enqueue(7), "duplicate pending work should coalesce");
    assert_eq!(agenda.len(), 1);
    assert_eq!(agenda.pop(), Some(7));
    assert!(agenda.is_empty());

    assert!(
        agenda.enqueue(7),
        "once popped, the same job should be enqueueable again"
    );
    assert_eq!(agenda.pop(), Some(7));
}

#[test]
fn compiler2_dependency_index_wakes_exact_waiters() {
    let mut deps = DependencyIndex::new();
    deps.replace_waits(3_u32, HashSet::from([ExactPattern("foo")]));

    let waiters = deps.waiters_matching(&"foo");
    assert_eq!(waiters, vec![3], "exact-pattern waiters should wake on matching fact");
}

#[test]
fn compiler2_scheduler_replaces_contributions_and_suppresses_no_change_wakeups() {
    let tel = ConfiguredTelemetry::new();
    let mut scheduler = TestScheduler::new(MaxU64);

    let subscriber = 2_u32;
    let writer = 1_u32;
    let fact = "foo";

    let subscribe = scheduler.complete(
        subscriber,
        JobOutcome {
            reads: HashSet::from([fact]),
            ..JobOutcome::new()
        },
        &tel,
    );
    assert!(
        matches!(subscribe, StepResult::Applied { .. }),
        "subscription registration should not fail"
    );

    let first = scheduler.complete(
        writer,
        JobOutcome {
            outputs: vec![(fact, 1)],
            ..JobOutcome::new()
        },
        &tel,
    );
    let first_enqueued = match first {
        StepResult::Applied { enqueued, .. } => enqueued,
        StepResult::Fatal { .. } => panic!("first write should not be fatal"),
    };
    assert_eq!(first_enqueued, vec![subscriber]);
    assert_eq!(scheduler.facts().get(&fact), Some(&1));
    assert_eq!(scheduler.pop(), Some(subscriber));

    let second = scheduler.complete(
        writer,
        JobOutcome {
            outputs: vec![(fact, 1)],
            ..JobOutcome::new()
        },
        &tel,
    );
    let second_changed = match second {
        StepResult::Applied { changed, enqueued } => {
            assert!(enqueued.is_empty(), "no-change writes should not wake subscribers");
            changed
        }
        StepResult::Fatal { .. } => panic!("same-value rewrite should not be fatal"),
    };
    assert!(
        second_changed.is_empty(),
        "same aggregate fingerprint should suppress changes"
    );

    let third = scheduler.complete(
        writer,
        JobOutcome {
            outputs: vec![(fact, 9)],
            ..JobOutcome::new()
        },
        &tel,
    );
    let third_enqueued = match third {
        StepResult::Applied { enqueued, .. } => enqueued,
        StepResult::Fatal { .. } => panic!("changed write should not be fatal"),
    };
    assert_eq!(third_enqueued, vec![subscriber]);
    assert_eq!(scheduler.facts().get(&fact), Some(&9));
}

#[test]
fn compiler2_scheduler_retracts_old_outputs_and_recomputes_aggregate() {
    let tel = ConfiguredTelemetry::new();
    let mut scheduler = TestScheduler::new(MaxU64);
    let fact = "foo";
    let subscriber = 9_u32;

    scheduler.complete(
        subscriber,
        JobOutcome {
            reads: HashSet::from([fact]),
            ..JobOutcome::new()
        },
        &tel,
    );
    scheduler.complete(
        1_u32,
        JobOutcome {
            outputs: vec![(fact, 5)],
            ..JobOutcome::new()
        },
        &tel,
    );
    scheduler.complete(
        2_u32,
        JobOutcome {
            outputs: vec![(fact, 7)],
            ..JobOutcome::new()
        },
        &tel,
    );
    assert_eq!(scheduler.facts().get(&fact), Some(&7));
    let _ = scheduler.pop();

    let retracted = scheduler.complete(2_u32, JobOutcome::new(), &tel);
    let (changed, enqueued) = match retracted {
        StepResult::Applied { changed, enqueued } => (changed, enqueued),
        StepResult::Fatal { .. } => panic!("retraction should not be fatal"),
    };
    assert_eq!(scheduler.facts().get(&fact), Some(&5));
    assert_eq!(changed.len(), 1, "retraction should change the aggregate");
    assert_eq!(
        changed[0].old_fingerprint.as_u64(),
        7,
        "old fingerprint should reflect the old aggregate"
    );
    assert_eq!(
        changed[0].new_fingerprint.as_u64(),
        5,
        "new fingerprint should reflect the recomputed aggregate"
    );
    assert_eq!(enqueued, vec![subscriber]);
}

#[test]
fn compiler2_scheduler_wakes_waiters_when_a_matching_fact_appears() {
    let tel = ConfiguredTelemetry::new();
    let mut scheduler = TestScheduler::new(MaxU64);
    let waiter = 4_u32;

    scheduler.complete(
        waiter,
        JobOutcome {
            waits: HashSet::from([ExactPattern("foo")]),
            ..JobOutcome::new()
        },
        &tel,
    );
    let result = scheduler.complete(
        1_u32,
        JobOutcome {
            outputs: vec![("foo", 1)],
            ..JobOutcome::new()
        },
        &tel,
    );
    let enqueued = match result {
        StepResult::Applied { enqueued, .. } => enqueued,
        StepResult::Fatal { .. } => panic!("waiter wakeup should not be fatal"),
    };
    assert_eq!(enqueued, vec![waiter]);
}

#[test]
fn compiler2_scheduler_stops_on_fatal_and_emits_telemetry() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());

    let mut scheduler = TestScheduler::new(MaxU64);
    assert!(scheduler.enqueue(1));
    assert!(scheduler.enqueue(2));

    let result = scheduler.drive(&tel, |_scheduler, job| {
        if *job == 1 {
            JobOutcome {
                fatal: Some(Diagnostic::error(
                    DiagCode("compiler2/fatal"),
                    "boom",
                    crate::compiler::source::Span::DUMMY,
                )),
                ..JobOutcome::new()
            }
        } else {
            panic!("fatal stop should prevent later jobs from running");
        }
    });

    assert_eq!(capture.count(&["fz", "diag", "error"]), 1);
    assert_eq!(capture.count(&["fz", "compiler2", "job", "fatal"]), 1);
    assert!(
        matches!(result, DriveResult::Fatal { job: 1 }),
        "drive should stop at the first fatal job"
    );
    assert_eq!(
        scheduler.pop(),
        Some(2),
        "later jobs should remain queued after a fatal stop"
    );
}

#[test]
fn compiler2_scheduler_reports_processed_jobs_when_the_agenda_drains() {
    let tel = ConfiguredTelemetry::new();
    let mut scheduler = TestScheduler::new(MaxU64);
    assert!(scheduler.enqueue(1));
    assert!(scheduler.enqueue(2));

    let result = scheduler.drive(&tel, |_scheduler, job| JobOutcome {
        follow_up: (*job == 1).then_some(3).into_iter().collect(),
        ..JobOutcome::new()
    });

    assert_eq!(
        result,
        DriveResult::Done(DriveDone { processed_jobs: 3 }),
        "drive should count original and follow-up jobs"
    );
    assert!(scheduler.agenda().is_empty());
}
