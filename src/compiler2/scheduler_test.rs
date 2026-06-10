use std::collections::HashSet;

use super::{Agenda, AppliedStep, DependencyIndex, Scheduler};

type TestScheduler = Scheduler<u32, &'static str>;

fn complete(
    scheduler: &mut TestScheduler,
    job: u32,
    reads: HashSet<&'static str>,
    waits: HashSet<&'static str>,
    outputs: Vec<(&'static str, bool)>,
    follow_up: Vec<u32>,
) -> AppliedStep<u32, &'static str> {
    scheduler.complete(job, reads, waits, outputs, follow_up)
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
    deps.replace_waits(3_u32, HashSet::from(["foo"]));

    let waiters = deps.waiters(&"foo");
    assert_eq!(waiters, vec![3], "exact fact waiters should wake on matching fact");
}

#[test]
fn compiler2_scheduler_wakes_on_content_change_suppresses_stable_republication() {
    let mut scheduler = TestScheduler::new();

    let subscriber = 2_u32;
    let writer = 1_u32;
    let fact = "foo";

    let subscribe = complete(
        &mut scheduler,
        subscriber,
        HashSet::from([fact]),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
    );
    assert!(
        subscribe.changed.is_empty(),
        "reads-only registration should not change facts"
    );
    assert!(
        subscribe.enqueued.is_empty(),
        "reads-only registration should not enqueue work"
    );
    assert!(
        subscribe.coalesced.is_empty(),
        "reads-only registration should not coalesce work"
    );

    let first = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec![(fact, true)],
        Vec::new(),
    );
    assert_eq!(first.enqueued, vec![subscriber]);
    assert_eq!(
        scheduler.facts().revision(&fact),
        Some(1),
        "the table-owned counter starts at 1 on first publication"
    );
    assert_eq!(scheduler.pop(), Some(subscriber));

    let second = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec![(fact, false)],
        Vec::new(),
    );
    assert!(
        second.enqueued.is_empty(),
        "republishing with changed=false should not wake subscribers"
    );
    assert!(
        second.changed.is_empty(),
        "stable republication should suppress changes"
    );

    let third = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec![(fact, true)],
        Vec::new(),
    );
    assert_eq!(third.enqueued, vec![subscriber]);
    assert_eq!(
        scheduler.facts().revision(&fact),
        Some(2),
        "republishing with changed=true increments the table counter"
    );
}

#[test]
fn compiler2_scheduler_retracts_outputs_a_job_stops_publishing() {
    let mut scheduler = TestScheduler::new();
    let fact = "foo";
    let subscriber = 9_u32;
    let writer = 1_u32;

    complete(
        &mut scheduler,
        subscriber,
        HashSet::from([fact]),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
    );
    complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec![(fact, true)],
        Vec::new(),
    );
    assert_eq!(scheduler.facts().revision(&fact), Some(1));
    let _ = scheduler.pop();

    let retracted = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
    );
    assert_eq!(scheduler.facts().revision(&fact), None);
    assert_eq!(retracted.changed.len(), 1, "retraction should be a fact change");
    assert_eq!(
        retracted.changed[0].old_revision,
        Some(1),
        "old revision should reflect the table counter at retraction"
    );
    assert_eq!(
        retracted.changed[0].new_revision, None,
        "a retracted fact should read as absent"
    );
    assert_eq!(retracted.enqueued, vec![subscriber]);
}

#[test]
fn compiler2_scheduler_wakes_waiters_when_a_matching_fact_appears() {
    let mut scheduler = TestScheduler::new();
    let waiter = 4_u32;

    complete(
        &mut scheduler,
        waiter,
        HashSet::new(),
        HashSet::from(["foo"]),
        Vec::new(),
        Vec::new(),
    );
    let result = complete(
        &mut scheduler,
        1_u32,
        HashSet::new(),
        HashSet::new(),
        vec![("foo", true)],
        Vec::new(),
    );
    assert_eq!(result.enqueued, vec![waiter]);
}

#[test]
fn compiler2_scheduler_has_unresolved_tracks_waiter_presence_without_materializing_frontier() {
    let mut scheduler = TestScheduler::new();
    assert!(
        !scheduler.has_unresolved(),
        "a fresh scheduler should not report unresolved waiters"
    );

    complete(
        &mut scheduler,
        4_u32,
        HashSet::new(),
        HashSet::from(["foo"]),
        Vec::new(),
        Vec::new(),
    );
    assert!(
        scheduler.has_unresolved(),
        "registering a waiter should make unresolved work observable"
    );

    complete(
        &mut scheduler,
        1_u32,
        HashSet::new(),
        HashSet::new(),
        vec![("foo", true)],
        Vec::new(),
    );
    assert_eq!(
        scheduler.pop(),
        Some(4_u32),
        "publishing the waited-for fact should enqueue the blocked job to rerun"
    );
    complete(
        &mut scheduler,
        4_u32,
        HashSet::new(),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
    );
    assert!(
        !scheduler.has_unresolved(),
        "once the waited-for fact appears and the waiter reruns, unresolved should clear"
    );
}

#[test]
fn compiler2_scheduler_complete_enqueues_follow_up_jobs_once() {
    let mut scheduler = TestScheduler::new();
    assert!(scheduler.enqueue(1));
    assert!(scheduler.enqueue(2));

    let step = complete(
        &mut scheduler,
        1,
        HashSet::new(),
        HashSet::new(),
        Vec::new(),
        vec![3, 3, 4],
    );

    assert_eq!(
        step.enqueued,
        vec![3, 4],
        "follow-up jobs should be coalesced before they hit the agenda"
    );
    assert_eq!(
        step.coalesced,
        vec![3],
        "duplicate follow-up jobs should be reported as coalesced work"
    );
    assert_eq!(scheduler.pop(), Some(1));
    assert_eq!(scheduler.pop(), Some(2));
    assert_eq!(scheduler.pop(), Some(3));
    assert_eq!(scheduler.pop(), Some(4));
    assert_eq!(scheduler.pop(), None);
}

#[test]
fn compiler2_scheduler_reports_blocked_exact_facts() {
    let mut scheduler = TestScheduler::new();

    let step = complete(
        &mut scheduler,
        1_u32,
        HashSet::new(),
        HashSet::from(["module_surface", "function_defined"]),
        Vec::new(),
        Vec::new(),
    );

    assert_eq!(
        step.blocked.into_iter().collect::<HashSet<_>>(),
        HashSet::from(["module_surface", "function_defined"]),
        "blocked facts should be the exact keys the completed job is waiting on"
    );
    let unresolved = scheduler.unresolved();
    assert_eq!(
        unresolved.into_iter().map(|wait| wait.fact).collect::<HashSet<_>>(),
        HashSet::from(["module_surface", "function_defined"]),
        "unresolved waits should expose exact fact keys, not patterns"
    );
}
