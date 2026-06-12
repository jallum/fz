use std::collections::HashSet;

use super::{Agenda, AppliedStep, DependencyIndex, FactUse, Scheduler};
use crate::compiler2::facts::ClaimShape;

type TestScheduler = Scheduler<u32, &'static str>;

// Test claim-shape convention: keys starting with "cum" are cumulative.
impl ClaimShape for &'static str {
    fn is_cumulative(&self) -> bool {
        self.starts_with("cum")
    }
}

fn current(fact: &'static str) -> FactUse<&'static str> {
    FactUse::current(fact)
}

fn settled(fact: &'static str) -> FactUse<&'static str> {
    FactUse::settled(fact)
}

fn complete(
    scheduler: &mut TestScheduler,
    job: u32,
    reads: HashSet<FactUse<&'static str>>,
    waits: HashSet<FactUse<&'static str>>,
    outputs: Vec<&'static str>,
    changed: Vec<&'static str>,
    follow_up: Vec<u32>,
) -> AppliedStep<u32, &'static str> {
    scheduler.complete(&job, reads, waits, outputs, changed, follow_up)
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
    deps.replace_waits(3_u32, HashSet::from([current("foo")]));

    let waiters = deps.waiters(&current("foo"));
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
        HashSet::from([current(fact)]),
        HashSet::new(),
        Vec::new(),
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
        vec![fact],
        vec![fact],
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
        vec![fact],
        Vec::new(),
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
        vec![fact],
        vec![fact],
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
        HashSet::from([current(fact)]),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec![fact],
        vec![fact],
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
        HashSet::from([current("foo")]),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    let result = complete(
        &mut scheduler,
        1_u32,
        HashSet::new(),
        HashSet::new(),
        vec!["foo"],
        vec!["foo"],
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
        HashSet::from([current("foo")]),
        Vec::new(),
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
        vec!["foo"],
        vec!["foo"],
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
        HashSet::from([current("module_surface"), current("function_defined")]),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );

    assert_eq!(
        step.blocked.into_iter().collect::<HashSet<_>>(),
        HashSet::from([current("module_surface"), current("function_defined")]),
        "blocked facts should be the exact keys the completed job is waiting on"
    );
    let unresolved = scheduler.unresolved();
    assert_eq!(
        unresolved.into_iter().map(|wait| wait.fact).collect::<HashSet<_>>(),
        HashSet::from([current("module_surface"), current("function_defined")]),
        "unresolved waits should expose exact fact keys, not patterns"
    );
}

#[test]
fn compiler2_scheduler_stable_recompute_wakes_settled_waiters_without_revision_bump() {
    let mut scheduler = TestScheduler::new();
    let upstream = 1_u32;
    let producer = 2_u32;
    let current_reader = 3_u32;
    let settled_waiter = 4_u32;

    complete(
        &mut scheduler,
        current_reader,
        HashSet::from([current("bar")]),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    complete(
        &mut scheduler,
        producer,
        HashSet::from([current("foo")]),
        HashSet::new(),
        vec!["bar"],
        vec!["bar"],
        Vec::new(),
    );
    assert!(scheduler.facts().is_settled(&"bar"));
    let _ = scheduler.pop();

    let upstream_change = complete(
        &mut scheduler,
        upstream,
        HashSet::new(),
        HashSet::new(),
        vec!["foo"],
        vec!["foo"],
        Vec::new(),
    );
    assert_eq!(
        upstream_change.enqueued,
        vec![producer],
        "a current dependency change should dirty the producer but not wake current readers of its dirty outputs",
    );
    assert!(!scheduler.facts().is_settled(&"bar"));
    assert_eq!(
        scheduler.facts().revision(&"bar"),
        Some(1),
        "dirtying an output should not invent a new content revision",
    );

    complete(
        &mut scheduler,
        settled_waiter,
        HashSet::new(),
        HashSet::from([settled("bar")]),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    assert!(scheduler.has_unresolved(), "a dirty fact should block settled waiters");

    let settled = complete(
        &mut scheduler,
        producer,
        HashSet::from([current("foo")]),
        HashSet::new(),
        vec!["bar"],
        Vec::new(),
        Vec::new(),
    );
    assert_eq!(
        settled.enqueued,
        vec![settled_waiter],
        "a stable recompute should wake settled waiters when readiness flips dirty -> settled",
    );
    assert!(scheduler.facts().is_settled(&"bar"));
    assert_eq!(scheduler.facts().revision(&"bar"), Some(1));
}

#[test]
fn compiler2_scheduler_multi_publisher_fact_settles_only_when_every_publisher_is_clean() {
    let mut scheduler = TestScheduler::new();
    let upstream_a = 1_u32;
    let upstream_b = 2_u32;
    let producer_a = 10_u32;
    let producer_b = 11_u32;

    complete(
        &mut scheduler,
        producer_a,
        HashSet::from([current("a")]),
        HashSet::new(),
        vec!["shared"],
        vec!["shared"],
        Vec::new(),
    );
    complete(
        &mut scheduler,
        producer_b,
        HashSet::from([current("b")]),
        HashSet::new(),
        vec!["shared"],
        Vec::new(),
        Vec::new(),
    );
    assert!(scheduler.facts().is_settled(&"shared"));

    complete(
        &mut scheduler,
        upstream_a,
        HashSet::new(),
        HashSet::new(),
        vec!["a"],
        vec!["a"],
        Vec::new(),
    );
    assert!(
        !scheduler.facts().is_settled(&"shared"),
        "one dirty publisher should make a shared fact unsettled",
    );

    complete(
        &mut scheduler,
        upstream_b,
        HashSet::new(),
        HashSet::new(),
        vec!["b"],
        vec!["b"],
        Vec::new(),
    );
    assert!(!scheduler.facts().is_settled(&"shared"));

    complete(
        &mut scheduler,
        producer_a,
        HashSet::from([current("a")]),
        HashSet::new(),
        vec!["shared"],
        Vec::new(),
        Vec::new(),
    );
    assert!(
        !scheduler.facts().is_settled(&"shared"),
        "the fact stays unsettled until every active publisher has rerun clean",
    );

    complete(
        &mut scheduler,
        producer_b,
        HashSet::from([current("b")]),
        HashSet::new(),
        vec!["shared"],
        Vec::new(),
        Vec::new(),
    );
    assert!(scheduler.facts().is_settled(&"shared"));
}

#[test]
fn compiler2_scheduler_waiting_completion_preserves_standing_claims() {
    let mut scheduler = TestScheduler::new();
    let job = 1_u32;

    complete(
        &mut scheduler,
        job,
        HashSet::new(),
        HashSet::new(),
        vec!["fact"],
        vec!["fact"],
        Vec::new(),
    );
    assert_eq!(scheduler.facts().revision(&"fact"), Some(1));
    assert!(scheduler.facts().is_settled(&"fact"));

    // A blocked re-run lists no outputs. Pausing must not read as recanting:
    // the standing claim survives, but it must not read as settled while the
    // publisher is blocked.
    complete(
        &mut scheduler,
        job,
        HashSet::new(),
        HashSet::from([current("gate")]),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    assert_eq!(
        scheduler.facts().revision(&"fact"),
        Some(1),
        "a waiting completion must not retract the publisher's standing claims",
    );
    assert!(
        !scheduler.facts().is_settled(&"fact"),
        "a blocked publisher's facts are never settled",
    );

    // A wait-free conclusion re-publishes and settles.
    complete(
        &mut scheduler,
        job,
        HashSet::new(),
        HashSet::new(),
        vec!["fact"],
        Vec::new(),
        Vec::new(),
    );
    assert_eq!(scheduler.facts().revision(&"fact"), Some(1));
    assert!(scheduler.facts().is_settled(&"fact"));
}

#[test]
fn compiler2_scheduler_waiting_completion_keeps_subscriptions() {
    let mut scheduler = TestScheduler::new();
    let reader = 2_u32;
    let writer = 1_u32;

    complete(
        &mut scheduler,
        reader,
        HashSet::from([current("foo")]),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    // A partial run reads less than the conclusion did. Its standing claims
    // still depend on the earlier reads, so the subscription must survive.
    complete(
        &mut scheduler,
        reader,
        HashSet::new(),
        HashSet::from([current("gate")]),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );

    let step = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["foo"],
        vec!["foo"],
        Vec::new(),
    );
    assert!(
        step.enqueued.contains(&reader),
        "a waiting completion must not unsubscribe the job from its prior reads",
    );
}

#[test]
fn compiler2_scheduler_waiting_completion_publishes_alongside_the_wait() {
    // The seed_root shape: a job publishes its root fact in the same
    // completion that waits on the entry function's definition.
    let mut scheduler = TestScheduler::new();
    let job = 3_u32;

    complete(
        &mut scheduler,
        job,
        HashSet::new(),
        HashSet::from([current("gate")]),
        vec!["root"],
        Vec::new(),
        Vec::new(),
    );
    assert_eq!(
        scheduler.facts().revision(&"root"),
        Some(1),
        "outputs published alongside a wait must land as claims",
    );
    assert!(
        !scheduler.facts().is_settled(&"root"),
        "claims published by a blocked job stay unsettled until it concludes",
    );
}

// Claim-shape conventions for these tests: keys starting with "cum" are
// cumulative (monotone join content), everything else is replacing.

#[test]
fn compiler2_scheduler_replacing_change_rebases_readers_without_retracting() {
    let mut scheduler = TestScheduler::new();
    let writer = 1_u32;
    let reader = 2_u32;

    complete(
        &mut scheduler,
        reader,
        HashSet::from([current("def")]),
        HashSet::new(),
        vec!["claim"],
        vec!["claim"],
        Vec::new(),
    );
    // First appearance is an ascent: news, not a shift.
    let step = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["def"],
        vec!["def"],
        Vec::new(),
    );
    assert!(step.enqueued.contains(&reader));
    assert!(
        !scheduler.rebased(&reader),
        "first appearance of a fact wakes readers without rebasing them",
    );
    let _ = scheduler.pop();

    // A content change to a replacing fact is a ground shift.
    let step = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["def"],
        vec!["def"],
        Vec::new(),
    );
    assert!(step.enqueued.contains(&reader));
    assert!(
        scheduler.rebased(&reader),
        "a replacing fact's content change rebases its readers",
    );
    assert_eq!(
        scheduler.facts().revision(&"claim"),
        Some(1),
        "a ground shift leaves the reader's claims standing",
    );
    assert!(
        !scheduler.facts().is_settled(&"claim"),
        "a shifted reader's claims are unsettled until it re-concludes",
    );
}

#[test]
fn compiler2_scheduler_cumulative_ascent_wakes_without_rebasing() {
    let mut scheduler = TestScheduler::new();
    let writer = 1_u32;
    let reader = 2_u32;

    complete(
        &mut scheduler,
        reader,
        HashSet::from([current("cum_ret")]),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_ret"],
        vec!["cum_ret"],
        Vec::new(),
    );
    let _ = scheduler.pop();
    let step = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_ret"],
        vec!["cum_ret"],
        Vec::new(),
    );
    assert!(step.enqueued.contains(&reader));
    assert!(
        !scheduler.rebased(&reader),
        "growth of a cumulative fact is an ascent: readers re-run and join, no rebase",
    );
}

#[test]
fn compiler2_scheduler_retraction_always_shifts() {
    let mut scheduler = TestScheduler::new();
    let writer = 1_u32;
    let reader = 2_u32;

    complete(
        &mut scheduler,
        reader,
        HashSet::from([current("cum_ret")]),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_ret"],
        vec!["cum_ret"],
        Vec::new(),
    );
    let _ = scheduler.pop();
    // The writer concludes without the fact: retraction, even of a cumulative
    // claim, is never an ascent.
    let step = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    assert!(step.enqueued.contains(&reader));
    assert!(scheduler.rebased(&reader), "retraction is a ground shift");
}

#[test]
fn compiler2_scheduler_rebased_conclusion_propagates_changes_as_shifts() {
    let mut scheduler = TestScheduler::new();
    let upstream = 1_u32;
    let middle = 2_u32;
    let downstream = 3_u32;

    // downstream reads middle's cumulative fact; middle reads upstream's def.
    complete(
        &mut scheduler,
        downstream,
        HashSet::from([current("cum_mid")]),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    complete(
        &mut scheduler,
        middle,
        HashSet::from([current("def")]),
        HashSet::new(),
        vec!["cum_mid"],
        vec!["cum_mid"],
        Vec::new(),
    );
    complete(
        &mut scheduler,
        upstream,
        HashSet::new(),
        HashSet::new(),
        vec!["def"],
        vec!["def"],
        Vec::new(),
    );
    while scheduler.pop().is_some() {}
    // Shift middle via a def content change.
    complete(
        &mut scheduler,
        upstream,
        HashSet::new(),
        HashSet::new(),
        vec!["def"],
        vec!["def"],
        Vec::new(),
    );
    assert!(scheduler.rebased(&middle));

    // A rebased conclusion's changes propagate as shifts even on a
    // cumulative fact — this is the lazy transitivity of narrowing.
    let step = complete(
        &mut scheduler,
        middle,
        HashSet::from([current("def")]),
        HashSet::new(),
        vec!["cum_mid"],
        vec!["cum_mid"],
        Vec::new(),
    );
    assert!(step.enqueued.contains(&downstream));
    assert!(
        scheduler.rebased(&downstream),
        "a rebased publisher's content changes shift its readers in turn",
    );
    assert!(!scheduler.rebased(&middle), "concluding clears the publisher's rebase",);
}

#[test]
fn compiler2_scheduler_rebased_equal_conclusion_stops_the_cone() {
    let mut scheduler = TestScheduler::new();
    let upstream = 1_u32;
    let middle = 2_u32;
    let downstream = 3_u32;

    complete(
        &mut scheduler,
        downstream,
        HashSet::from([current("cum_mid")]),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    complete(
        &mut scheduler,
        middle,
        HashSet::from([current("def")]),
        HashSet::new(),
        vec!["cum_mid"],
        vec!["cum_mid"],
        Vec::new(),
    );
    complete(
        &mut scheduler,
        upstream,
        HashSet::new(),
        HashSet::new(),
        vec!["def"],
        vec!["def"],
        Vec::new(),
    );
    while scheduler.pop().is_some() {}
    complete(
        &mut scheduler,
        upstream,
        HashSet::new(),
        HashSet::new(),
        vec!["def"],
        vec!["def"],
        Vec::new(),
    );
    assert!(scheduler.rebased(&middle));

    // The rebased job re-derives the same content (changed empty): the cone
    // stops here — downstream is woken by nothing and keeps its standing.
    let step = complete(
        &mut scheduler,
        middle,
        HashSet::from([current("def")]),
        HashSet::new(),
        vec!["cum_mid"],
        Vec::new(),
        Vec::new(),
    );
    assert!(
        !step.enqueued.contains(&downstream),
        "equal recomputation propagates nothing",
    );
    assert!(!scheduler.rebased(&downstream));
    assert!(!scheduler.rebased(&middle), "concluding clears rebase");
}

#[test]
fn compiler2_scheduler_waiting_keeps_rebase_pending() {
    let mut scheduler = TestScheduler::new();
    let writer = 1_u32;
    let reader = 2_u32;

    complete(
        &mut scheduler,
        reader,
        HashSet::from([current("def")]),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["def"],
        vec!["def"],
        Vec::new(),
    );
    let _ = scheduler.pop();
    complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["def"],
        vec!["def"],
        Vec::new(),
    );
    assert!(scheduler.rebased(&reader));

    // A blocked re-run does not discharge the rebase: the job has not yet
    // re-derived its claims from the shifted ground.
    complete(
        &mut scheduler,
        reader,
        HashSet::new(),
        HashSet::from([current("gate")]),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
    assert!(scheduler.rebased(&reader), "waiting keeps rebase pending");
}
