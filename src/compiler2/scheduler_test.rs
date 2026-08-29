use std::collections::HashSet;

use super::{Agenda, AppliedStep, DependencyIndex, FactUse, Scheduler, Wake, WakeDisposition};
use crate::compiler2::facts::ClaimShape;

type TestScheduler = Scheduler<u32, &'static str>;
type TestStep = AppliedStep<u32, &'static str>;

/// The jobs `step` newly started (`WakeDisposition::Enqueued`), in wake
/// order, standing in for the retired `AppliedStep::enqueued` field: same
/// intent (a job's own new work start), read off `wakes` instead.
fn enqueued_jobs(step: &TestStep) -> Vec<u32> {
    wakes_with(step, WakeDisposition::Enqueued)
}

/// The jobs `step` found already pending (`WakeDisposition::Coalesced`), in
/// wake order — standing in for the retired `AppliedStep::coalesced` field.
/// Unlike the retired field, this is not deduped: a job coalesced by two
/// distinct causes in the same `complete` call appears twice, once per
/// cause, which is the whole point of carrying causes at all.
fn coalesced_jobs(step: &TestStep) -> Vec<u32> {
    wakes_with(step, WakeDisposition::Coalesced)
}

fn wakes_with(step: &TestStep, disposition: WakeDisposition) -> Vec<u32> {
    step.wakes
        .iter()
        .filter(|wake| wake.disposition == disposition)
        .map(|wake| wake.job)
        .collect()
}

/// The `Wake` records in `step` attributing `job`, whatever the
/// disposition — for tests that need to inspect cause attribution directly
/// rather than just the woken-job list.
fn wakes_for(step: &TestStep, job: u32) -> Vec<&Wake<u32, &'static str>> {
    step.wakes.iter().filter(|wake| wake.job == job).collect()
}

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

fn settled_presence(fact: &'static str) -> FactUse<&'static str> {
    FactUse::settled_presence(fact)
}

fn complete(
    scheduler: &mut TestScheduler,
    job: u32,
    reads: HashSet<FactUse<&'static str>>,
    waits: HashSet<FactUse<&'static str>>,
    outputs: Vec<&'static str>,
    changed: Vec<&'static str>,
) -> AppliedStep<u32, &'static str> {
    scheduler.complete(&job, reads, waits, outputs, changed)
}

#[test]
fn compiler2_scheduler_settled_presence_ignores_content_revision_bumps() {
    let mut scheduler = TestScheduler::new();
    let producer = 1_u32;
    let waiter = 2_u32;

    complete(
        &mut scheduler,
        waiter,
        HashSet::new(),
        HashSet::from([settled_presence("summary")]),
        Vec::new(),
        Vec::new(),
    );
    let appeared = complete(
        &mut scheduler,
        producer,
        HashSet::new(),
        HashSet::new(),
        vec!["summary"],
        vec!["summary"],
    );
    assert_eq!(
        enqueued_jobs(&appeared),
        vec![waiter],
        "settled-presence waiters should wake when the fact first settles",
    );
    let _ = scheduler.pop();
    complete(
        &mut scheduler,
        waiter,
        HashSet::from([settled_presence("summary")]),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
    );

    let moved = complete(
        &mut scheduler,
        producer,
        HashSet::new(),
        HashSet::new(),
        vec!["summary"],
        vec!["summary"],
    );
    assert!(
        !enqueued_jobs(&moved).contains(&waiter),
        "settled-presence readers are readiness subscribers, not content subscribers",
    );
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
    );
    assert!(
        subscribe.changed.is_empty(),
        "reads-only registration should not change facts"
    );
    assert!(
        enqueued_jobs(&subscribe).is_empty(),
        "reads-only registration should not enqueue work"
    );
    assert!(
        coalesced_jobs(&subscribe).is_empty(),
        "reads-only registration should not coalesce work"
    );

    let first = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec![fact],
        vec![fact],
    );
    assert_eq!(enqueued_jobs(&first), vec![subscriber]);
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
    );
    assert!(
        enqueued_jobs(&second).is_empty(),
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
    );
    assert_eq!(enqueued_jobs(&third), vec![subscriber]);
    assert_eq!(
        scheduler.facts().revision(&fact),
        Some(2),
        "republishing with changed=true increments the table counter"
    );
}

#[test]
fn compiler2_scheduler_reports_the_full_fact_movement_wave() {
    let mut scheduler = TestScheduler::new();
    complete(
        &mut scheduler,
        1,
        HashSet::new(),
        HashSet::new(),
        vec!["source"],
        vec!["source"],
    );
    complete(
        &mut scheduler,
        2,
        HashSet::from([settled("source")]),
        HashSet::new(),
        vec!["derived"],
        vec!["derived"],
    );
    complete(
        &mut scheduler,
        3,
        HashSet::from([settled("derived")]),
        HashSet::new(),
        vec!["leaf"],
        vec!["leaf"],
    );

    let movement = complete(
        &mut scheduler,
        1,
        HashSet::new(),
        HashSet::new(),
        vec!["source"],
        vec!["source"],
    );

    assert_eq!(movement.changed.len(), 1);
    assert!(movement.changed.iter().any(|change| change.key == "source"));
    assert!(
        movement
            .movements
            .iter()
            .any(|movement| movement.key == "derived" && !movement.state.settled)
    );
    assert!(
        movement
            .movements
            .iter()
            .any(|movement| movement.key == "leaf" && !movement.state.settled)
    );
}

#[test]
fn compiler2_scheduler_reports_final_state_after_same_key_publication_then_dirtying() {
    let mut scheduler = TestScheduler::new();
    complete(
        &mut scheduler,
        1,
        HashSet::new(),
        HashSet::new(),
        vec!["claim"],
        vec!["claim"],
    );

    let blocked = complete(
        &mut scheduler,
        1,
        HashSet::new(),
        HashSet::from([current("missing")]),
        vec!["claim"],
        vec!["claim"],
    );
    let reported = blocked
        .movements
        .iter()
        .find(|movement| movement.key == "claim")
        .expect("the moved claim should be reported");
    assert_eq!(
        blocked
            .movements
            .iter()
            .filter(|movement| movement.key == "claim")
            .count(),
        1
    );

    assert_eq!(reported.state, scheduler.facts().state(&"claim"));
    assert_eq!(reported.state.revision, Some(2));
    assert!(!reported.state.settled);
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
    );
    complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec![fact],
        vec![fact],
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
    assert_eq!(enqueued_jobs(&retracted), vec![subscriber]);
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
    );
    let result = complete(
        &mut scheduler,
        1_u32,
        HashSet::new(),
        HashSet::new(),
        vec!["foo"],
        vec!["foo"],
    );
    assert_eq!(enqueued_jobs(&result), vec![waiter]);
}

#[test]
fn compiler2_scheduler_parks_waiters_until_their_full_wait_set_is_satisfied() {
    let mut scheduler = TestScheduler::new();
    let waiter = 4_u32;

    complete(
        &mut scheduler,
        waiter,
        HashSet::new(),
        HashSet::from([current("foo"), current("bar")]),
        Vec::new(),
        Vec::new(),
    );

    let foo = complete(
        &mut scheduler,
        1_u32,
        HashSet::new(),
        HashSet::new(),
        vec!["foo"],
        vec!["foo"],
    );
    assert!(
        enqueued_jobs(&foo).is_empty(),
        "a waiter blocked on foo + bar should stay parked when only foo appears",
    );
    assert_eq!(
        scheduler.pop(),
        None,
        "the partially satisfied waiter should not hit the agenda",
    );

    let bar = complete(
        &mut scheduler,
        2_u32,
        HashSet::new(),
        HashSet::new(),
        vec!["bar"],
        vec!["bar"],
    );
    assert_eq!(
        enqueued_jobs(&bar),
        vec![waiter],
        "the waiter should wake once every fact in its wait set is satisfied",
    );
    assert_eq!(scheduler.pop(), Some(waiter));
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
fn compiler2_scheduler_reports_blocked_exact_facts() {
    let mut scheduler = TestScheduler::new();

    let step = complete(
        &mut scheduler,
        1_u32,
        HashSet::new(),
        HashSet::from([current("module_surface"), current("function_defined")]),
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
    );
    complete(
        &mut scheduler,
        producer,
        HashSet::from([current("foo")]),
        HashSet::new(),
        vec!["bar"],
        vec!["bar"],
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
    );
    assert_eq!(
        enqueued_jobs(&upstream_change),
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
    );
    assert!(scheduler.has_unresolved(), "a dirty fact should block settled waiters");

    let settled = complete(
        &mut scheduler,
        producer,
        HashSet::from([current("foo")]),
        HashSet::new(),
        vec!["bar"],
        Vec::new(),
    );
    assert_eq!(
        enqueued_jobs(&settled),
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
    );
    complete(
        &mut scheduler,
        producer_b,
        HashSet::from([current("b")]),
        HashSet::new(),
        vec!["shared"],
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
    );
    assert!(!scheduler.facts().is_settled(&"shared"));

    complete(
        &mut scheduler,
        producer_a,
        HashSet::from([current("a")]),
        HashSet::new(),
        vec!["shared"],
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
    );

    let step = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["foo"],
        vec!["foo"],
    );
    assert!(
        enqueued_jobs(&step).contains(&reader),
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
    );
    // First appearance is an ascent: news, not a shift.
    let step = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["def"],
        vec!["def"],
    );
    assert!(enqueued_jobs(&step).contains(&reader));
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
    );
    assert!(enqueued_jobs(&step).contains(&reader));
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
    );
    complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_ret"],
        vec!["cum_ret"],
    );
    let _ = scheduler.pop();
    let step = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_ret"],
        vec!["cum_ret"],
    );
    assert!(enqueued_jobs(&step).contains(&reader));
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
    );
    complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_ret"],
        vec!["cum_ret"],
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
    );
    assert!(enqueued_jobs(&step).contains(&reader));
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
    );
    complete(
        &mut scheduler,
        middle,
        HashSet::from([current("def")]),
        HashSet::new(),
        vec!["cum_mid"],
        vec!["cum_mid"],
    );
    complete(
        &mut scheduler,
        upstream,
        HashSet::new(),
        HashSet::new(),
        vec!["def"],
        vec!["def"],
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
    );
    assert!(enqueued_jobs(&step).contains(&downstream));
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
    );
    complete(
        &mut scheduler,
        middle,
        HashSet::from([current("def")]),
        HashSet::new(),
        vec!["cum_mid"],
        vec!["cum_mid"],
    );
    complete(
        &mut scheduler,
        upstream,
        HashSet::new(),
        HashSet::new(),
        vec!["def"],
        vec!["def"],
    );
    while scheduler.pop().is_some() {}
    complete(
        &mut scheduler,
        upstream,
        HashSet::new(),
        HashSet::new(),
        vec!["def"],
        vec!["def"],
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
    );
    assert!(
        !enqueued_jobs(&step).contains(&downstream),
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
    );
    complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["def"],
        vec!["def"],
    );
    let _ = scheduler.pop();
    complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["def"],
        vec!["def"],
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
    );
    assert!(scheduler.rebased(&reader), "waiting keeps rebase pending");
}

#[test]
fn compiler2_scheduler_wake_attributes_each_coalesced_cause_to_a_single_evaluation() {
    // fz-kdt.34.3: two facts change in one `complete` call, both read by the
    // same subscriber. The subscriber must still land in the agenda exactly
    // once (coalescing is real), but each of the two causes that moved it
    // must be its own attributable `Wake` record — the whole point of
    // carrying causes is that coalescing a job's *evaluation* must not
    // coalesce away *why* it woke.
    let mut scheduler = TestScheduler::new();
    let subscriber = 5_u32;
    let producer = 1_u32;

    complete(
        &mut scheduler,
        subscriber,
        HashSet::from([current("f1"), current("f2")]),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
    );

    let step = complete(
        &mut scheduler,
        producer,
        HashSet::new(),
        HashSet::new(),
        vec!["f1", "f2"],
        vec!["f1", "f2"],
    );

    // One evaluation: the subscriber is queued exactly once even though two
    // of its reads moved in the same completion.
    assert_eq!(
        scheduler.pending_jobs(),
        1,
        "coalescing must not double-queue the subscriber's evaluation"
    );
    assert_eq!(scheduler.pop(), Some(subscriber));
    assert_eq!(
        scheduler.pop(),
        None,
        "the subscriber should appear in the agenda only once"
    );

    // This is inexpressible pre-change: `AppliedStep` had no `wakes` field
    // and no per-cause attribution at all, only a deduped job list.
    let subscriber_wakes = wakes_for(&step, subscriber);
    assert_eq!(
        subscriber_wakes.len(),
        2,
        "one wake record per distinct cause, even though the job itself was \
         enqueued only once: {subscriber_wakes:?}"
    );

    let enqueued_count = subscriber_wakes
        .iter()
        .filter(|wake| wake.disposition == WakeDisposition::Enqueued)
        .count();
    let coalesced_count = subscriber_wakes
        .iter()
        .filter(|wake| wake.disposition == WakeDisposition::Coalesced)
        .count();
    assert_eq!(
        enqueued_count, 1,
        "exactly one cause is the subscriber's real work start"
    );
    assert_eq!(
        coalesced_count, 1,
        "exactly one cause found the subscriber already pending"
    );

    assert!(
        subscriber_wakes.iter().any(|wake| wake.cause == current("f1")),
        "f1 should be attributed as a cause: {subscriber_wakes:?}"
    );
    assert!(
        subscriber_wakes.iter().any(|wake| wake.cause == current("f2")),
        "f2 should be attributed as a cause: {subscriber_wakes:?}"
    );
}

// ---------------------------------------------------------------------------
// fz-kdt.44: transitive finality.
//
// `Settled(F)` must mean F's whole upstream cone is quiescent, not merely that
// F's own publishers are clean. These tests are the spec's own TDD sequence.
// The chain built by `chain_a_b_c` is the shape every one of them starts from:
//
//     upstream --publishes--> "a" --read by--> job_b --publishes--> "b"
//                                   --read by--> job_c --publishes--> "c"
// ---------------------------------------------------------------------------

const UPSTREAM: u32 = 1;
const JOB_A: u32 = 2;
const JOB_B: u32 = 3;
const JOB_C: u32 = 4;

/// Builds `u -> a -> b -> c`, every link a `Current` read, and leaves every
/// fact settled with an empty agenda.
fn chain_a_b_c() -> TestScheduler {
    let mut scheduler = TestScheduler::new();
    complete(
        &mut scheduler,
        UPSTREAM,
        HashSet::new(),
        HashSet::new(),
        vec!["u"],
        vec!["u"],
    );
    complete(
        &mut scheduler,
        JOB_A,
        HashSet::from([current("u")]),
        HashSet::new(),
        vec!["a"],
        vec!["a"],
    );
    complete(
        &mut scheduler,
        JOB_B,
        HashSet::from([current("a")]),
        HashSet::new(),
        vec!["b"],
        vec!["b"],
    );
    complete(
        &mut scheduler,
        JOB_C,
        HashSet::from([current("b")]),
        HashSet::new(),
        vec!["c"],
        vec!["c"],
    );
    while scheduler.pop().is_some() {}
    scheduler
}

/// Spec test 1. Dirtying the head of a chain without moving any content must
/// make `Settled` unavailable all the way down — and must cost nothing: no
/// downstream formula re-evaluates, because no content moved.
#[test]
fn compiler2_scheduler_dirtying_a_chain_head_unsettles_the_whole_chain_without_evaluating_it() {
    let mut scheduler = chain_a_b_c();
    assert!(scheduler.facts().is_settled(&"c"));

    let step = complete(
        &mut scheduler,
        UPSTREAM,
        HashSet::new(),
        HashSet::new(),
        vec!["u"],
        vec!["u"],
    );

    assert_eq!(
        enqueued_jobs(&step),
        vec![JOB_A],
        "only the direct content reader may evaluate; readiness travels without re-running anyone",
    );
    assert!(!scheduler.facts().is_settled(&"a"), "a's publisher is dirty");
    assert!(
        !scheduler.facts().is_settled(&"b"),
        "b's publisher reads a fact that can still move, so b is not final",
    );
    assert!(
        !scheduler.facts().is_settled(&"c"),
        "finality is transitive: c is downstream of a dirty fact",
    );
    assert!(
        scheduler.facts().is_locally_settled(&"c"),
        "c's own publisher is clean — local cleanliness and finality are different questions",
    );
    assert_eq!(
        scheduler.facts().revision(&"c"),
        Some(1),
        "unfinality must not invent a content revision",
    );

    let _ = scheduler.pop();
    let concluded = complete(
        &mut scheduler,
        JOB_A,
        HashSet::from([current("u")]),
        HashSet::new(),
        vec!["a"],
        Vec::new(),
    );

    assert_eq!(
        enqueued_jobs(&concluded),
        Vec::<u32>::new(),
        "an unchanged conclusion re-finalizes the chain without evaluating anyone",
    );
    assert!(scheduler.facts().is_settled(&"a"));
    assert!(scheduler.facts().is_settled(&"b"));
    assert!(
        scheduler.facts().is_settled(&"c"),
        "the chain becomes final again when its head concludes unchanged",
    );
}

/// The tempting one-liner, rejected. Sending readiness-only movement through
/// `enqueue_dependents(Current(..))` would also satisfy "Settled(C) becomes
/// unavailable" — by re-running B and C on input that did not move. The model
/// promises minimal work, so correctness alone is not enough: a readiness-only
/// movement must produce ZERO evaluations.
#[test]
fn compiler2_scheduler_readiness_only_movement_evaluates_nobody() {
    let mut scheduler = chain_a_b_c();

    let step = complete(
        &mut scheduler,
        UPSTREAM,
        HashSet::new(),
        HashSet::new(),
        vec!["u"],
        vec!["u"],
    );
    let _ = scheduler.pop();
    let concluded = complete(
        &mut scheduler,
        JOB_A,
        HashSet::from([current("u")]),
        HashSet::new(),
        vec!["a"],
        Vec::new(),
    );

    let readiness_only_wakes: Vec<u32> = step
        .wakes
        .iter()
        .chain(concluded.wakes.iter())
        .filter(|wake| matches!(wake.cause, FactUse::Current(fact) if fact == "a" || fact == "b"))
        .map(|wake| wake.job)
        .collect();
    assert_eq!(
        readiness_only_wakes,
        Vec::<u32>::new(),
        "a fact that lost or regained finality without moving its content must wake no Current reader",
    );
    assert_eq!(scheduler.pending_jobs(), 0, "nothing may be left to evaluate");
}

/// Spec test 2. When the head's content really does move, only the transitive
/// CONTENT readers evaluate — one hop per completion, exactly as before this
/// ticket. Transitive finality adds no evaluations.
#[test]
fn compiler2_scheduler_content_movement_still_evaluates_only_content_readers() {
    let mut scheduler = chain_a_b_c();

    complete(
        &mut scheduler,
        UPSTREAM,
        HashSet::new(),
        HashSet::new(),
        vec!["u"],
        vec!["u"],
    );
    let _ = scheduler.pop();
    let moved = complete(
        &mut scheduler,
        JOB_A,
        HashSet::from([current("u")]),
        HashSet::new(),
        vec!["a"],
        vec!["a"],
    );
    assert_eq!(
        enqueued_jobs(&moved),
        vec![JOB_B],
        "a's content moved, so exactly its reader evaluates",
    );

    let _ = scheduler.pop();
    let moved = complete(
        &mut scheduler,
        JOB_B,
        HashSet::from([current("a")]),
        HashSet::new(),
        vec!["b"],
        vec!["b"],
    );
    assert_eq!(enqueued_jobs(&moved), vec![JOB_C]);

    let _ = scheduler.pop();
    complete(
        &mut scheduler,
        JOB_C,
        HashSet::from([current("b")]),
        HashSet::new(),
        vec!["c"],
        vec!["c"],
    );
    assert!(scheduler.facts().is_settled(&"c"));
}

/// Spec test 3, and the proof that counting alone is insufficient.
///
/// `job_a` reads `cum_b` and publishes `cum_a`; `job_b` reads `cum_a` and
/// publishes `cum_b`. Once both have concluded, each fact's only publisher
/// reads the other fact, so each counts the other as unfinal — forever. No
/// local rule can break that: the counts are correct and the fixed point they
/// describe is "both unfinal", which is wrong the moment the agenda drains.
///
/// The drain arbiter is what decides it: with nothing left to run, a locally
/// clean cone containing no dirty fact cannot move, so it is final.
#[test]
fn compiler2_scheduler_a_quiesced_cycle_needs_the_drain_arbiter_to_become_final() {
    let mut scheduler = TestScheduler::new();
    let waiter = 9_u32;

    complete(
        &mut scheduler,
        JOB_A,
        HashSet::from([current("cum_b")]),
        HashSet::new(),
        vec!["cum_a"],
        vec!["cum_a"],
    );
    complete(
        &mut scheduler,
        JOB_B,
        HashSet::from([current("cum_a")]),
        HashSet::new(),
        vec!["cum_b"],
        vec!["cum_b"],
    );
    // The peers converge by re-reading each other's current content.
    let _ = scheduler.pop();
    complete(
        &mut scheduler,
        JOB_A,
        HashSet::from([current("cum_b")]),
        HashSet::new(),
        vec!["cum_a"],
        Vec::new(),
    );
    complete(
        &mut scheduler,
        waiter,
        HashSet::new(),
        HashSet::from([settled("cum_a")]),
        Vec::new(),
        Vec::new(),
    );
    while scheduler.pop().is_some() {}

    assert!(
        scheduler.facts().is_locally_settled(&"cum_a") && scheduler.facts().is_locally_settled(&"cum_b"),
        "the cycle has quiesced: every publisher is clean",
    );
    assert!(
        !scheduler.facts().is_settled(&"cum_a"),
        "counting alone can never finalize a cycle — each clean member counts the other as unfinal",
    );

    let drained = scheduler.settle_quiescent(&["cum_a"]);

    assert!(
        scheduler.facts().is_settled(&"cum_a") && scheduler.facts().is_settled(&"cum_b"),
        "at a drain a locally clean cone with no dirty member is quiescent, so it is final",
    );
    assert_eq!(
        enqueued_jobs(&drained),
        vec![waiter],
        "the settled waiter wakes from the arbiter's readiness movement",
    );
    assert!(
        drained
            .movements
            .iter()
            .any(|movement| movement.key == "cum_a" && movement.state.settled),
        "the flip must appear as a real movement so the wake is attributable",
    );
    assert!(
        drained
            .changed
            .iter()
            .all(|change| !change.content_changed() && change.readiness_changed()),
        "the arbiter moves readiness only; no cell value changes",
    );
}

/// The arbiter is not a licence to call anything final. A fact whose own
/// publisher is dirty has not been re-derived from the ground it stands on,
/// and no amount of drain quiet changes that.
#[test]
fn compiler2_scheduler_the_drain_arbiter_refuses_a_fact_whose_own_publisher_is_dirty() {
    let mut scheduler = chain_a_b_c();
    complete(
        &mut scheduler,
        UPSTREAM,
        HashSet::new(),
        HashSet::new(),
        vec!["u"],
        vec!["u"],
    );
    // `job_a` is pending, so "a" is dirty. Drain the agenda WITHOUT running
    // it, which is the shape a blocked publisher leaves behind.
    while scheduler.pop().is_some() {}

    let step = scheduler.settle_quiescent(&["a", "c"]);

    assert!(!scheduler.facts().is_settled(&"a"), "a's own publisher never re-ran");
    assert!(
        step.changed.iter().all(|change| change.key != "a"),
        "the arbiter may not vouch for a fact whose publisher is dirty",
    );
    assert!(
        scheduler.facts().is_settled(&"c"),
        "c's own publishers are clean, and at a drain nothing can move without waking them first",
    );
}

/// The arbiter is a DRAIN rule and nothing else. While work is queued, the
/// transitive answer stands: a fact whose cone is still moving is not final,
/// however loudly someone asks.
#[test]
fn compiler2_scheduler_the_drain_arbiter_does_nothing_while_work_is_queued() {
    let mut scheduler = chain_a_b_c();
    complete(
        &mut scheduler,
        UPSTREAM,
        HashSet::new(),
        HashSet::new(),
        vec!["u"],
        vec!["u"],
    );
    assert_eq!(scheduler.pending_jobs(), 1, "job_a is queued to re-run");

    let step = scheduler.settle_quiescent(&["c"]);

    assert!(
        step.changed.is_empty(),
        "the arbiter is inert while the agenda holds work"
    );
    assert!(!scheduler.facts().is_settled(&"c"));
}

/// Spec test 4. A read added mid-ascent joins the finality graph immediately:
/// the standing values stay, and the new reader's own claims stop being final
/// because of the fact it just started reading.
#[test]
fn compiler2_scheduler_adding_a_read_updates_finality_incrementally() {
    let mut scheduler = chain_a_b_c();
    let late = 7_u32;

    complete(
        &mut scheduler,
        late,
        HashSet::new(),
        HashSet::new(),
        vec!["late"],
        vec!["late"],
    );
    while scheduler.pop().is_some() {}
    assert!(scheduler.facts().is_settled(&"late"));

    // Dirty the chain head; "late" reads nothing, so it stays final.
    complete(
        &mut scheduler,
        UPSTREAM,
        HashSet::new(),
        HashSet::new(),
        vec!["u"],
        vec!["u"],
    );
    assert!(scheduler.facts().is_settled(&"late"));

    // Now `late` re-concludes having read "b" — an edge added while the chain
    // above it is still moving.
    let step = complete(
        &mut scheduler,
        late,
        HashSet::from([current("b")]),
        HashSet::new(),
        vec!["late"],
        Vec::new(),
    );
    assert_eq!(
        scheduler.facts().revision(&"late"),
        Some(1),
        "adding a read must not disturb the standing value",
    );
    assert!(
        !scheduler.facts().is_settled(&"late"),
        "the new read reaches a fact that can still move, so the claim is no longer final",
    );
    assert_eq!(
        enqueued_jobs(&step),
        Vec::<u32>::new(),
        "adding a read evaluates nobody",
    );

    // Replacing the read with one that reaches nothing unfinal restores it.
    let _ = scheduler.pop();
    complete(
        &mut scheduler,
        JOB_A,
        HashSet::from([current("u")]),
        HashSet::new(),
        vec!["a"],
        Vec::new(),
    );
    assert!(scheduler.facts().is_settled(&"late"));
}

/// Spec test 5. Retraction and rebase reach the fixed point without leaving a
/// stale settled read behind: a retracted fact is nobody's ground, so its
/// former readers stop counting it, while the reader that rebased on the
/// retraction is dirty until it re-concludes.
#[test]
fn compiler2_scheduler_retraction_reaches_the_fixed_point_without_stale_settled_reads() {
    let mut scheduler = chain_a_b_c();

    // `job_a` retracts "a" by omission.
    let retracted = complete(
        &mut scheduler,
        JOB_A,
        HashSet::from([current("u")]),
        HashSet::new(),
        Vec::new(),
        vec!["a"],
    );
    assert_eq!(scheduler.facts().revision(&"a"), None);
    assert!(
        enqueued_jobs(&retracted).contains(&JOB_B),
        "a retraction is a ground shift for its readers",
    );
    assert!(scheduler.rebased(&JOB_B), "the reader of a retracted fact rebases",);
    assert!(
        !scheduler.facts().is_settled(&"b") && !scheduler.facts().is_settled(&"c"),
        "b is dirty and c is downstream of it",
    );

    let _ = scheduler.pop();
    complete(
        &mut scheduler,
        JOB_B,
        HashSet::from([current("a")]),
        HashSet::new(),
        vec!["b"],
        Vec::new(),
    );
    while scheduler.pop().is_some() {}

    assert!(
        scheduler.facts().is_settled(&"b"),
        "reading an absent fact is not reading an unfinal one — nobody is deriving it",
    );
    assert!(
        scheduler.facts().is_settled(&"c"),
        "the fixed point is reached with no publisher left dirty and no cone left moving",
    );
}
