use std::collections::HashSet;

use super::{Agenda, AppliedStep, DependencyIndex, FactUse, Scheduler, Wake, WakeDisposition};
use crate::compiler2::facts::ClaimShape;
use crate::compiler2::facts::DerivationId;
use crate::compiler2::scheduler::DerivationEffects;
use crate::compiler2::scheduler::take_next_fact_change;
use crate::compiler2::semantic::SemanticOrd;

struct TestOrder;

impl SemanticOrd<TestOrder> for u32 {
    fn semantic_cmp(&self, other: &Self, _ctx: &TestOrder) -> std::cmp::Ordering {
        self.cmp(other)
    }
}

impl SemanticOrd<TestOrder> for &'static str {
    fn semantic_cmp(&self, other: &Self, _ctx: &TestOrder) -> std::cmp::Ordering {
        self.cmp(other)
    }
}

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

#[test]
fn compiler2_scheduler_fact_frontier_preserves_newest_first_equal_key_chronology() {
    let change = |key: &'static str, revision: u64| crate::compiler2::FactChange {
        key,
        old_revision: revision.checked_sub(1),
        new_revision: Some(revision),
        old_settled: false,
        new_settled: false,
    };
    let mut pending = vec![change("a", 1), change("c", 2), change("b", 3), change("c", 4)];
    let mut revisions = Vec::new();
    while let Some(change) = take_next_fact_change(&mut pending, &TestOrder) {
        revisions.push(change.new_revision.expect("fixture movements have revisions"));
    }
    assert_eq!(
        revisions,
        vec![1, 3, 4, 2],
        "typed minimum keys drain first, while interleaved equal keys retain newest-first chronology",
    );
}

#[test]
fn compiler2_scheduler_keeps_claims_in_the_ledger_not_the_completion_report() {
    let mut scheduler = TestScheduler::new();
    let step = complete(
        &mut scheduler,
        1,
        HashSet::new(),
        HashSet::new(),
        vec!["answer"],
        vec!["answer"],
    );

    let AppliedStep {
        changed,
        movements,
        wakes,
        blocked,
    } = step;
    assert_eq!(changed.len(), 1);
    assert_eq!(movements.len(), 1);
    assert!(wakes.is_empty());
    assert!(blocked.is_empty());
    assert_eq!(
        scheduler.output_keys(&1).iter().copied().collect::<Vec<_>>(),
        vec!["answer"]
    );
}

fn current(fact: &'static str) -> FactUse<&'static str> {
    FactUse::current(fact)
}

fn settled(fact: &'static str) -> FactUse<&'static str> {
    FactUse::settled(fact)
}

/// One job, one answer: the whole-body derivation every job that does not
/// split its ownership publishes under. An unblocked run concludes it; a
/// blocked run did not reach it, which is exactly today's "a blocked
/// publisher's claims are all dirty".
fn complete(
    scheduler: &mut TestScheduler,
    job: u32,
    reads: HashSet<FactUse<&'static str>>,
    waits: HashSet<FactUse<&'static str>>,
    outputs: Vec<&'static str>,
    changed: Vec<&'static str>,
) -> AppliedStep<u32, &'static str> {
    let concluded = waits.is_empty();
    scheduler.complete_ordered(
        &job,
        waits,
        vec![DerivationEffects::sole(reads, outputs, changed, concluded)],
        &TestOrder,
    )
}

/// A job that reports several independent answers in one run. Each tuple is
/// `(derivation, reads, outputs, changed, concluded)` — `concluded` says the
/// run reached that answer, which only a blocked run can answer `false` to.
type Reported = (
    DerivationId,
    HashSet<FactUse<&'static str>>,
    Vec<&'static str>,
    Vec<&'static str>,
    bool,
);

fn complete_derivations(
    scheduler: &mut TestScheduler,
    job: u32,
    waits: HashSet<FactUse<&'static str>>,
    derivations: Vec<Reported>,
) -> AppliedStep<u32, &'static str> {
    let effects = derivations
        .into_iter()
        .map(|(derivation, reads, outputs, changed, concluded)| DerivationEffects {
            derivation,
            reads,
            outputs,
            changed,
            concluded,
        })
        .collect();
    scheduler.complete_ordered(&job, waits, effects, &TestOrder)
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

    let waiters = deps.waiters(&current("foo"), &TestOrder);
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
    let unresolved = scheduler.unresolved(&TestOrder);
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

/// fz-kdt.84: a cumulative fact's first claim carrying NO content is presence,
/// not a movement.
///
/// A cumulative fact's store maintains a join, and a join has a bottom. A
/// `Current` reader of the empty join gets exactly what a reader of the absent
/// key gets, so nothing a reader could act on happened -- the claim announces
/// only that someone is now deriving the key. Waking every `Current` reader of
/// nothing is work with no evidence behind it.
///
/// The other question the slot answers still moves, and must: the fact is
/// SETTLED, so the settled waiter wakes on the readiness edge alone.
#[test]
fn compiler2_scheduler_cumulative_appearance_at_bottom_wakes_no_current_reader() {
    let mut scheduler = TestScheduler::new();
    let writer = 1_u32;
    let reader = 2_u32;
    let settled_waiter = 3_u32;

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
        settled_waiter,
        HashSet::new(),
        HashSet::from([settled("cum_ret")]),
        Vec::new(),
        Vec::new(),
    );
    // The claim lists the key as an output but marks nothing changed: the
    // publisher is deriving it and has reached bottom.
    let step = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_ret"],
        Vec::new(),
    );

    assert!(
        wakes_for(&step, reader).is_empty(),
        "a Current reader of the empty join must not wake: it would re-derive from the same \
         nothing it already read. Wakes: {:?}",
        step.wakes.iter().map(|wake| wake.job).collect::<Vec<_>>(),
    );
    assert_eq!(
        scheduler.facts().revision(&"cum_ret"),
        Some(0),
        "a cumulative claim with no content is PRESENT at bottom -- revision 0, the reading a \
         Current reader cannot tell from absence",
    );
    assert!(
        scheduler.facts().is_settled(&"cum_ret"),
        "the claim is clean and its publisher read nothing, so the fact settles",
    );
    assert_eq!(
        enqueued_jobs(&step),
        vec![settled_waiter],
        "settledness DID move, so the settled waiter wakes",
    );
}

/// fz-kdt.84's other half: suppressing the bottom appearance loses no
/// evidence. The first claim that actually carries content wakes the `Current`
/// reader, and wakes it exactly once -- the bottom claim before it contributed
/// no second wake.
#[test]
fn compiler2_scheduler_first_cumulative_content_after_bottom_wakes_the_reader_once() {
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
    let at_bottom = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_ret"],
        Vec::new(),
    );
    let ascent = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_ret"],
        vec!["cum_ret"],
    );

    assert_eq!(
        at_bottom.wakes.len() + wakes_for(&ascent, reader).len(),
        1,
        "the reader must be woken once across the pair: never by the bottom claim, always by \
         the content. Bottom wakes: {:?}",
        at_bottom.wakes.iter().map(|wake| wake.job).collect::<Vec<_>>(),
    );
    assert_eq!(
        scheduler.facts().revision(&"cum_ret"),
        Some(1),
        "the first real evidence moves the fact off bottom",
    );
    assert!(
        !scheduler.rebased(&reader),
        "climbing off bottom is an ascent, not a ground shift",
    );
}

/// fz-kdt.84's sibling guard. The rule is about the fact's CONTENT ALGEBRA,
/// not about whether the publisher marked the key changed.
///
/// A replacing fact has no bottom to be at: whatever it says on arrival is
/// content a reader can see and act on -- `CallSiteSummary`'s `Unresolved`
/// is a reader-visible answer, not the absence of one. So its first
/// appearance stays a movement even when the publisher lists nothing changed,
/// and the demand facts (`Activation`, `Executable`) that gate whole cones on
/// presence keep waking their readers the way they always have.
#[test]
fn compiler2_scheduler_replacing_appearance_wakes_current_readers_unmarked() {
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
    let step = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["def"],
        Vec::new(),
    );

    assert_eq!(
        scheduler.facts().revision(&"def"),
        Some(1),
        "a replacing fact appears with content, so it appears at revision 1",
    );
    assert_eq!(
        enqueued_jobs(&step),
        vec![reader],
        "a replacing fact's first appearance is news for its Current readers whether or not the \
         publisher marked it changed",
    );
}

#[test]
fn compiler2_scheduler_contentful_retraction_shifts() {
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

    let drained = scheduler.settle_quiescent_ordered(&["cum_a"], &TestOrder);

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

    let step = scheduler.settle_quiescent_ordered(&["a", "c"], &TestOrder);

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

    let step = scheduler.settle_quiescent_ordered(&["c"], &TestOrder);

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

// ---------------------------------------------------------------------------
// fz-kdt.13.1 — the publisher is a DERIVATION, not a job.
//
// The shape every case below uses is one job with two independent answers:
//
//     "cum_a" --read by--> D1 of PUBLISHER --publishes--> "x"
//     "cum_b" --read by--> D2 of PUBLISHER --publishes--> "y"
//
// Moving "cum_a" is news about "x" and nothing else. Job-granular publisher
// identity cannot say that: one publisher owns both claims, so one woken read
// dirties both and unfinalises everything downstream of either. Deriving "y"
// from ground that did not move is what makes it settled, and that is a
// statement about the ANSWER, not about the body that computed it.
// ---------------------------------------------------------------------------

const PUBLISHER: u32 = 20;
const GROUND_A: u32 = 21;
const GROUND_B: u32 = 22;
const Y_WAITER: u32 = 23;

const D1: DerivationId = DerivationId(1);
const D2: DerivationId = DerivationId(2);

/// `cum_a -> x` and `cum_b -> y`, published by ONE job under two derivations,
/// with a settled waiter parked on "y". Everything is quiet and the agenda is
/// empty on return.
fn two_answer_publisher() -> TestScheduler {
    let mut scheduler = TestScheduler::new();
    complete(
        &mut scheduler,
        GROUND_A,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_a"],
        vec!["cum_a"],
    );
    complete(
        &mut scheduler,
        GROUND_B,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_b"],
        vec!["cum_b"],
    );
    complete_derivations(
        &mut scheduler,
        PUBLISHER,
        HashSet::new(),
        vec![
            (D1, HashSet::from([current("cum_a")]), vec!["x"], vec!["x"], true),
            (D2, HashSet::from([current("cum_b")]), vec!["y"], vec!["y"], true),
        ],
    );
    complete(
        &mut scheduler,
        Y_WAITER,
        HashSet::new(),
        HashSet::from([settled("y")]),
        Vec::new(),
        Vec::new(),
    );
    while scheduler.pop().is_some() {}
    scheduler
}

/// The before-behavior, kept as a characterization: with the whole body as ONE
/// publisher, movement under "x" takes "y" down with it. Nothing about "y"'s
/// own ground changed — the pessimism is entirely in the identity.
#[test]
fn compiler2_scheduler_job_granular_identity_unsettles_an_untouched_sibling_answer() {
    let mut scheduler = TestScheduler::new();
    complete(
        &mut scheduler,
        GROUND_A,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_a"],
        vec!["cum_a"],
    );
    complete(
        &mut scheduler,
        GROUND_B,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_b"],
        vec!["cum_b"],
    );
    complete(
        &mut scheduler,
        PUBLISHER,
        HashSet::from([current("cum_a"), current("cum_b")]),
        HashSet::new(),
        vec!["x", "y"],
        vec!["x", "y"],
    );
    while scheduler.pop().is_some() {}
    assert!(scheduler.facts().is_settled(&"y"));

    complete(
        &mut scheduler,
        GROUND_A,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_a"],
        vec!["cum_a"],
    );

    assert!(
        !scheduler.facts().is_settled(&"y"),
        "one publisher for the whole body means one woken read unsettles every claim it holds",
    );
}

/// The refinement. Same two answers, two derivations: moving the input of one
/// leaves the other settled, and evaluates the job exactly once.
#[test]
fn compiler2_scheduler_moving_one_derivations_input_leaves_its_sibling_settled() {
    let mut scheduler = two_answer_publisher();
    assert!(scheduler.facts().is_settled(&"y"), "the graph starts quiet");

    let moved = complete(
        &mut scheduler,
        GROUND_A,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_a"],
        vec!["cum_a"],
    );

    assert!(
        scheduler.facts().is_settled(&"y"),
        "\"y\" is derived from \"cum_b\" alone; moving \"cum_a\" cannot unsettle it",
    );
    assert!(
        !scheduler.facts().is_settled(&"x"),
        "\"x\" IS derived from what moved, so its own answer is provisional",
    );
    assert_eq!(
        enqueued_jobs(&moved),
        vec![PUBLISHER],
        "the job runs whole, so the agenda entry is still the job",
    );
    assert!(
        scheduler.facts().is_quiet(&"cum_b"),
        "the sibling's ground is never disturbed",
    );

    let _ = scheduler.pop();
    complete_derivations(
        &mut scheduler,
        PUBLISHER,
        HashSet::new(),
        vec![
            (D1, HashSet::from([current("cum_a")]), vec!["x"], vec!["x"], true),
            (D2, HashSet::from([current("cum_b")]), vec!["y"], Vec::new(), true),
        ],
    );
    assert!(
        scheduler.facts().is_settled(&"x") && scheduler.facts().is_settled(&"y"),
        "re-concluding both answers re-finalises the one that moved",
    );
}

/// A `Settled` waiter is the sharp end of the same question: it must not fire
/// on movement under a sibling answer, and it must still fire when its own
/// answer's ground moves.
#[test]
fn compiler2_scheduler_a_settled_waiter_fires_only_when_its_own_answers_ground_moves() {
    let mut scheduler = two_answer_publisher();

    let sibling_moved = complete(
        &mut scheduler,
        GROUND_A,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_a"],
        vec!["cum_a"],
    );
    assert!(
        !enqueued_jobs(&sibling_moved).contains(&Y_WAITER),
        "a waiter on \"y\" must not be disturbed by movement under \"x\"",
    );
    while scheduler.pop().is_some() {}

    let own_moved = complete(
        &mut scheduler,
        GROUND_B,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_b"],
        vec!["cum_b"],
    );
    assert!(
        !scheduler.facts().is_settled(&"y"),
        "\"y\"'s own ground moved, so \"y\" is provisional until it is re-derived",
    );
    assert!(
        !enqueued_jobs(&own_moved).contains(&Y_WAITER),
        "a settled wait is not satisfied by an unsettled fact",
    );

    let _ = scheduler.pop();
    let republished = complete_derivations(
        &mut scheduler,
        PUBLISHER,
        HashSet::new(),
        vec![
            (D1, HashSet::from([current("cum_a")]), vec!["x"], Vec::new(), true),
            (D2, HashSet::from([current("cum_b")]), vec!["y"], vec!["y"], true),
        ],
    );

    assert!(
        enqueued_jobs(&republished).contains(&Y_WAITER),
        "the waiter fires when the answer it waits on re-settles",
    );
}

/// Rebase vetoes all scoping. A ground shift means the woken job's next
/// conclusion may NARROW its cumulative stores, and the rebase flag that
/// selects narrowing is the job's — so every answer the job holds goes
/// provisional, sibling or not.
#[test]
fn compiler2_scheduler_a_ground_shift_dirties_every_derivation_of_the_woken_job() {
    let mut scheduler = two_answer_publisher();

    let retracted = complete(
        &mut scheduler,
        GROUND_A,
        HashSet::new(),
        HashSet::new(),
        Vec::new(),
        vec!["cum_a"],
    );

    assert!(scheduler.rebased(&PUBLISHER), "a retraction shifts its reader's ground");
    assert!(
        !scheduler.facts().is_settled(&"x") && !scheduler.facts().is_settled(&"y"),
        "a rebased job may narrow any answer it holds, so scoping the dirt would be unsound",
    );
    assert!(
        !scheduler.facts().is_locally_settled(&"y"),
        "the shift reaches the sibling answer's own claim, not just its finality",
    );
    assert_eq!(
        enqueued_jobs(&retracted),
        vec![PUBLISHER],
        "dirtying every answer still evaluates the job exactly once",
    );
}

/// A blocked run reports what it reached. The answers it concluded before the
/// block are vouched for; the ones it never got to stay dirty. This is the
/// traffic the epidemic rode: most completions block.
#[test]
fn compiler2_scheduler_a_blocked_run_keeps_the_answers_it_reached_clean() {
    let mut scheduler = TestScheduler::new();
    complete(
        &mut scheduler,
        GROUND_A,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_a"],
        vec!["cum_a"],
    );

    complete_derivations(
        &mut scheduler,
        PUBLISHER,
        HashSet::from([current("missing")]),
        vec![
            (D1, HashSet::from([current("cum_a")]), vec!["x"], vec!["x"], true),
            (D2, HashSet::new(), vec!["y"], vec!["y"], false),
        ],
    );

    assert!(
        scheduler.facts().is_settled(&"x"),
        "the answer the run reached stands on quiet ground and is final",
    );
    assert!(
        !scheduler.facts().is_locally_settled(&"y"),
        "the answer the run never reached is dirty, exactly as a whole blocked job used to be",
    );
}

/// The drain arbiter, restated at derivation granularity. Its licence has
/// always been "the publishers of THIS key are clean and nothing is left to
/// run" — and the publishers of a key are the derivations whose answer it is.
/// A dirty sibling publishes other keys and is correctly not consulted.
#[test]
fn compiler2_scheduler_the_drain_arbiter_settles_a_clean_answer_beside_a_dirty_sibling() {
    let mut scheduler = TestScheduler::new();
    complete(
        &mut scheduler,
        GROUND_B,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_b"],
        vec!["cum_b"],
    );
    // `ground_b` pauses, so "cum_b" is dirty and every reader of it is unfinal.
    complete(
        &mut scheduler,
        GROUND_B,
        HashSet::new(),
        HashSet::from([current("missing_b")]),
        vec!["cum_b"],
        Vec::new(),
    );
    complete_derivations(
        &mut scheduler,
        PUBLISHER,
        HashSet::from([current("missing")]),
        vec![
            (D1, HashSet::from([current("cum_b")]), vec!["x"], vec!["x"], true),
            (D2, HashSet::new(), vec!["y"], vec!["y"], false),
        ],
    );
    while scheduler.pop().is_some() {}

    assert!(
        scheduler.facts().is_locally_settled(&"x") && !scheduler.facts().is_settled(&"x"),
        "x's own answer is clean but reads a fact that can still move",
    );

    let drained = scheduler.settle_quiescent_ordered(&["x", "y"], &TestOrder);

    assert!(
        scheduler.facts().is_settled(&"x"),
        "at a drain the claimants of x are clean and nothing can run, so x is final",
    );
    assert!(
        !scheduler.facts().is_settled(&"y"),
        "the arbiter still refuses a key whose OWN claimant never re-ran",
    );
    assert!(
        drained
            .changed
            .iter()
            .all(|change| !change.content_changed() && change.readiness_changed()),
        "the arbiter moves readiness only; no cell value changes",
    );
}

/// Retraction-by-omission, lifted. A concluding job that stops giving an
/// answer withdraws it whole — its claims retract and its subscriptions go —
/// which is how a vanished decision boundary prunes what it used to own.
#[test]
fn compiler2_scheduler_a_conclusion_withdraws_the_answers_it_no_longer_gives() {
    let mut scheduler = two_answer_publisher();

    let withdrawn = complete_derivations(
        &mut scheduler,
        PUBLISHER,
        HashSet::new(),
        vec![(D1, HashSet::from([current("cum_a")]), vec!["x"], Vec::new(), true)],
    );

    assert_eq!(
        scheduler.facts().revision(&"y"),
        None,
        "an answer the job no longer gives is retracted, not left standing",
    );
    assert!(
        withdrawn.movements.iter().any(|movement| movement.key == "y"),
        "the withdrawal is a real movement, so readers hear it",
    );
    assert_eq!(
        scheduler.facts().revision(&"x"),
        Some(1),
        "the answer it still gives is untouched",
    );

    // The withdrawn answer's subscription is gone with it.
    complete(
        &mut scheduler,
        GROUND_B,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_b"],
        vec!["cum_b"],
    );
    assert_eq!(
        scheduler.pending_jobs(),
        0,
        "a retracted answer's reads no longer wake the job that gave it",
    );
}

/// The job-level fold of per-derivation finality: what a readiness-ordered pop
/// would ask. It is a projection of the ledger, never a second copy of it.
#[test]
fn compiler2_scheduler_job_level_unfinal_reads_fold_every_derivation() {
    let mut scheduler = two_answer_publisher();
    assert_eq!(
        scheduler.unfinal_reads(&PUBLISHER),
        0,
        "every answer stands on quiet ground",
    );

    // `ground_b` pauses, so "cum_b" can still move and the answer that reads it
    // — and only that answer — becomes provisional.
    complete(
        &mut scheduler,
        GROUND_B,
        HashSet::new(),
        HashSet::from([current("missing_b")]),
        vec!["cum_b"],
        Vec::new(),
    );

    assert_eq!(
        scheduler.unfinal_reads(&PUBLISHER),
        1,
        "exactly one answer's ground is moving, and the fold says so",
    );
    assert!(
        scheduler.facts().is_settled(&"x") && !scheduler.facts().is_settled(&"y"),
        "the unfinality lands on the answer that read the moving ground, not on the body",
    );
}

/// The waiter half of fz-kdt.84's law: `satisfies` and the wake path must
/// never disagree. A `Current` wait is satisfied by PRESENCE, so a cumulative
/// fact appearing at bottom -- no content movement -- must still wake a
/// waiter whose last unsatisfied wait it was, or that waiter is
/// satisfied-and-asleep forever.
#[test]
fn compiler2_scheduler_current_waiter_on_a_cumulative_bottom_claim_is_woken() {
    let mut scheduler = TestScheduler::new();
    let writer = 1_u32;
    let waiter = 2_u32;

    complete(
        &mut scheduler,
        waiter,
        HashSet::new(),
        HashSet::from([current("cum_ret")]),
        Vec::new(),
        Vec::new(),
    );

    let step = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        vec!["cum_ret"],
        Vec::new(),
    );

    assert!(
        scheduler.facts().satisfies(&current("cum_ret")),
        "a bottom claim is present, so the Current wait is satisfied",
    );
    assert_eq!(
        enqueued_jobs(&step),
        vec![waiter],
        "the satisfied waiter must be woken -- satisfies and the wake path may never disagree",
    );
    assert!(
        step.wakes.iter().all(|wake| !wake.shift),
        "presence is not a ground shift: nothing the waiter could have read moved",
    );
}

/// The retraction half: taking away a BOTTOM claim removes nothing anyone
/// could have read, so it is not a ground shift and wakes no `Current`
/// reader; the readiness flip still reaches settled waiters. (The sibling
/// `contentful_retraction_shifts` pins the shift for claims that carried
/// content.)
#[test]
fn compiler2_scheduler_bottom_claim_retraction_is_not_a_shift() {
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
        Vec::new(),
    );

    // The writer concludes again WITHOUT the claim: a bottom claim retracts.
    let step = complete(
        &mut scheduler,
        writer,
        HashSet::new(),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
    );

    assert!(
        wakes_for(&step, reader).is_empty(),
        "retracting a bottom claim takes away nothing the reader could have read; wakes: {:?}",
        step.wakes.iter().map(|wake| wake.job).collect::<Vec<_>>(),
    );
    assert!(
        !scheduler.rebased(&reader),
        "no ground shifted: the reader read nothing then, and reads nothing now",
    );
    assert_eq!(scheduler.facts().revision(&"cum_ret"), None, "the claim is gone",);
}

/// Two schedulers that arrive at the same set of standing waits by opposite
/// histories must describe that set identically (fz-kdt.109).
///
/// `unresolved()` is what a stalled compile's error message renders, so its
/// order is user-facing text. It used to be `HashMap` order, which is a
/// per-process `RandomState` artifact: one binary printed a different message
/// run to run for any program that could not settle. Two schedulers in one
/// process stand in for two runs — their waiter maps carry different seeds and
/// different insertion orders, and the wait SET they hold is the same, so any
/// difference in the rendering is order leaking out.
#[test]
fn compiler2_unresolved_renders_the_same_whatever_order_the_waits_arrived_in() {
    const FACTS: [&str; 12] = [
        "alpha", "bravo", "charlie", "delta", "echo", "foxtrot", "golf", "hotel", "india", "juliet", "kilo", "lima",
    ];

    let mut ascending = TestScheduler::new();
    for (job, fact) in FACTS.iter().enumerate() {
        complete(
            &mut ascending,
            job as u32,
            HashSet::new(),
            HashSet::from([current(fact), settled(fact)]),
            Vec::new(),
            Vec::new(),
        );
    }

    let mut descending = TestScheduler::new();
    for (job, fact) in FACTS.iter().enumerate().rev() {
        complete(
            &mut descending,
            job as u32,
            HashSet::new(),
            HashSet::from([current(fact), settled(fact)]),
            Vec::new(),
            Vec::new(),
        );
    }

    assert_eq!(
        format!("{:?}", ascending.unresolved(&TestOrder)),
        format!("{:?}", descending.unresolved(&TestOrder)),
        "the same standing waits should render the same however they were recorded"
    );
}
