use std::collections::HashSet;

use super::{Agenda, DependencyIndex, ExactPattern, FactValue, Scheduler};
use crate::types::Types;

type TestScheduler = Scheduler<u32, &'static str, ExactPattern<&'static str>>;

fn presence(fact: &'static str, revision: u64) -> (&'static str, FactValue) {
    (fact, FactValue::presence(revision))
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
    let mut scheduler = TestScheduler::new();

    let subscriber = 2_u32;
    let writer = 1_u32;
    let fact = "foo";

    let subscribe = scheduler.complete(
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

    let first = scheduler.complete(
        writer,
        HashSet::new(),
        HashSet::new(),
        vec![presence(fact, 1)],
        Vec::new(),
    );
    let first_enqueued = first.enqueued;
    assert_eq!(first_enqueued, vec![subscriber]);
    assert_eq!(scheduler.facts().fingerprint(&fact), Some(1));
    assert_eq!(scheduler.pop(), Some(subscriber));

    let second = scheduler.complete(
        writer,
        HashSet::new(),
        HashSet::new(),
        vec![presence(fact, 1)],
        Vec::new(),
    );
    assert!(
        second.enqueued.is_empty(),
        "no-change writes should not wake subscribers"
    );
    let second_changed = second.changed;
    assert!(
        second_changed.is_empty(),
        "same aggregate revision should suppress changes"
    );

    let third = scheduler.complete(
        writer,
        HashSet::new(),
        HashSet::new(),
        vec![presence(fact, 9)],
        Vec::new(),
    );
    let third_enqueued = third.enqueued;
    assert_eq!(third_enqueued, vec![subscriber]);
    assert_eq!(scheduler.facts().fingerprint(&fact), Some(9));
}

#[test]
fn compiler2_scheduler_retracts_old_outputs_and_recomputes_aggregate() {
    let mut scheduler = TestScheduler::new();
    let fact = "foo";
    let subscriber = 9_u32;

    scheduler.complete(
        subscriber,
        HashSet::from([fact]),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
    );
    scheduler.complete(
        1_u32,
        HashSet::new(),
        HashSet::new(),
        vec![presence(fact, 5)],
        Vec::new(),
    );
    scheduler.complete(
        2_u32,
        HashSet::new(),
        HashSet::new(),
        vec![presence(fact, 7)],
        Vec::new(),
    );
    assert_eq!(scheduler.facts().fingerprint(&fact), Some(7));
    let _ = scheduler.pop();

    let retracted = scheduler.complete(2_u32, HashSet::new(), HashSet::new(), Vec::new(), Vec::new());
    let changed = retracted.changed;
    let enqueued = retracted.enqueued;
    assert_eq!(scheduler.facts().fingerprint(&fact), Some(5));
    assert_eq!(changed.len(), 1, "retraction should change the aggregate");
    assert_eq!(
        changed[0].old_fingerprint,
        Some(7),
        "old fingerprint should reflect the old aggregate"
    );
    assert_eq!(
        changed[0].new_fingerprint,
        Some(5),
        "new fingerprint should reflect the recomputed aggregate"
    );
    assert_eq!(enqueued, vec![subscriber]);
}

#[test]
fn compiler2_scheduler_wakes_waiters_when_a_matching_fact_appears() {
    let mut scheduler = TestScheduler::new();
    let waiter = 4_u32;

    scheduler.complete(
        waiter,
        HashSet::new(),
        HashSet::from([ExactPattern("foo")]),
        Vec::new(),
        Vec::new(),
    );
    let result = scheduler.complete(
        1_u32,
        HashSet::new(),
        HashSet::new(),
        vec![presence("foo", 1)],
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

    scheduler.complete(
        4_u32,
        HashSet::new(),
        HashSet::from([ExactPattern("foo")]),
        Vec::new(),
        Vec::new(),
    );
    assert!(
        scheduler.has_unresolved(),
        "registering a waiter should make unresolved work observable"
    );

    scheduler.complete(
        1_u32,
        HashSet::new(),
        HashSet::new(),
        vec![presence("foo", 1)],
        Vec::new(),
    );
    assert_eq!(
        scheduler.pop(),
        Some(4_u32),
        "publishing the waited-for fact should enqueue the blocked job to rerun"
    );
    scheduler.complete(4_u32, HashSet::new(), HashSet::new(), Vec::new(), Vec::new());
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

    let step = scheduler.complete(1, HashSet::new(), HashSet::new(), Vec::new(), vec![3, 3, 4]);

    assert_eq!(
        step.enqueued,
        vec![3, 4],
        "follow-up jobs should be coalesced before they hit the agenda"
    );
    assert_eq!(scheduler.pop(), Some(1));
    assert_eq!(scheduler.pop(), Some(2));
    assert_eq!(scheduler.pop(), Some(3));
    assert_eq!(scheduler.pop(), Some(4));
    assert_eq!(scheduler.pop(), None);
}

#[test]
fn compiler2_scheduler_joins_input_values_and_wakes_only_when_join_changes() {
    let mut scheduler = TestScheduler::new();
    let subscriber = 9_u32;
    let fact = "activation";

    scheduler.complete(
        subscriber,
        HashSet::from([fact]),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
    );

    let mut types = crate::types::new();
    let int = types.int();
    let empty = types.empty_list();
    let non_empty_int = types.non_empty_list(int.clone());
    let list_int = types.list(int);

    let first = scheduler.complete(
        1_u32,
        HashSet::new(),
        HashSet::new(),
        vec![(fact, FactValue::inputs(vec![empty]))],
        Vec::new(),
    );
    assert_eq!(
        first.enqueued,
        vec![subscriber],
        "the first activation-input contribution should wake the subscriber"
    );
    assert_eq!(scheduler.pop(), Some(subscriber));

    let second = scheduler.complete(
        2_u32,
        HashSet::new(),
        HashSet::new(),
        vec![(fact, FactValue::inputs(vec![non_empty_int.clone()]))],
        Vec::new(),
    );
    assert_eq!(
        second.enqueued,
        vec![subscriber],
        "a contribution that widens the aggregate input should wake the subscriber"
    );
    assert_eq!(
        scheduler.facts().slot(&fact).and_then(|slot| slot.value()),
        Some(&FactValue::inputs(vec![list_int])),
        "activation-input slots should aggregate caller inputs with refine_widen"
    );
    assert_eq!(scheduler.pop(), Some(subscriber));

    let third = scheduler.complete(
        2_u32,
        HashSet::new(),
        HashSet::new(),
        vec![(fact, FactValue::inputs(vec![non_empty_int]))],
        Vec::new(),
    );
    assert!(
        third.changed.is_empty(),
        "rewriting an equal contribution should not change the joined input value"
    );
    assert!(
        third.enqueued.is_empty(),
        "stable activation-input joins should not wake subscribers"
    );
}
