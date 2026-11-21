use super::*;
use crate::any_value::AnyValueRef;
use crate::any_value::ValueKind;
use crate::bits::{SharedBinHandle, alloc_buffer_view};
use crate::exec_ctx::ExecCtx;
use crate::heap::StubSite;
use crate::heap::{SchemaRegistry, pool_drain_for_test, pool_outstanding_blocks, pool_total_cached_blocks};
use crate::park::park_test::{code_of, frame_of, leaked_site};
use crate::park::{MatcherFn, ParkRecord, ReceiveClause, Roots};
use crate::sync::Ordering;
use std::cell::RefCell;
use std::ptr::read;
use std::rc::Rc;

extern "C" fn match_42(_process: *mut Process, msg: u64, _frame: u64, out: *mut AnyValueRef) -> u32 {
    let msg_ref = AnyValueRef::from_raw_word(msg).expect("msg ref");
    if msg_ref.tag() == ValueKind::INT && msg_ref.load_int().expect("int msg") == 42 {
        unsafe {
            *out = msg_ref;
        }
        1
    } else {
        0
    }
}

fn shared_refs(handle: &SharedBinHandle) -> usize {
    unsafe { (*handle.as_raw()).refcount.load(Ordering::Relaxed) }
}

fn int_ref(n: i64) -> AnyValueRef {
    let slot = Box::leak(Box::new(n as u64));
    AnyValueRef::from_scalar_slot(ValueKind::INT, slot as *const u64).expect("test int ref")
}

fn fresh_task() -> Process {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    Process::new(schemas)
}

const CLAUSE_CODE: usize = 0xdead_beef;
const AFTER_CODE: usize = 0xcafe_babe;

/// A parked receive of one clause whose matcher writes `root_count` roots, with an
/// after body, over a frame that captures nothing.
fn record_of(task: &mut Process, matcher: MatcherFn, root_count: u32, timer: Option<TimerId>) -> ParkRecord {
    let clause = ReceiveClause {
        code: CLAUSE_CODE,
        projector: None,
        root_count,
        argument_count: root_count,
        empty_slots: 0,
    };
    ParkRecord {
        site: leaked_site(matcher, Some((AFTER_CODE, 0)), 0, &[clause]),
        frame: frame_of(&mut task.heap, &[]),
        after_deadline_ms: timer.map(|_| 0),
        after_timer_id: timer,
    }
}

fn record_on_42(task: &mut Process, timer: Option<TimerId>) -> ParkRecord {
    record_of(task, match_42, 1, timer)
}

fn park_on_42(task: &mut Process, timer: Option<TimerId>) {
    let record = record_on_42(task, timer);
    task.delivery.lock().install_park(record);
    task.state = ProcessState::Blocked;
}

fn running_task() -> Process {
    let mut task = fresh_task();
    task.state = ProcessState::Running;
    task
}

fn mailbox_ints(task: &Process) -> Vec<i64> {
    task.mailbox.messages().map(|v| v.load_int().unwrap()).collect()
}

/// A sender's list `[n]`, allocated on the sender's heap so the copy has
/// something to gift.
fn sender_list(sender: &mut Process, n: i64) -> AnyValueRef {
    sender
        .heap
        .alloc_list_cons_int(n, AnyValueRef::empty_list())
        .expect("sender list ref")
}

/// Matches any list and writes its whole cell twice as two roots, so both
/// roots alias one cell: a clause that crosses a non-structural boundary
/// can overlap itself this way.
extern "C" fn bind_list_twice(_process: *mut Process, msg: u64, _frame: u64, out: *mut AnyValueRef) -> u32 {
    let msg_ref = AnyValueRef::from_raw_word(msg).expect("msg ref");
    if msg_ref.tag() != ValueKind::LIST || msg_ref.is_empty_list() {
        return 0;
    }
    unsafe {
        *out = msg_ref;
        *out.add(1) = msg_ref;
    }
    1
}

/// Matches a list of two lists and writes the first element of each as a root:
/// two disjoint positions of the message, with the outer cells left behind.
extern "C" fn bind_both_elements(_process: *mut Process, msg: u64, _frame: u64, out: *mut AnyValueRef) -> u32 {
    use crate::ir_runtime::{fz_list_head_ref, fz_list_tail_ref};
    let word = |w: u64| AnyValueRef::from_raw_word(w).expect("ref word");
    let rest = fz_list_tail_ref(msg);
    unsafe {
        *out = word(fz_list_head_ref(msg));
        *out.add(1) = word(fz_list_head_ref(rest));
    }
    1
}

/// Matches the integer 7 and binds nothing.
extern "C" fn match_7_binding_nothing(_process: *mut Process, msg: u64, _frame: u64, _out: *mut AnyValueRef) -> u32 {
    let msg_ref = AnyValueRef::from_raw_word(msg).expect("msg ref");
    u32::from(msg_ref.tag() == ValueKind::INT && msg_ref.load_int().expect("int msg") == 7)
}

fn park_binding_nothing(task: &mut Process) {
    let record = record_of(task, match_7_binding_nothing, 0, None);
    task.delivery.lock().install_park(record);
    task.state = ProcessState::Blocked;
}

fn park_binding_both_elements(task: &mut Process) {
    let record = record_of(task, bind_both_elements, 2, None);
    task.delivery.lock().install_park(record);
    task.state = ProcessState::Blocked;
}

fn park_binding_twice(task: &mut Process) {
    let record = record_of(task, bind_list_twice, 2, None);
    task.delivery.lock().install_park(record);
    task.state = ProcessState::Blocked;
}

fn pending_match(task: &Process) -> Option<(usize, Roots)> {
    task.delivery
        .lock()
        .queued_gifts()
        .find_map(|gift| match &gift.payload {
            GiftPayload::Match { clause_idx, roots } => Some((*clause_idx, roots.clone())),
            GiftPayload::Message(_) => None,
        })
}

fn drain(task: &mut Process) -> Option<(usize, Roots)> {
    let mut delivery = task.delivery.lock();
    drain_in_queue(&mut delivery, &mut task.heap, &mut task.mailbox)
}

#[test]
fn probe_sender_hit_queues_the_match_and_leaves_the_receiver_untouched_until_it_runs() {
    let mut sender = running_task();
    let mut task = fresh_task();
    park_on_42(&mut task, None);
    let receiver_bytes = task.heap.bytes_used();
    let probe = probe_sender(&mut sender, &task, int_ref(42));
    assert_eq!(probe.outcome, ProbeOutcome::Hit);
    assert_eq!(probe.receiver, task.pid);
    assert!(
        task.delivery.lock().park().is_some(),
        "the park record stays until the receiver delivers"
    );
    assert_eq!(
        task.state,
        ProcessState::Blocked,
        "only the scheduling core flips Ready"
    );
    assert!(task.runnable_closure().is_none());
    assert_eq!(
        task.heap.bytes_used(),
        receiver_bytes,
        "a sender never writes the receiver's heap"
    );
    assert!(task.mailbox.is_empty());
    let (clause_idx, bound) = pending_match(&task).expect("the match waits in the in-queue");
    assert_eq!(clause_idx, 0);
    assert_eq!(bound.len(), 1);
    assert!(task.delivery.lock().has_pending_match());
}

#[test]
fn deliver_in_queue_finishes_a_matched_receive_with_the_gifted_values() {
    let mut sender = running_task();
    let mut task = fresh_task();
    park_on_42(&mut task, None);
    probe_sender(&mut sender, &task, int_ref(42));
    deliver_in_queue(&mut task);
    assert!(task.delivery.lock().park().is_none());
    assert!(task.delivery.lock().queued_gifts().next().is_none());
    let runnable = task
        .runnable_closure()
        .expect("the match queued a runnable closure")
        .closure_addr()
        .expect("runnable closure addr");
    unsafe {
        assert_eq!(read((runnable as *const u8).add(8) as *const u64), CLAUSE_CODE as u64);
        let capture_ref =
            AnyValueRef::from_raw_word(any_value::closure_capture_ref_word(runnable, 1)).expect("capture ref");
        assert_eq!(capture_ref.load_int().expect("capture int ref"), 42);
    }
    assert!(task.mailbox.is_empty());
}

#[test]
fn probe_sender_miss_queues_the_message_and_keeps_the_park() {
    let mut sender = running_task();
    let mut task = fresh_task();
    park_on_42(&mut task, None);
    let msg = sender_list(&mut sender, 99);
    let probe = probe_sender(&mut sender, &task, msg);
    assert_eq!(probe.outcome, ProbeOutcome::Miss);
    assert_eq!(probe.gift_bytes, 16, "one cons cell crosses");
    assert_eq!(probe.gift_blocks, 1);
    assert!(task.delivery.lock().park().is_some());
    assert_eq!(task.state, ProcessState::Blocked);
    assert!(task.runnable_closure().is_none());
    assert!(task.mailbox.is_empty(), "the message waits in the in-queue");
    assert_eq!(task.delivery.lock().queued_gifts().count(), 1);
    deliver_in_queue(&mut task);
    assert_eq!(task.mailbox.len(), 1);
    let delivered = task.mailbox.front().expect("delivered");
    let delivered_addr = delivered.list_addr().expect("list");
    assert!(
        !task.heap.contains_heap_addr(delivered_addr),
        "the message waits outside the receiver's heap"
    );
    task.mailbox.take(0, &mut task.heap);
    assert!(
        task.heap.contains_heap_addr(delivered_addr),
        "the receive that takes it brings it into the heap"
    );
    assert!(
        task.delivery.lock().park().is_some(),
        "a miss never decides the receive"
    );
}

#[test]
fn probe_sender_not_parked_queues_the_message_and_returns_miss() {
    let mut sender = running_task();
    let task = fresh_task();
    let probe = probe_sender(&mut sender, &task, int_ref(7));
    assert_eq!(probe.outcome, ProbeOutcome::Miss);
    assert_eq!(task.delivery.lock().queued_gifts().count(), 1);
    assert!(!task.delivery.lock().has_pending_match());
}

/// A clause's roots are disjoint positions of the message, so a hit copies
/// each once and leaves everything between and around them behind.
#[test]
fn a_hit_copies_each_of_a_clauses_disjoint_roots_once() {
    let mut sender = running_task();
    let mut task = fresh_task();
    park_binding_both_elements(&mut task);
    let first = sender_list(&mut sender, 1);
    let second = sender_list(&mut sender, 2);
    let tail = sender
        .heap
        .alloc_list_cons_any(AnyValue::from_ref(second).expect("second"), AnyValueRef::empty_list())
        .expect("outer tail");
    let msg = sender
        .heap
        .alloc_list_cons_any(AnyValue::from_ref(first).expect("first"), tail)
        .expect("outer list");
    let probe = probe_sender(&mut sender, &task, msg);
    assert_eq!(probe.outcome, ProbeOutcome::Hit);
    assert_eq!(probe.gift_roots, 2);
    assert_eq!(probe.gift_bytes, 32, "the two root cells cross; the outer cells stay");
    let (_, roots) = pending_match(&task).expect("match queued");
    assert_eq!(roots.len(), 2);
    assert_ne!(roots[0].raw_word(), roots[1].raw_word());
}

/// A send copies a term the way BEAM does: with no record of what it has
/// copied. Roots that overlap, which a clause can only produce across a
/// non-structural boundary, each arrive as a copy of their own.
#[test]
fn roots_that_overlap_arrive_as_separate_copies() {
    let mut sender = running_task();
    let mut task = fresh_task();
    park_binding_twice(&mut task);
    let msg = sender_list(&mut sender, 5);
    let probe = probe_sender(&mut sender, &task, msg);
    assert_eq!(probe.outcome, ProbeOutcome::Hit);
    assert_eq!(probe.gift_bytes, 32, "two roots on one cell copy it twice");
    let (_, roots) = pending_match(&task).expect("match queued");
    assert_eq!(roots.len(), 2);
    assert_ne!(
        roots[0].raw_word(),
        roots[1].raw_word(),
        "each root points at a copy of its own"
    );
}

#[test]
fn a_hit_that_binds_nothing_gifts_nothing() {
    pool_drain_for_test();
    let mut sender = running_task();
    let mut task = fresh_task();
    park_binding_nothing(&mut task);
    let cached_before = pool_total_cached_blocks();
    let probe = probe_sender(&mut sender, &task, int_ref(7));
    assert_eq!(probe.outcome, ProbeOutcome::Hit);
    assert_eq!(
        (probe.gift_bytes, probe.gift_blocks),
        (0, 0),
        "no window opens for an empty binding"
    );
    assert_eq!(pool_total_cached_blocks(), cached_before, "no block was taken");
    let (clause_idx, bound) = pending_match(&task).expect("the match waits in the in-queue");
    assert_eq!((clause_idx, bound.len()), (0, 0));
    deliver_in_queue(&mut task);
    assert!(task.delivery.lock().park().is_none());
    assert!(task.runnable_closure().is_some());
    drop(task);
    drop(sender);
    pool_drain_for_test();
}

#[test]
fn a_second_sender_does_not_probe_a_receive_that_is_already_matched() {
    let mut first = running_task();
    let mut second = running_task();
    let mut task = fresh_task();
    park_on_42(&mut task, None);
    assert_eq!(probe_sender(&mut first, &task, int_ref(42)).outcome, ProbeOutcome::Hit);
    assert_eq!(
        probe_sender(&mut second, &task, int_ref(42)).outcome,
        ProbeOutcome::Miss,
        "the receive is decided; a later 42 is an ordinary arrival"
    );
    deliver_in_queue(&mut task);
    assert!(task.delivery.lock().park().is_none());
    assert_eq!(mailbox_ints(&task), vec![42], "the second 42 waits in the mailbox");
}

#[test]
#[should_panic(expected = "one match per parked receive")]
fn a_second_match_for_one_parked_receive_is_refused() {
    let mut sender = running_task();
    let mut task = fresh_task();
    park_on_42(&mut task, None);
    probe_sender(&mut sender, &task, int_ref(42));
    let (segment, roots) = gift_copy(&mut sender.heap, &[int_ref(42)]);
    task.delivery.lock().push_gift(Gift {
        segment,
        payload: GiftPayload::Match { clause_idx: 0, roots },
    });
}

#[test]
fn drain_in_queue_keeps_messages_waiting_in_arrival_order() {
    let mut sender = running_task();
    let mut task = fresh_task();
    for n in [1, 2, 3] {
        let msg = sender_list(&mut sender, n);
        probe_sender(&mut sender, &task, msg);
    }
    assert!(drain(&mut task).is_none());
    assert!(task.delivery.lock().queued_gifts().next().is_none());
    let heads: Vec<i64> = task
        .mailbox
        .messages()
        .map(|m| task.heap.read_list_head_ref(m).unwrap().load_int().unwrap())
        .collect();
    assert_eq!(heads, vec![1, 2, 3]);
    for m in task.mailbox.messages() {
        assert!(
            !task.heap.contains_heap_addr(m.list_addr().expect("list")),
            "a drained message waits outside the receiver's heap"
        );
    }
}

#[test]
fn a_dropped_receiver_returns_its_pending_gifts_to_the_pool_and_releases_their_binaries() {
    pool_drain_for_test();
    let witness = SharedBinHandle::from_bytes(&[0x55; 16]);
    let mut sender = running_task();
    let task = Box::new(fresh_task());
    let binary = alloc_buffer_view(
        &mut sender.heap,
        witness.clone(),
        witness.bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    );
    let binary_ref =
        AnyValueRef::from_heap_object(ValueKind::BINVIEW, binary.as_raw() as *const u8).expect("binview ref");
    probe_sender(&mut sender, &task, binary_ref);
    let msg = sender_list(&mut sender, 1);
    probe_sender(&mut sender, &task, msg);
    assert_eq!(task.delivery.lock().queued_gifts().count(), 2);
    assert_eq!(
        shared_refs(&witness),
        3,
        "the sender's stub and the gifted copy each hold the binary"
    );
    let cached_before = pool_total_cached_blocks();
    drop(task);
    assert_eq!(
        pool_total_cached_blocks(),
        cached_before + 3,
        "the receiver's own block and both gift blocks are back in the pool"
    );
    assert_eq!(shared_refs(&witness), 2, "the dropped gift released its reference");
    drop(sender);
    pool_drain_for_test();
}

#[test]
fn self_send_copies_the_message_into_the_mailbox_and_leaves_the_senders_heap_as_it_was() {
    let mut task = running_task();
    let msg = sender_list(&mut task, 7);
    let live_before = task.heap.live_count();
    let young_before = task.heap.young_bytes();
    self_send(&mut task, msg);
    assert_eq!(
        task.heap.live_count(),
        live_before,
        "the copy is a gift outside the sender's heap"
    );
    assert_eq!(task.heap.young_bytes(), young_before);
    assert_eq!(task.mailbox.len(), 1);
    let queued = task.mailbox.messages().last().expect("pushed");
    assert_ne!(
        queued.list_addr().expect("list"),
        msg.list_addr().expect("list"),
        "the mailbox holds a copy, not the reference the sender passed"
    );
    assert_eq!(task.heap.read_list_head_ref(queued).unwrap().load_int().unwrap(), 7);
    assert_eq!(
        task.state,
        ProcessState::Running,
        "delivery to self changes no scheduling state"
    );
}

#[test]
fn reach_receive_with_an_empty_mailbox_parks() {
    let mut task = running_task();
    let record = record_on_42(&mut task, None);
    assert_eq!(reach_receive(&mut task, record), ReceiveStep::Parked);
    assert!(task.delivery.lock().park().is_some());
    assert_eq!(task.state, ProcessState::Blocked);
}

#[test]
fn reach_receive_hit_continues_with_the_clause_and_splices_the_message_out() {
    let mut task = running_task();
    task.mailbox.push(int_ref(1), GiftSegment::empty());
    task.mailbox.push(int_ref(2), GiftSegment::empty());
    task.mailbox.push(int_ref(42), GiftSegment::empty());
    task.mailbox.push(int_ref(3), GiftSegment::empty());
    let record = record_on_42(&mut task, None);
    let ReceiveStep::Continue(cont) = reach_receive(&mut task, record) else {
        panic!("a matching message in the mailbox must continue the receive");
    };
    let cont = cont.closure_addr().expect("continuation closure addr");
    unsafe {
        assert_eq!(read(cont.add(8) as *const u64), CLAUSE_CODE as u64);
        let capture_ref =
            AnyValueRef::from_raw_word(any_value::closure_capture_ref_word(cont, 1)).expect("capture ref");
        assert_eq!(capture_ref.load_int().expect("capture int ref"), 42);
    }
    assert!(task.delivery.lock().park().is_none());
    assert_eq!(task.state, ProcessState::Running);
    assert_eq!(mailbox_ints(&task), vec![1, 2, 3]);
}

#[test]
fn reach_receive_takes_the_oldest_matching_message() {
    let mut task = running_task();
    task.mailbox.push(int_ref(42), GiftSegment::empty());
    task.mailbox.push(int_ref(42), GiftSegment::empty());
    task.mailbox.push(int_ref(7), GiftSegment::empty());
    let record = record_on_42(&mut task, None);
    assert!(matches!(reach_receive(&mut task, record), ReceiveStep::Continue(_)));
    assert_eq!(mailbox_ints(&task), vec![42, 7]);
}

#[test]
fn reach_receive_miss_parks_blocked_and_keeps_the_mailbox() {
    let mut task = running_task();
    task.mailbox.push(int_ref(1), GiftSegment::empty());
    task.mailbox.push(int_ref(2), GiftSegment::empty());
    let record = record_on_42(&mut task, None);
    assert_eq!(reach_receive(&mut task, record), ReceiveStep::Parked);
    assert_eq!(task.state, ProcessState::Blocked);
    assert!(task.delivery.lock().park().is_some());
    assert_eq!(mailbox_ints(&task), vec![1, 2]);
}

#[test]
fn reach_receive_after_zero_miss_continues_with_the_after_body() {
    let mut task = running_task();
    task.mailbox.push(int_ref(1), GiftSegment::empty());
    let mut record = record_on_42(&mut task, None);
    record.after_deadline_ms = Some(0);
    let ReceiveStep::Continue(after) = reach_receive(&mut task, record) else {
        panic!("an `after 0` receive that misses must continue");
    };
    assert_eq!(code_of(after), AFTER_CODE);
    assert!(task.delivery.lock().park().is_none());
    assert_eq!(task.state, ProcessState::Running);
    assert_eq!(mailbox_ints(&task), vec![1]);
}

#[test]
fn reach_receive_after_zero_hit_prefers_the_clause_to_the_after_body() {
    let mut task = running_task();
    task.mailbox.push(int_ref(42), GiftSegment::empty());
    let mut record = record_on_42(&mut task, None);
    record.after_deadline_ms = Some(0);
    let ReceiveStep::Continue(cont) = reach_receive(&mut task, record) else {
        panic!("a matching message must continue the receive");
    };
    assert_eq!(code_of(cont), CLAUSE_CODE);
    assert!(task.mailbox.is_empty());
}

#[test]
fn reach_receive_never_leaves_the_process_ready() {
    for messages in [vec![], vec![1], vec![42], vec![1, 42]] {
        let mut task = running_task();
        for m in &messages {
            task.mailbox.push(int_ref(*m), GiftSegment::empty());
        }
        let record = record_on_42(&mut task, None);
        reach_receive(&mut task, record);
        assert_ne!(task.state, ProcessState::Ready, "mailbox {messages:?}");
    }
}

thread_local! {
    /// The process whose delivery lock `match_42_noting_the_lock` watches.
    static WATCHED: std::cell::Cell<*const Process> = const { std::cell::Cell::new(std::ptr::null()) };
    /// One entry per matcher run: was the watched delivery lock held?
    static LOCK_HELD_AT_MATCH: RefCell<Vec<bool>> = const { RefCell::new(Vec::new()) };
}

/// `match_42`, noting whether the watched process's delivery lock was held
/// while the matcher ran.
extern "C" fn match_42_noting_the_lock(process: *mut Process, msg: u64, frame: u64, out: *mut AnyValueRef) -> u32 {
    let watched = WATCHED.with(std::cell::Cell::get);
    let held = unsafe { &*watched }.delivery.try_lock().is_none();
    LOCK_HELD_AT_MATCH.with(|notes| notes.borrow_mut().push(held));
    match_42(process, msg, frame, out)
}

fn watch_matches_on(task: &mut Process) -> ParkRecord {
    WATCHED.with(|watched| watched.set(task as *const Process));
    LOCK_HELD_AT_MATCH.with(|notes| notes.borrow_mut().clear());
    record_of(task, match_42_noting_the_lock, 1, None)
}

fn matcher_runs_and_whether_the_lock_was_held() -> Vec<bool> {
    LOCK_HELD_AT_MATCH.with(|notes| notes.borrow().clone())
}

const TIMER: TimerId = 9;

#[test]
fn a_hit_then_the_timer_decides_the_receive_once_and_the_timer_finds_it_stale() {
    let mut sender = running_task();
    let mut task = fresh_task();
    park_on_42(&mut task, Some(TIMER));

    let probe = probe_sender(&mut sender, &task, int_ref(42));
    assert_eq!(probe.outcome, ProbeOutcome::Hit);
    assert!(
        !fire_after_timer(&mut task, TIMER),
        "the hit cancelled the timer, so its firing is stale"
    );
    assert!(task.runnable_closure().is_none(), "the stale timer woke nothing");

    deliver_in_queue(&mut task);
    assert!(task.runnable_closure().is_some(), "the hit's delivery is the one wake");
    assert!(task.delivery.lock().park().is_none());
}

#[test]
fn the_timer_then_a_sender_decides_the_receive_once_and_the_sender_delivers_a_miss() {
    let mut sender = running_task();
    let mut task = fresh_task();
    let record = watch_matches_on(&mut task);
    task.delivery.lock().install_park(ParkRecord {
        after_timer_id: Some(TIMER),
        ..record
    });

    assert!(fire_after_timer(&mut task, TIMER), "the timer took the park");
    assert_eq!(
        task.runnable_closure().map(code_of),
        Some(AFTER_CODE),
        "the timer woke the after body"
    );

    let probe = probe_sender(&mut sender, &task, int_ref(42));
    assert_eq!(
        probe.outcome,
        ProbeOutcome::Miss,
        "the park is gone, so the arrival is a plain miss"
    );
    assert_eq!(probe.reductions, 0);
    assert!(
        matcher_runs_and_whether_the_lock_was_held().is_empty(),
        "no park, no matcher run"
    );
    assert!(!task.delivery.lock().has_pending_match());
    deliver_in_queue(&mut task);
    assert_eq!(mailbox_ints(&task), vec![42], "the message waits for a later receive");
    assert_eq!(
        task.runnable_closure().map(code_of),
        Some(AFTER_CODE),
        "the sender woke nothing"
    );
}

#[test]
fn a_second_timer_fire_for_a_decided_receive_is_stale() {
    let mut task = fresh_task();
    park_on_42(&mut task, Some(TIMER));
    assert!(fire_after_timer(&mut task, TIMER));
    assert!(!fire_after_timer(&mut task, TIMER), "the park is already taken");
}

#[test]
fn a_matcher_run_by_a_sender_holds_the_receivers_delivery_lock() {
    let mut sender = running_task();
    let mut task = fresh_task();
    let record = watch_matches_on(&mut task);
    task.delivery.lock().install_park(record);

    probe_sender(&mut sender, &task, int_ref(42));

    assert_eq!(
        matcher_runs_and_whether_the_lock_was_held(),
        vec![true],
        "the sender decides the receive with the lock held, read to queue"
    );
    assert!(
        task.delivery.try_lock().is_some(),
        "the lock is released after the probe"
    );
}

#[test]
fn a_delivery_waits_out_the_receive_entry_and_is_probed_against_the_installed_park() {
    let mut sender = running_task();
    let mut task = running_task();
    task.mailbox.push(int_ref(1), GiftSegment::empty());
    task.mailbox.push(int_ref(2), GiftSegment::empty());
    let record = watch_matches_on(&mut task);

    assert_eq!(reach_receive(&mut task, record), ReceiveStep::Parked);
    assert_eq!(
        matcher_runs_and_whether_the_lock_was_held(),
        vec![true, true],
        "the delivery path cannot take the lock while the walk is running"
    );
    assert!(
        task.delivery.try_lock().is_some(),
        "the entry released the lock with the park installed"
    );

    let probe = probe_sender(&mut sender, &task, int_ref(42));
    assert_eq!(
        probe.outcome,
        ProbeOutcome::Hit,
        "the delivery is probed against the installed park"
    );
    assert_eq!(matcher_runs_and_whether_the_lock_was_held(), vec![true, true, true]);
}

/// Arming the after-timer happens between the mailbox walk and the park
/// install. The hook notes whether the delivery lock is held at that point.
extern "C" fn note_the_lock_while_arming_the_timer(_scheduler: *mut (), _pid: u32, _after_ms: u64) -> u64 {
    let watched = WATCHED.with(std::cell::Cell::get);
    let held = unsafe { &*watched }.delivery.try_lock().is_none();
    LOCK_HELD_AT_MATCH.with(|notes| notes.borrow_mut().push(held));
    TIMER
}

#[test]
fn the_lock_stays_held_from_the_end_of_the_walk_to_the_park_install() {
    let mut task = running_task();
    task.mailbox.push(int_ref(1), GiftSegment::empty());
    let mut record = watch_matches_on(&mut task);
    record.after_deadline_ms = Some(10);
    let mut ctx = ExecCtx {
        timer_schedule: Some(note_the_lock_while_arming_the_timer),
        ..ExecCtx::empty()
    };
    task.ctx = &mut ctx;

    assert_eq!(reach_receive(&mut task, record), ReceiveStep::Parked);

    assert_eq!(
        matcher_runs_and_whether_the_lock_was_held(),
        vec![true, true],
        "the walk's one matcher run and the timer arming, which sits between walk and install, both hold the lock"
    );
    assert_eq!(task.delivery.lock().park().and_then(|p| p.after_timer_id), Some(TIMER));
    task.ctx = std::ptr::null_mut();
}

#[test]
fn a_receiver_dropped_with_queued_gifts_leaves_no_block_outstanding() {
    let outstanding_before = pool_outstanding_blocks();
    {
        let mut sender = running_task();
        let receiver = fresh_task();
        probe_sender(&mut sender, &receiver, int_ref(1));
        probe_sender(&mut sender, &receiver, int_ref(2));
        assert!(
            pool_outstanding_blocks() > outstanding_before,
            "the heaps and the gifts hold blocks while they live"
        );
    }
    assert_eq!(pool_outstanding_blocks(), outstanding_before);
}

/// A binary sent to another process, then appended to by the sender, leaves
/// the receiver's bytes intact: the send froze the buffer, so the sender's
/// append went to a new one.
#[test]
fn a_sender_appending_to_a_binary_it_sent_leaves_the_receivers_bytes_intact() {
    let mut sender = running_task();
    let mut receiver = fresh_task();
    let sent = sender.heap.alloc_bitstring(&[b'a'; 100], 100 * 8);
    let sent_view = unsafe {
        let word = sent.heap_object_word().unwrap();
        crate::bits::BinView::from_raw(crate::any_value::heap_word_addr(word))
    };
    let grown = unsafe {
        let ptr = sent_view.bytes_ptr();
        // A concatenation gives a buffer room; the first call allocates it.
        sender
            .heap
            .alloc_concatenation(std::slice::from_raw_parts(ptr, 100), Some(sent_view), b"b")
    };
    let grown_ref = grown.ref_word();
    let (segment, delivered) = gift_copy(&mut sender.heap, &[grown_ref]);
    receiver.heap.graft(segment);
    let received = delivered[0];

    let appended = unsafe {
        let view = crate::bits::BinView::from_raw(grown.heap_addr().unwrap());
        sender
            .heap
            .alloc_concatenation(std::slice::from_raw_parts(view.bytes_ptr(), 101), Some(view), b"XYZ")
    };

    let received_bytes = unsafe {
        let word = received.heap_object_word().unwrap();
        std::slice::from_raw_parts(
            crate::bits::bitstring_byte_ptr(word),
            crate::bits::bitstring_bit_len(word) as usize / 8,
        )
    };
    let mut expected = vec![b'a'; 100];
    expected.push(b'b');
    assert_eq!(received_bytes, expected.as_slice());
    let appended_addr = appended.heap_addr().unwrap();
    assert_ne!(
        unsafe { crate::bits::BinView::from_raw(appended_addr) }.bytes_ptr(),
        received_bytes.as_ptr(),
        "the sender's append went to a new buffer"
    );
}
