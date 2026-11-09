use super::*;
use crate::any_value::AnyValueRef;
use crate::any_value::ValueKind;
use crate::exec_ctx::ExecCtx;
use crate::heap::{SchemaRegistry, pool_drain_for_test, pool_outstanding_blocks, pool_total_cached_blocks};
use crate::park::ParkRecord;
use crate::procbin::{SharedBinHandle, alloc_procbin};
use crate::sync::Ordering;
use std::cell::RefCell;
use std::ptr::{read, write};
use std::rc::Rc;

extern "C" fn match_42(_process: *mut Process, msg: u64, _pinned: *const AnyValueRef, out: *mut AnyValueRef) -> u32 {
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

fn template_closure(task: &mut Process, stub: usize) -> *mut u8 {
    let bits = task
        .heap
        .alloc_closure_slots(crate::any_value::ClosureDenotationId::user(0), 0, 1, 0);
    let p = any_value::closure_addr_from_tagged(bits).expect("template closure ptr");
    unsafe {
        write(p.add(8) as *mut u64, stub as u64);
        any_value::closure_capture_set(p, 0, AnyValue::null());
    }
    bits as *mut u8
}

fn record_on_42(task: &mut Process, timer: Option<TimerId>) -> ParkRecord {
    let template = template_closure(task, 0xdead_beef);
    ParkRecord {
        matcher_fn: match_42,
        pinned: vec![],
        clause_bodies: vec![template],
        clause_bound_counts: vec![1],
        bound_arity: 1,
        after_deadline_ms: timer.map(|_| 0),
        after_cont: 0xcafe_babe as *mut u8,
        after_timer_id: timer,
    }
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
    task.mailbox.iter().map(|v| v.load_int().unwrap()).collect()
}

/// A sender's list `[n]`, allocated on the sender's heap so the copy has
/// something to gift.
fn sender_list(sender: &mut Process, n: i64) -> AnyValueRef {
    sender
        .heap
        .alloc_list_cons_int(n, AnyValueRef::empty_list())
        .expect("sender list ref")
}

/// Matches any one-element list and binds the whole list twice, so both
/// bound values alias one cell.
extern "C" fn bind_list_twice(
    _process: *mut Process,
    msg: u64,
    _pinned: *const AnyValueRef,
    out: *mut AnyValueRef,
) -> u32 {
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

/// Matches the integer 7 and binds nothing.
extern "C" fn match_7_binding_nothing(
    _process: *mut Process,
    msg: u64,
    _pinned: *const AnyValueRef,
    _out: *mut AnyValueRef,
) -> u32 {
    let msg_ref = AnyValueRef::from_raw_word(msg).expect("msg ref");
    u32::from(msg_ref.tag() == ValueKind::INT && msg_ref.load_int().expect("int msg") == 7)
}

fn park_binding_nothing(task: &mut Process) {
    let template = template_closure(task, 0xdead_beef);
    task.delivery.lock().install_park(ParkRecord {
        matcher_fn: match_7_binding_nothing,
        pinned: vec![],
        clause_bodies: vec![template],
        clause_bound_counts: vec![0],
        bound_arity: 0,
        after_deadline_ms: None,
        after_cont: 0xcafe_babe as *mut u8,
        after_timer_id: None,
    });
    task.state = ProcessState::Blocked;
}

fn park_binding_twice(task: &mut Process) {
    let template = template_closure(task, 0xdead_beef);
    task.delivery.lock().install_park(ParkRecord {
        matcher_fn: bind_list_twice,
        pinned: vec![],
        clause_bodies: vec![template],
        clause_bound_counts: vec![2],
        bound_arity: 2,
        after_deadline_ms: None,
        after_cont: 0xcafe_babe as *mut u8,
        after_timer_id: None,
    });
    task.state = ProcessState::Blocked;
}

fn pending_match(task: &Process) -> Option<(usize, Vec<AnyValueRef>)> {
    task.delivery
        .lock()
        .queued_gifts()
        .find_map(|gift| match &gift.payload {
            GiftPayload::Match { clause_idx, bound_vals } => Some((*clause_idx, bound_vals.clone())),
            GiftPayload::Message(_) => None,
        })
}

fn drain(task: &mut Process) -> Option<(usize, Vec<AnyValueRef>)> {
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
    assert!(task.runnable_ptr().is_null());
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
    let runnable = task.runnable_ptr();
    assert!(!runnable.is_null());
    unsafe {
        assert_eq!(read((runnable as *const u8).add(8) as *const u64), 0xdead_beef);
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
    assert!(task.runnable_ptr().is_null());
    assert!(task.mailbox.is_empty(), "the message waits in the in-queue");
    assert_eq!(task.delivery.lock().queued_gifts().count(), 1);
    deliver_in_queue(&mut task);
    assert_eq!(task.mailbox.len(), 1);
    let delivered = task.mailbox[0];
    assert!(task.heap.contains_heap_addr(delivered.list_addr().expect("list")));
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

#[test]
fn bound_values_that_share_structure_keep_sharing_through_one_forwarding_map() {
    let mut sender = running_task();
    let mut task = fresh_task();
    park_binding_twice(&mut task);
    let msg = sender_list(&mut sender, 5);
    let probe = probe_sender(&mut sender, &task, msg);
    assert_eq!(probe.outcome, ProbeOutcome::Hit);
    assert_eq!(probe.gift_bytes, 16, "two bindings of one cell copy it once");
    let (_, bound) = pending_match(&task).expect("match queued");
    assert_eq!(bound.len(), 2);
    assert_eq!(
        bound[0].raw_word(),
        bound[1].raw_word(),
        "both bindings point at the one copy"
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
    assert!(!task.runnable_ptr().is_null());
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
    let (segment, bound_vals) = gift_copy(&mut sender.heap, &[int_ref(42)]);
    task.delivery.lock().push_gift(Gift {
        segment,
        payload: GiftPayload::Match {
            clause_idx: 0,
            bound_vals,
        },
    });
}

#[test]
fn drain_in_queue_grafts_in_arrival_order() {
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
        .iter()
        .map(|m| task.heap.read_list_head_ref(*m).unwrap().load_int().unwrap())
        .collect();
    assert_eq!(heads, vec![1, 2, 3]);
    for m in &task.mailbox {
        assert!(
            task.heap.contains_heap_addr(m.list_addr().expect("list")),
            "grafted cells are the receiver's"
        );
    }
}

#[test]
fn a_dropped_receiver_returns_its_pending_gifts_to_the_pool_and_releases_their_binaries() {
    pool_drain_for_test();
    let witness = SharedBinHandle::from_bytes(&[0x55; 16], 128);
    let mut sender = running_task();
    let task = Box::new(fresh_task());
    let binary = alloc_procbin(&mut sender.heap, witness.clone(), 0);
    let binary_ref =
        AnyValueRef::from_heap_object(ValueKind::PROCBIN, binary.as_raw() as *const u8).expect("procbin ref");
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
        cached_before + 1,
        "the receiver's own block is back in the pool; both exact gift blocks went to the system allocator"
    );
    assert_eq!(shared_refs(&witness), 2, "the dropped gift released its reference");
    drop(sender);
    pool_drain_for_test();
}

#[test]
fn self_send_pushes_the_senders_own_reference_and_allocates_nothing() {
    let mut task = running_task();
    let msg = int_ref(7);
    let live_before = task.heap.live_count();
    self_send(&mut task, msg);
    assert_eq!(
        task.heap.live_count(),
        live_before,
        "a self-send allocates nothing on the sender's heap"
    );
    assert_eq!(task.mailbox.len(), 1);
    assert_eq!(
        task.mailbox.back().expect("pushed").raw_word(),
        msg.raw_word(),
        "the mailbox holds the very reference the sender passed"
    );
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
    task.mailbox.push_back(int_ref(1));
    task.mailbox.push_back(int_ref(2));
    task.mailbox.push_back(int_ref(42));
    task.mailbox.push_back(int_ref(3));
    let record = record_on_42(&mut task, None);
    let ReceiveStep::Continue(cont) = reach_receive(&mut task, record) else {
        panic!("a matching message in the mailbox must continue the receive");
    };
    unsafe {
        assert_eq!(read(cont.add(8) as *const u64), 0xdead_beef);
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
    task.mailbox.push_back(int_ref(42));
    task.mailbox.push_back(int_ref(42));
    task.mailbox.push_back(int_ref(7));
    let record = record_on_42(&mut task, None);
    assert!(matches!(reach_receive(&mut task, record), ReceiveStep::Continue(_)));
    assert_eq!(mailbox_ints(&task), vec![42, 7]);
}

#[test]
fn reach_receive_miss_parks_blocked_and_keeps_the_mailbox() {
    let mut task = running_task();
    task.mailbox.push_back(int_ref(1));
    task.mailbox.push_back(int_ref(2));
    let record = record_on_42(&mut task, None);
    assert_eq!(reach_receive(&mut task, record), ReceiveStep::Parked);
    assert_eq!(task.state, ProcessState::Blocked);
    assert!(task.delivery.lock().park().is_some());
    assert_eq!(mailbox_ints(&task), vec![1, 2]);
}

#[test]
fn reach_receive_after_zero_miss_continues_with_the_after_body() {
    let mut task = running_task();
    task.mailbox.push_back(int_ref(1));
    let mut record = record_on_42(&mut task, None);
    record.after_deadline_ms = Some(0);
    assert_eq!(
        reach_receive(&mut task, record),
        ReceiveStep::Continue(0xcafe_babe as *mut u8)
    );
    assert!(task.delivery.lock().park().is_none());
    assert_eq!(task.state, ProcessState::Running);
    assert_eq!(mailbox_ints(&task), vec![1]);
}

#[test]
fn reach_receive_after_zero_hit_prefers_the_clause_to_the_after_body() {
    let mut task = running_task();
    task.mailbox.push_back(int_ref(42));
    let mut record = record_on_42(&mut task, None);
    record.after_deadline_ms = Some(0);
    let ReceiveStep::Continue(cont) = reach_receive(&mut task, record) else {
        panic!("a matching message must continue the receive");
    };
    assert_ne!(cont, 0xcafe_babe as *mut u8);
    assert!(task.mailbox.is_empty());
}

#[test]
fn reach_receive_never_leaves_the_process_ready() {
    for messages in [vec![], vec![1], vec![42], vec![1, 42]] {
        let mut task = running_task();
        for m in &messages {
            task.mailbox.push_back(int_ref(*m));
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
extern "C" fn match_42_noting_the_lock(
    process: *mut Process,
    msg: u64,
    pinned: *const AnyValueRef,
    out: *mut AnyValueRef,
) -> u32 {
    let watched = WATCHED.with(std::cell::Cell::get);
    let held = unsafe { &*watched }.delivery.try_lock().is_none();
    LOCK_HELD_AT_MATCH.with(|notes| notes.borrow_mut().push(held));
    match_42(process, msg, pinned, out)
}

fn watch_matches_on(task: &mut Process) -> ParkRecord {
    WATCHED.with(|watched| watched.set(task as *const Process));
    LOCK_HELD_AT_MATCH.with(|notes| notes.borrow_mut().clear());
    let mut record = record_on_42(task, None);
    record.matcher_fn = match_42_noting_the_lock;
    record
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
    assert!(task.runnable_ptr().is_null(), "the stale timer woke nothing");

    deliver_in_queue(&mut task);
    assert!(!task.runnable_ptr().is_null(), "the hit's delivery is the one wake");
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
        task.runnable_ptr(),
        0xcafe_babe as *mut u8,
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
    assert_eq!(task.runnable_ptr(), 0xcafe_babe as *mut u8, "the sender woke nothing");
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
    task.mailbox.push_back(int_ref(1));
    task.mailbox.push_back(int_ref(2));
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
    task.mailbox.push_back(int_ref(1));
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
