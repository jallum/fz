use super::*;
use crate::any_value::AnyValueRef;
use crate::any_value::ValueKind;
use crate::heap::SchemaRegistry;
use crate::park::ParkRecord;
use std::cell::RefCell;
use std::ptr::{read, write};
use std::rc::Rc;

extern "C" fn match_42(_process: *mut Process, msg: u64, _pinned: *const AnyValueRef, out: *mut AnyValueRef) -> u32 {
    let msg_ref = AnyValueRef::from_raw_word(msg).expect("msg ref");
    if msg_ref.load_int().expect("int msg") == 42 {
        unsafe {
            *out = msg_ref;
        }
        1
    } else {
        0
    }
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
    task.wait = Some(Box::new(record));
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

#[test]
fn probe_sender_hit_sets_runnable_and_leaves_the_state_to_the_core() {
    let mut task = fresh_task();
    park_on_42(&mut task, None);
    assert_eq!(probe_sender(&mut task, int_ref(42)), ProbeOutcome::Hit);
    assert!(task.wait.is_none());
    assert_eq!(
        task.state,
        ProcessState::Blocked,
        "only the scheduling core flips Ready"
    );
    let runnable = task.runnable_ptr();
    assert!(!runnable.is_null());
    unsafe {
        assert_eq!(read((runnable as *const u8).add(8) as *const u64), 0xdead_beef);
        let cont_addr = runnable;
        let capture_ref =
            AnyValueRef::from_raw_word(any_value::closure_capture_ref_word(cont_addr, 1)).expect("capture ref");
        assert_eq!(capture_ref.load_int().expect("capture int ref"), 42);
    }
    assert!(task.mailbox.is_empty());
}

#[test]
fn probe_sender_miss_pushes_mailbox_keeps_park() {
    let mut task = fresh_task();
    park_on_42(&mut task, None);
    assert_eq!(probe_sender(&mut task, int_ref(99)), ProbeOutcome::Miss);
    assert!(task.wait.is_some());
    assert_eq!(task.state, ProcessState::Blocked);
    assert!(task.runnable_ptr().is_null());
    assert_eq!(task.mailbox.len(), 1);
}

#[test]
fn probe_sender_not_parked_pushes_mailbox_returns_miss() {
    let mut task = fresh_task();
    assert_eq!(probe_sender(&mut task, int_ref(7)), ProbeOutcome::Miss);
    assert_eq!(task.mailbox.len(), 1);
}

#[test]
fn reach_receive_with_an_empty_mailbox_parks() {
    let mut task = running_task();
    let record = record_on_42(&mut task, None);
    assert_eq!(reach_receive(&mut task, record), ReceiveStep::Parked);
    assert!(task.wait.is_some());
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
    assert!(task.wait.is_none());
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
    assert!(task.wait.is_some());
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
    assert!(task.wait.is_none());
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
