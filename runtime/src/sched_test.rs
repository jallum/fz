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
    let bits = task.heap.alloc_closure_slots(0, 1, 0);
    let p = any_value::closure_addr_from_tagged(bits).expect("template closure ptr");
    unsafe {
        write(p.add(8) as *mut u64, stub as u64);
        any_value::closure_capture_set(p, 0, AnyValue::null());
    }
    bits as *mut u8
}

fn park_on_42(task: &mut Process, timer: Option<TimerId>) {
    let template = template_closure(task, 0xdead_beef);
    task.wait = Some(Box::new(ParkRecord {
        matcher_fn: match_42,
        pinned: vec![],
        clause_bodies: vec![template],
        clause_bound_counts: vec![1],
        bound_arity: 1,
        after_deadline_ms: timer.map(|_| 0),
        after_cont: 0xcafe_babe as *mut u8,
        after_timer_id: timer,
    }));
    task.state = ProcessState::Blocked;
}

#[test]
fn probe_sender_hit_sets_runnable_and_flips_ready() {
    let mut task = fresh_task();
    park_on_42(&mut task, None);
    assert_eq!(probe_sender(&mut task, int_ref(42)), ProbeOutcome::Hit);
    assert!(task.wait.is_none());
    assert_eq!(task.state, ProcessState::Ready);
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
fn initial_scan_not_applicable_without_park() {
    let mut task = fresh_task();
    task.mailbox.push_back(int_ref(42));
    assert_eq!(initial_scan(&mut task), ScanOutcome::NotApplicable);
    assert_eq!(task.mailbox.len(), 1);
}

#[test]
fn initial_scan_not_applicable_with_empty_mailbox() {
    let mut task = fresh_task();
    park_on_42(&mut task, None);
    assert_eq!(initial_scan(&mut task), ScanOutcome::NotApplicable);
    assert!(task.wait.is_some());
}

#[test]
fn initial_scan_hit_splices_and_preserves_prefix_order() {
    let mut task = fresh_task();
    park_on_42(&mut task, None);
    task.mailbox.push_back(int_ref(1));
    task.mailbox.push_back(int_ref(2));
    task.mailbox.push_back(int_ref(42));
    task.mailbox.push_back(int_ref(3));
    assert_eq!(initial_scan(&mut task), ScanOutcome::Hit);
    assert!(task.wait.is_none());
    assert!(!task.runnable_ptr().is_null());
    // 1, 2, 3 stay in arrival order; 42 was spliced out.
    let mb: Vec<i64> = task.mailbox.iter().map(|v| v.load_int().unwrap()).collect();
    assert_eq!(mb, vec![1, 2, 3]);
}

#[test]
fn initial_scan_miss_blocks_and_preserves_mailbox() {
    let mut task = fresh_task();
    park_on_42(&mut task, None);
    task.mailbox.push_back(int_ref(1));
    task.mailbox.push_back(int_ref(2));
    assert_eq!(initial_scan(&mut task), ScanOutcome::Miss);
    assert_eq!(task.state, ProcessState::Blocked);
    assert!(task.wait.is_some());
    let mb: Vec<i64> = task.mailbox.iter().map(|v| v.load_int().unwrap()).collect();
    assert_eq!(mb, vec![1, 2]);
}

#[test]
fn fire_after_timer_matches_id_and_transitions() {
    let mut task = fresh_task();
    park_on_42(&mut task, Some(7));
    assert!(fire_after_timer(&mut task, 7));
    assert!(task.wait.is_none());
    assert_eq!(task.state, ProcessState::Ready);
    assert_eq!(task.runnable_ptr() as usize, 0xcafe_babe);
}

#[test]
fn fire_after_timer_stale_id_no_transition() {
    let mut task = fresh_task();
    park_on_42(&mut task, Some(7));
    assert!(!fire_after_timer(&mut task, 99));
    assert!(task.wait.is_some());
    assert_eq!(task.state, ProcessState::Blocked);
}

#[test]
fn fire_after_timer_unparked_no_transition() {
    let mut task = fresh_task();
    assert!(!fire_after_timer(&mut task, 7));
}
