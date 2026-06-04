use super::*;
use crate::any_value::ValueKind;
use std::ptr::null_mut;

static INT_42: u64 = 42;
static INT_99: u64 = 99;
static INT_100: u64 = 100;
static INT_123: u64 = 123;

fn int_ref(slot: &'static u64) -> AnyValueRef {
    AnyValueRef::from_scalar_slot(ValueKind::INT, slot).expect("int ref")
}

/// A deterministic mock matcher used by the runtime tests. Layout:
///   pinned[0]: expected message value.
///   out[0]: matched int value.
/// Returns 1 if `msg == pinned[0]`, else 0.
extern "C" fn mock_eq_matcher(
    _process: *mut Process,
    msg: u64,
    pinned: *const AnyValueRef,
    out: *mut AnyValueRef,
) -> u32 {
    let want = unsafe { *pinned };
    if msg == want.raw_word() {
        unsafe {
            *out = AnyValueRef::from_raw_word(msg).expect("msg ref");
        }
        1
    } else {
        0
    }
}

#[test]
fn park_record_holds_matcher_and_pinned() {
    let p = ParkRecord {
        matcher_fn: mock_eq_matcher,
        pinned: vec![int_ref(&INT_42)],
        clause_bodies: vec![null_mut()],
        clause_bound_counts: vec![1],
        bound_arity: 1,
        after_deadline_ms: None,
        after_cont: null_mut(),
        after_timer_id: None,
    };
    assert_eq!(p.pinned, vec![int_ref(&INT_42)]);
    assert_eq!(p.bound_arity, 1);
    assert!(p.after_timer_id.is_none());
}

#[test]
fn try_match_hit_returns_clause_and_bound_vals() {
    let p = ParkRecord {
        matcher_fn: mock_eq_matcher,
        pinned: vec![int_ref(&INT_99)],
        clause_bodies: vec![null_mut()],
        clause_bound_counts: vec![1],
        bound_arity: 1,
        after_deadline_ms: None,
        after_cont: null_mut(),
        after_timer_id: None,
    };
    let hit = p.try_match(null_mut(), int_ref(&INT_99));
    assert!(hit.is_some());
    let (idx, vals) = hit.unwrap();
    assert_eq!(idx, 0);
    assert_eq!(vals.len(), 1);
    assert_eq!(vals[0], int_ref(&INT_99));
}

#[test]
fn try_match_trims_scratch_to_winning_clause_bound_count() {
    extern "C" fn second_clause(
        _process: *mut Process,
        _msg: u64,
        _pinned: *const AnyValueRef,
        out: *mut AnyValueRef,
    ) -> u32 {
        unsafe {
            *out = int_ref(&INT_123);
        }
        2
    }
    let p = ParkRecord {
        matcher_fn: second_clause,
        pinned: vec![],
        clause_bodies: vec![null_mut(), null_mut()],
        clause_bound_counts: vec![1, 0],
        bound_arity: 1,
        after_deadline_ms: None,
        after_cont: null_mut(),
        after_timer_id: None,
    };
    let (idx, vals) = p.try_match(null_mut(), int_ref(&INT_99)).expect("match");
    assert_eq!(idx, 1);
    assert!(vals.is_empty());
}

#[test]
fn try_match_miss_returns_none() {
    let p = ParkRecord {
        matcher_fn: mock_eq_matcher,
        pinned: vec![int_ref(&INT_99)],
        clause_bodies: vec![null_mut()],
        clause_bound_counts: vec![1],
        bound_arity: 1,
        after_deadline_ms: None,
        after_cont: null_mut(),
        after_timer_id: None,
    };
    assert!(p.try_match(null_mut(), int_ref(&INT_100)).is_none());
}
