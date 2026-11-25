use super::*;
use crate::any_value::{ClosureDenotationId, closure_capture_set_ref_word, closure_capture_value};
use crate::heap::SchemaRegistry;
use std::alloc::{Layout, alloc};
use std::cell::RefCell;
use std::mem::{align_of, size_of, size_of_val};
use std::ptr::{copy_nonoverlapping, null_mut};
use std::rc::Rc;

/// A receive site that lives for the rest of the test process, laid out the
/// way codegen emits one: the record, then its clauses. `after` is the after
/// body's code and empty slot count.
pub(crate) fn leaked_site(
    matcher: MatcherFn,
    after: Option<(usize, u32)>,
    pinned_count: u32,
    clauses: &[ReceiveClause],
) -> &'static ReceiveSite {
    let (after_code, after_empty_slots) = after.unwrap_or((0, 0));
    let layout = Layout::from_size_align(
        size_of::<ReceiveSite>() + size_of_val(clauses),
        align_of::<ReceiveSite>(),
    )
    .expect("site layout");
    // SAFETY: the allocation holds the record and `clauses.len()` clauses behind it, and is never freed.
    unsafe {
        let site = alloc(layout) as *mut ReceiveSite;
        site.write(ReceiveSite {
            matcher,
            after_code,
            clause_count: clauses.len() as u32,
            pinned_count,
            root_arity: clauses.iter().map(|c| c.root_count).max().unwrap_or(0),
            after_empty_slots,
        });
        copy_nonoverlapping(clauses.as_ptr(), site.add(1) as *mut ReceiveClause, clauses.len());
        &*site
    }
}

/// A receive frame on `heap`: a null outer continuation, then `captures`
/// (the receive's captures followed by its pinned values).
pub(crate) fn frame_of(heap: &mut Heap, captures: &[AnyValueRef]) -> AnyValueRef {
    let bits = heap.alloc_closure_slots(ClosureDenotationId::user(0), 0, 1 + captures.len(), 0);
    let frame = closure_addr_from_tagged(bits).expect("frame ptr");
    // SAFETY: `frame` is a new closure of `1 + captures.len()` captures.
    unsafe {
        closure_capture_set(frame, 0, AnyValue::null());
        for (i, capture) in captures.iter().enumerate() {
            closure_capture_set_ref_word(frame, 1 + i, capture.raw_word());
        }
    }
    AnyValueRef::from_heap_object(ValueKind::CLOSURE, frame).expect("frame ref")
}

/// The code word of a closure.
pub(crate) fn code_of(closure: AnyValueRef) -> usize {
    let addr = closure.closure_addr().expect("closure addr");
    // SAFETY: a closure's code word is its second word.
    unsafe { read(addr.add(8) as *const u64) as usize }
}

/// A clause whose arguments are its roots, one for one.
fn clause(code: usize, root_count: u32, empty_slots: u32) -> ReceiveClause {
    ReceiveClause {
        code,
        projector: None,
        root_count,
        argument_count: root_count,
        empty_slots,
    }
}

fn int_ref(n: i64) -> AnyValueRef {
    let slot = Box::leak(Box::new(n as u64));
    AnyValueRef::from_scalar_slot(ValueKind::INT, slot as *const u64).expect("int ref")
}

fn int_stored(n: i64) -> Stored {
    Stored::of(AnyValue::Int(n))
}

fn fresh_process() -> Process {
    Process::new(Rc::new(RefCell::new(SchemaRegistry::new())))
}

fn record(site: &'static ReceiveSite, frame: AnyValueRef) -> ParkRecord {
    ParkRecord {
        site,
        frame,
        after_deadline_ms: None,
        after_timer_id: None,
    }
}

/// Matches a message equal to the last pinned value of the frame and binds it.
extern "C" fn pinned_eq_matcher(
    _process: *mut Process,
    msg_word: u64,
    msg_kind: u64,
    frame: u64,
    out: *mut Stored,
) -> u32 {
    let msg = Stored {
        word: msg_word,
        kind: msg_kind,
    };
    let want = AnyValueRef::from_raw_word(crate::ir_runtime::fz_receive_pinned_ref(frame, 1)).expect("pinned ref");
    if msg.value("int msg") != AnyValue::Int(want.load_int().expect("int pinned")) {
        return 0;
    }
    unsafe { *out = msg };
    1
}

/// Always picks the second clause, after writing one value into the buffer.
extern "C" fn second_clause(_process: *mut Process, word: u64, kind: u64, _frame: u64, out: *mut Stored) -> u32 {
    unsafe { *out = Stored { word, kind } };
    2
}

/// The matcher is handed the frame's pinned values, which sit behind the
/// captures: a capture that equals the message is not mistaken for one.
#[test]
fn the_matcher_reads_the_pinned_values_behind_the_frames_captures() {
    let mut process = fresh_process();
    let site = leaked_site(pinned_eq_matcher, None, 1, &[clause(0x10, 1, 0)]);
    let frame = frame_of(&mut process.heap, &[int_ref(7), int_ref(42)]);
    let park = record(site, frame);

    let mut roots = Roots::new();
    let (clause_idx, bound) = park
        .try_match(null_mut(), int_stored(42), &mut roots)
        .expect("42 is the pinned value");
    assert_eq!(clause_idx, 0);
    assert_eq!(bound.len(), 1);
    assert_eq!(bound[0].value("root"), AnyValue::Int(42));
    assert!(
        park.try_match(null_mut(), int_stored(7), &mut roots).is_none(),
        "7 is a capture, not the pinned value"
    );
}

#[test]
fn a_hit_hands_back_only_the_winning_clauses_roots() {
    let mut process = fresh_process();
    let site = leaked_site(second_clause, None, 0, &[clause(0x10, 1, 0), clause(0x20, 0, 0)]);
    let park = record(site, frame_of(&mut process.heap, &[]));

    let mut roots = Roots::new();
    let (clause_idx, bound) = park.try_match(null_mut(), int_stored(99), &mut roots).expect("match");
    assert_eq!(clause_idx, 1);
    assert!(bound.is_empty(), "the second clause has no roots");
}

/// The outcome closure is the frame re-cut for the winning clause: that
/// clause's code, the arguments right behind the outer continuation, the
/// captures behind them, the clause's empty slots last. Pinned values are for
/// the matcher only and do not travel.
#[test]
fn an_outcome_closure_is_the_winning_clauses_code_over_bound_values_then_captures() {
    let mut process = fresh_process();
    let site = leaked_site(pinned_eq_matcher, None, 1, &[clause(0x10, 0, 0), clause(0xbeef, 1, 2)]);
    let frame = frame_of(&mut process.heap, &[int_ref(7), int_ref(42)]);
    let park = record(site, frame);

    let outcome = park.outcome_closure(&mut process, 1, &[int_stored(99)]);

    assert_eq!(code_of(outcome), 0xbeef);
    let addr = outcome.closure_addr().expect("outcome addr");
    // SAFETY: `outcome` is a live closure.
    unsafe {
        assert_eq!(closure_flags_captured(closure_flags(addr)), 5);
        assert_eq!(closure_capture_value(addr, 0), AnyValue::null(), "outer continuation");
        assert_eq!(closure_capture_value(addr, 1), AnyValue::Int(99), "bound value");
        assert_eq!(closure_capture_value(addr, 2), AnyValue::Int(7), "capture");
        assert_eq!(closure_capture_value(addr, 3), AnyValue::nil_atom(), "empty slot");
        assert_eq!(closure_capture_value(addr, 4), AnyValue::nil_atom(), "empty slot");
    }
}

/// Writes the second root, then the first, as the clause's two arguments.
extern "C" fn swap_projector(_process: *mut Process, roots: *const Stored, out: *mut Stored) {
    unsafe {
        *out = *roots.add(1);
        *out.add(1) = *roots;
    }
}

/// A clause with a projector hands the receiver's heap and the roots to it,
/// and the outcome closure holds what it wrote, not the roots.
#[test]
fn an_outcome_closure_holds_the_arguments_the_projector_reads_out_of_the_roots() {
    let mut process = fresh_process();
    let projecting = ReceiveClause {
        code: 0xcafe,
        projector: Some(swap_projector),
        root_count: 2,
        argument_count: 2,
        empty_slots: 0,
    };
    let site = leaked_site(pinned_eq_matcher, None, 0, &[projecting]);
    let park = record(site, frame_of(&mut process.heap, &[]));

    let outcome = park.outcome_closure(&mut process, 0, &[int_stored(1), int_stored(2)]);

    let addr = outcome.closure_addr().expect("outcome addr");
    // SAFETY: `outcome` is a live closure.
    unsafe {
        assert_eq!(closure_capture_value(addr, 1), AnyValue::Int(2), "first argument");
        assert_eq!(closure_capture_value(addr, 2), AnyValue::Int(1), "second argument");
    }
}

#[test]
fn an_after_closure_is_the_after_bodys_code_over_the_captures() {
    let mut process = fresh_process();
    let site = leaked_site(pinned_eq_matcher, Some((0xaf7e, 1)), 1, &[clause(0x10, 1, 0)]);
    let frame = frame_of(&mut process.heap, &[int_ref(7), int_ref(42)]);
    let park = record(site, frame);
    assert!(park.has_after());

    let after = park.after_closure(&mut process.heap);

    assert_eq!(code_of(after), 0xaf7e);
    let addr = after.closure_addr().expect("after addr");
    // SAFETY: `after` is a live closure.
    unsafe {
        assert_eq!(closure_flags_captured(closure_flags(addr)), 3);
        assert_eq!(closure_capture_value(addr, 1), AnyValue::Int(7), "capture");
        assert_eq!(closure_capture_value(addr, 2), AnyValue::nil_atom(), "empty slot");
    }
}

#[test]
fn a_site_without_an_after_body_says_so() {
    let mut process = fresh_process();
    let site = leaked_site(pinned_eq_matcher, None, 0, &[clause(0x10, 1, 0)]);
    assert!(!record(site, frame_of(&mut process.heap, &[])).has_after());
}

/// A park record is the site, the frame and the after-timer's two fields, so
/// the delivery state holds it in place and parking allocates nothing for it.
#[test]
fn a_park_record_is_six_words() {
    assert_eq!(size_of::<ParkRecord>(), 6 * size_of::<usize>());
}
