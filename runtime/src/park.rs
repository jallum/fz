//! fz-yxs/fz-st5 — selective-receive park record.
//!
//! Holds the snapshot the receiver needs when it parks on a selective
//! `receive do … end`. Lives on `Process::parked_matched` while the
//! task is `Blocked`; cleared (and re-emitted as a runnable closure) the
//! moment a matcher hit fires.
//!
//! See `docs/receive-matched.md §2.5` / §2.6 for the design rationale.

use crate::tagged_value_ref::TaggedValueRef;

/// fz-yxs/fz-st5 — matcher ABI.
///
/// Called from both fz-compiled code (sender's `fz_send`, receiver's
/// initial scan) and runtime code. Pure leaf function — no allocation,
/// no extern, no `receive`. F3's `check_pure_codegen` is the static
/// invariant that proves this.
///
/// - `msg_ref`: the candidate message as a single opaque tagged value ref.
/// - `pinned`: pointer to `TaggedValueRef` entries in the order
///   they appear in `ParkRecord::pinned`.
/// - `out`: pointer to a caller-supplied `[TaggedValueRef; bound_arity]`
///   scratch buffer the matcher fills with bound-variable
///   values for the winning clause. Untouched on a miss. Only the winning
///   clause's own bound count is part of the resumed outcome env; wider
///   scratch slots are ignored.
///
/// Return: `k = 0` on miss; `k > 0` is the 1-based clause index the
/// caller's clause-body table indexes into via `cont = bodies[k-1]`.
pub type MatcherFn =
    extern "C" fn(msg_ref: u64, pinned: *const TaggedValueRef, out: *mut TaggedValueRef) -> u32;

/// Matcher for plain `receive()`: accept the first mailbox message and bind
/// it as the single outcome value.
pub(crate) extern "C" fn match_any_message(
    msg_ref: u64,
    _pinned: *const TaggedValueRef,
    out: *mut TaggedValueRef,
) -> u32 {
    write_match_out(
        out,
        TaggedValueRef::from_raw_word(msg_ref).expect("receive message ref"),
    );
    1
}

fn write_match_out(out: *mut TaggedValueRef, value: TaggedValueRef) {
    unsafe {
        *out = value;
    }
}

/// Park record stashed on `Process::parked_matched` while a task is
/// blocked on a selective receive. Cleared on a matcher hit (sender-
/// probe or after-timer fire); persists across mailbox arrivals that
/// the matcher rejects.
pub struct ParkRecord {
    pub matcher_fn: MatcherFn,
    /// Pinned-value snapshot in matcher order.
    pub pinned: Vec<TaggedValueRef>,
    /// One closure pointer per clause body, in source order. `k-1`
    /// from the matcher's return indexes here.
    pub clause_bodies: Vec<*mut u8>,
    /// One bound-variable count per clause body, in source order.
    pub clause_bound_counts: Vec<u16>,
    /// Maximum bound-var count across clauses — sizes the `out`
    /// buffer the prober supplies to `matcher_fn`.
    pub bound_arity: u16,
    /// Absolute wall-clock deadline (millis since some epoch the
    /// `Runtime`'s `TimerWheel` understands). `None` means no timer
    /// (`after :infinity` or no `after` clause at all).
    pub after_deadline_ms: Option<u64>,
    /// After-body closure pointer; null when there is no `after`.
    pub after_cont: *mut u8,
    /// Timer wheel id, if a timer was scheduled. The scheduler clears
    /// this when the timer fires or when a matcher-hit cancels.
    pub after_timer_id: Option<crate::timer::TimerId>,
}

impl ParkRecord {
    /// Try the registered matcher against `msg`. On a hit, returns
    /// `Some((clause_idx, bound_vals))` where `bound_vals.len()` is the
    /// winning clause's own bound-variable count. On a miss, returns `None`.
    pub fn try_match(&self, msg: TaggedValueRef) -> Option<(usize, Vec<TaggedValueRef>)> {
        let mut out_buf: Vec<TaggedValueRef> =
            vec![TaggedValueRef::null(); self.bound_arity as usize];
        let k = (self.matcher_fn)(msg.raw_word(), self.pinned.as_ptr(), out_buf.as_mut_ptr());
        if k == 0 {
            None
        } else {
            let clause_idx = (k - 1) as usize;
            let bound_count = self
                .clause_bound_counts
                .get(clause_idx)
                .copied()
                .unwrap_or(self.bound_arity) as usize;
            let bound_vals: Vec<TaggedValueRef> =
                out_buf.iter().take(bound_count).copied().collect();
            Some((clause_idx, bound_vals))
        }
    }

    /// Materialize the winning clause as the closure the receiver should
    /// resume through. The parked clause body is a template containing
    /// outer-cont + receive-site captures. A matcher hit inserts bound
    /// values between them:
    ///
    /// ```text
    /// template env: [outer_cont, cap0, cap1, ...]
    /// outcome  env: [outer_cont, bound0, ..., cap0, cap1, ...]
    /// ```
    pub fn outcome_closure(
        &self,
        heap: &mut crate::heap::Heap,
        clause_idx: usize,
        bound_vals: &[TaggedValueRef],
    ) -> *mut u8 {
        let template = self.clause_bodies[clause_idx];
        materialize_outcome_closure(heap, template, bound_vals)
    }
}

pub fn materialize_outcome_closure(
    heap: &mut crate::heap::Heap,
    template: *mut u8,
    bound_vals: &[TaggedValueRef],
) -> *mut u8 {
    use crate::fz_value::{closure_flags_captured, closure_flags_halt_kind};

    let template_bits = template as u64;
    let template_addr =
        crate::fz_value::closure_addr_from_tagged(template_bits).unwrap_or(template);
    let flags = unsafe { crate::fz_value::closure_flags(template_addr as *const u8) };
    let template_slots = closure_flags_captured(flags) as usize;
    assert!(
        template_slots >= 1,
        "receive outcome closure template must contain outer_cont"
    );
    let outcome_slots = template_slots + bound_vals.len();
    let outcome_bits = heap.alloc_closure_slots(
        unsafe { crate::fz_value::closure_schema_id(template_addr as *const u8) },
        outcome_slots,
        closure_flags_halt_kind(flags),
    );
    let outcome =
        crate::fz_value::closure_addr_from_tagged(outcome_bits).expect("materialized closure ptr");

    unsafe {
        let template_u8 = template_addr as *const u8;
        let outcome_u8 = outcome;
        let stub_fp = std::ptr::read(template_u8.add(8) as *const u64);
        std::ptr::write(outcome_u8.add(8) as *mut u64, stub_fp);

        crate::fz_value::closure_capture_copy(template_u8, 0, outcome_u8, 0);

        for (i, v) in bound_vals.iter().enumerate() {
            crate::fz_value::closure_capture_set_ref_word(outcome_u8, i + 1, v.raw_word());
        }

        let template_caps = template_slots - 1;
        for i in 0..template_caps {
            crate::fz_value::closure_capture_copy(
                template_u8,
                i + 1,
                outcome_u8,
                1 + bound_vals.len() + i,
            );
        }
    }

    outcome_bits as *mut u8
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tagged_value_ref::TaggedValueTag;

    static INT_42: u64 = 42;
    static INT_99: u64 = 99;
    static INT_100: u64 = 100;
    static INT_123: u64 = 123;

    fn int_ref(slot: &'static u64) -> TaggedValueRef {
        TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, slot).expect("int ref")
    }

    /// A deterministic mock matcher used by the runtime tests. Layout:
    ///   pinned[0]: expected message value.
    ///   out[0]: matched int value.
    /// Returns 1 if `msg == pinned[0]`, else 0.
    extern "C" fn mock_eq_matcher(
        msg: u64,
        pinned: *const TaggedValueRef,
        out: *mut TaggedValueRef,
    ) -> u32 {
        let want = unsafe { *pinned };
        if msg == want.raw_word() {
            unsafe {
                *out = TaggedValueRef::from_raw_word(msg).expect("msg ref");
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
            clause_bodies: vec![std::ptr::null_mut()],
            clause_bound_counts: vec![1],
            bound_arity: 1,
            after_deadline_ms: None,
            after_cont: std::ptr::null_mut(),
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
            clause_bodies: vec![std::ptr::null_mut()],
            clause_bound_counts: vec![1],
            bound_arity: 1,
            after_deadline_ms: None,
            after_cont: std::ptr::null_mut(),
            after_timer_id: None,
        };
        let hit = p.try_match(int_ref(&INT_99));
        assert!(hit.is_some());
        let (idx, vals) = hit.unwrap();
        assert_eq!(idx, 0);
        assert_eq!(vals.len(), 1);
        assert_eq!(vals[0], int_ref(&INT_99));
    }

    #[test]
    fn try_match_trims_scratch_to_winning_clause_bound_count() {
        extern "C" fn second_clause(
            _msg: u64,
            _pinned: *const TaggedValueRef,
            out: *mut TaggedValueRef,
        ) -> u32 {
            unsafe {
                *out = int_ref(&INT_123);
            }
            2
        }
        let p = ParkRecord {
            matcher_fn: second_clause,
            pinned: vec![],
            clause_bodies: vec![std::ptr::null_mut(), std::ptr::null_mut()],
            clause_bound_counts: vec![1, 0],
            bound_arity: 1,
            after_deadline_ms: None,
            after_cont: std::ptr::null_mut(),
            after_timer_id: None,
        };
        let (idx, vals) = p.try_match(int_ref(&INT_99)).expect("match");
        assert_eq!(idx, 1);
        assert!(vals.is_empty());
    }

    #[test]
    fn try_match_miss_returns_none() {
        let p = ParkRecord {
            matcher_fn: mock_eq_matcher,
            pinned: vec![int_ref(&INT_99)],
            clause_bodies: vec![std::ptr::null_mut()],
            clause_bound_counts: vec![1],
            bound_arity: 1,
            after_deadline_ms: None,
            after_cont: std::ptr::null_mut(),
            after_timer_id: None,
        };
        assert!(p.try_match(int_ref(&INT_100)).is_none());
    }
}
