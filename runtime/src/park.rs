//! fz-yxs/fz-st5 — selective-receive park record.
//!
//! Holds the snapshot the receiver needs when it parks on a selective
//! `receive do … end`. Lives on `Process::wait` while the
//! task is `Blocked`; cleared (and re-emitted as a runnable closure) the
//! moment a matcher hit fires.
//!
//! See `docs/receive-matched.md §2.5` / §2.6 for the design rationale.

use crate::any_value::{
    AnyValueRef, closure_addr_from_tagged, closure_capture_copy, closure_capture_set_ref_word, closure_flags,
    closure_flags_captured, closure_flags_halt_kind, closure_schema_id,
};
use crate::heap::Heap;
use crate::process::Process;
use crate::timer::TimerId;
use std::ptr::{read, write};

/// fz-yxs/fz-st5 — matcher ABI.
///
/// Called from both fz-compiled code (sender's `fz_send`, receiver's
/// initial scan) and runtime code. Pure leaf function — no allocation,
/// no extern, no `receive`. F3's `check_pure_codegen` is the static
/// invariant that proves this.
///
/// - `msg_ref`: the candidate message as a single opaque any value ref.
/// - `pinned`: pointer to `AnyValueRef` entries in the order
///   they appear in `ParkRecord::pinned`.
/// - `out`: pointer to a caller-supplied `[AnyValueRef; bound_arity]`
///   scratch buffer the matcher fills with bound-variable
///   values for the winning clause. Untouched on a miss. Only the winning
///   clause's own bound count is part of the resumed outcome env; wider
///   scratch slots are ignored.
///
/// Return: `k = 0` on miss; `k > 0` is the 1-based clause index the
/// caller's clause-body table indexes into via `cont = bodies[k-1]`.
pub type MatcherFn =
    extern "C" fn(process: *mut Process, msg_ref: u64, pinned: *const AnyValueRef, out: *mut AnyValueRef) -> u32;

/// Park record stashed on `Process::wait` while a task is
/// blocked on a selective receive. Cleared on a matcher hit (sender-
/// probe or after-timer fire); persists across mailbox arrivals that
/// the matcher rejects.
pub struct ParkRecord {
    pub matcher_fn: MatcherFn,
    /// Pinned-value snapshot in matcher order.
    pub pinned: Vec<AnyValueRef>,
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
    pub after_timer_id: Option<TimerId>,
}

impl ParkRecord {
    /// Try the registered matcher against `msg`. On a hit, returns
    /// `Some((clause_idx, bound_vals))` where `bound_vals.len()` is the
    /// winning clause's own bound-variable count. On a miss, returns `None`.
    pub fn try_match(&self, process: *mut Process, msg: AnyValueRef) -> Option<(usize, Vec<AnyValueRef>)> {
        let mut out_buf: Vec<AnyValueRef> = vec![AnyValueRef::null(); self.bound_arity as usize];
        let k = (self.matcher_fn)(process, msg.raw_word(), self.pinned.as_ptr(), out_buf.as_mut_ptr());
        if k == 0 {
            None
        } else {
            let clause_idx = (k - 1) as usize;
            let bound_count = self
                .clause_bound_counts
                .get(clause_idx)
                .copied()
                .unwrap_or(self.bound_arity) as usize;
            let bound_vals: Vec<AnyValueRef> = out_buf.iter().take(bound_count).copied().collect();
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
    pub fn outcome_closure(&self, heap: &mut Heap, clause_idx: usize, bound_vals: &[AnyValueRef]) -> *mut u8 {
        let template = self.clause_bodies[clause_idx];
        materialize_outcome_closure(heap, template, bound_vals)
    }
}

pub fn materialize_outcome_closure(heap: &mut Heap, template: *mut u8, bound_vals: &[AnyValueRef]) -> *mut u8 {
    let template_bits = template as u64;
    let template_addr = closure_addr_from_tagged(template_bits).unwrap_or(template);
    let flags = unsafe { closure_flags(template_addr as *const u8) };
    let template_slots = closure_flags_captured(flags) as usize;
    assert!(
        template_slots >= 1,
        "receive outcome closure template must contain outer_cont"
    );
    let outcome_slots = template_slots + bound_vals.len();
    let outcome_bits = heap.alloc_closure_slots(
        unsafe { closure_schema_id(template_addr as *const u8) },
        outcome_slots,
        closure_flags_halt_kind(flags),
    );
    let outcome = closure_addr_from_tagged(outcome_bits).expect("materialized closure ptr");

    unsafe {
        let template_u8 = template_addr as *const u8;
        let outcome_u8 = outcome;
        let code_ptr = read(template_u8.add(8) as *const u64);
        write(outcome_u8.add(8) as *mut u64, code_ptr);

        closure_capture_copy(template_u8, 0, outcome_u8, 0);

        for (i, v) in bound_vals.iter().enumerate() {
            closure_capture_set_ref_word(outcome_u8, i + 1, v.raw_word());
        }

        let template_caps = template_slots - 1;
        for i in 0..template_caps {
            closure_capture_copy(template_u8, i + 1, outcome_u8, 1 + bound_vals.len() + i);
        }
    }

    outcome
}

#[cfg(test)]
#[path = "park_test.rs"]
mod park_test;
