//! Selective-receive park record.
//!
//! A `receive do … end` has two parts. The site is what the compiler knows:
//! the matcher and each clause's code. An arrival is what one visit holds: the
//! outer continuation, the captures and the pinned values, in one frame.

use crate::any_value::{
    AnyValue, AnyValueRef, ValueKind, closure_addr_from_tagged, closure_arity, closure_capture_copy,
    closure_capture_ref_word, closure_capture_set, closure_capture_set_ref_word, closure_flags, closure_flags_captured,
    closure_flags_halt_kind,
};
use crate::heap::Heap;
use crate::process::Process;
use crate::timer::TimerId;
use std::ptr::{read, write};

/// Matcher ABI.
///
/// Called from both fz-compiled code (sender's `fz_send`, receiver's
/// mailbox scan) and runtime code. It is a leaf in the scheduling sense: it
/// never parks and runs no `receive` of its own, so it always returns to its
/// caller. It is not allocation-free — testing a raw scalar against a value
/// held as an `AnyValueRef` calls a runtime boxing extern on the process
/// heap. Nothing checks either property statically.
///
/// - `msg_ref`: the candidate message as a single opaque any value ref.
/// - `pinned`: pointer to `AnyValueRef` entries in the order
///   the receive's frame holds them.
/// - `out`: pointer to a caller-supplied `[AnyValueRef; bound_arity]`
///   scratch buffer the matcher fills with bound-variable
///   values for the winning clause. Untouched on a miss. Only the winning
///   clause's own bound count is part of the resumed outcome env; wider
///   scratch slots are ignored.
///
/// Return: `k = 0` on miss; `k > 0` is the 1-based clause index the
/// site's clauses index into via `clause = clauses[k-1]`.
pub type MatcherFn =
    extern "C" fn(process: *mut Process, msg_ref: u64, pinned: *const AnyValueRef, out: *mut AnyValueRef) -> u32;

/// One clause of a receive site: the code its outcome closure runs, the
/// number of values the matcher binds for it, and the number of slots its body
/// keeps empty behind the captures.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct ReceiveClause {
    pub code: usize,
    pub bound_count: u32,
    pub empty_slots: u32,
}

/// Everything about a `receive` that is fixed when the program is compiled.
/// Codegen emits one read-only record per receive, and its clauses follow it
/// in memory, in source order.
#[repr(C)]
#[derive(Debug)]
pub struct ReceiveSite {
    pub matcher: MatcherFn,
    /// The `after` body's code, or zero when the receive has no `after`.
    pub after_code: usize,
    pub clause_count: u32,
    /// The number of pinned values the matcher reads.
    pub pinned_count: u32,
    /// The largest bound count of any clause: the size of the buffer the
    /// matcher writes into.
    pub bound_arity: u32,
    /// The slots the `after` body keeps empty behind the captures.
    pub after_empty_slots: u32,
}

impl ReceiveSite {
    /// # Safety
    ///
    /// `clause_count` clauses follow this record in memory.
    unsafe fn clauses(&self) -> &[ReceiveClause] {
        let first = unsafe { (self as *const Self).add(1) } as *const ReceiveClause;
        unsafe { std::slice::from_raw_parts(first, self.clause_count as usize) }
    }
}

/// One arrival at a receive site, held on the process's delivery state while
/// the process is `Blocked`. It is cleared the moment the receive is decided:
/// a matcher hit or the after-timer.
///
/// The frame is a closure that is never called. Its captures are the values
/// this arrival holds:
///
/// ```text
/// frame env: [outer_cont, cap0, cap1, ..., pinned0, pinned1, ...]
/// ```
#[derive(Debug)]
pub struct ParkRecord {
    pub site: &'static ReceiveSite,
    pub frame: AnyValueRef,
    /// The `after` timeout as a duration in millis. `None` means no timer
    /// (`after :infinity` or no `after` clause at all).
    pub after_deadline_ms: Option<u64>,
    /// Timer wheel id, if a timer was scheduled. The scheduler clears
    /// this when the timer fires or when a matcher-hit cancels.
    pub after_timer_id: Option<TimerId>,
}

impl ParkRecord {
    fn frame_addr(&self) -> *const u8 {
        self.frame.closure_addr().expect("a receive frame is a closure ref")
    }

    /// The captures the frame holds between the outer continuation and the
    /// pinned values.
    fn capture_count(&self) -> usize {
        // SAFETY: the frame is a live closure this record owns and the collector keeps current.
        let slots = closure_flags_captured(unsafe { closure_flags(self.frame_addr()) }) as usize;
        slots - 1 - self.site.pinned_count as usize
    }

    fn pinned(&self) -> Vec<AnyValueRef> {
        let first = 1 + self.capture_count();
        (0..self.site.pinned_count as usize)
            .map(|i| {
                // SAFETY: the frame's last `pinned_count` captures are its pinned values.
                let word = unsafe { closure_capture_ref_word(self.frame_addr(), first + i) };
                AnyValueRef::from_raw_word(word).expect("a pinned capture is a value ref")
            })
            .collect()
    }

    /// Try the site's matcher against `msg`. On a hit, returns
    /// `Some((clause_idx, bound_vals))` where `bound_vals.len()` is the
    /// winning clause's own bound-variable count. On a miss, returns `None`.
    pub fn try_match(&self, process: *mut Process, msg: AnyValueRef) -> Option<(usize, Vec<AnyValueRef>)> {
        let pinned = self.pinned();
        let mut out_buf: Vec<AnyValueRef> = vec![AnyValueRef::null(); self.site.bound_arity as usize];
        let k = (self.site.matcher)(process, msg.raw_word(), pinned.as_ptr(), out_buf.as_mut_ptr());
        if k == 0 {
            return None;
        }
        let clause_idx = (k - 1) as usize;
        // SAFETY: a site's clauses follow it in memory.
        let bound_count = unsafe { self.site.clauses() }[clause_idx].bound_count as usize;
        out_buf.truncate(bound_count);
        Some((clause_idx, out_buf))
    }

    /// The closure the receiver resumes through when clause `clause_idx`
    /// wins: the bound values go between the outer continuation and the
    /// frame's captures.
    ///
    /// ```text
    /// frame   env: [outer_cont, cap0, cap1, ..., pinned...]
    /// outcome env: [outer_cont, bound0, ..., cap0, cap1, ..., empty...]
    /// ```
    pub fn outcome_closure(&self, heap: &mut Heap, clause_idx: usize, bound_vals: &[AnyValueRef]) -> AnyValueRef {
        // SAFETY: a site's clauses follow it in memory.
        let clause = unsafe { self.site.clauses() }[clause_idx];
        self.resume_closure(heap, clause.code, bound_vals, clause.empty_slots as usize)
    }

    /// Does this receive have an `after` body?
    pub fn has_after(&self) -> bool {
        self.site.after_code != 0
    }

    /// The closure the receiver resumes through when the `after` fires.
    pub fn after_closure(&self, heap: &mut Heap) -> AnyValueRef {
        assert!(self.has_after(), "this receive has no after body");
        self.resume_closure(heap, self.site.after_code, &[], self.site.after_empty_slots as usize)
    }

    fn resume_closure(
        &self,
        heap: &mut Heap,
        code: usize,
        bound_vals: &[AnyValueRef],
        empty_slots: usize,
    ) -> AnyValueRef {
        let frame = self.frame_addr();
        let captures = self.capture_count();
        // SAFETY: the frame is a live closure this record owns and the collector keeps current.
        let (flags, arity, denotation) = unsafe {
            (
                closure_flags(frame),
                closure_arity(frame),
                crate::any_value::closure_denotation(frame),
            )
        };
        let slots = 1 + bound_vals.len() + captures + empty_slots;
        let bits = heap.alloc_closure_slots(denotation, arity, slots, closure_flags_halt_kind(flags));
        let resume = closure_addr_from_tagged(bits).expect("resume closure ptr");
        // SAFETY: `resume` is a new closure of `slots` captures nothing else holds, and `frame` is live.
        unsafe {
            write(resume.add(8) as *mut u64, code as u64);
            closure_capture_copy(frame, 0, resume, 0);
            for (i, v) in bound_vals.iter().enumerate() {
                closure_capture_set_ref_word(resume, 1 + i, v.raw_word());
            }
            for i in 0..captures {
                closure_capture_copy(frame, 1 + i, resume, 1 + bound_vals.len() + i);
            }
            for i in slots - empty_slots..slots {
                closure_capture_set(resume, i, AnyValue::nil_atom());
            }
        }
        AnyValueRef::from_heap_object(ValueKind::CLOSURE, resume).expect("resume closure ref")
    }
}

/// # Safety
///
/// `template` must point at a live closure whose first capture is the outer continuation.
pub unsafe fn materialize_outcome_closure(heap: &mut Heap, template: *mut u8, bound_vals: &[AnyValueRef]) -> *mut u8 {
    let flags = unsafe { closure_flags(template as *const u8) };
    let template_slots = closure_flags_captured(flags) as usize;
    assert!(
        template_slots >= 1,
        "receive outcome closure template must contain outer_cont"
    );
    let outcome_slots = template_slots + bound_vals.len();
    let outcome_bits = heap.alloc_closure_slots(
        unsafe { crate::any_value::closure_denotation(template) },
        unsafe { closure_arity(template as *const u8) },
        outcome_slots,
        closure_flags_halt_kind(flags),
    );
    let outcome = closure_addr_from_tagged(outcome_bits).expect("materialized closure ptr");

    unsafe {
        let template_u8 = template as *const u8;
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
pub(crate) mod park_test;
