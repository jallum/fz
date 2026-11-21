//! Selective-receive park record.
//!
//! A `receive do … end` has two parts. The site is what the compiler knows:
//! the matcher and each clause's code. An arrival is what one visit holds: the
//! outer continuation, the captures and the pinned values, in one frame.

use crate::any_value::{
    AnyValue, AnyValueRef, Stored, ValueKind, closure_addr_from_tagged, closure_arity, closure_capture_copy,
    closure_capture_set, closure_capture_set_ref_word, closure_flags, closure_flags_captured, closure_flags_halt_kind,
};
use crate::heap::Heap;
use crate::process::Process;
use crate::timer::TimerId;
use smallvec::SmallVec;
use std::ptr::{read, write};

/// The values a matcher hands back for the winning clause: its roots. Inline up
/// to eight, which covers every clause a program is likely to write.
pub type Roots = SmallVec<[AnyValueRef; 8]>;

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
/// - `frame`: the arrival's frame closure, as a ref word. The matcher reads
///   its pinned values out of the frame's last captures.
/// - `out`: pointer to a caller-supplied `[AnyValueRef; root_arity]`
///   scratch buffer the matcher fills with the winning clause's roots.
///   Untouched on a miss. Only the winning clause's own root count is
///   meaningful; wider scratch slots are ignored.
///
/// Return: `k = 0` on miss; `k > 0` is the 1-based clause index the
/// site's clauses index into via `clause = clauses[k-1]`.
pub type MatcherFn = extern "C" fn(process: *mut Process, msg_ref: u64, frame: u64, out: *mut AnyValueRef) -> u32;

/// Reads a clause's outcome arguments out of its roots.
///
/// - `roots`: the clause's `root_count` roots, in the order the matcher wrote them.
/// - `out`: pointer to a `[AnyValueRef; argument_count]` buffer the projector
///   fills, one slot per outcome argument, in argument order.
///
/// The roots are values in `process`'s heap. A projector follows list heads,
/// list tails, tuple fields and struct fields and nothing else, so it
/// allocates nothing.
pub type ProjectorFn = extern "C" fn(process: *mut Process, roots: *const AnyValueRef, out: *mut AnyValueRef);

/// One clause of a receive site: the code its outcome closure runs, how its
/// outcome arguments are read from the roots the matcher binds, and the number
/// of slots its body keeps empty behind the captures.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct ReceiveClause {
    pub code: usize,
    /// Reads the clause's arguments out of its roots. `None` when the
    /// arguments are the roots, one for one.
    pub projector: Option<ProjectorFn>,
    /// The number of roots the matcher writes for this clause.
    pub root_count: u32,
    /// The number of outcome arguments the clause body takes.
    pub argument_count: u32,
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
    /// The largest root count of any clause: the size of the buffer the
    /// matcher writes into.
    pub root_arity: u32,
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

    /// Try the site's matcher against `msg`. On a hit, returns the winning
    /// clause's index and its roots, which the matcher wrote into `roots`. On a
    /// miss, returns `None`.
    pub fn try_match<'a>(
        &self,
        process: *mut Process,
        msg: AnyValueRef,
        roots: &'a mut Roots,
    ) -> Option<(usize, &'a [AnyValueRef])> {
        roots.clear();
        roots.resize(self.site.root_arity as usize, AnyValueRef::null());
        let k = (self.site.matcher)(process, msg.raw_word(), self.frame.raw_word(), roots.as_mut_ptr());
        if k == 0 {
            return None;
        }
        let clause_idx = (k - 1) as usize;
        // SAFETY: a site's clauses follow it in memory.
        let root_count = unsafe { self.site.clauses() }[clause_idx].root_count as usize;
        Some((clause_idx, &roots[..root_count]))
    }

    /// The closure the receiver resumes through when clause `clause_idx`
    /// wins: the clause's arguments, read out of `roots` in `task`'s heap, go
    /// between the outer continuation and the frame's captures.
    ///
    /// ```text
    /// frame   env: [outer_cont, cap0, cap1, ..., pinned...]
    /// outcome env: [outer_cont, arg0, ..., cap0, cap1, ..., empty...]
    /// ```
    pub fn outcome_closure(&self, task: &mut Process, clause_idx: usize, roots: &[AnyValueRef]) -> AnyValueRef {
        // SAFETY: a site's clauses follow it in memory.
        let clause = unsafe { self.site.clauses() }[clause_idx];
        let empty_slots = clause.empty_slots as usize;
        let Some(project) = clause.projector else {
            return self.resume_closure(&mut task.heap, clause.code, roots, empty_slots);
        };
        let mut arguments = Roots::from_elem(AnyValueRef::null(), clause.argument_count as usize);
        project(task, roots.as_ptr(), arguments.as_mut_ptr());
        self.resume_closure(&mut task.heap, clause.code, &arguments, empty_slots)
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
        arguments: &[AnyValueRef],
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
        let slots = 1 + arguments.len() + captures + empty_slots;
        let bits = heap.alloc_closure_slots(denotation, arity, slots, closure_flags_halt_kind(flags));
        let resume = closure_addr_from_tagged(bits).expect("resume closure ptr");
        // SAFETY: `resume` is a new closure of `slots` captures nothing else holds, and `frame` is live.
        unsafe {
            write(resume.add(8) as *mut u64, code as u64);
            closure_capture_copy(frame, 0, resume, 0);
            for (i, v) in arguments.iter().enumerate() {
                closure_capture_set_ref_word(resume, 1 + i, v.raw_word());
            }
            for i in 0..captures {
                closure_capture_copy(frame, 1 + i, resume, 1 + arguments.len() + i);
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
pub unsafe fn materialize_outcome_closure(heap: &mut Heap, template: *mut u8, arguments: &[Stored]) -> *mut u8 {
    let flags = unsafe { closure_flags(template as *const u8) };
    let template_slots = closure_flags_captured(flags) as usize;
    assert!(
        template_slots >= 1,
        "receive outcome closure template must contain outer_cont"
    );
    let outcome_slots = template_slots + arguments.len();
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

        for (i, v) in arguments.iter().enumerate() {
            closure_capture_set(outcome_u8, i + 1, v.value("outcome closure argument"));
        }

        let template_caps = template_slots - 1;
        for i in 0..template_caps {
            closure_capture_copy(template_u8, i + 1, outcome_u8, 1 + arguments.len() + i);
        }
    }

    outcome
}

#[cfg(test)]
#[path = "park_test.rs"]
pub(crate) mod park_test;
