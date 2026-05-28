use std::collections::HashMap;

use super::*;
use crate::fz_ir::{FnId, Module};
use crate::types::Types;

// ===== Interp-internal scheduler (fz-ul4.23.5.8 / fz-sched.3) =====
//
// The interp owns its own task registry separate from runtime.rs::Runtime
// (which is wired into the JIT trampoline). They share the Process type,
// the canonical value rep, and the heap — so messages and mailboxes are byte-
// compatible between paths.
//
// Scheduling model (fz-sched.3): cooperative run-queue, BEAM-correct.
// Builtin::Spawn enqueues the child and returns immediately; the parent
// continues its own quantum. Term::Receive parks the task (InterpStep::Blocked)
// if the mailbox is empty; the scheduler records the resume state and moves on.
// interp_send flips a Blocked receiver to Ready, prepends the message to its
// resume args, and re-enqueues it. run_main drives the loop until the queue
// is empty.
//
// Limitation: Blocked propagates as an error through non-tail call sites
// (Term::Call / Term::CallClosure). In practice all fixture receive sites are
// in tail position inside spawned fns, so this doesn't matter yet.

/// Returned by run_fn to signal either completion or a receive-park.
pub(super) enum InterpStep {
    Done(AnyValue),
    /// Task yielded cooperatively at a scheduler-safe back edge. The next
    /// quantum resumes by calling `resume_fn(args...)`, then drains `after`
    /// continuations exactly like a receive resume.
    Yielded {
        resume_fn: FnId,
        resume_args: Vec<AnyValue>,
        after: Vec<(FnId, Vec<AnyValue>)>,
        remaining_reductions: i32,
        reason: u8,
    },
    /// Task parked on receive. `resume_fn(msg, cap_vals...)` is called when
    /// the message arrives. `after` is a chain of (fn_id, caps) continuations
    /// to call in order with each successive return value — built up when
    /// Blocked propagates through Term::Call frames.
    Blocked(FnId, Vec<AnyValue>, Vec<(FnId, Vec<AnyValue>)>),
    /// fz-yxs/fz-2v3 — task parked on a selective `receive do … end`. The
    /// park record snapshots every clause's pattern + body / guard FnId
    /// plus the pinned ^name and capture AnyValues from the receive site
    /// so that `interp_send` can probe new messages without recreating
    /// any of that state.
    BlockedMatched(ParkRecord, Vec<(FnId, Vec<AnyValue>)>),
}

/// fz-yxs/fz-2v3 — interp park record for a selective receive.
/// `after` is consumed inline at park time (the `after 0` case fires
/// before we park; non-zero/`:infinity` is treated as "no timer" in the
/// interp since there's no wall clock — the real timer wiring lands
/// for JIT/AOT in B2 via F2). So this struct only stores what the
/// sender-side probe needs.
#[derive(Clone)]
pub(super) struct ParkRecord {
    pub(super) clauses: Vec<MatchedClause>,
    pub(super) matcher: std::sync::Arc<crate::matcher::Matcher>,
    pub(super) pinned: HashMap<String, AnyValue>,
    pub(super) captures: Vec<AnyValue>,
}

#[derive(Clone)]
pub(super) struct MatchedClause {
    pub(super) bound_names: Vec<String>,
    pub(super) guard: Option<FnId>,
    pub(super) body: FnId,
}

impl IrInterpRuntime {
    fn next_pid(&mut self) -> u32 {
        let pid = self.next_pid;
        self.next_pid += 1;
        pid
    }

    pub(super) fn send<T: Types<Ty = crate::types::Ty>>(
        &mut self,
        t: &mut T,
        module: &Module,
        tel: &dyn crate::telemetry::Telemetry,
        receiver_pid: u32,
        msg: AnyValue,
    ) -> Result<(), String> {
        use fz_runtime::process::ProcessState;
        let sender_heap =
            &fz_runtime::process::current_process().heap as *const fz_runtime::heap::Heap;
        // fz-yxs/fz-2v3 — sender-side probe for selective receive. If the
        // receiver is parked on a Term::ReceiveMatched, run the parked
        // matcher inline against the new message; on a hit, set up the
        // matched clause's body as the receiver's next resume and wake it
        // without touching the mailbox.
        let parked = self.parked.remove(&receiver_pid);
        if let Some((park, after_chain)) = parked {
            let hit = try_match_clauses(
                self,
                t,
                module,
                tel,
                &park.clauses,
                &park.matcher,
                msg,
                &park.pinned,
                &park.captures,
            )?;
            match hit {
                Some((idx, bound_vals)) => {
                    let body = park.clauses[idx].body;
                    let mut args = bound_vals;
                    args.extend(park.captures.iter().copied());
                    self.resume.insert(receiver_pid, (body, args, after_chain));
                    self.set_process_state(receiver_pid, ProcessState::Ready);
                    self.run_queue.push_back(receiver_pid);
                    return Ok(());
                }
                None => {
                    // Miss: park stays in place; message lands in mailbox.
                    self.parked.insert(receiver_pid, (park, after_chain));
                    let msg_ref = msg.as_any_value_ref()?;
                    if let Some(task) = self.tasks.get_mut(&receiver_pid) {
                        let mut forwarding = std::collections::HashMap::new();
                        let copied = fz_runtime::heap::deep_copy_any_value_ref(
                            msg_ref,
                            unsafe { &*sender_heap },
                            &mut task.heap,
                            &mut forwarding,
                        );
                        task.mailbox.push_back(copied);
                    } else {
                        tel.event(
                            &["fz", "runtime", "send_to_unknown_pid"],
                            crate::metadata! { pid: receiver_pid as u64 },
                        );
                    }
                    return Ok(());
                }
            }
        }

        let msg_ref = msg.as_any_value_ref()?;
        let Some(task) = self.tasks.get_mut(&receiver_pid) else {
            tel.event(
                &["fz", "runtime", "send_to_unknown_pid"],
                crate::metadata! { pid: receiver_pid as u64 },
            );
            return Ok(());
        };

        let mut forwarding = std::collections::HashMap::new();
        let copied = fz_runtime::heap::deep_copy_any_value_ref(
            msg_ref,
            unsafe { &*sender_heap },
            &mut task.heap,
            &mut forwarding,
        );
        if task.state == ProcessState::Blocked {
            let copied_msg =
                AnyValue::from_any_value_ref(copied).expect("copied interpreter message ref");
            if let Some(entry) = self.resume.get_mut(&receiver_pid) {
                entry.1.insert(0, copied_msg);
            }
            task.state = ProcessState::Ready;
            self.run_queue.push_back(receiver_pid);
        } else {
            task.mailbox.push_back(copied);
        }
        Ok(())
    }

    /// Spawn a new task: enqueue it and return its pid immediately.
    /// The child runs in a later scheduler quantum, not in the parent's.
    pub(crate) fn spawn(
        &mut self,
        module: &Module,
        fn_id: FnId,
        args: Vec<AnyValue>,
    ) -> Result<u32, String> {
        use fz_runtime::process::ProcessState;
        let pid = self.next_pid();
        let user_schemas = self.schemas();
        let mut child = Box::new(Process::new(user_schemas));
        child.pid = pid;
        child.atom_names = module.atom_names.clone();
        child.state = ProcessState::Ready;
        self.insert_task(pid, child);
        let image = fz_runtime::process::CURRENT_PROCESS
            .try_with(|current| {
                let proc_ptr = current.get();
                (!proc_ptr.is_null())
                    .then(|| unsafe { (*proc_ptr).pid })
                    .and_then(|parent_pid| self.task_code_image(parent_pid))
            })
            .ok()
            .flatten()
            .unwrap_or_else(|| std::rc::Rc::new(CodeImage::new(module)));
        self.set_task_code_image(pid, image);
        self.enqueue_resume(pid, (fn_id, args, vec![]));
        Ok(pid)
    }
}
