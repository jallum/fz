//! fz-ul4.19.1 — Runtime + Worker pool + task scheduler.
//!
//! Concurrency model: libdispatch-style. Many fz processes (tasks)
//! serviced by a small native worker pool. Pool size for v1 ships at 1
//! (a single-threaded scheduler loop on the calling thread); the API
//! shape assumes task != thread so going to N>1 is a Scheduler-internals
//! change, not an architectural rewrite.
//!
//! A Process (defined in ir_codegen.rs by fz-ul4.11.32) is the task; the
//! Runtime owns each Process via `Box<Process>` in a registry. spawn()
//! creates a fresh Process bound to a CompiledModule and enqueues its
//! pid. `run_until_idle()` drains the ready queue.
//!
//! Yield points in v1:
//!   - HALT (entry fn returns, or the process fails): trampoline returns
//!     null; worker transitions task to Exited.
//!   - (post-.19.3) RECEIVE BLOCK: fz_receive sets state = Blocked and
//!     returns a sentinel that breaks the trampoline. Worker stops; send
//!     (.19.3) transitions Blocked -> Ready and re-enqueues.
//!
//! For v1 we ship pool size 1 (no OS-thread pool yet). The worker loop
//! runs on the calling thread. When pool size > 1 lands:
//!   - the core's run queue becomes contended (currently a plain VecDeque; will
//!     wrap in Mutex when threads matter).
//!   - tasks registry: HashMap becomes RwLock<HashMap> or per-worker
//!     local + global registry.
//!   - Process needs Send (currently `Heap` holds Rc — will switch to
//!     Arc when threading lands).

use crate::fz_ir::FnId;
use crate::ir_codegen::{CompiledModule, PidId, Process, ProcessState};
use crate::telemetry::{Telemetry, TelemetryExt as _};
use fz_runtime::any_value::AnyValueRef;
use fz_runtime::exec_ctx::{Argv, ExecCtx, NO_ARGV};
use fz_runtime::heap::deep_copy_any_value_ref;
use fz_runtime::output::{OUTPUT_HOOK, OutputContext, OutputSink, STDOUT_OUTPUT};
use fz_runtime::pinned_abi::call2;
use fz_runtime::procbin::mso_drop_all_deferred;
use fz_runtime::sched::{
    ProbeOutcome, SendProbe, deliver_in_queue, fire_after_timer, mint_entry_thunk, mint_main_inner, probe_sender,
    self_send,
};
use fz_runtime::sched_core::{Scheduler, SchedulingCore, next_runnable, timer_cancel_hook, timer_schedule_hook};
use fz_runtime::timer::TimerId;
#[cfg(test)]
use std::cell::RefCell;
use std::collections::HashMap;
use std::ptr::null_mut;
#[cfg(test)]
use std::rc::Rc;
use std::time::Duration;

/// Task scheduler bound to a single CompiledModule. v1 is single-worker /
/// single-threaded — `run_until_idle` drives all spawned tasks to
/// completion on the calling thread.
pub struct Runtime<'a, T: Telemetry + ?Sized> {
    compiled: &'a CompiledModule,
    tasks: HashMap<PidId, Box<Process>>,
    /// The run queue and timer wheel. `next_runnable` decides what runs next
    /// and when the runtime is idle.
    core: SchedulingCore,
    next_pid: u32,
    pool_outstanding_before_run: usize,

    /// Observability sink. The run loop emits `fz.runtime.process_exited`
    /// at each task exit (see `ExitRecord`), which is the seam tests observe
    /// instead of poking task internals.
    tel: &'a T,
    output: &'a dyn OutputSink,
    argv: &'a Argv,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExitRecord {
    pub pid: PidId,
    pub halt_value: i64,
    pub live_count: usize,
    pub bytes_used: usize,
    pub list_retention_attempts: u64,
    pub list_retention_hits: u64,
    pub failed: bool,
}

impl ExitRecord {
    pub fn emit<T: Telemetry + ?Sized>(tel: &T, pid: &PidId, process: &Process) {
        tel.raw_event2(&["fz", "runtime", "process_exited"], pid, process);
    }
}

/// Emitted each time the scheduling core sleeps for a pending timer; carries
/// the `Duration` it is about to wait.
pub const SCHEDULER_SLEPT: [&str; 3] = ["fz", "runtime", "scheduler_slept"];

/// What the block pool holds once a run has torn down every process.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RunEnded {
    /// Blocks handed out and not returned when the run began. The compiler's
    /// own heaps live on the same thread, so this is never zero.
    pub pool_outstanding_before_run: usize,
    /// The same count once every process has been torn down. Equal to
    /// `pool_outstanding_before_run` means the run returned every block it took.
    pub pool_outstanding_after_run: usize,
    /// Blocks resting in the pool's free lists.
    pub pool_cached_blocks: usize,
}

/// Emitted once per run, after every process has been torn down, on the JIT
/// and interpreter paths; carries the `RunEnded` pool census.
pub const RUN_ENDED: [&str; 3] = ["fz", "runtime", "run_ended"];

/// Report the pool census at the end of a run.
pub fn emit_run_ended<T: Telemetry + ?Sized>(tel: &T, pool_outstanding_before_run: usize) {
    tel.raw_event1(
        &RUN_ENDED,
        &RunEnded {
            pool_outstanding_before_run,
            pool_outstanding_after_run: fz_runtime::heap::pool_outstanding_blocks(),
            pool_cached_blocks: fz_runtime::heap::pool_total_cached_blocks(),
        },
    );
}

/// Emitted once per cross-process send on the JIT and interpreter paths;
/// carries the `SendProbe` the sender's probe produced.
pub const SEND_PROBE: [&str; 4] = ["fz", "runtime", "send", "probe"];

/// Report one send's probe on the telemetry bus.
pub fn emit_send_probe<T: Telemetry + ?Sized>(tel: &T, probe: &SendProbe) {
    tel.raw_event1(&SEND_PROBE, probe);
}

/// fz-ul4.23.10 scheduler-hook thunks. These are the extern "C" fns the
/// runtime crate dispatches through when fz_spawn / fz_send fire from
/// JIT'd code. They translate the raw-u32 hook ABI back into the
/// FnId/PidId newtypes Runtime expects and call the existing impls.
extern "C" fn spawn_hook_thunk<T: Telemetry + ?Sized>(
    sender: *mut Process,
    scheduler: *mut (),
    closure_bits: u64,
) -> u32 {
    spawn_closure_via::<T>(sender, scheduler, closure_bits)
}

extern "C" fn send_hook_thunk<T: Telemetry + ?Sized>(
    sender: *mut Process,
    scheduler: *mut (),
    receiver_pid: u32,
    msg_ref_word: u64,
) {
    let msg_ref = AnyValueRef::from_raw_word(msg_ref_word).expect("send hook message ref");
    send_via::<T>(sender, scheduler, receiver_pid, msg_ref);
}

/// fz-ul4.29.5: called from fz_spawn (runtime FFI) to enqueue a new task
/// from a closure. Deep-copies the closure into the new task's heap and
/// records it as a pending closure entry for the child task's next quantum.
/// Panics outside a running Runtime.
pub fn spawn_closure_via<T: Telemetry + ?Sized>(sender: *mut Process, scheduler: *mut (), closure_bits: u64) -> PidId {
    assert!(
        !scheduler.is_null(),
        "spawn() called with no scheduler in the execution context"
    );
    let rt = unsafe { &mut *(scheduler as *mut Runtime<'_, T>) };
    rt.spawn_closure(sender, closure_bits)
}

/// fz-ul4.19.3: called from fz_send (ir_codegen.rs FFI) to deliver a
/// message. Deep-copies `msg` from the sender's heap (= current_process's
/// heap) into the receiver's heap and hands it to `sched::probe_sender`, which
/// mailboxes it and wakes the receiver when it completes the receive the
/// receiver is waiting on.
///
/// Sender and receiver are distinct Processes — the sender is currently
/// running (its Box<Process> has been taken OUT of the registry by
/// run_until_idle), the receiver is sitting in the registry. No borrow
/// conflict. The sender matches and copies on its own heap and queues the
/// gift on the receiver; the receiver's heap is untouched until it runs.
pub fn send_via<T: Telemetry + ?Sized>(
    sender: *mut Process,
    scheduler: *mut (),
    receiver_pid: PidId,
    msg: AnyValueRef,
) {
    assert!(
        !scheduler.is_null(),
        "send() called with no scheduler in the execution context"
    );
    let rt = unsafe { &mut *(scheduler as *mut Runtime<'_, T>) };
    assert!(!sender.is_null(), "send() called with no sender process");
    let sender = unsafe { &mut *sender };
    if sender.pid == receiver_pid {
        self_send(sender, msg);
        return;
    }
    let Some(receiver) = rt.tasks.get_mut(&receiver_pid) else {
        return;
    };
    if receiver.state == ProcessState::Exited {
        return;
    }
    let probe = probe_sender(sender, receiver, msg);
    emit_send_probe(rt.tel, &probe);
    if probe.outcome == ProbeOutcome::Hit {
        rt.core.make_runnable(receiver_pid, &mut receiver.state);
    }
}

impl<'a, T: Telemetry + ?Sized> Runtime<'a, T> {
    /// Create a Runtime bound to `compiled`. `workers` configures the pool
    /// size; v1 only supports 1 (panics otherwise so the limitation is
    /// loud, not silent).
    pub fn new(compiled: &'a CompiledModule, workers: usize, tel: &'a T) -> Self {
        assert!(
            workers == 1,
            "v1 only supports pool size 1; multi-worker is a follow-up to fz-ul4.19.1"
        );
        Self {
            compiled,
            tasks: HashMap::new(),
            core: SchedulingCore::new(),
            next_pid: 1,
            pool_outstanding_before_run: fz_runtime::heap::pool_outstanding_blocks(),
            tel,
            output: &STDOUT_OUTPUT,
            argv: &NO_ARGV,
        }
    }

    pub fn with_output(mut self, output: &'a dyn OutputSink) -> Self {
        self.output = output;
        self
    }

    /// The command line `System.argv/0` reads for every task this runtime runs.
    pub fn with_argv(mut self, argv: &'a Argv) -> Self {
        self.argv = argv;
        self
    }

    /// Whether the task `pid` failed. Exited tasks stay in the registry, so a
    /// driver reads this after `run_until_idle` to give a failed main process
    /// its exit status.
    pub fn failed(&self, pid: PidId) -> bool {
        self.tasks.get(&pid).is_some_and(|task| task.failed)
    }

    /// Spawn a new task that begins execution at `fn_id` (which must take
    /// zero entry params — the typical "main" shape for v1). Returns the
    /// fresh pid. The task is enqueued immediately; `run_until_idle()`
    /// will drive it.
    pub fn spawn(&mut self, fn_id: FnId) -> PidId {
        // Every fn is Tail-CC, including main. Make the entry a closure: mint
        // a synthetic inner closure carrying the raw `(cont)` main fp (via
        // `fz_main_trampoline`), wrap it in an entry thunk, and queue that as
        // `runnable`. The scheduler resumes it through the one `fz_resume`
        // verb — the same path a spawned user closure takes.
        let pid = self.next_pid;
        self.next_pid += 1;
        let mut process = self.compiled.make_process();
        process.pid = pid;
        let fp = self
            .compiled
            .fn_ptr(fn_id)
            .unwrap_or_else(|| panic!("no fn ptr for entry {}", fn_id.0));
        let halt_kind = self.compiled.fn_halt_kinds.get(&fn_id.0).copied().unwrap_or(0) as u16;
        let inner = mint_main_inner(&mut process.heap, self.compiled.main_trampoline_addr, fp, halt_kind);
        let thunk = mint_entry_thunk(&mut process.heap, self.compiled.entry_thunk_addr, inner);
        process.set_runnable_closure(thunk);
        // The entry thunk + inner are scheduler scaffolding prepared before
        // the task's own code runs; reset so alloc telemetry measures only the
        // task's execution (and matches the raw-fp entry's zero-alloc start).
        process.heap.reset_alloc_stats();
        self.queue_task(pid, Box::new(process));
        pid
    }

    /// Queue `task` to run and keep it in the registry under `pid`; the
    /// scheduling core performs its transition to Ready.
    fn queue_task(&mut self, pid: PidId, mut task: Box<Process>) {
        self.core.make_runnable(pid, &mut task.state);
        self.tasks.insert(pid, task);
    }

    /// fz-ul4.29.5: spawn a task from a closure value owned by the
    /// currently-running process. Deep-copies the closure into the new
    /// task's heap, then stores it as a pending entry. The scheduler later
    /// dispatches that closure via fz_spawn_entry in the child task's quantum.
    pub fn spawn_closure(&mut self, sender: *mut Process, closure_ref_word: u64) -> PidId {
        let pid = self.next_pid;
        self.next_pid += 1;
        let mut process = self.compiled.make_process();
        process.pid = pid;

        // Deep-copy the closure from sender's heap into the new task's heap.
        assert!(!sender.is_null(), "spawn_closure: no sender process");
        let sender = unsafe { &*sender };
        let mut forwarding: HashMap<*mut u8, *mut u8> = HashMap::new();
        let closure_ref = AnyValueRef::from_raw_word(closure_ref_word).expect("spawn_closure: closure ref");
        closure_ref
            .closure_addr()
            .expect("spawn_closure: closure must be a closure");
        let copied = deep_copy_any_value_ref(closure_ref, &sender.heap.view(), &mut process.heap, &mut forwarding);
        let copied_addr = copied
            .closure_addr()
            .expect("spawn_closure: copied closure must be a closure");

        // Wrap the copied closure in an entry thunk and queue it as
        // `runnable`; the scheduler resumes it via `fz_resume` on the next
        // quantum. The registry holds the child before it runs so a
        // cross-task send() during its quantum can find this pid.
        process.next_frame = null_mut();
        let thunk = mint_entry_thunk(&mut process.heap, self.compiled.entry_thunk_addr, copied_addr);
        process.set_runnable_closure(thunk);
        // Scheduler scaffolding (entry thunk + copied entry closure) is
        // prepared before the child runs; reset so its alloc telemetry
        // measures only the child's own execution.
        process.heap.reset_alloc_stats();
        self.queue_task(pid, Box::new(process));
        pid
    }

    /// Drive ready tasks until every task has halted or blocked.
    pub fn run_until_idle(&mut self) {
        // This Runtime is erased into the per-context dispatch table; its
        // callbacks re-narrow the handle to &mut Runtime.
        let self_ptr = self as *mut Runtime<'a, T> as *mut ();
        // Each task points at this stack-scoped dispatch table for the whole
        // quantum; no callback retains it.
        let output = OutputContext::new(self.output);
        let mut exec_ctx = ExecCtx {
            scheduler: self_ptr,
            output_context: output.as_ptr(),
            spawn: Some(spawn_hook_thunk::<T>),
            send: Some(send_hook_thunk::<T>),
            fault: Some(fz_runtime::failure::STDERR_FAULT_HOOK),
            output: Some(OUTPUT_HOOK),
            timer_schedule: Some(timer_schedule_hook::<Self>()),
            timer_cancel: Some(timer_cancel_hook::<Self>()),
            argv: self.argv,
        };
        let ctx_ptr: *mut ExecCtx = &mut exec_ctx;
        while let Some(pid) = next_runnable(self) {
            let mut task = self.tasks.remove(&pid).expect("task in run_queue not in registry");
            task.state = ProcessState::Running;
            task.reset_reduction_budget();
            task.ctx = ctx_ptr;
            debug_assert!(!task.ctx.is_null(), "task.ctx installed before dispatch");
            // Gifts queued by senders become this heap's before any code
            // runs; a matched receive becomes the runnable closure here.
            deliver_in_queue(&mut task);
            self.compiled.run_quantum(&mut task);
            // After a quantum the task is in one of three states: still
            // Running with a continuation in `runnable` (a mid-flight
            // yield), Blocked on a receive that found nothing, or halted.
            if task.state == ProcessState::Running && task.runnable.is_some() {
                // Closure-shaped mid-flight yield: the continuation closure
                // captures live loop state and is the primary GC root.
                task.boundary_maintenance::<()>(|p| {
                    let mut root = p.runnable_ptr();
                    p.heap.gc_process_roots(&mut root, &mut p.mailbox);
                    p.set_runnable_closure(root);
                    Ok(())
                })
                .expect("compiled boundary maintenance is infallible");
                self.queue_task(pid, task);
                continue;
            } else if task.state == ProcessState::Blocked {
                // Parked on a receive: keep in registry, no re-enqueue. A
                // send or the after-timer wakes it.
            } else if task.next_frame.is_null() {
                task.state = ProcessState::Exited;
                // fz-4mk.3a — task is exiting; before the Heap drops at
                // task-cleanup time, flush surviving MSO resources onto
                // `pending_dtors` and dispatch each dtor closure body as
                // real fz code through the `fz_drain_dtor_entry` shim. The dtor
                // body reaches this process through the pinned register set by
                // the `pinned_abi::call2` entry below.
                let ptr: *mut Process = &mut *task;
                mso_drop_all_deferred(&mut task.heap);
                // Enter the dtor body through pinned_abi so the pinned register
                // holds this process: the dtor is real fz code and its closure
                // BIFs (alloc_closure, get_halt_cont, …) read the process from
                // the pinned register, like every other scheduler-facing entry.
                let drain_addr = self.compiled.drain_dtor_entry_addr;
                while let Some((closure, payload_ref)) = task.heap.pending_dtors.pop_front() {
                    let payload_tag = AnyValueRef::from_raw_word(payload_ref)
                        .expect("pending dtor payload should be a valid value ref")
                        .tag();
                    assert_eq!(
                        payload_tag,
                        fz_runtime::any_value::ValueKind::INT,
                        "pending dtor payload should stay boxed as an integer ref",
                    );
                    let _ = unsafe { call2(drain_addr, ptr, closure, payload_ref) };
                }
                ExitRecord::emit(self.tel, &pid, &task);
            } else if task.state == ProcessState::Running {
                // Other cooperative yield (future builtin).
                self.queue_task(pid, task);
                continue;
            }
            // Keep Exited / Blocked tasks in the registry so callers can
            // inspect halt_value / mailbox after the runtime drains, and
            // so send() can find a Blocked receiver.
            self.tasks.insert(pid, task);
        }
    }
}

impl<T: Telemetry + ?Sized> Drop for Runtime<'_, T> {
    /// The registry keeps exited and parked tasks until the runtime goes
    /// away; drop them all, then report what the pool still holds.
    fn drop(&mut self) {
        self.tasks.clear();
        emit_run_ended(self.tel, self.pool_outstanding_before_run);
    }
}

impl<T: Telemetry + ?Sized> Scheduler for Runtime<'_, T> {
    fn core(&mut self) -> &mut SchedulingCore {
        &mut self.core
    }

    fn wake_expired(&mut self, pid: PidId, timer: TimerId) {
        if let Some(task) = self.tasks.get_mut(&pid)
            && fire_after_timer(task, timer)
        {
            self.core.make_runnable(pid, &mut task.state);
        }
    }

    fn about_to_sleep(&mut self, wait: Duration) {
        self.tel.raw_event1(&SCHEDULER_SLEPT, &wait);
    }
}

#[cfg(test)]
pub struct ProcessExitCapture {
    records: Rc<RefCell<Vec<ExitRecord>>>,
}

#[cfg(test)]
impl ProcessExitCapture {
    pub fn new() -> Self {
        Self {
            records: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub fn install(&self, telemetry: &crate::telemetry::ConfiguredTelemetry) {
        let records = Rc::clone(&self.records);
        telemetry.attach_raw_event2::<PidId, Process, _>(
            &["fz", "runtime", "process_exited"],
            move |_, _, _, pid, process| {
                records.borrow_mut().push(ExitRecord {
                    pid: *pid,
                    halt_value: process.halt_value,
                    live_count: process.heap.live_count(),
                    bytes_used: process.heap.bytes_used(),
                    list_retention_attempts: process.list_retention_attempts,
                    list_retention_hits: process.list_retention_hits,
                    failed: process.failed,
                });
            },
        );
    }

    pub fn by_pid(&self, pid: PidId) -> Option<ExitRecord> {
        self.records.borrow().iter().copied().find(|record| record.pid == pid)
    }

    pub fn last(&self) -> Option<ExitRecord> {
        self.records.borrow().last().copied()
    }
}

#[cfg(test)]
pub struct DbgCapture {
    lines: Rc<RefCell<Vec<String>>>,
}

#[cfg(test)]
impl DbgCapture {
    pub fn new() -> Self {
        Self {
            lines: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub fn sink(&self) -> Box<dyn OutputSink> {
        Box::new(DbgSink {
            lines: self.lines.clone(),
        })
    }

    pub fn lines(&self) -> Vec<String> {
        self.lines.borrow().clone()
    }
}

#[cfg(test)]
impl OutputSink for DbgCapture {
    fn emit(&self, bytes: &[u8]) {
        self.lines
            .borrow_mut()
            .push(std::str::from_utf8(bytes).unwrap_or("<non-utf8 dbg line>").to_string());
    }
}

#[cfg(test)]
struct DbgSink {
    lines: Rc<RefCell<Vec<String>>>,
}

#[cfg(test)]
impl OutputSink for DbgSink {
    fn emit(&self, bytes: &[u8]) {
        self.lines
            .borrow_mut()
            .push(std::str::from_utf8(bytes).unwrap_or("<non-utf8 dbg line>").to_string());
    }
}

#[cfg(test)]
#[path = "runtime_test.rs"]
mod runtime_test;
