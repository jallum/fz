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
use fz_runtime::heap::{AddressMap, deep_copy_any_value_ref};
use fz_runtime::output::{OUTPUT_HOOK, OutputContext, OutputSink, STDOUT_OUTPUT};
use fz_runtime::pinned_abi::call2;
use fz_runtime::process::Disposition;
use fz_runtime::sched::{
    ProbeOutcome, deliver_in_queue, fire_after_timer, mint_entry_thunk, mint_main_inner, probe_sender, self_send,
};
use fz_runtime::sched_core::{
    Scheduler, SchedulingCore, end_quantum, halt_hook, next_runnable, timer_cancel_hook, timer_schedule_hook,
};
use fz_runtime::telemetry::{
    EXECUTION_READY, GC, PROCESS_EXITED, RAISE, RUN_ENDED, Raise, RunEnded, RuntimeEvent, SCHEDULER_SLEPT, SEND_PROBE,
};
use fz_runtime::timer::TimerId;
#[cfg(test)]
use std::cell::RefCell;
use std::collections::HashMap;
use std::ptr::null_mut;
#[cfg(test)]
use std::rc::Rc;

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
    /// at each task exit, which is the seam tests observe
    /// instead of poking task internals.
    tel: &'a T,
    output: &'a dyn OutputSink,
    argv: &'a Argv,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExitRecord {
    pub pid: PidId,
    pub halt_value: i64,
    pub live_count: usize,
    pub bytes_used: usize,
    pub list_retention_attempts: u64,
    pub list_retention_hits: u64,
    pub raises_delivered: u64,
    pub reduction_yields: u64,
    pub failed: bool,
    pub dtors_dispatched: u64,
}

/// Raise `event` on the telemetry bus as the typed raw event hosts attach to.
pub fn emit_runtime_event<T: Telemetry + ?Sized>(tel: &T, event: RuntimeEvent<'_>) {
    match event {
        RuntimeEvent::ExecutionReady => tel.raw_event0(&EXECUTION_READY),
        RuntimeEvent::ProcessExited(process) => tel.raw_event2(&PROCESS_EXITED, &process.pid, process),
        RuntimeEvent::SchedulerSlept(wait) => tel.raw_event1(&SCHEDULER_SLEPT, &wait),
        RuntimeEvent::SendProbe(probe) => tel.raw_event1(&SEND_PROBE, probe),
        RuntimeEvent::Raise(raise) => tel.raw_event1(&RAISE, raise),
        RuntimeEvent::Gc(collection) => tel.raw_event1(&GC, collection),
        RuntimeEvent::RunEnded(ended) => tel.raw_event1(&RUN_ENDED, &ended),
    }
}

/// The raise hook of a compiled run: every raise becomes a `fz.runtime.raise`
/// event on the runtime's telemetry.
unsafe extern "C" fn raise_hook_thunk<T: Telemetry + ?Sized>(
    scheduler: *mut (),
    kind: *const u8,
    kind_len: usize,
    name: *const u8,
    name_len: usize,
    depth: usize,
    stack_bytes: usize,
) {
    let rt = unsafe { &*(scheduler as *mut Runtime<'_, T>) };
    let record = unsafe { Raise::from_hook_args(kind, kind_len, name, name_len, depth, stack_bytes) };
    emit_runtime_event(rt.tel, RuntimeEvent::Raise(&record));
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
    emit_runtime_event(rt.tel, RuntimeEvent::SendProbe(&probe));
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

    /// The status the program ended with, once it has halted: a process called
    /// `System.halt/1`, or the main process ended. `None` for a run that went
    /// idle without halting.
    pub fn halted(&self) -> Option<i32> {
        self.core.halted()
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
        let mut forwarding = AddressMap::default();
        let closure_ref = AnyValueRef::from_raw_word(closure_ref_word).expect("spawn_closure: closure ref");
        closure_ref
            .closure_addr()
            .expect("spawn_closure: closure must be a closure");
        let copied = deep_copy_any_value_ref(closure_ref, &sender.heap.view(), &mut process.heap, &mut forwarding);
        copied
            .closure_addr()
            .expect("spawn_closure: copied closure must be a closure");

        // Wrap the copied closure in an entry thunk and queue it as
        // `runnable`; the scheduler resumes it via `fz_resume` on the next
        // quantum. The registry holds the child before it runs so a
        // cross-task send() during its quantum can find this pid.
        process.next_frame = null_mut();
        let thunk = mint_entry_thunk(&mut process.heap, self.compiled.entry_thunk_addr, copied);
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
            halt: Some(halt_hook::<Self>()),
            raise: Some(raise_hook_thunk::<T>),
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
            match end_quantum(self, &mut task) {
                Disposition::Requeue => {
                    self.queue_task(pid, task);
                    continue;
                }
                // Parked on a receive: keep in registry, no re-enqueue. A send
                // or the after-timer wakes it.
                Disposition::Parked | Disposition::Exited => {}
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
        emit_runtime_event(
            self.tel,
            RuntimeEvent::RunEnded(RunEnded::sample(self.pool_outstanding_before_run)),
        );
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

    fn observe(&mut self, event: RuntimeEvent<'_>) {
        emit_runtime_event(self.tel, event);
    }

    /// Enter the destructor through `pinned_abi` so the pinned register holds
    /// this process: the destructor is real fz code and its closure BIFs
    /// (alloc_closure, ...) read the process from the pinned
    /// register, like every other scheduler-facing entry.
    fn run_destructor(&mut self, process: &mut Process, closure: u64, payload: u64) {
        let process: *mut Process = process;
        let _ = unsafe { call2(self.compiled.drain_dtor_entry_addr, process, closure, payload) };
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
                    raises_delivered: process.raises_delivered,
                    reduction_yields: process.reduction_yields,
                    failed: process.ended_in_failure(),
                    dtors_dispatched: process.dtors_dispatched,
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

/// Collects the bytes a program prints. The sink is a byte sink, so `lines()`
/// is a view: the received bytes split on `\n`, a trailing partial line being
/// an entry of its own.
#[cfg(test)]
pub struct DbgCapture {
    bytes: Rc<RefCell<Vec<u8>>>,
}

#[cfg(test)]
impl DbgCapture {
    pub fn new() -> Self {
        Self {
            bytes: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub fn sink(&self) -> Box<dyn OutputSink> {
        Box::new(DbgSink {
            bytes: self.bytes.clone(),
        })
    }

    pub fn lines(&self) -> Vec<String> {
        let bytes = self.bytes.borrow();
        String::from_utf8_lossy(&bytes)
            .split_terminator('\n')
            .map(str::to_string)
            .collect()
    }
}

#[cfg(test)]
impl OutputSink for DbgCapture {
    fn emit(&self, bytes: &[u8]) {
        self.bytes.borrow_mut().extend_from_slice(bytes);
    }
}

#[cfg(test)]
struct DbgSink {
    bytes: Rc<RefCell<Vec<u8>>>,
}

#[cfg(test)]
impl OutputSink for DbgSink {
    fn emit(&self, bytes: &[u8]) {
        self.bytes.borrow_mut().extend_from_slice(bytes);
    }
}

#[cfg(test)]
#[path = "runtime_test.rs"]
mod runtime_test;
