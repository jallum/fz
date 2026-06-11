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
//!   - HALT (entry fn returns / Term::Halt fires): trampoline returns
//!     null; worker transitions task to Exited.
//!   - (post-.19.3) RECEIVE BLOCK: fz_receive sets state = Blocked and
//!     returns a sentinel that breaks the trampoline. Worker stops; send
//!     (.19.3) transitions Blocked -> Ready and re-enqueues.
//!
//! For v1 we ship pool size 1 (no OS-thread pool yet). The worker loop
//! runs on the calling thread. When pool size > 1 lands:
//!   - run_queue becomes contended (currently a plain VecDeque; will
//!     wrap in Mutex when threads matter).
//!   - tasks registry: HashMap becomes RwLock<HashMap> or per-worker
//!     local + global registry.
//!   - Process needs Send (currently `Heap` holds Rc — will switch to
//!     Arc when threading lands).

use crate::fz_ir::{FnId, Module};
use crate::ir_codegen::{CompiledModule, PidId, Process, ProcessState};
use crate::ir_interp::make_resource_in_current_process;
use crate::telemetry::Telemetry;
#[cfg(test)]
use crate::telemetry::handler::{Event, Handler};
use crate::telemetry::value::opaque;
use fz_runtime::any_value::{AnyValue, AnyValueRef};
use fz_runtime::exec_ctx::{ExecCtx, timer_cancel};
use fz_runtime::heap::{Heap, deep_copy_any_value_ref};
use fz_runtime::park::materialize_outcome_closure;
use fz_runtime::pinned_abi::call2;
use fz_runtime::procbin::mso_drop_all_deferred;
use fz_runtime::sched::{fire_after_timer, mint_entry_thunk, mint_main_inner};
use fz_runtime::timer::TimerWheel;
#[cfg(test)]
use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::ptr::{null, null_mut};
#[cfg(test)]
use std::rc::Rc;
use std::slice::from_raw_parts;
use std::str::from_utf8;
use std::time::{Duration, Instant};

/// Task scheduler bound to a single CompiledModule. v1 is single-worker /
/// single-threaded — `run_until_idle` drives all spawned tasks to
/// completion on the calling thread.
pub struct Runtime<'a> {
    compiled: &'a CompiledModule,
    tasks: HashMap<PidId, Box<Process>>,
    run_queue: VecDeque<PidId>,
    next_pid: u32,
    /// fz-swt.10 — optional IR `Module` the `MakeResourceHook` thunk
    /// walks to resolve dtor closures. Set via `with_module(&m)` before
    /// `run_until_idle`. None means programs that call `make_resource`
    /// will panic with a clear "no module attached" message — fine for
    /// programs that don't use resources.
    module: Option<&'a Module>,

    /// fz-yxs/fz-st5 — sorted-vec timer wheel (F2). Stored inside the
    /// Runtime so per-Process `wait.after_deadline_ms` can be
    /// honoured via `dispatch_timer_schedule`; the run loop drains
    /// expired entries each iteration and emits ResumeMatched for the
    /// after-cont closure.
    pub(crate) timers: TimerWheel,

    /// Observability sink. The run loop emits `fz.runtime.process_exited`
    /// at each task exit (see `ExitRecord`), which is the seam tests observe
    /// instead of poking task internals.
    tel: &'a dyn Telemetry,
}

/// The facts observed when a task exits, projected from its `Process`. This is
/// the single place that reads `Process` internals for the
/// `fz.runtime.process_exited` event: the scalars become event measurements,
/// and a `ProcessExitCapture` reconstructs an `ExitRecord` from them. Sync
/// handlers needing a field this projection omits can downcast the event's
/// opaque `process` metadata directly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExitRecord {
    pub pid: PidId,
    pub halt_value: i64,
    pub live_count: usize,
    pub bytes_used: usize,
}

impl ExitRecord {
    pub fn project(pid: PidId, process: &Process) -> Self {
        Self {
            pid,
            halt_value: process.halt_value,
            live_count: process.heap.live_count(),
            bytes_used: process.heap.bytes_used(),
        }
    }

    /// The single emit site for `fz.runtime.process_exited`, shared by the
    /// compiled and interpreter schedulers so the event shape is identical
    /// across engines (durable measurements + opaque `&Process`).
    pub fn emit(tel: &dyn Telemetry, pid: PidId, process: &Process) {
        let exit = Self::project(pid, process);
        tel.execute(
            &["fz", "runtime", "process_exited"],
            &crate::measurements! {
                halt_value: exit.halt_value,
                live_count: exit.live_count as u64,
                bytes_used: exit.bytes_used as u64,
            },
            &crate::metadata! {
                pid: exit.pid as u64,
                process: opaque(process),
            },
        );
    }
}

/// fz-ul4.23.10 scheduler-hook thunks. These are the extern "C" fns the
/// runtime crate dispatches through when fz_spawn / fz_send fire from
/// JIT'd code. They translate the raw-u32 hook ABI back into the
/// FnId/PidId newtypes Runtime expects and call the existing impls.
extern "C" fn spawn_hook_thunk(sender: *mut Process, scheduler: *mut (), closure_bits: u64) -> u32 {
    spawn_closure_via(sender, scheduler, closure_bits)
}

extern "C" fn spawn_opt_hook_thunk(
    sender: *mut Process,
    scheduler: *mut (),
    closure_bits: u64,
    _min_heap_size: u32,
) -> u32 {
    spawn_closure_via(sender, scheduler, closure_bits)
}

extern "C" fn send_hook_thunk(sender: *mut Process, scheduler: *mut (), receiver_pid: u32, msg_ref_word: u64) {
    let msg_ref = AnyValueRef::from_raw_word(msg_ref_word).expect("send hook message ref");
    send_via(sender, scheduler, receiver_pid, msg_ref);
}

/// Output sink for `dbg`/print: the runtime's `emit_print_line` forwards each
/// rendered line through `ExecCtx.output` (per-context, set at scheduler entry)
/// with the context's telemetry sink. Emits it as `fz.runtime.dbg` — the
/// observation channel beside production stdout — engine-uniformly. `tel` is the
/// erased `&dyn Telemetry` the scheduler stored in the ExecCtx; null = no sink.
pub(crate) extern "C" fn output_hook_thunk(tel: *const (), line_ptr: *const u8, line_len: usize) {
    if tel.is_null() {
        return;
    }
    // ExecCtx.tel is `(&sink) as *const &dyn Telemetry` — a thin pointer to the
    // scheduler's `&dyn Telemetry`; deref it back to the fat reference.
    let tel: &dyn Telemetry = unsafe { *(tel as *const &dyn Telemetry) };
    let bytes = unsafe { from_raw_parts(line_ptr, line_len) };
    let line = from_utf8(bytes).unwrap_or("<non-utf8 dbg line>");
    tel.event(&["fz", "runtime", "dbg"], crate::metadata! { line: line });
}

// fz-swt.10 — `MakeResourceHook` installed by the binary so the runtime
// crate's `fz_make_resource` BIF (callable from JIT/AOT-emitted code) can
// resolve the user-supplied dtor closure. The thunk reads the IR Module
// pointer the binary stashed in `CURRENT_MODULE` (set/cleared with the
// same lifetime as the running task) and delegates to the shared helper
// in `ir_interp::make_resource_in_current_process`. The helper walks the
// closure's wrapper-fn body to find the underlying `Prim::Extern` and
// resolves its symbol — uniform across all three legs.
extern "C" fn make_resource_hook_thunk(
    process: *mut Process,
    module: *const (),
    payload_raw: u64,
    dtor_ref: u64,
) -> u64 {
    assert!(
        !module.is_null(),
        "fz_make_resource called with no IR Module in the execution context"
    );
    let module: &Module = unsafe { &*(module as *const Module) };
    let dtor_ref = AnyValueRef::from_raw_word(dtor_ref).expect("fz_make_resource: dtor ref");
    let payload = payload_raw as i64;
    let dtor = AnyValue::from_ref(dtor_ref).expect("fz_make_resource: dtor value");
    let res = make_resource_in_current_process(process, module, payload, dtor);
    match res {
        Ok(value) => value.ref_word().raw_word(),
        // Mirror the assertion/extern-error contract used elsewhere: a
        // resolution failure on the JIT/AOT path is unrecoverable (the
        // generated code expects a value back and has no error channel),
        // so we panic with a clear message rather than handing back NIL.
        Err(msg) => panic!("fz_make_resource: {}", msg),
    }
}

/// fz-yxs/fz-st5 — installed via `install_timer_schedule_hook`. Called
/// by `fz_receive_park_matched` when the after-clause carries a real
/// timeout. Routes through `CURRENT_RUNTIME`'s `TimerWheel`.
extern "C" fn timer_schedule_hook_thunk(scheduler: *mut (), pid: u32, after_ms: u64) -> u64 {
    let rt = unsafe { &mut *(scheduler as *mut Runtime<'static>) };
    rt.timers.schedule(pid, Duration::from_millis(after_ms))
}

extern "C" fn timer_cancel_hook_thunk(scheduler: *mut (), timer_id: u64) {
    if scheduler.is_null() {
        return;
    }
    let rt = unsafe { &mut *(scheduler as *mut Runtime<'static>) };
    rt.timers.cancel(timer_id);
}

/// fz-ul4.29.5: called from fz_spawn (runtime FFI) to enqueue a new task
/// from a closure. Deep-copies the closure into the new task's heap and
/// records it as a pending closure entry for the child task's next quantum.
/// Panics outside a running Runtime.
pub fn spawn_closure_via(sender: *mut Process, scheduler: *mut (), closure_bits: u64) -> PidId {
    assert!(
        !scheduler.is_null(),
        "spawn() called with no scheduler in the execution context"
    );
    let rt = unsafe { &mut *(scheduler as *mut Runtime<'static>) };
    rt.spawn_closure(sender, closure_bits)
}

/// fz-ul4.19.3: called from fz_send (ir_codegen.rs FFI) to deliver a
/// message. Deep-copies `msg` from the sender's heap (= current_process's
/// heap) into the receiver's heap, pushes to the receiver's mailbox, and
/// wakes the receiver if it was Blocked.
///
/// Sender and receiver are distinct Processes — the sender is currently
/// running (its Box<Process> has been taken OUT of the registry by
/// run_until_idle), the receiver is sitting in the registry. No borrow
/// conflict.
pub fn send_via(sender: *mut Process, scheduler: *mut (), receiver_pid: PidId, msg: AnyValueRef) {
    assert!(
        !scheduler.is_null(),
        "send() called with no scheduler in the execution context"
    );
    let rt = unsafe { &mut *(scheduler as *mut Runtime<'static>) };
    assert!(!sender.is_null(), "send() called with no sender process");
    let sender = unsafe { &mut *sender };
    if sender.pid == receiver_pid {
        // Self-send: sender is currently OUT of rt.tasks (run_until_idle
        // has it borrowed). We can't .get_mut from rt.tasks. Write
        // directly to the sender's mailbox.
        //
        // Deep-copy is still semantically required (a process sending
        // to itself should still observe the message as a fresh copy),
        // but src_heap == dst_heap == sender.heap. We can't borrow it
        // both ways at once; split borrows are fine because each
        // deep_copy_slot alloc is a self-contained &mut access.
        //
        // For self-send we use a single &mut borrow path: alloc into
        // the same heap. Since src and dst are the same heap, the
        // existing forwarding-pointer technique handles sharing.
        let mut forwarding: HashMap<*mut u8, *mut u8> = HashMap::new();
        // SAFETY: split the &mut Process into &Heap (for read) and
        // &mut Heap (for write). The pointers are aliased but Rust's
        // borrow checker can't see that the same Heap is both src and
        // dst. The deep_copy_slot impl doesn't mutate src; we use
        // distinct raw-pointer reads from src vs &mut writes through
        // dst. Equivalent to running deep_copy on a clone of the heap,
        // which would be correct.
        let heap_ptr: *mut Heap = &mut sender.heap as *mut _;
        let src_heap: &Heap = unsafe { &*heap_ptr };
        let dst_heap: &mut Heap = unsafe { &mut *heap_ptr };
        let copied = deep_copy_any_value_ref(msg, src_heap, dst_heap, &mut forwarding);
        sender.mailbox.push_back(copied);
        // No state transition needed: sender is Running.
        return;
    }
    let receiver = rt
        .tasks
        .get_mut(&receiver_pid)
        .unwrap_or_else(|| panic!("send: receiver pid {} not in task registry", receiver_pid));
    if receiver.wait.is_some() {
        let receiver_ptr: *mut Process = &mut **receiver;
        let hit = receiver
            .wait
            .as_ref()
            .and_then(|park| park.try_match(receiver_ptr, msg));
        match hit {
            Some((clause_idx, bound_vals)) => {
                let (template, timer_id) = {
                    let park = receiver.wait.as_ref().expect("checked above");
                    (park.clause_bodies[clause_idx], park.after_timer_id)
                };
                let mut forwarding: HashMap<*mut u8, *mut u8> = HashMap::new();
                let copied_bound_vals: Vec<AnyValueRef> = bound_vals
                    .into_iter()
                    .map(|v| deep_copy_any_value_ref(v, &sender.heap, &mut receiver.heap, &mut forwarding))
                    .collect();
                let cont = materialize_outcome_closure(&mut receiver.heap, template, &copied_bound_vals);
                receiver.wait = None;
                if let Some(id) = timer_id {
                    timer_cancel(receiver, id);
                }
                receiver.set_runnable_closure(cont);
                receiver.state = ProcessState::Ready;
                rt.run_queue.push_back(receiver_pid);
            }
            None => {
                let mut forwarding: HashMap<*mut u8, *mut u8> = HashMap::new();
                let copied = deep_copy_any_value_ref(msg, &sender.heap, &mut receiver.heap, &mut forwarding);
                receiver.mailbox.push_back(copied);
            }
        }
        return;
    }

    let mut forwarding: HashMap<*mut u8, *mut u8> = HashMap::new();
    let copied = deep_copy_any_value_ref(msg, &sender.heap, &mut receiver.heap, &mut forwarding);

    receiver.mailbox.push_back(copied);
    if receiver.state == ProcessState::Blocked {
        receiver.state = ProcessState::Ready;
        rt.run_queue.push_back(receiver_pid);
    }
}

impl<'a> Runtime<'a> {
    /// Create a Runtime bound to `compiled`. `workers` configures the pool
    /// size; v1 only supports 1 (panics otherwise so the limitation is
    /// loud, not silent).
    pub fn new(compiled: &'a CompiledModule, workers: usize, tel: &'a dyn Telemetry) -> Self {
        assert!(
            workers == 1,
            "v1 only supports pool size 1; multi-worker is a follow-up to fz-ul4.19.1"
        );
        Self {
            compiled,
            tasks: HashMap::new(),
            run_queue: VecDeque::new(),
            next_pid: 1,
            timers: TimerWheel::new(),
            module: None,
            tel,
        }
    }

    /// fz-swt.10 — attach the IR Module so the `MakeResourceHook` thunk
    /// can walk dtor closures during `make_resource(_, &name/arity)`
    /// calls. The Module must outlive `run_until_idle`.
    pub fn with_module(mut self, module: &'a Module) -> Self {
        self.module = Some(module);
        self
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
        process.state = ProcessState::Ready;
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
        self.tasks.insert(pid, Box::new(process));
        self.run_queue.push_back(pid);
        pid
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
        process.state = ProcessState::Ready;

        // Deep-copy the closure from sender's heap into the new task's heap.
        assert!(!sender.is_null(), "spawn_closure: no sender process");
        let sender = unsafe { &*sender };
        let mut forwarding: HashMap<*mut u8, *mut u8> = HashMap::new();
        let closure_ref = AnyValueRef::from_raw_word(closure_ref_word).expect("spawn_closure: closure ref");
        closure_ref
            .closure_addr()
            .expect("spawn_closure: closure must be a closure");
        let copied = deep_copy_any_value_ref(closure_ref, &sender.heap, &mut process.heap, &mut forwarding);
        let copied_addr = copied
            .closure_addr()
            .expect("spawn_closure: copied closure must be a closure");

        // Wrap the copied closure in an entry thunk and queue it as
        // `runnable`; the scheduler resumes it via `fz_resume` on the next
        // quantum. Insert into the task registry before queueing so a
        // cross-task send() during the new task's run can find this pid.
        process.next_frame = null_mut();
        let thunk = mint_entry_thunk(&mut process.heap, self.compiled.entry_thunk_addr, copied_addr);
        process.set_runnable_closure(thunk);
        // Scheduler scaffolding (entry thunk + copied entry closure) is
        // prepared before the child runs; reset so its alloc telemetry
        // measures only the child's own execution.
        process.heap.reset_alloc_stats();
        self.tasks.insert(pid, Box::new(process));
        self.run_queue.push_back(pid);
        pid
    }

    /// Drive ready tasks to completion (or to a yield point — once
    /// .19.3 adds receive). v1: no yield points, so this runs each task
    /// in turn until it halts.
    pub fn run_until_idle(&mut self) {
        // fz-ul4.19.2: install Runtime in TLS so fz_spawn (.19.2) and
        // future scheduler-bound FFI fns can reach back. Pointer is
        // This Runtime, erased to *mut () for the per-context dispatch table
        // below; the callbacks re-narrow it back to &mut Runtime.
        let self_ptr = self as *mut Runtime<'a> as *mut ();
        // The per-context dispatch table for this Runtime: the same scheduler
        // handle, telemetry sink, module, and callbacks installed above as
        // thread-globals, gathered into one value each task points its `ctx`
        // at. Lives on this stack frame, which outlives every quantum below.
        // Populated now; dispatch still reads the globals until the `fz-vdt`
        // arc moves each reader onto `process->ctx`.
        let mut exec_ctx = ExecCtx {
            scheduler: self_ptr,
            tel: (&self.tel) as *const &dyn Telemetry as *const (),
            module: self.module.map_or(null(), |m| m as *const _ as *const ()),
            spawn: Some(spawn_hook_thunk),
            spawn_opt: Some(spawn_opt_hook_thunk),
            send: Some(send_hook_thunk),
            output: Some(output_hook_thunk),
            make_resource: self.module.is_some().then_some(make_resource_hook_thunk),
            timer_schedule: Some(timer_schedule_hook_thunk),
            timer_cancel: Some(timer_cancel_hook_thunk),
        };
        let ctx_ptr: *mut ExecCtx = &mut exec_ctx;
        loop {
            // fz-yxs/fz-st5 — service any expired after-timers before
            // picking the next task. Cheaper to do here than on every
            // step inside run_quantum: timers only matter at scheduler
            // boundaries (a task can't park between expirations).
            self.drain_expired_timers();
            let Some(pid) = self.run_queue.pop_front() else {
                break;
            };
            let mut task = self.tasks.remove(&pid).expect("task in run_queue not in registry");
            task.state = ProcessState::Running;
            task.reset_reduction_budget();
            task.ctx = ctx_ptr;
            task.attach_heap_owner();
            debug_assert!(!task.ctx.is_null(), "task.ctx installed before dispatch");
            self.compiled.run_quantum(&mut task);
            // Possible post-quantum states (fz-ul4.19.3):
            //
            // 1. next_frame is null -> trampoline halted, task is done.
            //    Mark Exited; keep in registry for inspection.
            //
            // 2. next_frame non-null and state is Blocked -> task yielded
            //    on receive (fz_receive_attempt returned YIELD_PTR; the
            //    trampoline parked at the receive frame and set state =
            //    Blocked). Keep in registry; do NOT re-enqueue. A future
            //    send to this pid will flip state back to Ready and
            //    re-enqueue (via send_via_current_runtime).
            //
            // 3. next_frame non-null and state still Running -> yielded
            //    without explicit block. Closure-shaped mid-flight yield
            //    stores the continuation in `runnable`, which is the
            //    scheduler-owned primary root.
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
                task.state = ProcessState::Ready;
                self.tasks.insert(pid, task);
                self.run_queue.push_back(pid);
                continue;
            } else if task.next_frame.is_null() && task.wait.is_none() {
                // A pending `wait` means the task is suspended on receive,
                // not finished. Without this check the run loop would
                // mis-classify the receiver as Exited and never call its
                // initial-scan branch.
                task.state = ProcessState::Exited;
                task.quiet_quanta = task.quiet_quanta.saturating_add(1);
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
                ExitRecord::emit(self.tel, pid, &task);
            } else if task.state == ProcessState::Blocked {
                // Park: keep in registry, no re-enqueue. send() will
                // wake.
                task.quiet_quanta = task.quiet_quanta.saturating_add(1);
            } else if task.state == ProcessState::Ready {
                // Selective-receive park detected a pending message in our
                // own mailbox (self-send → receive); it set state=Ready so
                // the scheduler immediately re-runs the task through the
                // receive initial-scan path.
                task.quiet_quanta = task.quiet_quanta.saturating_add(1);
                self.tasks.insert(pid, task);
                self.run_queue.push_back(pid);
                continue;
            } else if task.state == ProcessState::Running {
                // Other cooperative yield (future builtin).
                task.quiet_quanta = task.quiet_quanta.saturating_add(1);
                task.state = ProcessState::Ready;
                self.tasks.insert(pid, task);
                self.run_queue.push_back(pid);
                continue;
            }
            // Keep Exited / Blocked tasks in the registry so callers can
            // inspect halt_value / mailbox after the runtime drains, and
            // so send() can find a Blocked receiver.
            self.tasks.insert(pid, task);
        }
    }

    /// fz-yxs/fz-st5 — drain expired timers and wake the matching
    /// parked tasks. Called by the run loop each iteration. For each
    /// expired entry whose pid is still parked on a Term::ReceiveMatched
    /// with that timer id, stash a runnable closure of the after-cont
    /// (no bound args; captures are already baked into the closure)
    /// and re-enqueue.
    pub(crate) fn drain_expired_timers(&mut self) {
        let now = Instant::now();
        let expired = self.timers.drain_expired(now);
        for entry in expired {
            let Some(task) = self.tasks.get_mut(&entry.pid) else {
                continue;
            };
            if fire_after_timer(task, entry.id) {
                self.run_queue.push_back(entry.pid);
            }
        }
    }

    /// Read-only access to a task (for tests / inspection).
    #[cfg(test)]
    pub fn task(&self, pid: PidId) -> Option<&Process> {
        self.tasks.get(&pid).map(|b| &**b)
    }

    /// fz-yxs/fz-st5 — test-only mutable accessor. Lets the unit tests
    /// in this module pre-seed a receiver with a `wait`
    /// record before driving the sender-probe path.
    #[cfg(test)]
    pub fn task_mut(&mut self, pid: PidId) -> Option<&mut Process> {
        self.tasks.get_mut(&pid).map(|b| &mut **b)
    }
}

/// Test seam: a telemetry handler that projects each `fz.runtime.process_exited`
/// event into an owned `ExitRecord` (read from the durable measurements). Tests
/// attach it to a `ConfiguredTelemetry`, run, then read the records — observing
/// the run instead of poking the `Process`.
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

    pub fn handler(&self) -> Box<dyn Handler> {
        Box::new(ProcessExitHandler {
            records: self.records.clone(),
        })
    }

    pub fn last(&self) -> Option<ExitRecord> {
        self.records.borrow().last().copied()
    }

    pub fn by_pid(&self, pid: PidId) -> Option<ExitRecord> {
        self.records.borrow().iter().copied().find(|record| record.pid == pid)
    }
}

/// Test seam: records the `fz.runtime.dbg` line stream. Attach to a
/// `ConfiguredTelemetry`, run, then read `lines()` — the telemetry-based
/// replacement for the old `TEST_CAPTURE` print buffer. Works for both
/// engines, since both route output through `route_output_to`.
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

    pub fn handler(&self) -> Box<dyn Handler> {
        Box::new(DbgHandler {
            lines: self.lines.clone(),
        })
    }

    pub fn lines(&self) -> Vec<String> {
        self.lines.borrow().clone()
    }
}

#[cfg(test)]
struct DbgHandler {
    lines: Rc<RefCell<Vec<String>>>,
}

#[cfg(test)]
impl Handler for DbgHandler {
    fn handle(&self, ev: &Event<'_, '_, '_>) {
        use crate::telemetry::value::Value;
        if ev.name != ["fz", "runtime", "dbg"] {
            return;
        }
        if let Some(Value::Str(s)) = ev.metadata.get("line") {
            self.lines.borrow_mut().push(s.as_ref().to_string());
        }
    }
}

#[cfg(test)]
struct ProcessExitHandler {
    records: Rc<RefCell<Vec<ExitRecord>>>,
}

#[cfg(test)]
impl Handler for ProcessExitHandler {
    fn handle(&self, ev: &Event<'_, '_, '_>) {
        use crate::telemetry::value::Value;
        if ev.name != ["fz", "runtime", "process_exited"] {
            return;
        }
        let pid = match ev.metadata.get("pid") {
            Some(Value::U64(v)) => *v as PidId,
            _ => 0,
        };
        let halt_value = match ev.measurements.get("halt_value") {
            Some(Value::I64(v)) => *v,
            _ => 0,
        };
        let live_count = match ev.measurements.get("live_count") {
            Some(Value::U64(v)) => *v as usize,
            _ => 0,
        };
        let bytes_used = match ev.measurements.get("bytes_used") {
            Some(Value::U64(v)) => *v as usize,
            _ => 0,
        };
        self.records.borrow_mut().push(ExitRecord {
            pid,
            halt_value,
            live_count,
            bytes_used,
        });
    }
}

#[cfg(test)]
#[path = "runtime_test.rs"]
mod runtime_test;
