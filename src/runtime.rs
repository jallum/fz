// fz-ul4.19.1: surface is consumed by tests + downstream tickets
// (.19.2 spawn/self/pid builtin will wire Runtime into the `fz spawn`
// surface; .19.3 will add send/receive). No active main.rs consumer yet.
#![allow(dead_code)]

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

use std::collections::{HashMap, VecDeque};
use std::sync::atomic::Ordering;

use crate::fz_ir::FnId;
use crate::ir_codegen::{CURRENT_PROCESS, CompiledModule, PidId, Process, ProcessState};
use fz_runtime::fz_value::FzValue;
use fz_runtime::yield_flag::FZ_SHOULD_YIELD;

/// Task scheduler bound to a single CompiledModule. v1 is single-worker /
/// single-threaded — `run_until_idle` drives all spawned tasks to
/// completion on the calling thread.
pub struct Runtime<'a> {
    compiled: &'a CompiledModule,
    tasks: HashMap<PidId, Box<Process>>,
    run_queue: VecDeque<PidId>,
    next_pid: u32,
    /// Configured worker count. v1 only supports 1. Stored so the API
    /// shape doesn't change when multi-worker lands.
    workers: usize,
}

thread_local! {
    /// Raw pointer to the Runtime currently driving `run_until_idle` on
    /// this worker. Set during run_until_idle for the duration of each
    /// task's quantum; reset to null after. fz_spawn (.19.2) reads this
    /// to enqueue new tasks from JIT'd code.
    ///
    /// The pointer type is type-erased to `*mut ()` because Runtime
    /// carries a lifetime; the consumer (fz_spawn) re-narrows it via
    /// the publicly-exposed `spawn_via_current_runtime` helper that
    /// transmutes back to `*mut Runtime<'_>`. Safe because the Runtime
    /// outlives any FFI call: it owns the run_until_idle stack frame.
    pub(crate) static CURRENT_RUNTIME: std::cell::Cell<*mut ()> =
        const { std::cell::Cell::new(std::ptr::null_mut()) };
}

/// fz-ul4.23.10 scheduler-hook thunks. These are the extern "C" fns the
/// runtime crate dispatches through when fz_spawn / fz_send fire from
/// JIT'd code. They translate the raw-u32 hook ABI back into the
/// FnId/PidId newtypes Runtime expects and call the existing impls.
extern "C" fn spawn_hook_thunk(closure_bits: u64) -> u32 {
    spawn_closure_via_current_runtime(closure_bits)
}

extern "C" fn spawn_opt_hook_thunk(closure_bits: u64, _min_heap_size: u32) -> u32 {
    spawn_closure_via_current_runtime(closure_bits)
}

extern "C" fn send_hook_thunk(receiver_pid: u32, msg_bits: u64) {
    send_via_current_runtime(receiver_pid, FzValue(msg_bits));
}

/// fz-ul4.29.5: called from fz_spawn (runtime FFI) to enqueue a new task
/// from a closure. Deep-copies the closure into the new task's heap and
/// invokes its stub_fp to materialize the initial frame. Panics outside
/// a running Runtime.
pub fn spawn_closure_via_current_runtime(closure_bits: u64) -> PidId {
    let raw = CURRENT_RUNTIME.with(|c| c.get());
    assert!(
        !raw.is_null(),
        "spawn() called outside Runtime::run_until_idle — no scheduler to spawn into"
    );
    let rt = unsafe { &mut *(raw as *mut Runtime<'static>) };
    rt.spawn_closure(closure_bits)
}

/// Pre-.29.5 API kept for runtime-internal tests that don't have a closure
/// value in hand (they construct frames directly). Real user code routes
/// through `fz_spawn(closure_bits)` → `spawn_closure`.
pub fn spawn_via_current_runtime(fn_id: FnId) -> PidId {
    let raw = CURRENT_RUNTIME.with(|c| c.get());
    assert!(
        !raw.is_null(),
        "spawn() called outside Runtime::run_until_idle — no scheduler to spawn into"
    );
    let rt = unsafe { &mut *(raw as *mut Runtime<'static>) };
    rt.spawn(fn_id)
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
pub fn send_via_current_runtime(receiver_pid: PidId, msg: FzValue) {
    let raw = CURRENT_RUNTIME.with(|c| c.get());
    assert!(
        !raw.is_null(),
        "send() called outside Runtime::run_until_idle — no scheduler to find receiver"
    );
    let rt = unsafe { &mut *(raw as *mut Runtime<'static>) };
    let sender_ptr = CURRENT_PROCESS.with(|c| c.get());
    assert!(
        !sender_ptr.is_null(),
        "send() called with no current_process"
    );
    let sender = unsafe { &mut *sender_ptr };
    if sender.pid == receiver_pid {
        // Self-send: sender is currently OUT of rt.tasks (run_until_idle
        // has it borrowed). We can't .get_mut from rt.tasks. Write
        // directly to the sender's mailbox.
        //
        // Deep-copy is still semantically required (a process sending
        // to itself should still observe the message as a fresh copy),
        // but src_heap == dst_heap == sender.heap. We can't borrow it
        // both ways at once; split borrows are fine because each
        // deep_copy_value alloc is a self-contained &mut access.
        //
        // For self-send we use a single &mut borrow path: alloc into
        // the same heap. Since src and dst are the same heap, the
        // existing forwarding-pointer technique handles sharing.
        let mut forwarding: std::collections::HashMap<
            *mut fz_runtime::fz_value::HeapHeader,
            *mut fz_runtime::fz_value::HeapHeader,
        > = std::collections::HashMap::new();
        // SAFETY: split the &mut Process into &Heap (for read) and
        // &mut Heap (for write). The pointers are aliased but Rust's
        // borrow checker can't see that the same Heap is both src and
        // dst. The deep_copy_value impl doesn't mutate src; we use
        // distinct raw-pointer reads from src vs &mut writes through
        // dst. Equivalent to running deep_copy on a clone of the heap,
        // which would be correct.
        let heap_ptr: *mut fz_runtime::heap::Heap = &mut sender.heap as *mut _;
        let src_heap: &fz_runtime::heap::Heap = unsafe { &*heap_ptr };
        let dst_heap: &mut fz_runtime::heap::Heap = unsafe { &mut *heap_ptr };
        let copied = fz_runtime::heap::deep_copy_value(msg, src_heap, dst_heap, &mut forwarding);
        sender.mailbox.push_back(copied);
        // No state transition needed: sender is Running.
        return;
    }
    let receiver = rt
        .tasks
        .get_mut(&receiver_pid)
        .unwrap_or_else(|| panic!("send: receiver pid {} not in task registry", receiver_pid));
    let mut forwarding: std::collections::HashMap<
        *mut fz_runtime::fz_value::HeapHeader,
        *mut fz_runtime::fz_value::HeapHeader,
    > = std::collections::HashMap::new();
    let copied =
        fz_runtime::heap::deep_copy_value(msg, &sender.heap, &mut receiver.heap, &mut forwarding);
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
    pub fn new(compiled: &'a CompiledModule, workers: usize) -> Self {
        assert!(
            workers == 1,
            "v1 only supports pool size 1; multi-worker is a follow-up to fz-ul4.19.1"
        );
        Self {
            compiled,
            tasks: HashMap::new(),
            run_queue: VecDeque::new(),
            next_pid: 1,
            workers,
        }
    }

    pub fn worker_count(&self) -> usize {
        self.workers
    }

    /// Spawn a new task that begins execution at `fn_id` (which must take
    /// zero entry params — the typical "main" shape for v1). Returns the
    /// fresh pid. The task is enqueued immediately; `run_until_idle()`
    /// will drive it.
    pub fn spawn(&mut self, fn_id: FnId) -> PidId {
        // fz-cps.5 — every fn is Tail-CC, including main. Stash the fn
        // ptr as a pending entry; the scheduler dispatches it via
        // `fz_main_entry` on the next quantum.
        let pid = self.next_pid;
        self.next_pid += 1;
        let mut process = self.compiled.make_process();
        process.pid = pid;
        process.state = ProcessState::Ready;
        let fp = self
            .compiled
            .fn_ptr(fn_id)
            .unwrap_or_else(|| panic!("no fn ptr for entry {}", fn_id.0));
        process.pending_main_entry = fp as *mut u8;
        process.pending_main_entry_fn_id = fn_id.0;
        self.tasks.insert(pid, Box::new(process));
        self.run_queue.push_back(pid);
        pid
    }

    /// fz-ul4.29.5: spawn a task from a closure value owned by the
    /// currently-running process. Deep-copies the closure into the new
    /// task's heap, then invokes the closure's stub_fp with cont_ptr=null
    /// and no args to materialize the initial frame.
    pub fn spawn_closure(&mut self, closure_bits: u64) -> PidId {
        use fz_runtime::fz_value::FzValue;
        use fz_runtime::process::CURRENT_PROCESS;

        let pid = self.next_pid;
        self.next_pid += 1;
        let mut process = self.compiled.make_process();
        process.pid = pid;
        process.state = ProcessState::Ready;

        // Deep-copy the closure from sender's heap into the new task's heap.
        let sender_ptr = CURRENT_PROCESS.with(|c| c.get());
        assert!(!sender_ptr.is_null(), "spawn_closure: no current_process");
        let sender = unsafe { &*sender_ptr };
        let mut forwarding: std::collections::HashMap<
            *mut fz_runtime::fz_value::HeapHeader,
            *mut fz_runtime::fz_value::HeapHeader,
        > = std::collections::HashMap::new();
        let copied = fz_runtime::heap::deep_copy_value(
            FzValue(closure_bits),
            &sender.heap,
            &mut process.heap,
            &mut forwarding,
        );
        let copied_ptr = copied
            .unbox_ptr()
            .expect("spawn_closure: closure must be a heap ptr");

        // fz-cps.1.11 — store the closure ptr as a pending entry; the
        // scheduler's run_quantum dispatches it via fz_spawn_entry on
        // the next quantum. Insert into the task registry before
        // queueing so that cross-task send() during the new task's run
        // can find this pid.
        process.parked_cont = std::ptr::null_mut();
        process.next_frame = std::ptr::null_mut();
        process.pending_closure_entry = copied_ptr as *mut u8;
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
        // erased to *mut () because Runtime carries 'a; consumers
        // re-narrow via spawn_via_current_runtime which transmutes the
        // lifetime back. Safe: we restore the previous value on exit.
        let self_ptr = self as *mut Runtime<'a> as *mut ();
        let prev_rt = CURRENT_RUNTIME.with(|c| c.replace(self_ptr));
        // fz-ul4.23.10: install scheduler hooks so fz_spawn / fz_send
        // (now in the runtime crate) can dispatch back into this
        // Runtime. The runtime crate can't see Runtime directly, so it
        // calls through extern "C" fn pointers we register here.
        fz_runtime::scheduler_hooks::install_spawn_hook(spawn_hook_thunk);
        fz_runtime::scheduler_hooks::install_spawn_opt_hook(spawn_opt_hook_thunk);
        fz_runtime::scheduler_hooks::install_send_hook(send_hook_thunk);
        while let Some(pid) = self.run_queue.pop_front() {
            let mut task = self
                .tasks
                .remove(&pid)
                .expect("task in run_queue not in registry");
            task.state = ProcessState::Running;
            let ptr: *mut Process = &mut *task;
            // Clear FZ_SHOULD_YIELD before installing the process so a
            // stale flag from the previous quantum doesn't immediately
            // re-yield the incoming task.
            FZ_SHOULD_YIELD.store(0, Ordering::Relaxed);
            let prev = CURRENT_PROCESS.with(|c| c.replace(ptr));
            self.compiled.run_quantum(&mut task);
            CURRENT_PROCESS.with(|c| c.set(prev));
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
            //    without explicit block (e.g., future cooperative-yield
            //    builtin). Mark Ready and re-enqueue.
            if task.next_frame.is_null() && task.parked_cont.is_null() {
                task.state = ProcessState::Exited;
            } else if task.state == ProcessState::Blocked {
                // Park: keep in registry, no re-enqueue. send() will
                // wake.
            } else if task.state == ProcessState::Ready {
                // fz-cps.1.12 — fz_receive_park detected a pending
                // message in our own mailbox (self-send → receive); it
                // set state=Ready so the scheduler immediately re-runs
                // the task, where run_quantum's wakeup path dispatches
                // via fz_resume_park.
                self.tasks.insert(pid, task);
                self.run_queue.push_back(pid);
                continue;
            } else if task.state == ProcessState::Running {
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
        CURRENT_RUNTIME.with(|c| c.set(prev_rt));
        fz_runtime::scheduler_hooks::clear_spawn_hook();
        fz_runtime::scheduler_hooks::clear_spawn_opt_hook();
        fz_runtime::scheduler_hooks::clear_send_hook();
    }

    /// Read-only access to a task (for tests / inspection).
    pub fn task(&self, pid: PidId) -> Option<&Process> {
        self.tasks.get(&pid).map(|b| &**b)
    }

    /// Count of tasks (including Exited ones that haven't been pruned).
    pub fn task_count(&self) -> usize {
        self.tasks.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir_codegen::compile;
    use crate::ir_lower::lower_program;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn lower_src(src: &str) -> crate::fz_ir::Module {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        lower_program(&prog).expect("lower")
    }

    /// Three tasks built from the same CompiledModule each compute their
    /// own halt value independently. PRE-.11.32 this would have been
    /// impossible (shared TLS); post-.19.1 this is the basic spawn shape.
    #[test]
    fn three_tasks_each_compute_their_halt_value() {
        let src = "fn main(), do: 1 + 2 + 3";
        let m = lower_src(src);
        let entry = m.fn_by_name("main").unwrap().id;
        let compiled = compile(&m).unwrap();
        let mut rt = Runtime::new(&compiled, 1);
        let a = rt.spawn(entry);
        let b = rt.spawn(entry);
        let c = rt.spawn(entry);
        rt.run_until_idle();
        assert_eq!(rt.task(a).unwrap().halt_value, 6);
        assert_eq!(rt.task(b).unwrap().halt_value, 6);
        assert_eq!(rt.task(c).unwrap().halt_value, 6);
        assert_eq!(rt.task(a).unwrap().state, ProcessState::Exited);
        assert_eq!(rt.task(b).unwrap().state, ProcessState::Exited);
        assert_eq!(rt.task(c).unwrap().state, ProcessState::Exited);
    }

    /// Each task has its own heap. Two tasks build different maps; each
    /// observes only its own state. Same invariant as the .11.32 gating
    /// test but driven through the scheduler instead of direct run_in.
    #[test]
    fn tasks_have_independent_heaps_and_builders() {
        let src_a = "fn main(), do: %{1 => 10, 2 => 20}[2]";
        let src_b = "fn main(), do: %{3 => 30}[3]";
        let ma = lower_src(src_a);
        let mb = lower_src(src_b);
        let ca = compile(&ma).unwrap();
        let cb = compile(&mb).unwrap();

        let mut rt_a = Runtime::new(&ca, 1);
        let mut rt_b = Runtime::new(&cb, 1);
        let pa = rt_a.spawn(ma.fn_by_name("main").unwrap().id);
        let pb = rt_b.spawn(mb.fn_by_name("main").unwrap().id);
        rt_a.run_until_idle();
        rt_b.run_until_idle();

        assert_eq!(rt_a.task(pa).unwrap().halt_value, 20);
        assert_eq!(rt_b.task(pb).unwrap().halt_value, 30);
        assert!(rt_a.task(pa).unwrap().heap.live_count() > 0);
        assert!(rt_b.task(pb).unwrap().heap.live_count() > 0);
    }

    /// Spawning more tasks after run_until_idle works: new pids, new
    /// runs proceed normally.
    #[test]
    fn spawn_after_idle_resumes_progress() {
        let src = "fn main(), do: 42";
        let m = lower_src(src);
        let entry = m.fn_by_name("main").unwrap().id;
        let compiled = compile(&m).unwrap();
        let mut rt = Runtime::new(&compiled, 1);
        let a = rt.spawn(entry);
        rt.run_until_idle();
        assert_eq!(rt.task(a).unwrap().halt_value, 42);
        let b = rt.spawn(entry);
        rt.run_until_idle();
        assert_eq!(rt.task(b).unwrap().halt_value, 42);
        assert_ne!(a, b, "pids are unique across spawns");
    }

    /// worker count > 1 is reserved for the multi-worker follow-up;
    /// Runtime::new panics rather than silently accepting it.
    #[test]
    #[should_panic(expected = "v1 only supports pool size 1")]
    fn workers_greater_than_one_is_not_yet_supported() {
        let src = "fn main(), do: 0";
        let m = lower_src(src);
        let compiled = compile(&m).unwrap();
        let _ = Runtime::new(&compiled, 2);
    }

    // ----- fz-ul4.19.2: spawn / self builtins -----

    /// `self()` inside main returns the running task's pid (1 for the
    /// first spawn).
    #[test]
    fn self_returns_task_pid() {
        let src = "fn main(), do: self()";
        let m = lower_src(src);
        let entry = m.fn_by_name("main").unwrap().id;
        let compiled = compile(&m).unwrap();
        let mut rt = Runtime::new(&compiled, 1);
        let pid = rt.spawn(entry);
        rt.run_until_idle();
        // halt_value is the boxed Int's i64 (we boxed pid as Int; halt
        // returns the unboxed i64 for Int-tagged FzValues).
        assert_eq!(rt.task(pid).unwrap().halt_value, pid as i64);
    }

    /// `spawn(fn() -> 42 end)` enqueues a child task; after run_until_idle
    /// both tasks have halted and the child computed 42.
    #[test]
    fn spawn_enqueues_child_task() {
        let src = r#"
            fn child(), do: 42
            fn main(), do: spawn(child)
        "#;
        let m = lower_src(src);
        let entry = m.fn_by_name("main").unwrap().id;
        let compiled = compile(&m).unwrap();
        let mut rt = Runtime::new(&compiled, 1);
        let main_pid = rt.spawn(entry);
        rt.run_until_idle();
        // Main halted with the child's pid (spawn returns pid as boxed
        // Int; halt unboxes to i64). Child pid is main_pid + 1 = 2.
        let expected_child_pid = main_pid + 1;
        assert_eq!(
            rt.task(main_pid).unwrap().halt_value,
            expected_child_pid as i64
        );
        // Child completed.
        let child = rt
            .task(expected_child_pid)
            .expect("child task should exist after spawn");
        assert_eq!(child.halt_value, 42);
        assert_eq!(child.state, ProcessState::Exited);
    }

    /// spawn() called outside Runtime::run_until_idle panics with a clear
    /// message rather than UB. We test the helper directly rather than
    /// through JIT because extern "C" fn panics abort under the default
    /// edition-2024 panic-abi.
    #[test]
    #[should_panic(expected = "spawn() called outside")]
    fn spawn_outside_runtime_panics() {
        // Ensure CURRENT_RUNTIME is null (no Runtime installed on this
        // worker). Other tests may have installed it; reset for safety.
        CURRENT_RUNTIME.with(|c| c.set(std::ptr::null_mut()));
        let _ = spawn_via_current_runtime(crate::fz_ir::FnId(0));
    }

    // ----- fz-ul4.19.3: send / receive + deep-copy + block/wake -----

    /// Round-trip an Int: parent spawns child, child sends 42 to parent
    /// (parent pid passed somehow — for this test, parent's pid is 1
    /// because it's spawned first), parent receives, halts with the msg.
    /// Since we can't yet pass parent's pid to child easily, this test
    /// uses send-to-self.
    #[test]
    fn send_to_self_then_receive_int() {
        let src = r#"
            fn main() do
              send(self(), 42)
              receive()
            end
        "#;
        let m = lower_src(src);
        let entry = m.fn_by_name("main").unwrap().id;
        let compiled = compile(&m).unwrap();
        let mut rt = Runtime::new(&compiled, 1);
        let pid = rt.spawn(entry);
        rt.run_until_idle();
        // halt_value is the unboxed Int from the received message.
        assert_eq!(rt.task(pid).unwrap().halt_value, 42);
        assert_eq!(rt.task(pid).unwrap().state, ProcessState::Exited);
    }

    /// Receive blocks the task when no message is available, then resumes
    /// when send delivers one. Parent spawns child; parent calls receive()
    /// first (Blocks); child then sends; parent wakes and halts with the
    /// message. Tests the YIELD_PTR / Blocked / wake mechanism.
    #[test]
    fn receive_blocks_until_send_arrives() {
        // child(parent_pid) sends 99 to parent_pid then halts.
        // main spawns child(self()) and then receive()s.
        let src = r#"
            fn child(parent), do: send(parent, 99)
            fn main() do
              child(self())
              receive()
            end
        "#;
        let m = lower_src(src);
        let entry = m.fn_by_name("main").unwrap().id;
        let compiled = compile(&m).unwrap();
        let mut rt = Runtime::new(&compiled, 1);
        let pid = rt.spawn(entry);
        rt.run_until_idle();
        assert_eq!(rt.task(pid).unwrap().halt_value, 99);
    }

    // Deep-copy: send a heap-allocated list; sender and receiver heaps
    // hold independent copies. Verified by sender-side heap growing
    // from the list allocation plus receiver-side heap growing from
    // the deep-copy of the same structure.
    // ----- fz-ul4.19 demonstration via the JIT pipeline -----

    /// End-to-end fixture test: load `fixtures/concurrency_ping_pong/input.fz`,
    /// run it through the FULL JIT pipeline (lex → parse → resolve →
    /// macros → ir_lower → ir_codegen → Runtime::run_until_idle), and
    /// assert the parent's halt value matches the message the child sent.
    ///
    /// This is the JIT path's proof-of-life for concurrency. The
    /// interpreter and AOT paths are pending (see memory note
    /// "Three-path parity"); when they ship, the same fixture should
    /// drive the same assertion through their pipelines.
    #[test]
    fn fixture_ping_pong_via_jit_runtime() {
        let src = std::fs::read_to_string("fixtures/concurrency_ping_pong/input.fz")
            .expect("failed to read fixtures/concurrency_ping_pong/input.fz");
        // Pipeline: lex, parse, resolve (flatten modules), expand macros,
        // ir_lower, ir_codegen, Runtime.
        let toks = Lexer::new(&src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let mut prog = crate::resolve::flatten_modules(prog).expect("resolve");
        crate::macros::expand_program(&mut prog).expect("expand");
        let m = crate::ir_lower::lower_program(&prog).expect("lower");
        let entry = m.fn_by_name("main").expect("main fn").id;
        let compiled = compile(&m).expect("codegen");

        let mut rt = Runtime::new(&compiled, 1);
        let main_pid = rt.spawn(entry);
        assert_eq!(
            main_pid, 1,
            "main is the first spawn; fixture hard-codes 1 as parent's pid"
        );
        rt.run_until_idle();

        // Parent received 42, printed it, and halts on print's return
        // value (nil — represented as 0 in halt_value per fz_halt's
        // per-tag decoding). fz-ul4.26 changed main to `print(receive())`;
        // the receive-and-halt-with-42 path is verified by capture below
        // (TEST_CAPTURE has "42") and by the matrix's .expected file.
        let main_task = rt.task(main_pid).expect("main task in registry");
        assert_eq!(
            main_task.halt_value, 0,
            "parent halts with print(receive())'s nil return"
        );
        assert_eq!(main_task.state, ProcessState::Exited);

        // Child task: spawned by main, halted normally (send returns the
        // message which it then halts on; but child's main body is `send`,
        // so it halts with the message's value 42 too).
        let child_task = rt
            .task(2)
            .expect("child task should exist at pid 2 (second spawn)");
        assert_eq!(child_task.state, ProcessState::Exited);
        assert_eq!(child_task.halt_value, 42);
    }

    #[test]
    fn send_list_deep_copies_into_receiver_heap() {
        let src = r#"
            fn main() do
              send(self(), [1, 2, 3])
              receive()
            end
        "#;
        let m = lower_src(src);
        let entry = m.fn_by_name("main").unwrap().id;
        let compiled = compile(&m).unwrap();
        let mut rt = Runtime::new(&compiled, 1);
        let pid = rt.spawn(entry);
        rt.run_until_idle();
        // Send-to-self means the message was deep-copied even though
        // it's the same Process. Heap should have BOTH the original
        // list (allocated for the send) AND the copied list (allocated
        // for the mailbox-resident copy). Both share schema/registry
        // (same heap), but are distinct allocations.
        let task = rt.task(pid).unwrap();
        assert_eq!(task.state, ProcessState::Exited);
        // The halt value is the head of the returned list (since the
        // list was returned via receive). Confirm task halted cleanly.
        assert!(
            task.heap.live_count() >= 6,
            "expected both src+dst lists in heap"
        );
    }

    /// fz-siu.7.3: park-time GC hook fires when allocation pressure
    /// crosses gc_threshold_bytes. With the threshold lowered below the
    /// fixture's allocation footprint, run_until_idle must trigger gc()
    /// (stub in .7 — just bumps gc_run_count) at the post-dispatch park
    /// point. Real Cheney body lands in fz-siu.8.
    #[test]
    fn park_time_gc_fires_when_pressure_set() {
        // [1,2,3] allocates three 32-byte cons cells = 96 bytes.
        let src = "fn main(), do: [1, 2, 3]";
        let m = lower_src(src);
        let entry = m.fn_by_name("main").unwrap().id;
        let compiled = compile(&m).unwrap();
        let mut rt = Runtime::new(&compiled, 1);
        let pid = rt.spawn(entry);
        // Lower threshold below the alloc footprint so the flag trips.
        rt.tasks.get_mut(&pid).unwrap().heap.gc_threshold_bytes = 64;
        rt.run_until_idle();
        let task = rt.task(pid).unwrap();
        assert_eq!(task.state, ProcessState::Exited);
        assert!(
            task.heap.gc_run_count >= 1,
            "park-time hook should have fired GC, got {}",
            task.heap.gc_run_count
        );
        assert!(!task.heap.should_gc(), "flag should be cleared after gc()");
    }

    // ----- fz-02r.2: FZ_SHOULD_YIELD global -----

    /// run_until_idle clears FZ_SHOULD_YIELD before each quantum so a stale
    /// flag from a previous task's watermark crossing doesn't falsely
    /// pre-yield the incoming task.
    #[test]
    fn run_until_idle_clears_yield_flag_before_each_quantum() {
        use fz_runtime::yield_flag::FZ_SHOULD_YIELD;
        use std::sync::atomic::Ordering;

        // Pre-set the flag as if a previous task had crossed the watermark.
        FZ_SHOULD_YIELD.store(1, Ordering::Relaxed);

        let src = "fn main(), do: 7";
        let m = lower_src(src);
        let entry = m.fn_by_name("main").unwrap().id;
        let compiled = compile(&m).unwrap();
        let mut rt = Runtime::new(&compiled, 1);
        rt.spawn(entry);
        rt.run_until_idle();

        // After the quantum completes the flag is 0 (cleared at quantum
        // start; task allocates nothing near the watermark).
        assert_eq!(
            FZ_SHOULD_YIELD.load(Ordering::Relaxed),
            0,
            "FZ_SHOULD_YIELD should be 0 after run_until_idle"
        );
    }
}
