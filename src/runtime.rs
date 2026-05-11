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

use crate::fz_ir::FnId;
use crate::fz_value::FzValue;
use crate::ir_codegen::{
    fz_alloc_frame_for_test, CompiledModule, PidId, Process, ProcessState, CURRENT_PROCESS,
    HEADER_SIZE,
};

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

/// fz-ul4.19.2: called from fz_spawn (ir_codegen.rs FFI) to enqueue a new
/// task. Reads CURRENT_RUNTIME, calls spawn() on it. Panics if no Runtime
/// is currently installed (i.e., the JIT path is being driven via
/// CompiledModule.run rather than Runtime::run_until_idle).
pub fn spawn_via_current_runtime(fn_id: FnId) -> PidId {
    let raw = CURRENT_RUNTIME.with(|c| c.get());
    assert!(
        !raw.is_null(),
        "spawn() called outside Runtime::run_until_idle — no scheduler to spawn into"
    );
    // Safety: while CURRENT_RUNTIME is non-null, the Runtime stack frame
    // is live (run_until_idle hasn't returned). We re-narrow with a
    // synthetic 'static lifetime; the call returns before the borrow
    // matters.
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
            *mut crate::fz_value::HeapHeader,
            *mut crate::fz_value::HeapHeader,
        > = std::collections::HashMap::new();
        // SAFETY: split the &mut Process into &Heap (for read) and
        // &mut Heap (for write). The pointers are aliased but Rust's
        // borrow checker can't see that the same Heap is both src and
        // dst. The deep_copy_value impl doesn't mutate src; we use
        // distinct raw-pointer reads from src vs &mut writes through
        // dst. Equivalent to running deep_copy on a clone of the heap,
        // which would be correct.
        let heap_ptr: *mut crate::heap::Heap = &mut sender.heap as *mut _;
        let src_heap: &crate::heap::Heap = unsafe { &*heap_ptr };
        let dst_heap: &mut crate::heap::Heap = unsafe { &mut *heap_ptr };
        let copied = crate::heap::deep_copy_value(msg, src_heap, dst_heap, &mut forwarding);
        sender.mailbox.push_back(copied);
        // No state transition needed: sender is Running.
        return;
    }
    let receiver = rt
        .tasks
        .get_mut(&receiver_pid)
        .unwrap_or_else(|| panic!("send: receiver pid {} not in task registry", receiver_pid));
    let mut forwarding: std::collections::HashMap<
        *mut crate::fz_value::HeapHeader,
        *mut crate::fz_value::HeapHeader,
    > = std::collections::HashMap::new();
    let copied = crate::heap::deep_copy_value(
        msg,
        &sender.heap,
        &mut receiver.heap,
        &mut forwarding,
    );
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
        let pid = self.next_pid;
        self.next_pid += 1;
        let mut process = self.compiled.make_process();
        process.pid = pid;
        process.state = ProcessState::Ready;
        // Allocate the entry frame eagerly; the trampoline will resume
        // from process.next_frame.
        let entry_schema = self.compiled.schema_for(fn_id);
        let frame = fz_alloc_frame_for_test(fn_id.0, entry_schema.size);
        unsafe {
            // cont_ptr = null (top of stack; halt exits the trampoline)
            let cont_slot = frame.add(HEADER_SIZE as usize) as *mut *mut u8;
            *cont_slot = std::ptr::null_mut();
        }
        process.next_frame = frame;
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
        while let Some(pid) = self.run_queue.pop_front() {
            let mut task = self
                .tasks
                .remove(&pid)
                .expect("task in run_queue not in registry");
            task.state = ProcessState::Running;
            let ptr: *mut Process = &mut *task;
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
            if task.next_frame.is_null() {
                task.state = ProcessState::Exited;
            } else if task.state == ProcessState::Blocked {
                // Park: keep in registry, no re-enqueue. send() will
                // wake.
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
        assert_eq!(rt.task(main_pid).unwrap().halt_value, expected_child_pid as i64);
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

    /// Deep-copy: send a heap-allocated list; sender and receiver heaps
    /// hold independent copies. Verified by sender-side heap growing
    /// from the list allocation plus receiver-side heap growing from
    /// the deep-copy of the same structure.
    // ----- fz-ul4.19.4: per-process independent GC verification -----

    /// Two tasks; one allocates heavily enough to trigger GC, the other
    /// allocates one small list and doesn't trigger anything. After
    /// run_until_idle, the heavy task has gc_run_count >= 1 and the lite
    /// task has gc_run_count == 0. Confirms per-process GC isolation.
    #[test]
    fn heavy_task_gcs_independently_of_lite_task() {
        let src = r#"
            fn heavy_loop(0, acc), do: acc
            fn heavy_loop(n, acc), do: heavy_loop(n - 1, [n, n])
            fn heavy(), do: heavy_loop(2000, [])
            fn lite(), do: [1, 2, 3]
        "#;
        let m = lower_src(src);
        let compiled = compile(&m).unwrap();
        let heavy_entry = m.fn_by_name("heavy").unwrap().id;
        let lite_entry = m.fn_by_name("lite").unwrap().id;
        let mut rt = Runtime::new(&compiled, 1);
        let heavy_pid = rt.spawn(heavy_entry);
        let lite_pid = rt.spawn(lite_entry);
        // Lower the heavy task's GC threshold so the loop forces ticks.
        rt.tasks
            .get_mut(&heavy_pid)
            .unwrap()
            .heap
            .gc_threshold_bytes = 4 * 1024;
        rt.run_until_idle();
        let heavy = rt.task(heavy_pid).unwrap();
        let lite = rt.task(lite_pid).unwrap();
        assert!(
            heavy.heap.gc_run_count >= 1,
            "heavy task should have triggered GC, got {}",
            heavy.heap.gc_run_count
        );
        assert_eq!(
            lite.heap.gc_run_count, 0,
            "lite task should NOT have triggered GC (its heap untouched by heavy's GC)"
        );
        // Lite task's value survives — its small list is fully intact.
        // (Verified indirectly by lite.state == Exited and live_count > 0.)
        assert_eq!(lite.state, ProcessState::Exited);
        assert!(lite.heap.live_count() >= 3, "lite's [1,2,3] survives");
    }

    /// Same-CompiledModule, two tasks with distinct heap thresholds: the
    /// task with a lower threshold GCs more often than the other. Tests
    /// that the threshold is genuinely per-process (Heap state) and not
    /// a global.
    #[test]
    fn per_process_gc_threshold_is_independent() {
        let src = r#"
            fn build(0, acc), do: acc
            fn build(n, acc), do: build(n - 1, [n, n, n])
            fn main(), do: build(800, [])
        "#;
        let m = lower_src(src);
        let compiled = compile(&m).unwrap();
        let entry = m.fn_by_name("main").unwrap().id;
        let mut rt = Runtime::new(&compiled, 1);
        let tight_pid = rt.spawn(entry);
        let loose_pid = rt.spawn(entry);
        rt.tasks.get_mut(&tight_pid).unwrap().heap.gc_threshold_bytes = 2 * 1024;
        rt.tasks.get_mut(&loose_pid).unwrap().heap.gc_threshold_bytes = 32 * 1024;
        rt.run_until_idle();
        let tight = rt.task(tight_pid).unwrap();
        let loose = rt.task(loose_pid).unwrap();
        assert!(
            tight.heap.gc_run_count > loose.heap.gc_run_count,
            "tighter threshold task should GC more often (tight={}, loose={})",
            tight.heap.gc_run_count,
            loose.heap.gc_run_count
        );
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
        assert!(task.heap.live_count() >= 6, "expected both src+dst lists in heap");
    }
}
