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
            // v1: a quantum runs to halt (next_frame became null).
            // Future receive yields will leave next_frame non-null with
            // state == Blocked; that path is .19.3.
            if task.next_frame.is_null() {
                task.state = ProcessState::Exited;
            } else if task.state == ProcessState::Running {
                // Yielded but didn't halt — re-enqueue. Currently
                // unreachable (no yield builtin) but the path is here
                // for .19.3.
                task.state = ProcessState::Ready;
                self.tasks.insert(pid, task);
                self.run_queue.push_back(pid);
                continue;
            }
            // Keep Exited tasks in the registry so callers can inspect
            // halt_value / mailbox after the runtime drains.
            self.tasks.insert(pid, task);
        }
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
}
