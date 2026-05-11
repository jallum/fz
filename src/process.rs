//! Per-task runtime state and the TLS plumbing that lets FFI fns reach it.
//!
//! Lifted out of ir_codegen.rs by fz-ul4.23.4.2 so that any execution path
//! (JIT, future interp/AOT) can stand up a Process without dragging the
//! codegen module along. The Process owns the per-task heap and builders;
//! the Runtime in src/runtime.rs schedules Processes; FFI fns in
//! src/ir_runtime.rs read/write the currently-running Process through
//! `current_process()`.

/// Per-task runtime state. One Process per fz-level task; the worker thread
/// installs `*mut Process` in `CURRENT_PROCESS` for the duration of a run,
/// and FFI fns reach the running task's state via `current_process()`.
///
/// libdispatch-style: TLS records the currently-running task's pointer per
/// worker; a task is owned by exactly one worker at a time (scheduler
/// invariant, .19.1). FFI fns do not yield, so TLS is stable within any FFI
/// call.
pub struct Process {
    pub heap: crate::heap::Heap,
    pub halt_value: i64,
    // Transient builder state — per-task so two interleaved tasks can't
    // corrupt one another's in-flight builders.
    pub map_builder: Option<Vec<(u64, u64)>>,
    pub bs_builder: Option<crate::bitstr::BitWriter>,
    pub vec_builder: Option<crate::ir_runtime::VecBuild>,
    pub closure_builder: Option<(u32, Vec<u64>)>,
    pub closure_args: Vec<u64>,
    // Per-CompiledModule constants copied at make_process() time. See
    // fz-ul4.19.1 follow-up to move these behind an Rc<CompiledModuleConsts>.
    pub frame_sizes: Vec<u32>,
    pub bs_tuple_arity1_schema: Option<u32>,
    pub bs_tuple_arity3_schema: Option<u32>,
    // fz-ul4.19.1 scheduler-level fields. Populated when a Process is
    // owned by a Runtime; the standalone `make_process()` / `run_in` path
    // leaves these at defaults.
    pub pid: PidId,
    pub state: ProcessState,
    /// Current continuation pointer. While running, the trampoline holds
    /// this in a local; on yield/halt boundaries the Runtime swaps state
    /// here. v1 only writes this on halt (next_frame = null).
    pub next_frame: *mut u8,
    pub mailbox: std::collections::VecDeque<crate::fz_value::FzValue>,
}

/// Stable per-Process identifier assigned at spawn time. v1: simple u32
/// counter; .19.5 may add a (node_id, generation) tuple. Pid is exposed
/// to fz code via the Pid struct schema (.19.2 — separate ticket).
pub type PidId = u32;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProcessState {
    /// Default; created but not yet ever scheduled.
    New,
    /// Ready to run / in run_queue.
    Ready,
    /// Currently running on a worker (a worker has it installed in TLS).
    Running,
    /// Awaiting a message (.19.3); send wakes back to Ready.
    Blocked,
    /// Halted; halt_value is final.
    Exited,
}

impl Process {
    #[allow(dead_code)]
    pub fn new(schemas: std::rc::Rc<std::cell::RefCell<crate::heap::SchemaRegistry>>) -> Self {
        Self {
            heap: crate::heap::Heap::new(64 * 1024, schemas),
            halt_value: 0,
            map_builder: None,
            bs_builder: None,
            vec_builder: None,
            closure_builder: None,
            closure_args: Vec::new(),
            frame_sizes: Vec::new(),
            bs_tuple_arity1_schema: None,
            bs_tuple_arity3_schema: None,
            pid: 0,
            state: ProcessState::New,
            next_frame: std::ptr::null_mut(),
            mailbox: std::collections::VecDeque::new(),
        }
    }
}

thread_local! {
    /// Raw pointer to the Process currently being run by this worker (this
    /// thread). Set by `run_in` for the duration of the run; cleared
    /// afterwards. FFI fns called from JIT'd code read it via
    /// `current_process()`.
    pub static CURRENT_PROCESS: std::cell::Cell<*mut Process> =
        const { std::cell::Cell::new(std::ptr::null_mut()) };
    /// Backing storage for the convenience `compiled.run(fn_id)` path: a
    /// Process is constructed, stashed here, and CURRENT_PROCESS points at
    /// it. After the run, CURRENT_PROCESS is cleared but the Process remains
    /// here so test helpers (heap_live_count, heap_gc, ...) can inspect.
    /// Tests using the explicit `run_in(fn_id, &mut Process)` path own
    /// their Process directly and don't use this slot.
    pub static DEFAULT_PROCESS: std::cell::RefCell<Option<Process>> =
        const { std::cell::RefCell::new(None) };
}

/// Access the currently-installed Process via the raw TLS pointer. Must only
/// be called from FFI fns invoked synchronously inside `run_in`. The Process
/// is owned by either the caller (run_in path) or by DEFAULT_PROCESS (run
/// path); the pointer is valid for the duration of the run.
pub fn current_process() -> &'static mut Process {
    let p = CURRENT_PROCESS.with(|c| c.get());
    assert!(!p.is_null(), "current_process(): no Process installed (running outside run_in?)");
    unsafe { &mut *p }
}
