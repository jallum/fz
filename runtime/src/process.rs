//! Per-task runtime state and the TLS plumbing that lets FFI fns reach it.
//!
//! Lifted out of ir_codegen.rs by fz-ul4.23.4.2 so that any execution path
//! (JIT, future interp/AOT) can stand up a Process without dragging the
//! codegen module along. The Process owns the per-task heap and builders;
//! the Runtime in src/runtime.rs schedules Processes; FFI fns in
//! src/ir_runtime.rs read/write the currently-running Process through
//! `current_process()`.

use std::alloc::{Layout, alloc_zeroed, dealloc, handle_alloc_error};
use std::ptr::NonNull;

pub const DEFAULT_REDUCTIONS_PER_QUANTUM: i32 = 4000;
pub const YIELD_REASON_REDUCTIONS: u8 = 1 << 0;
pub const YIELD_REASON_ALLOCATION_PRESSURE: u8 = 1 << 1;
pub const YIELD_REASON_EXPLICIT: u8 = 1 << 2;

pub struct AlignedClosureStorage {
    ptr: NonNull<u8>,
    layout: Layout,
}

impl AlignedClosureStorage {
    pub fn zeroed() -> Self {
        let layout = Layout::from_size_align(crate::any_value::closure_size_for_count(0), 16)
            .expect("zero-capture closure layout");
        let ptr = unsafe { alloc_zeroed(layout) };
        let Some(ptr) = NonNull::new(ptr) else {
            handle_alloc_error(layout);
        };
        debug_assert_eq!(ptr.as_ptr() as u64 & crate::any_value::TAG_MASK, 0);
        Self { ptr, layout }
    }

    pub fn as_ptr(&mut self) -> *mut u8 {
        self.ptr.as_ptr()
    }
}

impl Drop for AlignedClosureStorage {
    fn drop(&mut self) {
        unsafe {
            dealloc(self.ptr.as_ptr(), self.layout);
        }
    }
}

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
    pub bs_builder: Option<crate::bitstr::BitWriter>,
    // fz-ul4.29.5: closure_builder / closure_args fields removed. Closure
    // construction is inlined at codegen; capture storage is schema-backed,
    // and invocation is a direct call_indirect through the closure code ptr.
    // Per-CompiledModule constants copied at make_process() time. See
    // fz-ul4.19.1 follow-up to move these behind an Rc<CompiledModuleConsts>.
    pub frame_sizes: Vec<u32>,
    /// Atom names indexed by id. Populated at task-setup time from the
    /// IR Module's atom_names. any_value::debug::render reads this to
    /// print `:source_name` instead of `:atom_N`. fz-ul4.25.
    pub atom_names: Vec<String>,
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
    pub mailbox: std::collections::VecDeque<crate::any_value::AnyValueRef>,
    /// Receive park snapshot. Plain `receive()` installs an accept-any
    /// matcher; selective receive installs its compiled matcher. Either way,
    /// a hit materializes `runnable_closure` and the scheduler runs that.
    pub parked_matched: Option<Box<crate::park::ParkRecord>>,
    /// General scheduler-runnable zero-arg closure. Long term, every
    /// scheduler re-entry path should move work here before enqueue/resume;
    /// the closure's captures carry the state needed to continue.
    pub runnable_closure: *mut u8,
    /// fz-ul4.27.22.3 — per-Process halt-cont singletons indexed by
    /// repr kind (0=ValueRef, 1=RawInt, 2=RawF64). Each slot holds a
    /// 24-byte closure whose +8 slot points at the matching
    /// `fz_halt_cont_body_<kind>` Cranelift body. Lazily allocated by
    /// `fz_get_halt_cont(addr, kind)` per kind, or pre-populated by
    /// `init_halt_cont_singletons` at make_process. Pointers alias
    /// aligned buffers in `static_closure_bufs`.
    pub halt_cont_singletons: [*mut u8; 3],
    /// fz-cps.1.11 — pending closure to invoke at the next scheduler
    /// quantum. Set by `Runtime::spawn_closure` to the closure pointer;
    /// `run_quantum` clears it and dispatches via the `fz_spawn_entry`
    /// SystemV→Tail-CC shim. Null means "no pending entry" (either
    /// trampoline-driven uniform main or already-resumed task).
    pub pending_closure_entry: *mut u8,
    /// fz-cps.5 — pending main-style entry fn ptr. Set by
    /// `Runtime::spawn(fn_id)`; the scheduler's `run_quantum`
    /// dispatches via the SystemV→Tail-CC `fz_main_entry` shim.
    pub pending_main_entry: *mut u8,
    /// fz-ul4.27.22.3 — FnId.0 of the pending entry. Used by
    /// `run_quantum` to look up the matching halt-cont singleton kind
    /// in `CompiledModule.fn_halt_kinds`. Defaults to 0 (ValueRef) if
    /// no entry is queued.
    pub pending_main_entry_fn_id: u32,
    /// fz-cps.1.7 — per-Process static zero-capture closure singletons.
    /// Indexed by lambda spec id (cl_sid). Null entries indicate "no
    /// singleton registered for this cl_sid." Each non-null entry points
    /// to a 16-byte-aligned off-heap buffer owned by `static_closure_bufs`
    /// (closure metadata + code_ptr, zero captures). Off-heap so the per-process
    /// GC arena does not own them — singletons live for the Process's
    /// lifetime. See docs/cps-in-clif.md §8.2.
    pub static_closures: Vec<*mut u8>,
    /// fz-cps.1.7 — backing storage for `static_closures`. One aligned
    /// allocation per registered singleton. The raw pointer in
    /// `static_closures` aliases the start of the corresponding allocation.
    pub static_closure_bufs: Vec<AlignedClosureStorage>,

    /// Consecutive quanta elapsed since the last GC triggered. Used by
    /// the proactive shrinkage heuristic: after N quiet quanta the
    /// scheduler may shrink the heap below `last_gc_live_bytes * 2`.
    pub quiet_quanta: u8,
    /// Cumulative compiled-code mid-flight yields for this process. Each
    /// increment means native code built a scheduler-owned continuation
    /// closure and returned to the scheduler through `fz_yield_mid_flight`.
    pub scheduler_yields: u64,
    /// Cumulative interpreter back-edge GC yields. These do not allocate
    /// scheduler continuation closures; the interpreter forwards roots
    /// synchronously and keeps running.
    pub interpreter_yields: u64,
    /// Reductions left in the current scheduler quantum. Dispatch resets this
    /// to `reductions_per_quantum`; loop back edges and runtime work spend it.
    pub reductions_remaining: i32,
    /// Reductions granted to this process at each scheduler dispatch.
    pub reductions_per_quantum: i32,
    /// Cumulative reductions charged to this process.
    pub reductions_executed: u64,
    /// Cumulative yields caused by ordinary reduction-budget exhaustion.
    pub reduction_yields: u64,
    /// Compact reason bits describing why the current/last quantum yielded.
    /// See `YIELD_REASON_*`.
    pub yield_reasons: u8,
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
    pub fn new(schemas: std::rc::Rc<std::cell::RefCell<crate::heap::SchemaRegistry>>) -> Self {
        Self {
            // §6.3: initial size on spawn = SIZE_TABLE[0] (1 KiB). Cheney
            // promotes to a higher size_class on first GC if the working
            // set demands it; shrink hysteresis (§6.5 / fz-siu.11) brings
            // it back down for short-lived spikes.
            heap: crate::heap::Heap::new(crate::heap::SIZE_TABLE[0], schemas),
            halt_value: 0,
            bs_builder: None,
            frame_sizes: Vec::new(),
            atom_names: Vec::new(),
            bs_tuple_arity1_schema: None,
            bs_tuple_arity3_schema: None,
            pid: 0,
            state: ProcessState::New,
            next_frame: std::ptr::null_mut(),
            mailbox: std::collections::VecDeque::new(),
            parked_matched: None,
            runnable_closure: std::ptr::null_mut(),
            halt_cont_singletons: [std::ptr::null_mut(); 3],
            pending_closure_entry: std::ptr::null_mut(),
            pending_main_entry: std::ptr::null_mut(),
            pending_main_entry_fn_id: 0,
            static_closures: Vec::new(),
            static_closure_bufs: Vec::new(),
            quiet_quanta: 0,
            scheduler_yields: 0,
            interpreter_yields: 0,
            reductions_remaining: DEFAULT_REDUCTIONS_PER_QUANTUM,
            reductions_per_quantum: DEFAULT_REDUCTIONS_PER_QUANTUM,
            reductions_executed: 0,
            reduction_yields: 0,
            yield_reasons: 0,
        }
    }

    /// fz-cps.1.7 — populate the static closure singleton table. Each
    /// target `(cl_sid, fn_id, code_ptr)` allocates one off-heap strict
    /// zero-capture closure and registers its tagged value at
    /// `static_closures[cl_sid as usize]`. Idempotent only
    /// in the sense that re-calling with the same targets re-allocates;
    /// callers (`CompiledModule::make_process`) call this exactly once
    /// per Process at construction time.
    pub fn init_static_closures(
        &mut self,
        targets: &[(
            u32,       /* cl_sid */
            u32,       /* fn_id */
            *const u8, /* code_ptr */
            u32,       /* halt_kind */
        )],
    ) {
        // Size table by max cl_sid encountered.
        let max = targets.iter().map(|(s, _, _, _)| *s).max().unwrap_or(0) as usize;
        if self.static_closures.len() < max + 1 {
            self.static_closures.resize(max + 1, std::ptr::null_mut());
        }
        let closure_schema = self.heap.closure_schema_id(0);
        for (cl_sid, fn_id, code_ptr, halt_kind) in targets {
            let mut buf = AlignedClosureStorage::zeroed();
            let base = buf.as_ptr();
            unsafe {
                let _ = fn_id;
                std::ptr::write(base as *mut u32, closure_schema);
                std::ptr::write(
                    base.add(4) as *mut u32,
                    crate::any_value::closure_flags_pack(0, *halt_kind as u16) as u32,
                );
                std::ptr::write(base.add(8) as *mut u64, *code_ptr as u64);
            }
            self.static_closures[*cl_sid as usize] = base;
            self.static_closure_bufs.push(buf);
        }
    }

    /// fz-ul4.27.22.3 — pre-allocate halt-cont singletons for each kind
    /// (0=ValueRef, 1=RawInt, 2=RawF64). Non-null `body_addrs[k]` seeds
    /// the corresponding slot; null entries leave the slot null
    /// (lazily filled by `fz_get_halt_cont` on first use). Called once
    /// per Process by `make_process`.
    pub fn init_halt_cont_singletons(&mut self, body_addrs: [*const u8; 3]) {
        let closure_schema = self.heap.closure_schema_id(0);
        for (slot, addr) in body_addrs.iter().enumerate() {
            if addr.is_null() {
                continue;
            }
            let mut buf = AlignedClosureStorage::zeroed();
            let base = buf.as_ptr();
            unsafe {
                std::ptr::write(base as *mut u32, closure_schema);
                std::ptr::write(base.add(4) as *mut u32, 0);
                std::ptr::write(base.add(8) as *mut u64, *addr as u64);
            }
            self.halt_cont_singletons[slot] = base;
            self.static_closure_bufs.push(buf);
        }
    }

    pub fn set_runnable_closure(&mut self, closure: *mut u8) {
        self.runnable_closure = closure;
    }

    pub fn take_runnable_closure(&mut self) -> Option<*mut u8> {
        if self.runnable_closure.is_null() {
            None
        } else {
            let closure = self.runnable_closure;
            self.runnable_closure = std::ptr::null_mut();
            Some(closure)
        }
    }

    pub fn reset_reduction_budget(&mut self) {
        self.reductions_remaining = self.reductions_per_quantum;
    }

    pub fn spend_reductions(&mut self, amount: i32) -> bool {
        debug_assert!(amount >= 0, "cannot spend negative reductions");
        if amount <= 0 {
            return self.reductions_remaining <= 0;
        }
        self.reductions_remaining = self.reductions_remaining.saturating_sub(amount);
        self.reductions_executed = self.reductions_executed.saturating_add(amount as u64);
        self.reductions_remaining <= 0
    }

    pub fn expire_reductions(&mut self, reason: u8) {
        self.reductions_remaining = 0;
        self.yield_reasons |= reason;
    }

    pub fn note_reduction_yield(&mut self) {
        self.reduction_yields = self.reduction_yields.saturating_add(1);
        self.yield_reasons |= YIELD_REASON_REDUCTIONS;
    }

    pub fn clear_yield_reasons(&mut self) {
        self.yield_reasons = 0;
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

pub struct CurrentProcessGuard {
    prev: *mut Process,
}

impl CurrentProcessGuard {
    pub fn install(ptr: *mut Process) -> Self {
        let prev = CURRENT_PROCESS.with(|c| c.replace(ptr));
        Self { prev }
    }
}

impl Drop for CurrentProcessGuard {
    fn drop(&mut self) {
        CURRENT_PROCESS.with(|c| c.set(self.prev));
    }
}

/// Access the currently-installed Process via the raw TLS pointer. Must only
/// be called from FFI fns invoked synchronously inside `run_in`. The Process
/// is owned by either the caller (run_in path) or by DEFAULT_PROCESS (run
/// path); the pointer is valid for the duration of the run.
pub fn current_process() -> &'static mut Process {
    let p = CURRENT_PROCESS.with(|c| c.get());
    assert!(
        !p.is_null(),
        "current_process(): no Process installed (running outside run_in?)"
    );
    unsafe { &mut *p }
}

pub fn try_current_process() -> Option<&'static mut Process> {
    let p = CURRENT_PROCESS.with(|c| c.get());
    (!p.is_null()).then(|| unsafe { &mut *p })
}

#[cfg(test)]
mod tests {
    use super::{Process, YIELD_REASON_REDUCTIONS};
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn aligned_closure_storage_is_taggable() {
        for _ in 0..128 {
            let mut buf = super::AlignedClosureStorage::zeroed();
            assert_eq!(buf.as_ptr() as u64 & crate::any_value::TAG_MASK, 0);
        }
    }

    #[test]
    fn reduction_budget_resets_and_spends() {
        let schemas = Rc::new(RefCell::new(crate::heap::SchemaRegistry::new()));
        let mut process = Process::new(schemas);
        process.reductions_per_quantum = 3;
        process.reset_reduction_budget();

        assert_eq!(process.reductions_remaining, 3);
        assert!(!process.spend_reductions(1));
        assert_eq!(process.reductions_remaining, 2);
        assert_eq!(process.reductions_executed, 1);
        assert!(process.spend_reductions(2));
        process.note_reduction_yield();
        assert_eq!(process.reductions_remaining, 0);
        assert_eq!(process.reduction_yields, 1);
        assert_eq!(
            process.yield_reasons & YIELD_REASON_REDUCTIONS,
            YIELD_REASON_REDUCTIONS
        );
    }
}
