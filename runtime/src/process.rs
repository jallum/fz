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
    // fz-ul4.29.5: closure_builder / closure_args fields removed. Closure
    // construction is inlined at codegen (alloc + stub_fp + kind-aware
    // capture writes); closure invocation is a direct call_indirect
    // through stub_fp, no arg staging needed.
    // Per-CompiledModule constants copied at make_process() time. See
    // fz-ul4.19.1 follow-up to move these behind an Rc<CompiledModuleConsts>.
    pub frame_sizes: Vec<u32>,
    /// Atom names indexed by id. Populated at task-setup time from the
    /// IR Module's atom_names. fz_value::debug::render reads this to
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
    pub mailbox: std::collections::VecDeque<crate::fz_value::FzValue>,
    /// fz-cps.1.2 — `Term::Receive` cutover per docs/cps-in-clif.md §4.
    /// When a task parks on `Receive`, `fz_receive_park` stashes the
    /// cont closure pointer here and sets `state = Blocked`. On message
    /// arrival the scheduler invokes a Cranelift thunk that
    /// `load parked_cont+16; call_indirect (msg, parked_cont)` —
    /// resuming the chain. Pointer because the closure lives in this
    /// Process's heap; layout per `Heap::alloc_closure`.
    pub parked_cont: *mut u8,
    /// fz-ul4.27.22.3 — per-Process halt-cont singletons indexed by
    /// repr kind (0=Tagged, 1=RawInt, 2=RawF64). Each slot holds a
    /// 24-byte closure whose +16 slot points at the matching
    /// `fz_halt_cont_body_<kind>` Cranelift body. Lazily allocated by
    /// `fz_get_halt_cont(addr, kind)` per kind, or pre-populated by
    /// `init_halt_cont_singletons` at make_process. Pointers alias
    /// Boxes in `static_closure_bufs`.
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
    /// in `CompiledModule.fn_halt_kinds`. Defaults to 0 (Tagged) if
    /// no entry is queued.
    pub pending_main_entry_fn_id: u32,
    /// fz-cps.1.7 — per-Process static zero-capture closure singletons.
    /// Indexed by lambda spec id (cl_sid). Null entries indicate "no
    /// singleton registered for this cl_sid." Each non-null entry points
    /// to a 24-byte off-heap buffer owned by `static_closure_bufs`
    /// (HeapHeader + code_ptr, zero captures). Off-heap so the per-process
    /// GC arena does not own them — singletons live for the Process's
    /// lifetime. See docs/cps-in-clif.md §8.2.
    pub static_closures: Vec<*mut u8>,
    /// fz-cps.1.7 — backing storage for `static_closures`. One Box per
    /// registered singleton. The raw pointer in `static_closures` aliases
    /// the start of the corresponding Box. Drop frees the boxes.
    pub static_closure_bufs: Vec<Box<[u64; 3]>>,

    // fz-02r.3 — mid-flight GC fields. Set by fz_yield_back_edge when
    // FZ_SHOULD_YIELD fires at a back-edge. The scheduler reads these to
    // run gc_mid_flight, then clears them before re-queueing.
    /// FnId.0 of the function that yielded. Informational (logging / future
    /// fairness accounting); not used for GC correctness.
    pub mid_flight_fn_id: u32,
    /// Number of live args stashed in `mid_flight_roots` (0..=8).
    pub mid_flight_root_count: u8,
    /// Slab of up to 8 live arg FzValues at the back-edge yield point.
    /// fz_yield_back_edge writes these; gc_mid_flight forwards them;
    /// the resume shim reads them back.
    pub mid_flight_roots: [crate::fz_value::FzValue; 8],
    /// Consecutive quanta elapsed since the last GC triggered. Used by
    /// the proactive shrinkage heuristic: after N quiet quanta the
    /// scheduler may shrink the heap below `last_gc_live_bytes * 2`.
    pub quiet_quanta: u8,
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
            // §6.3: initial size on spawn = SIZE_TABLE[0] (1 KiB). Cheney
            // promotes to a higher size_class on first GC if the working
            // set demands it; shrink hysteresis (§6.5 / fz-siu.11) brings
            // it back down for short-lived spikes.
            heap: crate::heap::Heap::new(crate::heap::SIZE_TABLE[0], schemas),
            halt_value: 0,
            map_builder: None,
            bs_builder: None,
            vec_builder: None,
            frame_sizes: Vec::new(),
            atom_names: Vec::new(),
            bs_tuple_arity1_schema: None,
            bs_tuple_arity3_schema: None,
            pid: 0,
            state: ProcessState::New,
            next_frame: std::ptr::null_mut(),
            mailbox: std::collections::VecDeque::new(),
            parked_cont: std::ptr::null_mut(),
            halt_cont_singletons: [std::ptr::null_mut(); 3],
            pending_closure_entry: std::ptr::null_mut(),
            pending_main_entry: std::ptr::null_mut(),
            pending_main_entry_fn_id: 0,
            static_closures: Vec::new(),
            static_closure_bufs: Vec::new(),
            mid_flight_fn_id: 0,
            mid_flight_root_count: 0,
            mid_flight_roots: [crate::fz_value::FzValue(0); 8],
            quiet_quanta: 0,
        }
    }

    /// fz-cps.1.7 — populate the static closure singleton table. Each
    /// target `(cl_sid, fn_id, code_ptr)` allocates one 24-byte off-heap
    /// closure object (HeapHeader + code_ptr, zero captures) and registers
    /// its pointer at `static_closures[cl_sid as usize]`. Idempotent only
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
        use crate::fz_value::{HeapHeader, HeapKind};
        // Size table by max cl_sid encountered.
        let max = targets.iter().map(|(s, _, _, _)| *s).max().unwrap_or(0) as usize;
        if self.static_closures.len() < max + 1 {
            self.static_closures.resize(max + 1, std::ptr::null_mut());
        }
        for (cl_sid, fn_id, code_ptr, halt_kind) in targets {
            // 24 bytes (HeapHeader 16 + code_ptr 8) with 8-byte alignment.
            let mut buf: Box<[u64; 3]> = Box::new([0u64; 3]);
            let base = buf.as_mut_ptr() as *mut u8;
            // fz-ul4.27.22.6: pack halt_kind into the closure flags so
            // fz_spawn_entry can pick the matching halt-cont singleton.
            let header = HeapHeader {
                kind: HeapKind::Closure as u16,
                flags: crate::fz_value::closure_flags_pack(0, *halt_kind as u16),
                size_bytes: 24,
                schema_id: 0,
                _reserved: *fn_id,
            };
            unsafe {
                std::ptr::write(base as *mut HeapHeader, header);
                std::ptr::write(base.add(16) as *mut u64, *code_ptr as u64);
            }
            self.static_closures[*cl_sid as usize] = base;
            self.static_closure_bufs.push(buf);
        }
    }

    /// fz-ul4.27.22.3 — pre-allocate halt-cont singletons for each kind
    /// (0=Tagged, 1=RawInt, 2=RawF64). Non-null `body_addrs[k]` seeds
    /// the corresponding slot; null entries leave the slot null
    /// (lazily filled by `fz_get_halt_cont` on first use). Called once
    /// per Process by `make_process`.
    pub fn init_halt_cont_singletons(&mut self, body_addrs: [*const u8; 3]) {
        use crate::fz_value::{HeapHeader, HeapKind};
        for (slot, addr) in body_addrs.iter().enumerate() {
            if addr.is_null() {
                continue;
            }
            let mut buf: Box<[u64; 3]> = Box::new([0u64; 3]);
            let base = buf.as_mut_ptr() as *mut u8;
            let header = HeapHeader {
                kind: HeapKind::Closure as u16,
                flags: 0,
                size_bytes: 24,
                schema_id: 0,
                _reserved: 0,
            };
            unsafe {
                std::ptr::write(base as *mut HeapHeader, header);
                std::ptr::write(base.add(16) as *mut u64, *addr as u64);
            }
            self.halt_cont_singletons[slot] = base;
            self.static_closure_bufs.push(buf);
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
    assert!(
        !p.is_null(),
        "current_process(): no Process installed (running outside run_in?)"
    );
    unsafe { &mut *p }
}
