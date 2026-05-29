//! Per-task runtime state.
//!
//! Lifted out of ir_codegen.rs by fz-ul4.23.4.2 so that any execution path
//! (JIT, interp, AOT) can stand up a Process without dragging the codegen
//! module along. The Process owns the per-task heap and builders; the Runtime
//! in src/runtime.rs schedules Processes. FFI/BIF fns in src/ir_runtime.rs
//! receive their `*mut Process` explicitly — compiled code passes the pinned
//! register, the interpreter threads it as a parameter — so there is no
//! ambient current-process and two schedulers can be live at once (fz-vdt).

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

/// Per-task runtime state. One Process per fz-level task; the scheduler hands
/// each running task's `*mut Process` to FFI fns explicitly — compiled code via
/// the pinned register, the interpreter as a threaded parameter — so there is
/// no ambient current-process.
///
/// libdispatch-style: TLS records the currently-running task's pointer per
/// worker; a task is owned by exactly one worker at a time (scheduler
/// invariant, .19.1). FFI fns do not yield, so TLS is stable within any FFI
/// call.
pub struct Process {
    pub heap: crate::heap::Heap,
    /// Execution-context dispatch table for this task: scheduler services,
    /// telemetry sink, and IR module, reached explicitly by BIFs instead of
    /// through thread-local singletons. Set by the owning scheduler (JIT
    /// `Runtime`, interpreter, or AOT shim) at each quantum entry; the pointee
    /// outlives any FFI call made under this process. Null until a scheduler
    /// installs one. The spawn/send/make_resource/timer/output BIFs dispatch
    /// through it — this is what replaced the `CURRENT_PROCESS`-era thread-local
    /// singletons (removed in `fz-vdt`), so two schedulers can be live at once.
    pub ctx: *mut crate::exec_ctx::ExecCtx,
    pub halt_value: i64,
    pub bs_builder: Option<crate::bitstr::BitWriter>,
    // fz-ul4.29.5: closure_builder / closure_args fields removed. Closure
    // construction is inlined at codegen; capture storage is schema-backed,
    // and invocation is a direct call_indirect through the closure code ptr.
    /// Node-global state shared by every Process in this execution context:
    /// the atom table and the per-fn frame-size table. Cloned (`Rc`) into each
    /// process, so spawn is a pointer copy, not a table copy. The atom table is
    /// shared and append-only across the context's processes — runtime atom
    /// interning is visible to every process, like the BEAM's node-global table.
    pub node: std::rc::Rc<Node>,
    pub bs_tuple_arity1_schema: Option<u32>,
    pub bs_tuple_arity3_schema: Option<u32>,
    // fz-ul4.19.1 scheduler-level fields. Populated when a Process is
    // owned by a Runtime; the standalone `make_process()` path
    // leaves these at defaults.
    pub pid: PidId,
    pub state: ProcessState,
    /// Current continuation pointer. While running, the trampoline holds
    /// this in a local; on yield/halt boundaries the Runtime swaps state
    /// here. v1 only writes this on halt (next_frame = null).
    pub next_frame: *mut u8,
    pub mailbox: std::collections::VecDeque<crate::any_value::AnyValueRef>,
    /// Receive-wait snapshot: the process is blocked in `receive`. Plain
    /// `receive()` installs an accept-any matcher; selective receive installs
    /// its compiled matcher. Either way, a hit clears `wait` and moves the
    /// outcome continuation into `runnable` for the scheduler to resume.
    pub wait: Option<Box<WaitState>>,
    /// The one re-entry verb: a `(self)`-callable closure the scheduler
    /// resumes via the single `fz_resume` shim. It is either a continuation
    /// (halt continuation baked into its captures, from a receive hit or
    /// mid-flight yield) or a fresh-task entry thunk (capturing the inner
    /// entry closure; the thunk supplies the halt continuation and enters it
    /// on first resume). `None` means no work is queued.
    pub runnable: Option<ClosureRef>,
    /// fz-ul4.27.22.3 — per-Process halt-cont singletons indexed by
    /// repr kind (0=ValueRef, 1=RawInt, 2=RawF64). Each slot holds a
    /// 24-byte closure whose +8 slot points at the matching
    /// `fz_halt_cont_body_<kind>` Cranelift body. Lazily allocated by
    /// `fz_get_halt_cont(addr, kind)` per kind, or pre-populated by
    /// `init_halt_cont_singletons` at make_process. Pointers alias
    /// aligned buffers in `static_closure_bufs`.
    pub halt_cont_singletons: [*mut u8; 3],
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
    /// closure and returned to the scheduler through `fz_yield_mid_flight_report`.
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
    /// Cumulative yields caused by allocation pressure expiring the current
    /// reduction budget.
    pub allocation_pressure_yields: u64,
    /// Compact reason bits pending for the next scheduler boundary. Allocation
    /// pressure (`expire_current_budget`) and the yielding back edge both set
    /// bits here; the boundary consumes them via `finish_yield_report` (which
    /// attributes the cumulative cause counters) and `boundary_maintenance`
    /// (which clears them). A bit can therefore be observed standing on a
    /// running process — e.g. a tail allocation trips the watermark after the
    /// final back edge and the process exits before yielding. The cumulative
    /// `reduction_yields` / `allocation_pressure_yields` counters, not this
    /// transient bitfield, are the authoritative yield-cause telemetry.
    /// See `YIELD_REASON_*`.
    pub yield_reasons: u8,
    /// Heap margin sampled before the compiled yield slow path starts building
    /// its scheduler continuation. Zero means no active sample.
    pub pending_yield_continuation_margin_before_bytes: u64,
    /// Largest scheduler continuation allocation window observed at a
    /// mid-flight yield. This includes the closure, scalar capture boxes, and
    /// materialized continuation state when the compiled slow path provides a
    /// begin sample.
    pub max_yield_continuation_bytes: u64,
    /// Lowest remaining in-block heap margin immediately before observed
    /// continuation materialization. Zero means no sample yet.
    pub min_yield_continuation_margin_before_bytes: u64,
    /// Lowest remaining in-block heap margin immediately after observed
    /// continuation materialization. Zero means no sample yet.
    pub min_yield_continuation_margin_after_bytes: u64,
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

/// The receive-wait snapshot a parked process carries. This is the
/// scheduler-facing name for the receive-matching record; the matcher,
/// pinned values, clause bodies, and after-timer continuation all live on it.
pub type WaitState = crate::park::ParkRecord;

/// A non-null pointer to a `(self)`-callable closure the scheduler can resume
/// through the `fz_resume` shim. Construction rejects null, so a
/// `Some(ClosureRef)` always names a real closure to run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClosureRef(*mut u8);

impl ClosureRef {
    /// Wrap a closure heap address; `None` if null (no work).
    pub fn new(ptr: *mut u8) -> Option<Self> {
        if ptr.is_null() {
            None
        } else {
            Some(Self(ptr))
        }
    }

    pub fn as_ptr(self) -> *mut u8 {
        self.0
    }
}

/// Node-global state shared by every Process in one execution context — a JIT
/// `Runtime`/`CompiledModule`, an interpreter instance, or an AOT run. The
/// smallest shared home a process points at; today it owns the atom table and
/// the per-fn frame-size table. Seeded from the linked module's compile-time
/// data and shared by `Rc` clone, so spawning a process copies a pointer rather
/// than cloning the tables. The obvious accretion point for later node-global
/// state (schemas, loaded code, pid allocation).
pub struct Node {
    /// Interned atom text, indexed by atom id. Seeded from the module's
    /// compile-time atoms; runtime atom interning (`process_atom_id`) appends
    /// here. Shared and append-only across the context's processes — the
    /// BEAM's node-global atom table, scaled to one execution context — so a
    /// runtime-interned atom has the same id in every process.
    pub atoms: std::cell::RefCell<Vec<String>>,
    /// Per-fn frame sizes, indexed by `FnId.0`. Read-only after construction
    /// (the JIT `fz_alloc_frame_dyn` reads it); empty under the interpreter and
    /// AOT, which do not use compiled frame tables.
    pub frame_sizes: Vec<u32>,
}

impl Node {
    pub fn new(atoms: Vec<String>, frame_sizes: Vec<u32>) -> Self {
        Self {
            atoms: std::cell::RefCell::new(atoms),
            frame_sizes,
        }
    }

    /// No node-global tables: the shape a bare `Process::new` carries.
    pub fn empty() -> Self {
        Self::new(Vec::new(), Vec::new())
    }
}

/// Per-`CompiledModule` construction inputs applied to a Process at spawn —
/// the bitstring-tuple schemas plus the static-closure and halt-cont singleton
/// seeds — as distinct from the per-spawn scheduler state (pid, mailbox, run
/// state) the spawner sets, and from the shared `Node` tables. `from_consts` is
/// the single construction site that applies them, so a newly-added field flows
/// through one path instead of diverging across the JIT, interpreter, and AOT
/// spawners.
pub struct CompiledModuleConsts {
    pub bs_tuple_arity1_schema: Option<u32>,
    pub bs_tuple_arity3_schema: Option<u32>,
    pub static_closure_targets: Vec<(
        u32,       /* cl_sid */
        u32,       /* fn_id */
        *const u8, /* code_ptr */
        u32,       /* halt_kind */
    )>,
    pub halt_cont_body_addrs: [*const u8; 3],
}

impl CompiledModuleConsts {
    /// No construction inputs: the shape a bare `Process::new` and the
    /// minimal-setup interpreter/AOT spawners carry.
    pub fn empty() -> Self {
        Self {
            bs_tuple_arity1_schema: None,
            bs_tuple_arity3_schema: None,
            static_closure_targets: Vec::new(),
            halt_cont_body_addrs: [std::ptr::null(); 3],
        }
    }
}

impl Process {
    /// The single Process construction site. Builds the heap and field
    /// defaults, applies the module constants, and seeds the static-closure
    /// and halt-cont singleton tables. Per-spawn scheduler state (run state,
    /// mailbox, pending entries) stays at defaults for the spawner to set.
    pub fn from_consts(
        node: std::rc::Rc<Node>,
        schemas: std::rc::Rc<std::cell::RefCell<crate::heap::SchemaRegistry>>,
        consts: &CompiledModuleConsts,
        pid: PidId,
        reductions_per_quantum: i32,
    ) -> Self {
        let mut p = Self {
            // §6.3: initial size on spawn = SIZE_TABLE[0] (1 KiB). Cheney
            // promotes to a higher size_class on first GC if the working
            // set demands it; shrink hysteresis (§6.5 / fz-siu.11) brings
            // it back down for short-lived spikes.
            heap: crate::heap::Heap::new(crate::heap::SIZE_TABLE[0], schemas),
            ctx: std::ptr::null_mut(),
            halt_value: 0,
            bs_builder: None,
            node,
            bs_tuple_arity1_schema: consts.bs_tuple_arity1_schema,
            bs_tuple_arity3_schema: consts.bs_tuple_arity3_schema,
            pid,
            state: ProcessState::New,
            next_frame: std::ptr::null_mut(),
            mailbox: std::collections::VecDeque::new(),
            wait: None,
            runnable: None,
            halt_cont_singletons: [std::ptr::null_mut(); 3],
            static_closures: Vec::new(),
            static_closure_bufs: Vec::new(),
            quiet_quanta: 0,
            scheduler_yields: 0,
            interpreter_yields: 0,
            reductions_remaining: reductions_per_quantum,
            reductions_per_quantum,
            reductions_executed: 0,
            reduction_yields: 0,
            allocation_pressure_yields: 0,
            yield_reasons: 0,
            pending_yield_continuation_margin_before_bytes: 0,
            max_yield_continuation_bytes: 0,
            min_yield_continuation_margin_before_bytes: 0,
            min_yield_continuation_margin_after_bytes: 0,
        };
        // An empty target set leaves `static_closures` empty (no cl_sid is
        // ever looked up); only build the table when the module carries one.
        if !consts.static_closure_targets.is_empty() {
            p.init_static_closures(&consts.static_closure_targets);
        }
        // Only seed halt-cont singletons when real body addrs are present.
        // `init_halt_cont_singletons` registers the `ClosureEnv0` schema even
        // for null addrs; running it on the empty/minimal paths would register
        // that schema at process setup and shift the compile-time-baked schema
        // ids the AOT runtime registry must match. Guarding keeps the bare
        // `Process::new`/interpreter/AOT-setup registries identical to a fresh
        // registry (only the JIT `make_process`, which supplies real addrs,
        // seeds them).
        if consts.halt_cont_body_addrs.iter().any(|a| !a.is_null()) {
            p.init_halt_cont_singletons(consts.halt_cont_body_addrs);
        }
        p
    }

    pub fn new(schemas: std::rc::Rc<std::cell::RefCell<crate::heap::SchemaRegistry>>) -> Self {
        Self::from_consts(
            std::rc::Rc::new(Node::empty()),
            schemas,
            &CompiledModuleConsts::empty(),
            0,
            DEFAULT_REDUCTIONS_PER_QUANTUM,
        )
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

    /// Queue a `(self)`-callable closure (continuation or entry thunk) as the
    /// next thing to resume. A null pointer clears the slot.
    pub fn set_runnable_closure(&mut self, closure: *mut u8) {
        self.runnable = ClosureRef::new(closure);
    }

    /// Take the queued runnable closure, clearing the slot.
    pub fn take_runnable_closure(&mut self) -> Option<*mut u8> {
        self.runnable.take().map(ClosureRef::as_ptr)
    }

    /// The queued runnable closure pointer, if any, without clearing it.
    pub fn runnable_ptr(&self) -> *mut u8 {
        self.runnable
            .map(ClosureRef::as_ptr)
            .unwrap_or(std::ptr::null_mut())
    }

    pub fn reset_reduction_budget(&mut self) {
        // Dispatch resets budget and reasons together: each quantum starts with
        // a clean slate so a reason bit cannot outlive the quantum that set it.
        self.reductions_remaining = self.reductions_per_quantum;
        self.yield_reasons = 0;
    }

    pub fn finish_yield_report(&mut self, remaining_reductions: i32, reason: u8) {
        // When allocation pressure expired the budget mid-quantum, the
        // reductions genuinely burned up to that point were already banked by
        // `expire_budget`, while `reductions_remaining` was still truthful.
        // Zeroing it there makes `reductions_per_quantum - remaining` an
        // invalid "burned" derivation, so re-deriving here would credit a
        // whole phantom quantum. In that case bank only the work done *since*
        // expiry — the cost of the back edge that finally observed the zeroed
        // budget and yielded; otherwise derive burned the normal way.
        let already_banked = (self.yield_reasons & YIELD_REASON_ALLOCATION_PRESSURE)
            == YIELD_REASON_ALLOCATION_PRESSURE;
        let burned = if already_banked {
            (-i64::from(remaining_reductions)).max(0)
        } else {
            i64::from(self.reductions_per_quantum) - i64::from(remaining_reductions)
        };
        self.reductions_remaining = remaining_reductions;
        if burned > 0 {
            self.reductions_executed = self.reductions_executed.saturating_add(burned as u64);
        }
        // Count cause off the accumulated reasons, not just this report's
        // bits: allocation pressure expires the budget directly on the
        // Process during the quantum (see `expire_budget`), so the back edge
        // that finally yields reports only REDUCTIONS while the
        // ALLOCATION_PRESSURE bit is already standing on `yield_reasons`.
        self.yield_reasons |= reason;
        let allocation_pressure = (self.yield_reasons & YIELD_REASON_ALLOCATION_PRESSURE)
            == YIELD_REASON_ALLOCATION_PRESSURE;
        if allocation_pressure {
            self.allocation_pressure_yields = self.allocation_pressure_yields.saturating_add(1);
        } else if (self.yield_reasons & YIELD_REASON_REDUCTIONS) == YIELD_REASON_REDUCTIONS {
            self.reduction_yields = self.reduction_yields.saturating_add(1);
        }
    }

    /// Force the reduction budget to expire so the next back edge yields,
    /// recording `reason`. Allocation pressure rides this path: it must drive
    /// `reductions_remaining` to zero to trip the single hot-path back-edge
    /// check. Before zeroing, bank the reductions genuinely burned so far —
    /// once per quantum, guarded on the reason bit — so the later
    /// `finish_yield_report` cannot misread the zeroed budget as a full
    /// quantum of work. See `finish_yield_report`.
    pub fn expire_budget(&mut self, reason: u8) {
        let first_pressure = reason == YIELD_REASON_ALLOCATION_PRESSURE
            && (self.yield_reasons & YIELD_REASON_ALLOCATION_PRESSURE) == 0;
        if first_pressure {
            let burned =
                i64::from(self.reductions_per_quantum) - i64::from(self.reductions_remaining);
            if burned > 0 {
                self.reductions_executed = self.reductions_executed.saturating_add(burned as u64);
            }
        }
        self.reductions_remaining = 0;
        self.yield_reasons |= reason;
    }

    pub fn clear_yield_reasons(&mut self) {
        self.yield_reasons = 0;
    }

    /// Scheduler-boundary maintenance shared by every execution mode. Decide
    /// whether this boundary must GC; if so, run the caller's mode-specific
    /// root-gather GC (compiled: runnable closure + mailbox; interpreter:
    /// resume args + after-conts) and reset the quiet-quanta shrink counter,
    /// otherwise advance it. Either way, clear the transient pressure and
    /// yield-reason signals so the next quantum starts clean.
    pub fn boundary_maintenance<E>(
        &mut self,
        gc_roots: impl FnOnce(&mut Self) -> Result<(), E>,
    ) -> Result<(), E> {
        if self.needs_boundary_gc() {
            gc_roots(self)?;
            self.quiet_quanta = 0;
        } else {
            self.quiet_quanta = self.quiet_quanta.saturating_add(1);
        }
        self.heap.clear_should_gc_flag();
        self.clear_yield_reasons();
        Ok(())
    }

    pub fn needs_boundary_gc(&self) -> bool {
        self.heap.should_gc()
            || (self.yield_reasons & YIELD_REASON_ALLOCATION_PRESSURE)
                == YIELD_REASON_ALLOCATION_PRESSURE
    }

    pub fn begin_yield_continuation_allocation(&mut self, margin_before: usize) {
        self.pending_yield_continuation_margin_before_bytes = margin_before as u64;
    }

    pub fn note_yield_continuation_allocation(&mut self, bytes: usize, margin_after: usize) {
        let observed_bytes = bytes as u64;
        let margin_after = margin_after as u64;
        let sampled_margin_before = self.pending_yield_continuation_margin_before_bytes;
        self.pending_yield_continuation_margin_before_bytes = 0;
        let margin_before = if sampled_margin_before == 0 {
            margin_after.saturating_add(observed_bytes)
        } else {
            sampled_margin_before
        };
        let bytes = margin_before
            .saturating_sub(margin_after)
            .max(observed_bytes);
        self.max_yield_continuation_bytes = self.max_yield_continuation_bytes.max(bytes);
        self.min_yield_continuation_margin_before_bytes = min_nonzero(
            self.min_yield_continuation_margin_before_bytes,
            margin_before,
        );
        self.min_yield_continuation_margin_after_bytes =
            min_nonzero(self.min_yield_continuation_margin_after_bytes, margin_after);
    }
}

fn min_nonzero(current: u64, candidate: u64) -> u64 {
    if current == 0 {
        candidate
    } else {
        current.min(candidate)
    }
}

// fz-vdt ctx.8: the ambient `CURRENT_PROCESS` thread-local, its
// `CurrentProcessGuard`, and the `current_process()`/`try_current_process()`
// accessors are gone. Every FFI/BIF now receives its `*mut Process` explicitly
// (in the pinned register for compiled code, threaded as a parameter for the
// interpreter), and the heap reaches its owning process for allocation-pressure
// budget expiry through `Heap::owner` (set per quantum at scheduler entry).
// This is what lets two schedulers be live at once on one thread.

#[cfg(test)]
mod tests {
    use super::{Process, YIELD_REASON_ALLOCATION_PRESSURE, YIELD_REASON_REDUCTIONS};
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
        process.finish_yield_report(-1, YIELD_REASON_REDUCTIONS);
        assert_eq!(process.reductions_remaining, -1);
        assert_eq!(process.reductions_executed, 4);
        assert_eq!(process.reduction_yields, 1);
        assert_eq!(process.allocation_pressure_yields, 0);
        assert_eq!(
            process.yield_reasons & YIELD_REASON_REDUCTIONS,
            YIELD_REASON_REDUCTIONS
        );
    }

    #[test]
    fn allocation_pressure_banks_only_genuine_reductions() {
        let schemas = Rc::new(RefCell::new(crate::heap::SchemaRegistry::new()));
        let mut process = Process::new(schemas);
        process.reductions_per_quantum = 4000;
        process.reset_reduction_budget();

        // Real work: back edges spent the budget down to 3950 (50 burned).
        process.reductions_remaining = 3950;

        // Allocation crosses the watermark mid-quantum and force-expires the
        // budget. The 50 genuinely-burned reductions are banked now, while
        // `reductions_remaining` is still truthful; the budget is then zeroed
        // to trip the next back edge.
        process.expire_budget(YIELD_REASON_ALLOCATION_PRESSURE);
        assert_eq!(process.reductions_remaining, 0);
        assert_eq!(process.reductions_executed, 50);

        // A second crossing in the same quantum must not double-count.
        process.expire_budget(YIELD_REASON_ALLOCATION_PRESSURE);
        assert_eq!(process.reductions_executed, 50);

        // The back edge that observes the zeroed budget yields, reporting a
        // slightly-negative remaining (its own cost). finish_yield_report
        // banks only that post-expiry work — NOT a re-credited full quantum.
        process.finish_yield_report(-1, YIELD_REASON_REDUCTIONS);
        assert_eq!(process.reductions_executed, 51);
        assert_eq!(process.allocation_pressure_yields, 1);
        assert_eq!(process.reduction_yields, 0);
    }

    #[test]
    fn reset_reduction_budget_clears_yield_reasons() {
        let schemas = Rc::new(RefCell::new(crate::heap::SchemaRegistry::new()));
        let mut process = Process::new(schemas);
        process.reductions_per_quantum = 5;
        process.reductions_remaining = 0;
        process.yield_reasons = YIELD_REASON_ALLOCATION_PRESSURE | YIELD_REASON_REDUCTIONS;

        process.reset_reduction_budget();

        assert_eq!(process.reductions_remaining, 5);
        assert_eq!(process.yield_reasons, 0);
    }

    #[test]
    fn allocation_pressure_yields_are_counted_by_cause() {
        let schemas = Rc::new(RefCell::new(crate::heap::SchemaRegistry::new()));
        let mut process = Process::new(schemas);

        process.finish_yield_report(
            9,
            YIELD_REASON_REDUCTIONS | YIELD_REASON_ALLOCATION_PRESSURE,
        );

        assert_eq!(process.reduction_yields, 0);
        assert_eq!(process.allocation_pressure_yields, 1);
        assert_eq!(
            process.yield_reasons & YIELD_REASON_ALLOCATION_PRESSURE,
            YIELD_REASON_ALLOCATION_PRESSURE
        );
    }
}
