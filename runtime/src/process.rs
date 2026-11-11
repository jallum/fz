//! Per-task runtime state.
//!
//! Any execution path
//! (JIT, interp, AOT) can stand up a Process without dragging the codegen
//! module along. The Process owns the per-task heap and builders; the Runtime
//! in src/runtime.rs schedules Processes. FFI/BIF fns in src/ir_runtime.rs
//! receive their `*mut Process` explicitly — compiled code passes the pinned
//! register, the interpreter threads it as a parameter — so there is no
//! ambient current-process and two schedulers can be live at once.

use crate::any_value::ClosureDenotationId;
use crate::function_denotation::FunctionDenotation;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{HashMap, VecDeque};
use std::ptr::null_mut;
use std::rc::Rc;
use std::sync::Arc;

use crate::any_value::AnyValueRef;
use crate::bitstr::BitWriter;
use crate::delivery::DeliveryLock;
use crate::exec_ctx::ExecCtx;
use crate::heap::{GcStats, Heap, SIZE_TABLE, SchemaRegistry};
use crate::park::ParkRecord;

pub const DEFAULT_REDUCTIONS_PER_QUANTUM: i32 = 4000;
pub const YIELD_REASON_REDUCTIONS: u8 = 1 << 0;
pub const YIELD_REASON_EXPLICIT: u8 = 1 << 1;

/// How a quantum ended, and so what a scheduler does with the process next.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Disposition {
    /// The process yielded and is still runnable: queue it behind the others.
    Requeue,
    /// The process parked on a receive that found nothing: a send or its
    /// after-timer wakes it.
    Parked,
    /// The process halted; its heap and its resources are released, never
    /// collected.
    Exited,
}

/// The scheduler boundary that asked for a collection. A halting process is
/// released rather than collected, so an exit is not a boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CollectionBoundary {
    /// The process ran out of budget and is still runnable.
    Yield,
    /// The process parked on a receive that found nothing.
    Park,
}

impl CollectionBoundary {
    pub fn as_str(self) -> &'static str {
        match self {
            CollectionBoundary::Yield => "yield",
            CollectionBoundary::Park => "park",
        }
    }
}

/// One heap collection a scheduler boundary performed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Collection {
    pub pid: PidId,
    pub boundary: CollectionBoundary,
    pub stats: GcStats,
}

/// Per-task runtime state. One Process per fz-level task; the scheduler hands
/// each running task's `*mut Process` to FFI fns explicitly — compiled code via
/// the pinned register, the interpreter as a threaded parameter — so there is
/// no ambient current-process.
///
/// A task is owned by exactly one worker at a time (scheduler invariant,
/// .19.1). FFI functions do not yield, so its explicit process pointer stays
/// valid for the duration of each call.
pub struct Process {
    /// The park record and the queue of gifts other processes made for this
    /// one, reachable only through the lock. Declared before `heap` so a
    /// process dropped with gifts still queued returns their storage first.
    pub delivery: DeliveryLock,
    pub heap: Heap,
    /// Execution-context dispatch table for this task: scheduler services and
    /// output context, reached explicitly by BIFs instead of through
    /// thread-local singletons. Set by the owning scheduler (JIT
    /// `Runtime`, interpreter, or AOT shim) at each quantum entry; the pointee
    /// outlives any FFI call made under this process. Null until a scheduler
    /// installs one. The spawn/send/fault/timer/output BIFs dispatch
    /// through it, so two schedulers can be live at once.
    pub ctx: *mut ExecCtx,
    pub halt_value: i64,
    /// Whether the process failed: set only by `fz_panic`, the one route an
    /// uncaught failure takes, never inferred from `halt_value`. Drivers read
    /// it at the exit boundary: a failed main process exits 1.
    pub failed: bool,
    pub bs_builder: Option<BitWriter>,
    /// Node-global state shared by every Process in this execution context:
    /// the atom table and the per-fn frame-size table. Cloned (`Rc`) into each
    /// process, so spawn is a pointer copy, not a table copy. The atom table is
    /// shared and append-only across the context's processes — runtime atom
    /// interning is visible to every process, like the BEAM's node-global table.
    pub node: Rc<Node>,
    // Scheduler-level fields. Populated when a Process is
    // owned by a Runtime; the standalone `make_process()` path
    // leaves these at defaults.
    pub pid: PidId,
    pub state: ProcessState,
    /// Current continuation pointer. While running, the trampoline holds
    /// this in a local; on yield/halt boundaries the Runtime swaps state
    /// here. v1 only writes this on halt (next_frame = null).
    pub next_frame: *mut u8,
    pub mailbox: VecDeque<AnyValueRef>,
    /// The one re-entry verb: a `(self)`-callable closure the scheduler
    /// resumes via the single `fz_resume` shim. It is either a continuation
    /// (halt continuation baked into its captures, from a receive hit or
    /// mid-flight yield) or a fresh-task entry thunk (capturing the inner
    /// entry closure; the thunk supplies the halt continuation and enters it
    /// on first resume). `None` means no work is queued.
    pub runnable: Option<ClosureRef>,

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
    /// Cumulative construction-owned list-retention attempts.
    pub list_retention_attempts: u64,
    /// Attempts that returned the source cell, unchanged or after guarded rewrite.
    pub list_retention_hits: u64,
    /// Cumulative resource destructors the scheduler dispatched for this
    /// process, after collections and at exit.
    pub dtors_dispatched: u64,
    /// Compact reason bits pending for the next scheduler boundary. A yielding
    /// back edge sets the reduction bit, and the boundary consumes it via
    /// `finish_yield_report` and `end_quantum`. Collection timing is
    /// decided by the heap, not here: collection has no authority to force a
    /// scheduler yield. See `YIELD_REASON_*`.
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
    /// Created and not yet queued.
    New,
    /// In the run queue. Only `SchedulingCore::make_runnable` writes this, so
    /// a process is queued exactly when it is Ready.
    Ready,
    /// Installed on a worker, executing a quantum.
    Running,
    /// Off the run queue, waiting to be made runnable: a receive that found no
    /// message, or a process kept alive between entries.
    Blocked,
    /// Halted; halt_value is final. Never runs again.
    Exited,
}

/// The receive-wait snapshot a parked process carries. This is the
/// scheduler-facing name for the receive-matching record; the matcher,
/// pinned values, clause bodies, and after-timer continuation all live on it.
pub type WaitState = ParkRecord;

/// A `(self)`-callable closure the scheduler can resume through the `fz_resume`
/// shim. It is a closure ref, so a closure the program ships as read-only data
/// keeps its literal bit. A `ClosureRef` always names a real closure to run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClosureRef(AnyValueRef);

impl ClosureRef {
    pub fn new(closure: AnyValueRef) -> Self {
        closure.closure_addr().expect("a runnable closure is a closure ref");
        assert!(
            !closure.is_empty_list() && !closure.storage_addr().is_null(),
            "a runnable closure is not null"
        );
        Self(closure)
    }

    pub fn as_ref(self) -> AnyValueRef {
        self.0
    }
}

/// The node-global atom table: text↔id, append-only. Seeded from a module's
/// compile-time atoms (ids 0..N, dense) and grown by runtime interning.
///
/// Atoms are integers once interned; the table is touched only at the
/// text↔index boundary (interning a new atom, rendering one to text). It keeps
/// both directions so each is O(1): `by_id` for id→text (dense `Vec`, since
/// atoms are append-only with no gaps — the next id is just `by_id.len()`),
/// and `by_name` for text→id so interning is a hash lookup, not a scan. The
/// BEAM shape (index array + interning hash table), scaled to one node.
pub struct AtomTable {
    by_id: Vec<String>,
    by_name: HashMap<String, u32>,
}

impl AtomTable {
    pub fn new(names: Vec<String>) -> Self {
        let by_name = names.iter().enumerate().map(|(i, n)| (n.clone(), i as u32)).collect();
        Self { by_id: names, by_name }
    }

    /// Return the atom's id, allocating a fresh one (the next dense index) if
    /// the name is new. O(1).
    pub fn intern(&mut self, name: &str) -> u32 {
        if let Some(&id) = self.by_name.get(name) {
            return id;
        }
        let id = self.by_id.len() as u32;
        self.by_id.push(name.to_string());
        self.by_name.insert(name.to_string(), id);
        id
    }

    /// The atom's text, or `None` if `id` is out of range. O(1).
    pub fn name(&self, id: u32) -> Option<&str> {
        self.by_id.get(id as usize).map(String::as_str)
    }

    /// Replace the whole table with `names` (ids 0..len). Used by the
    /// interpreter when a REPL chunk's code image carries a new cumulative
    /// atom set.
    pub fn reset_from(&mut self, names: &[String]) {
        self.by_id = names.to_vec();
        self.by_name = names.iter().enumerate().map(|(i, n)| (n.clone(), i as u32)).collect();
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
    /// The node-global atom table. Shared and append-only across the context's
    /// processes, so a runtime-interned atom has the same id in every process —
    /// the BEAM's node-global atom table, scaled to one execution context.
    /// Reached through `intern_atom` / `atom_name` / `reset_atoms`, never
    /// directly, so the interior mutability stays an implementation detail.
    atoms: RefCell<AtomTable>,
    /// Per-fn frame sizes, indexed by `FnId.0`. Read-only after construction
    /// (the JIT `fz_alloc_frame_dyn` reads it via `frame_size`); empty under
    /// the interpreter and AOT, which do not use compiled frame tables.
    frame_sizes: Vec<u32>,
    closure_denotations: RefCell<HashMap<ClosureDenotationId, Arc<FunctionDenotation>>>,
}

impl Node {
    pub fn new(atoms: Vec<String>, frame_sizes: Vec<u32>) -> Self {
        Self {
            atoms: RefCell::new(AtomTable::new(atoms)),
            frame_sizes,
            closure_denotations: RefCell::new(HashMap::new()),
        }
    }

    /// No node-global tables: the shape a bare `Process::new` carries.
    pub fn empty() -> Self {
        Self::new(Vec::new(), Vec::new())
    }

    pub fn register_closure_denotation(&self, id: ClosureDenotationId, origin: Arc<FunctionDenotation>) {
        id.user_index();
        let mut origins = self.closure_denotations.borrow_mut();
        match origins.entry(id) {
            std::collections::hash_map::Entry::Occupied(existing) => {
                if !Arc::ptr_eq(existing.get(), &origin) {
                    assert_eq!(existing.get(), &origin, "closure source denotations are immutable");
                }
            }
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(origin);
            }
        }
    }

    pub fn compare_closure_denotations(&self, left: ClosureDenotationId, right: ClosureDenotationId) -> Ordering {
        left.user_index();
        right.user_index();
        let origins = self.closure_denotations.borrow();
        let left = origins
            .get(&left)
            .expect("published closure must have a source denotation");
        let right = origins
            .get(&right)
            .expect("published closure must have a source denotation");
        if Arc::ptr_eq(left, right) {
            Ordering::Equal
        } else {
            left.semantic_cmp(right)
        }
    }

    #[cfg(test)]
    pub(crate) fn closure_denotation(&self, id: ClosureDenotationId) -> Arc<FunctionDenotation> {
        Arc::clone(
            self.closure_denotations
                .borrow()
                .get(&id)
                .expect("registered denotation"),
        )
    }

    /// Intern an atom into the node-global table, returning its id.
    pub fn intern_atom(&self, name: &str) -> u32 {
        self.atoms.borrow_mut().intern(name)
    }

    /// The atom's text, or `None` if `id` is unknown. Returns an owned `String`
    /// so callers do not hold the table borrow.
    pub fn atom_name(&self, id: u32) -> Option<String> {
        self.atoms.borrow().name(id).map(str::to_owned)
    }

    /// Compare atom ids by their node-global names without cloning either
    /// name. Published values always name registered atoms.
    pub fn cmp_atom_names(&self, left_id: u32, right_id: u32) -> Ordering {
        let atoms = self.atoms.borrow();
        let left = atoms.name(left_id).expect("published atom must be registered");
        let right = atoms.name(right_id).expect("published atom must be registered");
        left.cmp(right)
    }

    pub fn atom_names(&self) -> Vec<String> {
        self.atoms.borrow().by_id.clone()
    }

    /// Replace the atom table (interpreter REPL code-image refresh).
    pub fn reset_atoms(&self, names: &[String]) {
        self.atoms.borrow_mut().reset_from(names);
    }

    /// The compiled frame size for `fn_id`, or `None` if absent.
    pub fn frame_size(&self, fn_id: u32) -> Option<u32> {
        self.frame_sizes.get(fn_id as usize).copied()
    }
}

impl Process {
    /// The single Process construction site. Builds the heap and field
    /// defaults. Per-spawn scheduler state (run state, mailbox, pending
    /// entries) stays at defaults for the spawner to set.
    pub fn with_node(
        node: Rc<Node>,
        schemas: Rc<RefCell<SchemaRegistry>>,
        pid: PidId,
        reductions_per_quantum: i32,
    ) -> Self {
        Self {
            // §6.3: initial size on spawn = SIZE_TABLE[0] (1 KiB). Cheney
            // promotes to a larger block capacity on first GC if the working
            // set demands it; shrink hysteresis (§6.5) brings
            // it back down for short-lived spikes.
            delivery: DeliveryLock::default(),
            heap: Heap::with_node(SIZE_TABLE[0], schemas, Rc::clone(&node)),
            ctx: null_mut(),
            halt_value: 0,
            failed: false,
            bs_builder: None,
            node,
            pid,
            state: ProcessState::New,
            next_frame: null_mut(),
            mailbox: VecDeque::new(),
            runnable: None,
            scheduler_yields: 0,
            interpreter_yields: 0,
            reductions_remaining: reductions_per_quantum,
            reductions_per_quantum,
            reductions_executed: 0,
            reduction_yields: 0,
            list_retention_attempts: 0,
            list_retention_hits: 0,
            dtors_dispatched: 0,
            yield_reasons: 0,
            pending_yield_continuation_margin_before_bytes: 0,
            max_yield_continuation_bytes: 0,
            min_yield_continuation_margin_before_bytes: 0,
            min_yield_continuation_margin_after_bytes: 0,
        }
    }

    pub fn new(schemas: Rc<RefCell<SchemaRegistry>>) -> Self {
        Self::with_node(Rc::new(Node::empty()), schemas, 0, DEFAULT_REDUCTIONS_PER_QUANTUM)
    }

    /// Clear scheduler-owned pointers before handing this process back to a
    /// non-scheduler subsystem such as the quoted-source heap.
    pub fn detach_runtime_state(&mut self) {
        self.ctx = null_mut();
    }

    /// Queue a `(self)`-callable closure (continuation or entry thunk) as the
    /// next thing to resume.
    pub fn set_runnable_closure(&mut self, closure: AnyValueRef) {
        self.runnable = Some(ClosureRef::new(closure));
    }

    /// Take the queued runnable closure, clearing the slot.
    pub fn take_runnable_closure(&mut self) -> Option<AnyValueRef> {
        self.runnable.take().map(ClosureRef::as_ref)
    }

    /// The queued runnable closure, if any, without clearing it.
    pub fn runnable_closure(&self) -> Option<AnyValueRef> {
        self.runnable.map(ClosureRef::as_ref)
    }

    pub fn reset_reduction_budget(&mut self) {
        // Dispatch resets budget and reasons together: each quantum starts with
        // a clean slate so a reason bit cannot outlive the quantum that set it.
        self.reductions_remaining = self.reductions_per_quantum;
        self.yield_reasons = 0;
    }

    pub fn finish_yield_report(&mut self, remaining_reductions: i32, reason: u8) {
        let burned = i64::from(self.reductions_per_quantum) - i64::from(remaining_reductions);
        self.reductions_remaining = remaining_reductions;
        if burned > 0 {
            self.reductions_executed = self.reductions_executed.saturating_add(burned as u64);
        }
        self.yield_reasons |= reason;
        if (self.yield_reasons & YIELD_REASON_REDUCTIONS) == YIELD_REASON_REDUCTIONS {
            self.reduction_yields = self.reduction_yields.saturating_add(1);
        }
    }

    pub fn clear_yield_reasons(&mut self) {
        self.yield_reasons = 0;
    }

    /// How the quantum a process just ran ended: still runnable, waiting on a
    /// receive, or halted.
    pub fn quantum_end(&self) -> Disposition {
        match self.state {
            ProcessState::Running if self.runnable.is_some() => Disposition::Requeue,
            ProcessState::Blocked => Disposition::Parked,
            _ => Disposition::Exited,
        }
    }

    /// Collect this process's heap. The roots are everything the process
    /// holds into its heap, in one flat slice: the runnable closure, the park
    /// record (clause bodies, after body, pinned values), the mailbox and the
    /// caller's `transient` values. Each holds its forwarded value on return.
    ///
    /// The delivery lock is held throughout, so a sender cannot probe the
    /// park record while its closures and pinned values move. Gifts waiting in
    /// the in-queue are not roots (see `Heap::collect`).
    pub fn collect(&mut self, transient: &mut [AnyValueRef]) -> GcStats {
        let mut delivery = self.delivery.lock();
        let park = delivery.park_mut();
        let mut roots: Vec<AnyValueRef> = Vec::new();
        roots.extend(self.runnable_closure());
        if let Some(park) = park.as_deref() {
            roots.extend(park.clause_bodies.iter().copied());
            roots.extend(park.after_cont);
            roots.extend(park.pinned.iter().copied());
        }
        roots.extend(self.mailbox.iter().copied());
        roots.extend_from_slice(transient);

        let stats = self.heap.collect(&mut roots);

        let mut forwarded = roots.into_iter();
        let mut next = || forwarded.next().expect("one forwarded root per gathered root");
        if self.runnable.is_some() {
            self.runnable = Some(ClosureRef::new(next()));
        }
        if let Some(park) = park {
            for body in park.clause_bodies.iter_mut() {
                *body = next();
            }
            if park.after_cont.is_some() {
                park.after_cont = Some(next());
            }
            for pinned in park.pinned.iter_mut() {
                *pinned = next();
            }
        }
        for message in self.mailbox.iter_mut() {
            *message = next();
        }
        for value in transient.iter_mut() {
            *value = next();
        }
        stats
    }

    pub fn needs_boundary_gc(&self) -> bool {
        self.heap.should_gc()
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
        let bytes = margin_before.saturating_sub(margin_after).max(observed_bytes);
        self.max_yield_continuation_bytes = self.max_yield_continuation_bytes.max(bytes);
        self.min_yield_continuation_margin_before_bytes =
            min_nonzero(self.min_yield_continuation_margin_before_bytes, margin_before);
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

// There is no ambient current-process. Every FFI/BIF receives its `*mut Process` explicitly
// (in the pinned register for compiled code, threaded as a parameter for the
// interpreter). This is what lets two schedulers be live at once on one thread.

#[cfg(test)]
#[path = "process_test.rs"]
mod process_test;
