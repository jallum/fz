//! Per-task runtime state.
//!
//! Any execution path
//! (JIT, interp, AOT) can stand up a Process without dragging the codegen
//! module along. The Process owns the per-task heap and builders; the Runtime
//! in src/runtime.rs schedules Processes. FFI/BIF fns in src/ir_runtime.rs
//! receive their `*mut Process` explicitly — compiled code passes the pinned
//! register, the interpreter threads it as a parameter — so there is no
//! ambient current-process and two schedulers can be live at once.

use crate::any_value::{ClosureDenotationId, ValueKind, bitstring_object_image, closure_header_word};
use crate::function_denotation::FunctionDenotation;
use crate::term_hash::name_hash;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{HashMap, VecDeque};
use std::num::NonZeroU64;
use std::ptr::null_mut;
use std::rc::Rc;
use std::sync::Arc;

use crate::any_value::{AnyValue, AnyValueRef};
use crate::bitstr::BitWriter;
use crate::delivery::DeliveryLock;
use crate::exec_ctx::ExecCtx;
use crate::handler_stack::HandlerStack;
use crate::heap::{Footprint, GcStats, Heap, SIZE_TABLE, SchemaRegistry};
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
    /// The thread's memory once the collection finished: every block handed
    /// out and every live off-heap binary buffer, and the blocks resting idle.
    pub footprint: Footprint,
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
    /// Whether the process ended by a raise no handler took: set only by the
    /// raise route, never inferred from `halt_value`. An exit with a shutdown
    /// reason ends a process this way too, with status 0.
    pub failed: bool,
    /// The status a process that ended by an uncaught raise leaves: 1, or what
    /// the exit's shutdown reason says. Drivers read it at the exit boundary
    /// for the main process; it is 0 until the process fails.
    pub exit_status: i32,
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
    /// The compiled handler a raise just delivered: the materialized handler
    /// template, applied to `(kind, value, name)`. Unlike `runnable`, which
    /// means "queued for the scheduler", this slot is only ever filled while a
    /// quantum is unwinding to its entry; `run_quantum` resumes it before the
    /// quantum ends.
    pub delivered: Option<ClosureRef>,
    /// The handlers a raise can reach, innermost on top. See [`HandlerStack`].
    pub handlers: HandlerStack,
    /// A raise waiting for the interpreter's handler frame. Set by `fz_panic`
    /// when the innermost handler is the interpreter's; the interpreter takes
    /// it when the panicking extern returns.
    pub raised: Option<Raised>,
    /// Cumulative raises this process delivered to a handler rather than
    /// failing on.
    pub raises_delivered: u64,
    /// The machine-stack address at which the running quantum began; 0 when no
    /// quantum is running. A raise measures its depth against it.
    pub stack_base: usize,

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
    /// Cumulative quanta that ended with the process parked on a receive.
    pub parks: u64,
    /// Cumulative construction-owned list-retention attempts.
    pub list_retention_attempts: u64,
    /// Attempts that returned the source cell, unchanged or after guarded rewrite.
    pub list_retention_hits: u64,
    /// Cumulative updates of a struct in its own layout.
    pub struct_retention_attempts: u64,
    /// Updates that stored into the base itself, rewriting it in place.
    pub struct_retention_hits: u64,
    /// Cumulative resource destructors the scheduler dispatched for this
    /// process, after collections and at exit.
    pub dtors_dispatched: u64,
    /// Cumulative body frames copied to the heap tip because a store found
    /// the frame in a block a collection had kept (`fz_frame_for_write`).
    pub frame_copies: u64,
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
/// keeps its literal bit. A `ClosureRef` always names a real closure to run,
/// so its word is never zero and an `Option<ClosureRef>` is one word that is
/// zero when empty: compiled code reads that word.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClosureRef(NonZeroU64);

impl ClosureRef {
    pub fn new(closure: AnyValueRef) -> Self {
        closure.closure_addr().expect("a runnable closure is a closure ref");
        assert!(
            !closure.is_empty_list() && !closure.storage_addr().is_null(),
            "a runnable closure is not null"
        );
        Self(NonZeroU64::new(closure.raw_word()).expect("a closure ref word is not zero"))
    }

    pub fn as_ref(self) -> AnyValueRef {
        AnyValueRef::from_raw_word(self.0.get()).expect("a ClosureRef holds a valid ref word")
    }
}

/// A raise delivered to an interpreter handler, as the three values every
/// handler receives: the kind atom, the raised value, and the exception's
/// name atom (`nil` when the value is not an exception).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Raised {
    pub kind: AnyValueRef,
    pub value: AnyValueRef,
    pub name: AnyValueRef,
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
///
/// Each atom also keeps the hash of its name, computed once when the atom is
/// interned. A term hash reads it, so it depends on the name and never on the
/// id, which follows the order atoms happened to be interned in.
///
/// Each atom keeps the first eight bytes of its name too, as a word. Atoms
/// order by name, and for most pairs that word settles the order without
/// either name being read.
pub struct AtomTable {
    by_id: Vec<AtomName>,
    name_hashes: Vec<u64>,
    name_prefixes: Vec<u64>,
    by_name: HashMap<AtomName, u32>,
}

/// The first eight bytes of a name as one big-endian word, a shorter name
/// padded with zeros. Two prefixes that differ order as their names do.
fn name_prefix(name: &str) -> u64 {
    let mut prefix = [0u8; 8];
    let taken = name.len().min(8);
    prefix[..taken].copy_from_slice(&name.as_bytes()[..taken]);
    u64::from_be_bytes(prefix)
}

/// An atom's text, shared by every owner of the name: a module's atom list,
/// the node's table and a reader holding it all point at one allocation.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AtomName(Arc<str>);

impl AtomName {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::borrow::Borrow<str> for AtomName {
    fn borrow(&self) -> &str {
        &self.0
    }
}

impl From<&str> for AtomName {
    fn from(name: &str) -> Self {
        Self(Arc::from(name))
    }
}

impl std::ops::Deref for AtomName {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

impl PartialEq<str> for AtomName {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<&str> for AtomName {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl std::fmt::Display for AtomName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_str().fmt(f)
    }
}

impl std::fmt::Debug for AtomName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self.as_str(), f)
    }
}

impl AtomTable {
    pub fn new(names: Vec<AtomName>) -> Self {
        let by_name = names
            .iter()
            .enumerate()
            .map(|(id, name)| (name.clone(), id as u32))
            .collect();
        let name_hashes = names.iter().map(|name| name_hash(name)).collect();
        let name_prefixes = names.iter().map(|name| name_prefix(name)).collect();
        Self {
            by_id: names,
            name_hashes,
            name_prefixes,
            by_name,
        }
    }

    /// Return the atom's id, allocating a fresh one (the next dense index) if
    /// the name is new. O(1).
    pub fn intern(&mut self, name: &str) -> u32 {
        match self.id_of(name) {
            Some(id) => id,
            None => self.append(AtomName::from(name)),
        }
    }

    /// Like `intern`, for a name already shared with another owner: a new name
    /// is appended as that same allocation.
    pub fn intern_shared(&mut self, name: &AtomName) -> u32 {
        match self.id_of(name) {
            Some(id) => id,
            None => self.append(name.clone()),
        }
    }

    fn append(&mut self, name: AtomName) -> u32 {
        let id = self.by_id.len() as u32;
        self.name_hashes.push(name_hash(&name));
        self.name_prefixes.push(name_prefix(&name));
        self.by_id.push(name.clone());
        self.by_name.insert(name, id);
        id
    }

    /// The atom's id, or `None` if the name was never interned. O(1).
    fn id_of(&self, name: &str) -> Option<u32> {
        self.by_name.get(name).copied()
    }

    /// The atom's text, or `None` if `id` is out of range. O(1).
    pub fn name(&self, id: u32) -> Option<&AtomName> {
        self.by_id.get(id as usize)
    }

    /// The hash of the atom's name, or `None` if `id` is out of range. O(1).
    pub fn name_hash(&self, id: u32) -> Option<u64> {
        self.name_hashes.get(id as usize).copied()
    }
}

/// Node-global state shared by every Process in one execution context — a JIT
/// `Runtime`/`CompiledModule`, an interpreter instance, or an AOT run. The
/// smallest shared home a process points at; today it owns the atom table and
/// the closure denotations. Seeded from the linked module's compile-time
/// data and shared by `Rc` clone, so spawning a process copies a pointer rather
/// than cloning the tables. The obvious accretion point for later node-global
/// state (schemas, loaded code, pid allocation).
pub struct Node {
    /// The node-global atom table. Shared and append-only across the context's
    /// processes, so a runtime-interned atom has the same id in every process —
    /// the BEAM's node-global atom table, scaled to one execution context.
    /// Reached through `intern_atom` / `atom_name`, never
    /// directly, so the interior mutability stays an implementation detail.
    atoms: RefCell<AtomTable>,
    closure_denotations: RefCell<HashMap<ClosureDenotationId, ClosureOrigin>>,
    static_closures: RefCell<HashMap<StaticClosureKey, Box<StaticClosure>>>,
    static_bitstrings: RefCell<HashMap<StaticBitstringKey, Box<[StaticObjectChunk]>>>,
}

/// A bitstring literal's bytes and bit length; one object exists per key.
type StaticBitstringKey = (Box<[u8]>, u64);

/// Sixteen bytes of a read-only object the node owns, 16-aligned like a heap
/// object.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
struct StaticObjectChunk([u8; 16]);

/// What a zero-capture closure's header and code word say; one object exists
/// per key.
type StaticClosureKey = (ClosureDenotationId, u16, u64);

/// A zero-capture closure outside every process heap: the header word and the
/// code word, the whole of a heap closure with no captures. 16-aligned like a
/// heap object.
#[repr(C, align(16))]
struct StaticClosure([u64; 2]);

/// What the node keeps for a closure's denotation: its source origin, and the
/// hash of that origin, computed once at registration.
struct ClosureOrigin {
    origin: Arc<FunctionDenotation>,
    hash: u64,
}

impl Node {
    pub fn new(atoms: Vec<AtomName>) -> Self {
        Self {
            atoms: RefCell::new(AtomTable::new(atoms)),
            closure_denotations: RefCell::new(HashMap::new()),
            static_closures: RefCell::new(HashMap::new()),
            static_bitstrings: RefCell::new(HashMap::new()),
        }
    }

    /// No node-global tables: the shape a bare `Process::new` carries.
    pub fn empty() -> Self {
        Self::new(Vec::new())
    }

    pub fn register_closure_denotation(&self, id: ClosureDenotationId, origin: Arc<FunctionDenotation>) {
        id.user_index();
        let mut origins = self.closure_denotations.borrow_mut();
        match origins.entry(id) {
            std::collections::hash_map::Entry::Occupied(existing) => {
                if !Arc::ptr_eq(&existing.get().origin, &origin) {
                    assert_eq!(
                        &existing.get().origin,
                        &origin,
                        "closure source denotations are immutable"
                    );
                }
            }
            std::collections::hash_map::Entry::Vacant(entry) => {
                let hash = origin.semantic_hash();
                entry.insert(ClosureOrigin { origin, hash });
            }
        }
    }

    pub fn compare_closure_denotations(&self, left: ClosureDenotationId, right: ClosureDenotationId) -> Ordering {
        left.user_index();
        right.user_index();
        let origins = self.closure_denotations.borrow();
        let left = &origins
            .get(&left)
            .expect("published closure must have a source denotation")
            .origin;
        let right = &origins
            .get(&right)
            .expect("published closure must have a source denotation")
            .origin;
        if Arc::ptr_eq(left, right) {
            Ordering::Equal
        } else {
            left.semantic_cmp(right)
        }
    }

    /// The hash of a closure's source denotation: equal for every id whose
    /// denotations compare equal, and read from the table, not recomputed.
    pub fn closure_denotation_hash(&self, id: ClosureDenotationId) -> u64 {
        id.user_index();
        self.closure_denotations
            .borrow()
            .get(&id)
            .expect("published closure must have a source denotation")
            .hash
    }

    /// The module atom and the name of the function a closure was made from,
    /// when it is a named function in a module: what `&Mod.fun/arity` spells.
    /// A lambda and a function outside every module have no such spelling.
    pub fn closure_module_and_name(&self, id: ClosureDenotationId) -> Option<(String, String)> {
        id.user_index();
        let origins = self.closure_denotations.borrow();
        let denotation = &origins
            .get(&id)
            .expect("published closure must have a source denotation")
            .origin;
        if denotation.is_generated() {
            return None;
        }
        let (module, name) = denotation.elixir_module_and_name();
        Some((module?, name))
    }

    #[cfg(test)]
    pub(crate) fn closure_denotation(&self, id: ClosureDenotationId) -> Arc<FunctionDenotation> {
        Arc::clone(
            &self
                .closure_denotations
                .borrow()
                .get(&id)
                .expect("registered denotation")
                .origin,
        )
    }

    /// The one read-only closure with no captures that carries `code_word` as
    /// its code, under `denotation` and `arity`. It lives as long as the node,
    /// outside every process heap, and its ref carries the literal bit: a
    /// collection leaves it in place and a deep copy shares it. Asking again
    /// returns the same ref.
    pub fn static_closure(&self, denotation: ClosureDenotationId, arity: u16, code_word: u64) -> AnyValueRef {
        let mut table = self.static_closures.borrow_mut();
        let object = table.entry((denotation, arity, code_word)).or_insert_with(|| {
            let mut object = Box::new(StaticClosure([0; 2]));
            object.0[0] = closure_header_word(denotation, 0, 0, arity);
            object.0[1] = code_word;
            object
        });
        let addr = &mut object.0 as *mut [u64; 2] as *mut u8;
        AnyValueRef::from_heap_object(ValueKind::CLOSURE, addr)
            .expect("a boxed object has an address")
            .literal()
    }

    /// The one read-only bitstring holding `bytes` as `bit_len` bits. Like a
    /// static closure it lives as long as the node, outside every process
    /// heap, and its ref carries the literal bit. Asking again returns the
    /// same ref.
    pub fn static_bitstring(&self, bytes: &[u8], bit_len: u64) -> AnyValueRef {
        let mut table = self.static_bitstrings.borrow_mut();
        let object = table.entry((bytes.into(), bit_len)).or_insert_with(|| {
            bitstring_object_image(bytes, bit_len)
                .as_chunks::<16>()
                .0
                .iter()
                .map(|chunk| StaticObjectChunk(*chunk))
                .collect()
        });
        AnyValueRef::from_heap_object(ValueKind::BITSTRING, object.as_mut_ptr().cast())
            .expect("a boxed object has an address")
            .literal()
    }

    /// Intern an atom into the node-global table, returning its id.
    pub fn intern_atom(&self, name: &str) -> u32 {
        self.atoms.borrow_mut().intern(name)
    }

    /// The atom's text, or `None` if `id` is unknown.
    pub fn atom_name(&self, id: u32) -> Option<AtomName> {
        self.atoms.borrow().name(id).cloned()
    }

    /// Intern a name its caller already shares: a new atom keeps that
    /// allocation instead of copying the text.
    pub fn intern_shared_atom(&self, name: &AtomName) -> u32 {
        self.atoms.borrow_mut().intern_shared(name)
    }

    /// The hash of the atom's name, kept in the table since the atom was
    /// interned. Published values always name registered atoms.
    pub fn atom_name_hash(&self, id: u32) -> u64 {
        self.atoms
            .borrow()
            .name_hash(id)
            .expect("published atom must be registered")
    }

    /// Every atom's name in id order, shared with the table.
    pub fn atom_names(&self) -> Vec<AtomName> {
        self.atoms.borrow().by_id.clone()
    }

    /// Order two atoms by their names. The stored name prefixes settle most
    /// pairs; the names are read only when the prefixes agree. Published
    /// values always name registered atoms.
    pub fn cmp_atom_names(&self, left_id: u32, right_id: u32) -> Ordering {
        let atoms = self.atoms.borrow();
        let prefix = |id: u32| {
            *atoms
                .name_prefixes
                .get(id as usize)
                .expect("published atom must be registered")
        };
        prefix(left_id)
            .cmp(&prefix(right_id))
            .then_with(|| atoms.by_id[left_id as usize].cmp(&atoms.by_id[right_id as usize]))
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
            // A new process's tip is the smallest pooled block (1 KiB). Each
            // collection installs a tip sized to the young budget, which
            // follows the bytes the heap holds, up or down (`Heap::should_gc`).
            delivery: DeliveryLock::default(),
            heap: Heap::with_node(SIZE_TABLE[0], schemas, Rc::clone(&node)),
            ctx: null_mut(),
            halt_value: 0,
            failed: false,
            exit_status: 0,
            bs_builder: None,
            node,
            pid,
            state: ProcessState::New,
            next_frame: null_mut(),
            mailbox: VecDeque::new(),
            runnable: None,
            delivered: None,
            handlers: HandlerStack::default(),
            raised: None,
            raises_delivered: 0,
            stack_base: 0,
            scheduler_yields: 0,
            interpreter_yields: 0,
            reductions_remaining: reductions_per_quantum,
            reductions_per_quantum,
            reductions_executed: 0,
            reduction_yields: 0,
            parks: 0,
            list_retention_attempts: 0,
            list_retention_hits: 0,
            struct_retention_attempts: 0,
            struct_retention_hits: 0,
            dtors_dispatched: 0,
            frame_copies: 0,
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

    /// Hand a raise's materialized handler to the quantum that is unwinding
    /// from the raise.
    pub fn deliver_handler(&mut self, handler: AnyValueRef) {
        self.delivered = Some(ClosureRef::new(handler));
    }

    /// Whether a compiled raise delivered a handler the quantum has yet to run.
    pub fn has_delivered_handler(&self) -> bool {
        self.delivered.is_some()
    }

    /// Run one quantum starting at `first`. `resume` enters a closure and
    /// returns when the code unwinds to the quantum entry: because it yielded,
    /// parked, ended, failed, or delivered a raise to a handler. Only the last
    /// continues the quantum, with the handler, at once and on the same budget;
    /// every other way out hands the process back to the scheduler. This is the
    /// one place that answers whether the quantum continues.
    pub fn run_quantum(&mut self, first: AnyValueRef, mut resume: impl FnMut(&mut Process, AnyValueRef)) {
        let stack_marker = 0u8;
        self.stack_base = &stack_marker as *const u8 as usize;
        let mut closure = first;
        loop {
            resume(self, closure);
            match self.delivered.take() {
                Some(handler) => closure = handler.as_ref(),
                None => break,
            }
        }
        self.stack_base = 0;
    }

    /// Take the queued runnable closure, clearing the slot.
    pub fn take_runnable_closure(&mut self) -> Option<AnyValueRef> {
        self.runnable.take().map(ClosureRef::as_ref)
    }

    /// The queued runnable closure, if any, without clearing it.
    pub fn runnable_closure(&self) -> Option<AnyValueRef> {
        self.runnable.map(ClosureRef::as_ref)
    }

    /// Whether an uncaught raise ended the process with a non-zero status. An
    /// exit with a shutdown reason of 0 ends a process without failing it.
    pub fn ended_in_failure(&self) -> bool {
        self.failed && self.exit_status != 0
    }

    /// Whether a `never`-returning call has ended this process's current
    /// work: it failed, or a raise is waiting for the interpreter's handler
    /// frame.
    pub fn diverged(&self) -> bool {
        self.failed || self.raised.is_some()
    }

    /// Enter an interpreted `try`: the next raise reaches the interpreter's
    /// handler frame first.
    pub fn push_interpreter_handler(&mut self) {
        self.handlers.push_interpreter();
    }

    /// Leave a `try` whose body completed: its handler can no longer be
    /// reached.
    pub fn pop_handler(&mut self) {
        self.handlers.pop();
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
    /// record's frame, a delivered handler,
    /// the values the compiled handlers of the `try` bodies the process is inside capture, the mailbox and the
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
            roots.push(park.frame);
        }
        roots.extend(self.delivered.map(ClosureRef::as_ref));
        roots.extend(self.handlers.captures());
        roots.extend(self.mailbox.iter().copied());
        roots.extend_from_slice(transient);

        let stats = self.heap.collect(&mut roots);

        let mut forwarded = roots.into_iter();
        let mut next = || forwarded.next().expect("one forwarded root per gathered root");
        if self.runnable.is_some() {
            self.runnable = Some(ClosureRef::new(next()));
        }
        if let Some(park) = park {
            park.frame = next();
        }
        if self.delivered.is_some() {
            self.delivered = Some(ClosureRef::new(next()));
        }
        self.handlers.set_captures(&mut std::iter::from_fn(|| Some(next())));
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

    /// A copy of `bytes` as a binary of `bit_len` bits on this process's heap;
    /// see [`Heap::alloc_bitstring`].
    pub fn alloc_bitstring(&mut self, bytes: &[u8], bit_len: u64) -> AnyValue {
        let value = self.heap.alloc_bitstring(bytes, bit_len);
        self.end_quantum_when_binaries_due();
        value
    }

    /// A binary of `byte_len` bytes written in place by `fill`; see
    /// [`Heap::alloc_bitstring_with`].
    pub fn alloc_bitstring_with(
        &mut self,
        byte_len: usize,
        bit_len: u64,
        fill: impl FnOnce(&mut [std::mem::MaybeUninit<u8>]),
    ) -> AnyValue {
        let value = self.heap.alloc_bitstring_with(byte_len, bit_len, fill);
        self.end_quantum_when_binaries_due();
        value
    }

    /// The binary `left <> right`; see [`Heap::alloc_concatenation`].
    ///
    /// # Safety
    /// As [`Heap::alloc_concatenation`].
    pub unsafe fn alloc_concatenation(
        &mut self,
        left_bytes: &[u8],
        left_view: Option<crate::bits::BinView>,
        right: &[u8],
    ) -> AnyValue {
        let value = unsafe { self.heap.alloc_concatenation(left_bytes, left_view, right) };
        self.end_quantum_when_binaries_due();
        value
    }

    /// A running process reaches the end of its quantum at its next reduction
    /// check, where the boundary collects. A process that makes large binaries
    /// would otherwise keep them alive, dead or not, for the whole quantum, so
    /// the allocation that brings its binary bytes to the budget spends the
    /// rest of the quantum. Only the heap's owner can end its quantum: a
    /// message copy allocates on the receiver's heap through `Heap` and leaves
    /// the receiver's quantum alone.
    fn end_quantum_when_binaries_due(&mut self) {
        if self.heap.binary_budget.is_due() {
            self.reductions_remaining = 0;
        }
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
