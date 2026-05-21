//! Cranelift codegen for fz-IR (CPS form).
//!
//! Per-fz-IR-fn ABI: `extern "C" fn(frame_ptr: *mut u8, host_ctx: *mut u8) -> *mut u8`
//!   * `frame_ptr` points to a heap-allocated frame: HeapHeader (16 B) + slots.
//!     Slot 0 = continuation pointer. Slots 1..N+1 = entry params for this fn.
//!   * `host_ctx` is an opaque pointer the host (trampoline) supplies. Halt
//!     writes the final value through it.
//!   * Return value: the next frame pointer to invoke (the trampoline calls
//!     it next), or null to halt.
//!
//! Frame schema is regenerated here as the source of truth for codegen + the
//! GC tracer: [cont_ptr, ...entry_params], all FzValue slots. (Replaces the
//! placeholder schema computed in .11.6.)
//!
//! .11.8 scope additions over .11.7: Term::Call (allocates continuation frame
//!   + callee frame), Term::TailCall (frame reuse when callee shares schema,
//!     else fresh alloc), Term::Return (writes result into continuation frame's
//!     result slot or halts on null), real trampoline. Out of scope:
//!     Term::CallClosure / TailCallClosure (closure invocation needs heap-typed
//!     closures — lands later), and heap-typed prims (.11.10+).

use crate::fz_ir::{BinOp, Const, FnId, Module, Prim, Stmt, Term, UnOp};
use cranelift_codegen::Context;
use cranelift_codegen::ir::{
    self, AbiParam, BlockArg, InstBuilder, MemFlags, Signature,
    condcodes::{FloatCC, IntCC},
    types,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module as ClModule};
use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema};
use std::collections::HashMap;
use std::sync::Arc;

pub(crate) const HEADER_SIZE: i32 = 16;
pub(crate) const SLOT_BYTES: i32 = 8;

// FzValue tag scheme (matches src/fz_value.rs).
pub(crate) const TAG_INT: i64 = 0b001;
pub(crate) const TAG_ATOM: i64 = 0b010;
#[allow(dead_code)] // consumed by ir_codegen_receive; retracts when fz-70q.3 lands park-site
pub(crate) const TAG_PTR: i64 = 0b000;
#[allow(dead_code)]
pub(crate) const TAG_MASK: i64 = 0b111;
// fz-yan.1 — nil/true/false are atoms with reserved compile-time IDs.
// The bit-pattern constants are preserved so codegen call sites are
// unchanged; only the definitions move (from `TAG_SPECIAL`-tagged to
// `TAG_ATOM`-tagged). See runtime/src/fz_value.rs.
pub(crate) const NIL_BITS: i64 = fz_runtime::fz_value::NIL_BITS as i64;
pub(crate) const TRUE_BITS: i64 = fz_runtime::fz_value::TRUE_BITS as i64;
pub(crate) const FALSE_BITS: i64 = fz_runtime::fz_value::FALSE_BITS as i64;
/// fz-s9y.2 — empty-list sentinel. TAG_PTR with payload 1 → bit pattern
/// 0x8. Sits in unmapped page 0 so no allocator collides with it.
/// Distinct from NIL_BITS (the nil atom-like value).
pub(crate) const EMPTY_LIST_BITS: i64 = 1 << 3;

/// Errors from `compile()`. Backend-plumbing failures (cranelift
/// `declare_function` / `define_function` / `finalize_definitions`) carry
/// `Span::DUMMY` because they're internal — no fz source position maps to
/// "cranelift refused to declare a host function". The verify/define
/// per-fn paths populate `span` from `module.source.fn_span_of(f.id)` so
/// the diagnostic underlines the offending fn declaration.
#[derive(Debug, Clone)]
pub struct CodegenError {
    pub message: String,
    pub span: crate::diag::Span,
}
impl CodegenError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            span: crate::diag::Span::DUMMY,
        }
    }
    pub fn with_span(mut self, span: crate::diag::Span) -> Self {
        self.span = span;
        self
    }
    pub fn to_diagnostic(&self) -> crate::diag::Diagnostic {
        crate::diag::Diagnostic::error(
            crate::diag::codes::CODEGEN_SCHEMA_MISSING,
            format!("codegen: {}", self.message),
            self.span,
        )
    }
}
impl std::fmt::Display for CodegenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "codegen: {}", self.message)
    }
}
impl std::error::Error for CodegenError {}
impl From<String> for CodegenError {
    fn from(s: String) -> Self {
        Self::new(s)
    }
}

/// Compiled module: persistent JITModule + per-fn ptr table + schemas. The
/// host runs a fn via `compiled.run(fn_id)` (constructs an internal default
/// Process) or `compiled.run_in(fn_id, &mut Process)` (caller-owned Process).
pub struct CompiledModule {
    #[allow(dead_code)] // keep-alive: JIT memory is freed on drop
    module: JITModule,
    /// fz_fn_id -> compiled fn ptr.
    fn_ptrs: HashMap<u32, *const u8>,
    /// User-data SchemaRegistry (tuple, struct, list, map, closure, bitstring,
    /// vec, float). Lifted from TLS in fz-ul4.11.32. Each Process constructed
    /// via `make_process()` shares this registry through its Heap.
    pub(crate) user_schemas: std::rc::Rc<std::cell::RefCell<fz_runtime::heap::SchemaRegistry>>,
    /// Per-fn frame size (bytes), indexed by FnId.0. Consumed by
    /// `fz_alloc_frame_dyn` to allocate frames for fns whose id is known
    /// only dynamically (closure invocation). Copied into Process at
    /// make_process() time.
    pub(crate) frame_sizes: Vec<u32>,
    /// Heap-registered schema ids for the bitstring reader/result tuples.
    /// Set when any bitstring prim is present; None means "no bitstring prim
    /// in this module". Copied into Process at make_process() time.
    pub(crate) bs_tuple_arity1_schema: Option<u32>,
    pub(crate) bs_tuple_arity3_schema: Option<u32>,
    /// Atom names indexed by id. Copied into each Process at
    /// make_process() time so fz_value::debug::render can spell atoms
    /// out as `:name` (fz-ul4.25).
    pub(crate) atom_names: Vec<String>,
    /// .11.24.6 + .20.5: diagnostics surface (unreachable arms, dead
    /// branches). Structured via the central `diag::Diagnostic` type.
    pub(crate) diagnostics: crate::diag::Diagnostics,
    /// fz-cps.1.7 — zero-capture closure-target spec singletons resolved
    /// to code addresses at JIT-finalize time. `(cl_sid, fn_id, code_ptr)`
    /// per entry. `make_process` allocates one 24-byte off-heap closure
    /// per entry and registers it at `Process.static_closures[cl_sid]`.
    /// See docs/cps-in-clif.md §8.2.
    pub(crate) static_closure_targets: Vec<(u32, u32, *const u8, u32 /* halt_kind */)>,
    /// fz-cps.1.11 — finalized address of the SystemV scheduler shim
    /// `fz_resume_park(msg, parked_cont) -> i64`. The scheduler calls
    /// this via Rust FFI when a Blocked task wakes; the shim loads
    /// `parked_cont+16` and Tail-CC indirect-calls the cont body.
    pub(crate) resume_park_addr: *const u8,
    /// fz-cps.1.11 — finalized address of the SystemV scheduler shim
    /// `fz_spawn_entry(closure) -> i64`. Allocates a halt-cont and
    /// Tail-CC indirect-calls the zero-arg closure with `(self,
    /// halt_cont)`. Used by `Runtime::spawn_closure` to launch a task.
    pub(crate) spawn_entry_addr: *const u8,
    /// fz-cps.5 — finalized address of the SystemV scheduler shim
    /// `fz_main_entry(main_fp) -> i64`. Allocates a halt-cont and
    /// Tail-CC indirect-calls main with `(halt_cont)`. Used by
    /// `Runtime::spawn(fn_id)` / `CompiledModule::run_internal`.
    pub(crate) main_entry_addr: *const u8,
    /// fz-4mk.3a — finalized address of the SystemV scheduler shim
    /// `fz_drain_dtor_entry(closure, payload) -> i64`. The scheduler
    /// calls this once per entry on `process.heap.pending_dtors` at
    /// task-exit; the shim Tail-CC dispatches the closure body with
    /// payload + a fresh Tagged halt-cont.
    pub(crate) drain_dtor_entry_addr: *const u8,
    /// fz-ul4.27.22.3 — finalized addresses of the three Cranelift-emitted
    /// `fz_halt_cont_body_{tagged,i64,f64}` Tail-CC fns, indexed by repr
    /// kind (0=Tagged, 1=RawInt, 2=RawF64). `make_process` seeds matching
    /// Process singletons via `init_halt_cont_singletons`. Null slots
    /// (unused reprs for this program) are pre-populated lazily by
    /// `fz_get_halt_cont` at first use.
    pub(crate) halt_cont_body_addrs: [*const u8; 3],
    /// fz-ul4.27.22.3 — per-FnId halt-cont singleton kind. When the
    /// Rust scheduler dispatches a task via `fz_main_entry`, it picks
    /// `process.halt_cont_singletons[kind]` matching the entry fn's
    /// any-key return repr. Default kind 0 (Tagged) for fns not in
    /// the map.
    pub(crate) fn_halt_kinds: HashMap<u32, u32>,
    /// fz-02r.5 — SystemV shims for resuming a mid-flight back-edge yield.
    /// Indexed by arg count (0..=8). Shim N takes `(fn_ptr: u64) -> i64`,
    /// reads N values from `current_process().mid_flight_roots`, and
    /// `call_indirect Tail fn_ptr(arg0, ..., argN-1)`. Generated
    /// unconditionally; unused entries are never called.
    pub(crate) mid_flight_resume_addrs: [*const u8; 9],
    /// fz-70q (B3 step A+B) — SystemV shims for resuming a selective-
    /// receive matcher hit. Indexed by clause bound-arg count (0..=8).
    /// Shim N sig: `(a0:i64, ..., aN-1:i64, cont:i64) -> i64 system_v`.
    /// Body: `load cont+16 -> code; call_indirect Tail code(a0..aN-1,
    /// fz-70q.5.5 — single `fz_resume(cont) -> i64` SystemV shim.
    /// Loads `cont+16` and `call_indirect SystemV(cont)` into the cont
    /// stub. Bound args travel via `Process::resume_args` (written by
    /// the trampoline before dispatch), so arity is invisible to the
    /// shim. Replaces the nine `fz_resume_matched_N` siblings.
    pub(crate) resume_addr: *const u8,
}

impl CompiledModule {
    /// All typer-side diagnostics collected during `compile`. Includes
    /// both warnings (e.g. `TYPE_UNREACHABLE_ARM`, `TYPE_DEAD_BINOP`)
    /// and errors (e.g. `TYPE_OPAQUE_ARITHMETIC`). Drivers must route
    /// this through `diag::report_or_exit` so error-severity entries
    /// actually halt — historically called `warnings()` from when only
    /// warnings flowed here.
    pub fn diagnostics(&self) -> &crate::diag::Diagnostics {
        &self.diagnostics
    }
}

unsafe impl Send for CompiledModule {}

impl CompiledModule {
    pub fn fn_ptr(&self, fn_id: FnId) -> Option<*const u8> {
        self.fn_ptrs.get(&fn_id.0).copied()
    }

    /// Construct a fresh Process bound to this module's compile-time data
    /// (SchemaRegistry, frame_sizes, bs_tuple_arity*_schema). Multiple
    /// Processes can be made from the same CompiledModule and run
    /// concurrently (one worker at a time per Process; libdispatch model).
    pub fn make_process(&self) -> Process {
        let mut p = Process {
            heap: fz_runtime::heap::Heap::new(64 * 1024, std::rc::Rc::clone(&self.user_schemas)),
            halt_value: 0,
            map_builder: None,
            bs_builder: None,
            vec_builder: None,
            frame_sizes: self.frame_sizes.clone(),
            atom_names: self.atom_names.clone(),
            bs_tuple_arity1_schema: self.bs_tuple_arity1_schema,
            bs_tuple_arity3_schema: self.bs_tuple_arity3_schema,
            pid: 0,
            state: ProcessState::New,
            next_frame: std::ptr::null_mut(),
            mailbox: std::collections::VecDeque::new(),
            parked_cont: std::ptr::null_mut(),
            parked_matched: None,
            pending_resume_matched: None,
            resume_args: Vec::new(),
            halt_cont_singletons: [std::ptr::null_mut(); 3],
            pending_closure_entry: std::ptr::null_mut(),
            pending_main_entry: std::ptr::null_mut(),
            pending_main_entry_fn_id: 0,
            static_closures: Vec::new(),
            static_closure_bufs: Vec::new(),
            mid_flight_fn_ptr: 0,
            mid_flight_root_count: 0,
            mid_flight_roots: [fz_runtime::fz_value::FzValue(0); 8],
            quiet_quanta: 0,
        };
        // fz-cps.1.7 — allocate one static singleton per zero-cap
        // closure-target spec. See docs/cps-in-clif.md §8.2.
        p.init_static_closures(&self.static_closure_targets);
        // fz-ul4.27.22.3 — seed all three halt-cont singletons; each
        // slot's body sig matches its repr kind (Tagged / RawInt / RawF64).
        p.init_halt_cont_singletons(self.halt_cont_body_addrs);
        p
    }

    /// Run one quantum for a Process. Resumes from `process.next_frame`
    /// (which the caller — typically the Runtime in src/runtime.rs — must
    /// have set to a fresh entry frame or the saved continuation from a
    /// prior yield). The caller is responsible for CURRENT_PROCESS
    /// install/uninstall; we just trampoline. On halt the trampoline
    /// returns null; we write that back to process.next_frame so the
    /// caller can observe completion.
    pub(crate) fn run_quantum(&self, process: &mut Process) {
        /// Park-time GC trigger (cps-in-clif §7). Called at every
        /// shim-return boundary. Reads `process.heap.should_gc()`; if set,
        /// invokes Cheney with `parked_cont` as the sole root (§6.4 / §7).
        /// `gc()` may rewrite `parked_cont` to its to-space copy.
        fn park_time_gc(process: &mut Process) {
            if !process.heap.should_gc() {
                return;
            }
            process.heap.gc(&mut process.parked_cont);
            process.heap.clear_should_gc_flag();
            // After park-time GC the process is about to park on receive,
            // so FZ_SHOULD_YIELD no longer applies to this quantum.
            fz_runtime::yield_flag::FZ_SHOULD_YIELD.store(0, std::sync::atomic::Ordering::Relaxed);
        }

        // fz-qw6 — selective-receive initial scan lifted to runtime::sched.
        // Hit sets pending_resume_matched + cancels after-timer (via the
        // scheduler hook, which dispatches to whichever wheel is installed);
        // Miss blocks the task; NotApplicable is a no-op.
        match fz_runtime::sched::initial_scan(process) {
            fz_runtime::sched::ScanOutcome::Hit => {
                // Fall through to the dispatch branch below.
            }
            fz_runtime::sched::ScanOutcome::Miss => {
                process.next_frame = std::ptr::null_mut();
                return;
            }
            fz_runtime::sched::ScanOutcome::NotApplicable => {}
        }
        // fz-70q.5.5 — selective-receive wakeup. Set by the sender-probe
        // in `send_via_current_runtime` (or the after-timer fire in
        // `drain_expired_timers`, or the initial-scan branch above)
        // when a matcher hit picked the winning clause; the message has
        // already been consumed and the bound values extracted.
        //
        // Stash the bound args in the runtime resume_args slab (the
        // cont stub at cont+16 reads them via fz_resume_args_ptr) and
        // dispatch through the single SystemV `fz_resume(cont)` shim.
        // The shim does `load cont+16; call_indirect SystemV(cont)` —
        // arity is invisible to the seam.
        //
        // Mutually exclusive with parked_cont (different park kinds);
        // we check it first so a stale parked_cont doesn't shadow a
        // freshly-set resume request.
        if let Some(resume) = process.pending_resume_matched.take() {
            let cont_ptr = resume.cont;
            process.resume_args = resume.args;
            type Resume = extern "C" fn(u64) -> i64;
            let f: Resume = unsafe { std::mem::transmute(self.resume_addr) };
            let _ = f(cont_ptr as u64);
            // Clear the slab after dispatch — stale entries from this
            // resume could be misread by the *next* resume if its body
            // bound_arity is larger than this one's slab length.
            process.resume_args.clear();
            process.next_frame = std::ptr::null_mut();
            park_time_gc(process);
            return;
        }
        // fz-cps.1.11 — wakeup path: if the task has a parked_cont and
        // a message waiting, dispatch via the SystemV→Tail-CC
        // fz_resume_park shim. The shim cross-CC calls the cont closure
        // (`load parked_cont+16; call_indirect Tail (msg, parked_cont)`).
        // The cont chain runs synchronously to halt; halt_value is set
        // before fz_resume_park returns.
        if !process.parked_cont.is_null()
            && let Some(msg) = process.mailbox.pop_front()
        {
            let cont_ptr = process.parked_cont;
            process.parked_cont = std::ptr::null_mut();
            type ResumePark = extern "C" fn(u64, u64) -> i64;
            let f: ResumePark = unsafe { std::mem::transmute(self.resume_park_addr) };
            let _ = f(msg.0, cont_ptr as u64);
            process.next_frame = std::ptr::null_mut();
            park_time_gc(process);
            return;
        }
        // fz-02r.5 — mid-flight back-edge yield resume. fz_yield_back_edge
        // stored the callee's raw code ptr in mid_flight_fn_ptr and its live
        // args (all i64 / FzValues, post-GC-forwarding) in mid_flight_roots.
        // Dispatch via the matching fz_mid_flight_resume_N shim which
        // reads N args from the slab and Tail-CC indirect-calls fn_ptr.
        if process.mid_flight_fn_ptr != 0 {
            let fn_ptr = process.mid_flight_fn_ptr;
            let n = process.mid_flight_root_count as usize;
            process.mid_flight_fn_ptr = 0;
            process.mid_flight_root_count = 0;
            let shim = self.mid_flight_resume_addrs[n];
            type MidFlightResume = extern "C" fn(u64) -> i64;
            let f: MidFlightResume = unsafe { std::mem::transmute(shim) };
            let _ = f(fn_ptr);
            process.next_frame = std::ptr::null_mut();
            park_time_gc(process);
            return;
        }
        // fz-cps.5 — fresh main-style task entry: a fn ptr was queued
        // by `Runtime::spawn(fn_id)` or `run_internal`. Dispatch via
        // fz_main_entry (SystemV→Tail-CC). The fn body runs to halt
        // or Receive synchronously.
        if !process.pending_main_entry.is_null() {
            let fp = process.pending_main_entry;
            process.pending_main_entry = std::ptr::null_mut();
            // fz-ul4.27.22.3 — pick halt-cont singleton matching the
            // entry fn's return-repr kind. `pending_main_entry_fn_id`
            // is set alongside `pending_main_entry` by Runtime::spawn.
            let kind = self
                .fn_halt_kinds
                .get(&process.pending_main_entry_fn_id)
                .copied()
                .unwrap_or(0) as usize;
            let halt_cl = process.halt_cont_singletons[kind] as u64;
            type MainEntry = extern "C" fn(u64, u64) -> i64;
            let f: MainEntry = unsafe { std::mem::transmute(self.main_entry_addr) };
            let _ = f(fp as u64, halt_cl);
            process.next_frame = std::ptr::null_mut();
            park_time_gc(process);
            return;
        }
        // fz-cps.1.11 — fresh task entry: a closure was queued by
        // `Runtime::spawn_closure`. Dispatch via fz_spawn_entry (the
        // SystemV→Tail-CC launch shim). The closure body runs to halt
        // or Receive synchronously; on Receive it sets parked_cont and
        // the next quantum's wakeup path picks it up.
        if !process.pending_closure_entry.is_null() {
            let cl_ptr = process.pending_closure_entry;
            process.pending_closure_entry = std::ptr::null_mut();
            type SpawnEntry = extern "C" fn(u64) -> i64;
            let f: SpawnEntry = unsafe { std::mem::transmute(self.spawn_entry_addr) };
            let _ = f(cl_ptr as u64);
            process.next_frame = std::ptr::null_mut();
            park_time_gc(process);
            return;
        }
        // fz-cps.5 — the trampoline loop is unreachable. All fz fns are
        // Tail-CC; dispatch flows through the three SystemV shims above
        // (parked_cont resume, pending_main_entry, pending_closure_entry).
        // No uniform fns exist, so no frame-by-frame dispatch is needed.
        process.next_frame = std::ptr::null_mut();
    }
}

#[cfg(test)]
impl CompiledModule {
    /// fz-cps.1.7 — registered zero-capture closure-target specs.
    pub fn static_closure_targets(&self) -> &[(u32, u32, *const u8, u32)] {
        &self.static_closure_targets
    }

    /// Run the trampoline with `fn_id` as the entry fn, using a fresh Process
    /// stashed in DEFAULT_PROCESS for post-run inspection.
    pub fn run(&self, fn_id: FnId) -> i64 {
        DEFAULT_PROCESS.with(|c| *c.borrow_mut() = Some(self.make_process()));
        let ptr = DEFAULT_PROCESS.with(|c| {
            let mut b = c.borrow_mut();
            b.as_mut().unwrap() as *mut Process
        });
        let prev = CURRENT_PROCESS.with(|c| c.replace(ptr));
        let result = self.run_internal(fn_id);
        CURRENT_PROCESS.with(|c| c.set(prev));
        result
    }

    /// Run with a caller-owned Process.
    pub fn run_in(&self, fn_id: FnId, process: &mut Process) -> i64 {
        let ptr = process as *mut Process;
        let prev = CURRENT_PROCESS.with(|c| c.replace(ptr));
        let result = self.run_internal(fn_id);
        CURRENT_PROCESS.with(|c| c.set(prev));
        result
    }

    fn run_internal(&self, fn_id: FnId) -> i64 {
        let fp = self
            .fn_ptrs
            .get(&fn_id.0)
            .copied()
            .unwrap_or_else(|| panic!("no fn ptr for entry {}", fn_id.0));
        let kind = self.fn_halt_kinds.get(&fn_id.0).copied().unwrap_or(0) as usize;
        let halt_cl = current_process().halt_cont_singletons[kind] as u64;
        type MainEntry = extern "C" fn(u64, u64) -> i64;
        let f: MainEntry = unsafe { std::mem::transmute(self.main_entry_addr) };
        let _ = f(fp as u64, halt_cl);
        // fz-4mk — single-shot entry path: flush surviving MSO resources
        // and drain their dtor closures as fz code now, before returning.
        // Mirrors the JIT scheduler's task-exit drain in
        // `Runtime::run_until_idle` and the AOT loop's drain in
        // `aot_run_queue_loop`.
        {
            let proc_mut = current_process();
            fz_runtime::procbin::mso_drop_all_deferred(&mut proc_mut.heap);
            type DrainDtor = extern "C" fn(u64, u64) -> i64;
            let drain: DrainDtor = unsafe { std::mem::transmute(self.drain_dtor_entry_addr) };
            while let Some((closure, payload)) = proc_mut.heap.pending_dtors.pop_front() {
                let _ = drain(closure, payload);
            }
        }
        current_process().halt_value
    }
}

// Process, PidId, ProcessState, CURRENT_PROCESS, DEFAULT_PROCESS, and
// current_process() moved to src/process.rs (fz-ul4.23.4.2). Re-exported
// here for back-compat with downstream users (runtime.rs, ir_runtime.rs,
// tests) while consumers migrate to `fz_runtime::process::*`.
pub use fz_runtime::process::{CURRENT_PROCESS, PidId, Process, ProcessState};
#[cfg(test)]
use fz_runtime::process::{DEFAULT_PROCESS, current_process};

// Runtime FFI fns called from JIT'd code now live in src/ir_runtime.rs.
// Value rendering lives in fz_runtime::fz_value::debug (fz-ul4.23.4.3).

thread_local! {
    /// (.11.24.4) Per-fn Cranelift IR display text captured by compile()
    /// after compile_fn but before define_function consumes the context.
    /// Test-only; enable by calling `ir_text_record_enable()` before compile.
    pub static IR_TEXT_RECORD: std::cell::RefCell<Option<Vec<(String, String)>>> = const { std::cell::RefCell::new(None) };
    /// (fz-ul4.23.8) Per-fn machine-code disassembly captured by compile()
    /// when set_disasm is on. Enable with `asm_record_enable()` before
    /// compile; drain with `asm_record_take()` after.
    pub static ASM_RECORD: std::cell::RefCell<Option<Vec<(String, String)>>> = const { std::cell::RefCell::new(None) };
    /// fz-ul4.32.1 — per-fn Value → IR Ty map, populated by compile_fn
    /// at end-of-body. Consumed by the IR_TEXT_RECORD assembly step to
    /// annotate each `vN` definition with its typer result. Only the
    /// values bound to fz Vars (block params, Prim results, etc.) are
    /// recorded; pure Cranelift intermediates (iconst, ishl_imm, ...)
    /// have no fz-level type and stay unannotated.
    pub static VALUE_DESCR_RECORD: std::cell::RefCell<Option<HashMap<u32, crate::types_seam::Ty>>>
        = const { std::cell::RefCell::new(None) };
}

pub fn asm_record_enable() {
    ASM_RECORD.with(|c| *c.borrow_mut() = Some(Vec::new()));
}

pub fn asm_record_take() -> Vec<(String, String)> {
    ASM_RECORD.with(|c| c.borrow_mut().take().unwrap_or_default())
}

/// Drain the per-thread print-capture buffer. Tests in this file (and
/// the fixture_matrix integration tests) call this to read what
/// fz_print_value emitted during a compile/run. The actual storage lives
/// in the runtime crate alongside fz_print_value (fz-ul4.23.10).
#[cfg(test)]
pub fn test_capture_take() -> Vec<String> {
    fz_runtime::ir_runtime::test_capture_take()
}

/// Begin recording per-fn Cranelift IR display text. Subsequent `compile()`
/// calls on this thread will append `(fn_name, clif_text)` pairs to a TLS
/// buffer; `ir_text_record_take` drains and returns them.
///
/// Used by `fz dump --emit clif` (fz-ul4.23.3) and by unit tests that need
/// to assert on generated IR shape.
pub fn ir_text_record_enable() {
    IR_TEXT_RECORD.with(|c| *c.borrow_mut() = Some(Vec::new()));
    // fz-ul4.32.1 — pair the value-descr recorder so the assembled
    // text gets typer Descr annotations alongside the raw CLIF.
    VALUE_DESCR_RECORD.with(|c| *c.borrow_mut() = Some(HashMap::new()));
}

pub fn ir_text_record_take() -> Vec<(String, String)> {
    VALUE_DESCR_RECORD.with(|c| *c.borrow_mut() = None);
    IR_TEXT_RECORD.with(|c| c.borrow_mut().take().unwrap_or_default())
}

/// fz-ul4.32.1 — Build the per-fn header block that precedes annotated
/// CLIF. Two lines: typer's param/return Descrs and codegen's ArgReprs.
/// Disagreement between the two reveals where seam coercion lands.
fn build_typer_header<T: crate::types_seam::Types>(
    t: &mut T,
    f: &crate::fz_ir::FnIr,
    ft: &crate::ir_typer::FnTypes,
    spec_key: &[crate::types_seam::Ty],
    effective_return: &crate::types_seam::Ty,
    param_reprs: &[ArgRepr],
    return_repr: ArgRepr,
) -> String {
    use std::fmt::Write as _;
    let entry_params = &f.block(f.entry).params;
    let typer_params: Vec<String> = entry_params
        .iter()
        .map(|v| match ft.vars.get(v) {
            Some(d) => {
                let dy = t.from_concrete(d);
                t.display(&dy)
            }
            None => "?".to_string(),
        })
        .collect();
    // fz-i82.2 — `@spec` reports the same effective return that drives
    // `@abi` and the cont's slot-0 keying (`module_types.effective_returns`).
    // Halt-only specs converge to `none` in the LFP; show `_` for those
    // (matches the previous "no Term::Return found" rendering).
    let return_ty = t.from_concrete(effective_return);
    let none = t.none();
    let return_str = if t.is_subtype(&return_ty, &none) {
        "_".to_string()
    } else {
        t.display(&return_ty)
    };
    let codegen_repr = |r: &ArgRepr| -> &'static str {
        match r {
            ArgRepr::Tagged => "Tagged",
            ArgRepr::RawInt => "RawInt",
            ArgRepr::RawF64 => "RawF64",
            ArgRepr::Condition => "Condition",
        }
    };
    let codegen_params: Vec<String> = param_reprs
        .iter()
        .map(|r| codegen_repr(r).to_string())
        .collect();
    let key_params: Vec<String> = spec_key
        .iter()
        .map(|key| {
            let dy = t.from_concrete(key);
            t.display(&dy)
        })
        .collect();
    let mut out = String::new();
    let _ = writeln!(
        out,
        ";   @spec   {}({}) -> {}",
        f.name,
        typer_params.join(", "),
        return_str
    );
    let _ = writeln!(out, ";   @key    [{}]", key_params.join(", "));
    let _ = writeln!(
        out,
        ";   @abi    ({}) -> {}",
        codegen_params.join(", "),
        codegen_repr(&return_repr)
    );
    out
}

/// fz-ul4.32.1 — Annotate raw Cranelift IR text with IR-level types.
///
/// Inputs:
///   - `raw`: the text from `ctx.func.display()`.
///   - `value_tys`: Value.as_u32() → typer Ty for fz-Var-bound values.
///   - `header`: pre-built header lines (typer params/return, codegen
///     param_reprs/return_repr). Already starts with `; `.
///
/// Output: header lines + annotated CLIF. Per-`vN = ...` definitions get
/// an inline `; vN :: <ty>` comment appended; pure intermediates with
/// no fz Var binding are left alone. The `block0(...)` line annotates
/// each block-param with its type inline.
fn annotate_clif_dump(
    raw: &str,
    value_tys: &HashMap<u32, crate::types_seam::Ty>,
    func_names: &HashMap<u32, String>,
    header: &str,
) -> String {
    use crate::types_seam::Types;
    use std::fmt::Write as _;
    let mut t = crate::types_seam::ConcreteTypes;
    let mut out = String::new();
    out.push_str(header);
    if !header.ends_with('\n') {
        out.push('\n');
    }
    for line in raw.lines() {
        let resolved = resolve_user_func_refs(line, func_names);
        let trimmed = resolved.trim_start();
        // Block header: `blockN(v0: ty, v1: ty, ...):`
        if trimmed.starts_with("block") && trimmed.contains('(') && trimmed.ends_with(':') {
            let _ = writeln!(
                out,
                "{}",
                annotate_block_header(&mut t, &resolved, value_tys)
            );
            continue;
        }
        // Value definition: `    vN = <op> ...`
        if let Some(rest) = trimmed.strip_prefix('v')
            && let Some((id_str, _)) = rest.split_once(' ')
            && let Ok(id) = id_str.parse::<u32>()
            // Confirm it's actually `vN =` (not `vN+16` in a load).
            && rest.split_once(' ').map(|x| x.1.starts_with('=')).unwrap_or(false)
            && let Some(ty) = value_tys.get(&id)
        {
            let dy = t.from_concrete(ty);
            let _ = writeln!(
                out,
                "{}    ;; v{} :: {}",
                resolved.trim_end(),
                id,
                t.display(&dy)
            );
            continue;
        }
        let _ = writeln!(out, "{}", resolved);
    }
    out
}

// fz-323 — snapshot every declared function's linkage name keyed by FuncId.
// Used by the CLIF dumper to swap `u0:N` numeric refs for `@<name>` symbolic
// refs that are stable across additions of unrelated runtime helpers.
fn snapshot_func_names(decls: &cranelift_module::ModuleDeclarations) -> HashMap<u32, String> {
    decls
        .get_functions()
        .map(|(id, d)| (id.as_u32(), d.linkage_name(id).into_owned()))
        .collect()
}

// fz-323 — rewrite Cranelift's `u0:N` external-name tokens to `@<linkage_name>`.
// The number N is a `cranelift_module::FuncId` assigned in module-declaration
// order, so adding any new helper upstream shifts every later N and creates
// trivial merge conflicts in CLIF goldens. The linkage name was passed to
// `declare_function` and is source-derived (`fz_alloc_list_cons`, `fz_fn_17`,
// `fz_resume`, …), so it survives unrelated growth in the module.
fn resolve_user_func_refs(line: &str, func_names: &HashMap<u32, String>) -> String {
    if !line.contains("u0:") {
        return line.to_string();
    }
    let bytes = line.as_bytes();
    let mut out = String::with_capacity(line.len());
    let mut i = 0;
    let mut copy_from = 0;
    while i + 3 < bytes.len() {
        let at_boundary = i == 0 || {
            let p = bytes[i - 1];
            !(p.is_ascii_alphanumeric() || p == b'_')
        };
        if at_boundary && &bytes[i..i + 3] == b"u0:" && bytes[i + 3].is_ascii_digit() {
            let mut j = i + 3;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            let n: u32 = line[i + 3..j].parse().expect("u0:<digits> already matched");
            if let Some(name) = func_names.get(&n) {
                out.push_str(&line[copy_from..i]);
                out.push('@');
                out.push_str(name);
                i = j;
                copy_from = j;
                continue;
            }
            i = j;
            continue;
        }
        i += 1;
    }
    out.push_str(&line[copy_from..]);
    out
}

/// Inline-annotate the `(vN: ty, ...)` portion of a block header with the
/// IR type of each param. Skips params whose value-id is absent from
/// `value_tys`.
fn annotate_block_header(
    t: &mut crate::types_seam::ConcreteTypes,
    line: &str,
    value_tys: &HashMap<u32, crate::types_seam::Ty>,
) -> String {
    use crate::types_seam::Types;

    // Append a trailing `; vN :: ty, vM :: ty` comment AFTER the
    // existing line, leaving the original CLIF text intact.
    let Some(open) = line.find('(') else {
        return line.to_string();
    };
    let Some(close) = line.rfind(')') else {
        return line.to_string();
    };
    if close <= open + 1 {
        return line.to_string();
    }
    let inner = &line[open + 1..close];
    let mut notes: Vec<String> = Vec::new();
    for p in inner.split(',') {
        let p_trim = p.trim();
        if let Some(rest) = p_trim.strip_prefix('v')
            && let Some((id_str, _ty)) = rest.split_once(':')
            && let Ok(id) = id_str.trim().parse::<u32>()
            && let Some(ty) = value_tys.get(&id)
        {
            let dy = t.from_concrete(ty);
            notes.push(format!("v{} :: {}", id, t.display(&dy)));
        }
    }
    if notes.is_empty() {
        line.to_string()
    } else {
        format!("{}    ;; {}", line.trim_end(), notes.join(", "))
    }
}

// Halt: receives an FzValue from the JIT, unboxes per-tag into a
// debug-friendly i64 stored on the current Process's halt_value. Halt is a
// debugging seam; this preserves byte-for-byte halt values for existing
// scalar tests while not constraining heap-typed semantics later.
//
// The second arg is the per-fn ABI's `ctx: *mut u8` (= *mut Process). For
// the migration we ignore it in favor of current_process() — they point at
// the same Process, but using current_process() keeps the access pattern
// uniform with every other fz_* fn.
// fz_halt moved to ir_runtime.rs (.23.4.13).

// ----- Heap (managed cons-cell allocator) -----
//
// The JIT-side `fz_alloc_list_cons` routes through the current Process's heap
// so the GC tracer in src/heap.rs can reclaim cons cells. Frames stay on the
// system allocator for now (frames don't yet root-trace; .11.31).

/// Reset DEFAULT_PROCESS. Call at the start of any test that needs a clean
/// heap. Tests share threads via the cargo test runner's worker pool, so
/// leftover state is otherwise sticky.
#[cfg(test)]
pub fn heap_reset_for_test() {
    DEFAULT_PROCESS.with(|c| *c.borrow_mut() = None);
}

// fz_alloc_list_cons and fz_alloc_struct moved to ir_runtime.rs (.23.4.7).

// ----- Map runtime fns -----
//
// Maps use a heap-backed sorted-array layout. Build-time semantics: codegen
// emits begin -> push (per pair) -> finalize. MapUpdate emits clone(base) ->
// push (per override) -> finalize. The thread-local builder accumulates
// pairs as `(key_bits, val_bits)`; finalize sorts canonically (later writes
// win on duplicate keys) and allocates one heap Map.
//
// Key total ordering for canonical layout: Int < Atom < Special < Ptr;
// within each category, by raw bits (Int compares signed). Keys compare
// equal iff their u64 bits are equal — pointer-equal heap keys for v1.

// Map cluster moved to ir_runtime.rs (.23.4.8). MAP_BUILDER state lives
// on Process.map_builder (per fz-ul4.11.32).

// ----- Bitstring runtime fns -----
//
// Construction uses a thread-local BitWriter populated across a sequence of
// `fz_bs_write_field` calls between `fz_bs_begin` and `fz_bs_finalize`. The
// codegen for a single Prim::MakeBitstring emits this whole sequence within
// one block — no CPS splits between begin and finalize, so per-thread state
// is safe.
//
// Reader prims model the reader as a 3-tuple `[bs_ptr, bit_len_int, pos_int]`
// (heap-allocated via fz_alloc_struct). Each BitReadField allocates a fresh
// 3-tuple result `[ok, extracted, new_reader]` on success or 1-tuple
// `[false]` on failure. Tuple schema_ids for arities 1 and 3 are registered
// at compile() time when any bitstring prim is present.

// BS_BUILDER + BS_TUPLE_ARITY{1,3}_SCHEMA state moved to Process fields
// (per fz-ul4.11.32). Tuple-arity schema ids are filled in at make_process()
// time from CompiledModule's compile-time tables.

// Bitstring runtime cluster (fz_bs_*, decode_*) moved to ir_runtime.rs
// (.23.4.9). The codegen-time helpers below stay here.

fn encode_bit_type(t: crate::ast::BitType) -> u32 {
    use crate::ast::BitType;
    match t {
        BitType::Integer => 0,
        BitType::Float => 1,
        BitType::Binary => 2,
        BitType::Bits => 3,
        BitType::Utf8 => 4,
        BitType::Utf16 => 5,
        BitType::Utf32 => 6,
    }
}

fn encode_endian(e: crate::ast::Endian) -> u32 {
    use crate::ast::Endian;
    match e {
        Endian::Big => 0,
        Endian::Little => 1,
        Endian::Native => 2,
    }
}

/// Default unit per type, mirroring `crate::ir_lower::resolved_unit_for`.
fn default_unit_for(ty: crate::ast::BitType) -> u32 {
    use crate::ast::BitType;
    match ty {
        BitType::Integer | BitType::Float | BitType::Bits => 1,
        BitType::Binary => 8,
        BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => 1,
    }
}

// ----- Float runtime fns -----
//
// Boxed f64s. v1 representation: HeapKind::Float, layout `HeapHeader (16) +
// f64 (8) + pad (8)`. Tag::Ptr (low bits 000), so two distinct boxed floats
// with the same value are NOT bit-equal — comparison ops dispatch through
// fz_value_eq when at least one operand has Tag::Ptr.
//
// Arithmetic dispatch: codegen emits an inline both-int fast-path test
// (`((a^1) | (b^1)) & 7 == 0`); when at least one operand is non-Int the
// slow arm promotes both to f64 via fz_promote_f64 and emits native
// fadd/fsub/fmul/fdiv (or fz_fmod for `%`, since Cranelift has no frem),
// then boxes via fz_alloc_float. fz-ul4.27.9 inlined the slow path —
// previously a call to fz_arith_*. Typed float-float fast paths
// (.27.3) and typed int-int fast paths (.27.5.3) sit in front of the
// dispatch entirely. Eq/Neq do NOT promote: `1 == 1.0` is false.

// fz_alloc_float moved to ir_runtime.rs (.23.4.7).

// ----- fz-ul4.19.2: scheduler-bound builtins (spawn / self) -----
//
// Both consume a Runtime installed in TLS by Runtime::run_until_idle.
// Calling either outside the scheduler path panics with a clear message.

// fz_spawn(closure_bits) -> pid_bits. Extracts fn_id from the closure
// heap object and enqueues a new task at that fn. Returns the pid as a
// boxed FzValue Int (Pid-as-struct deferred to a follow-up).
//
// Arith / cmp / eq FFI cluster moved to src/ir_runtime.rs (fz-ul4.23.4.1).

// Vec cluster moved to ir_runtime.rs (.23.4.10).
// VEC_BUILDER state lives on Process.vec_builder (per fz-ul4.11.32),
// typed as Option<fz_runtime::ir_runtime::VecBuild>.

// Closure cluster moved to ir_runtime.rs (.23.4.11).

// fz_alloc_frame + fz_alloc_frame_for_test moved to ir_runtime.rs (.23.4.7).

// ---------------------------------------------------------------------------
// Compiler
// ---------------------------------------------------------------------------

fn host_isa() -> Arc<dyn cranelift_codegen::isa::TargetIsa> {
    host_isa_with(false)
}

/// Build a host ISA. `pic = false` is right for the JIT (no relocations
/// needed inside in-memory code). `pic = true` is required for AOT on
/// macOS, where the linker rejects text relocations in regular
/// executables.
fn host_isa_with(pic: bool) -> Arc<dyn cranelift_codegen::isa::TargetIsa> {
    let mut flag_builder = settings::builder();
    flag_builder.set("opt_level", "speed").unwrap();
    flag_builder
        .set("is_pic", if pic { "true" } else { "false" })
        .unwrap();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    // Cranelift's Tail CC implementation asserts frame pointers are present.
    // macOS preserves them by default; Linux does not.
    flag_builder.set("preserve_frame_pointers", "true").unwrap();
    let isa_builder = cranelift_native::builder().expect("host ISA");
    isa_builder
        .finish(settings::Flags::new(flag_builder))
        .expect("isa finish")
}

/// Build a [cont_ptr, ...entry_params] frame schema. The cont_ptr slot is
/// always `FzValue`; the param slots are described by `param_kinds`. All
/// slots are currently 8 bytes regardless of kind; VR.3.2+ flips storage to
/// raw f64 / raw i64 for the typed kinds. .5.1 (this ticket) is pure
/// FieldKind plumbing — every caller still passes `FzValue` for every
/// param, so behavior is unchanged.
fn build_frame_schema(name: &str, param_kinds: &[FieldKind]) -> Schema {
    let n_fields = 1 + param_kinds.len();
    let mut fields = Vec::with_capacity(n_fields);
    fields.push(FieldDescriptor {
        offset: 0,
        kind: FieldKind::FzValue,
    });
    for (i, k) in param_kinds.iter().enumerate() {
        fields.push(FieldDescriptor {
            offset: ((i + 1) * SLOT_BYTES as usize) as u32,
            kind: k.clone(),
        });
    }
    Schema {
        name: format!("Frame_{}", name),
        size: HEADER_SIZE as u32 + (n_fields as u32) * SLOT_BYTES as u32,
        fields,
    }
}

/// Abstraction over a Cranelift module backend. <code>compile_with_backend</code>
/// drives the whole shared pipeline through this trait; JIT and AOT pick
/// what's specific to them (linkage, metadata-carrier emission, finalize).
///
/// fz-ul4.23.12 unification: where the trait used to expose only
/// `module_mut` and the surrounding pipeline was duplicated in
/// `compile()` and `compile_aot()`, the surrounding pipeline is now
/// fz-ul4.27.13 — How a fz arg/return rides the Cranelift ABI for a native
/// fn. `Tagged` is the default FzValue i64 (low 3 bits = tag); `RawInt` is
/// an unshifted int payload as i64; `RawF64` is a raw f64.
///
/// Per-spec param/return reprs are derived from `ir_typer`'s Descrs:
/// float-only → `RawF64`, int-only → `RawInt`, else `Tagged`. `build_fn_
/// signature` picks the AbiParam type from the repr; `compile_fn` populates
/// `raw_*_vars` to match; call sites coerce at the seam.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ArgRepr {
    Tagged,
    RawInt,
    RawF64,
    /// Raw i1 from a comparison or TypeTest whose var is in `if_only_conds`
    /// — the tagged form is never materialised unless tagged_get is called,
    /// which emits bool_to_fz lazily at the use site (fz-h4q).
    Condition,
}

impl ArgRepr {
    fn from_ty<T: crate::types_seam::Types>(t: &mut T, d: &crate::types_seam::Ty) -> ArgRepr {
        let dy = t.from_concrete(d);
        if t.is_floating(&dy) {
            ArgRepr::RawF64
        } else if t.is_integer(&dy) {
            ArgRepr::RawInt
        } else {
            ArgRepr::Tagged
        }
    }

    // CLIF block params are always declared as i64. RawF64 (an actual f64
    // CLIF value) cannot cross a block-param boundary without a type error.
    // At block edges, only integers benefit from repr narrowing; floats must
    // remain Tagged (boxed heap pointer, i64) across block params.
    fn for_block_param_ty<T: crate::types_seam::Types>(
        t: &mut T,
        d: &crate::types_seam::Ty,
    ) -> ArgRepr {
        match Self::from_ty(t, d) {
            ArgRepr::RawInt => ArgRepr::RawInt,
            _ => ArgRepr::Tagged,
        }
    }
    fn cl_type(&self) -> types::Type {
        match self {
            ArgRepr::RawF64 => types::F64,
            ArgRepr::Condition => unreachable!("Condition vars are never block/fn params"),
            _ => types::I64,
        }
    }
    /// fz-ul4.27.22.3 — halt-cont singleton kind. 0=Tagged, 1=RawInt, 2=RawF64.
    fn halt_kind(&self) -> u32 {
        match self {
            ArgRepr::Tagged => 0,
            ArgRepr::RawInt => 1,
            ArgRepr::RawF64 => 2,
            ArgRepr::Condition => unreachable!("Condition vars never reach halt-cont"),
        }
    }
}

/// Allocate and return a halt-cont singleton for `repr` via `fz_get_halt_cont`.
/// Used when the caller has no cont_param and needs a halt-cont to pass to the
/// callee — the callee's Term::Return chains through it to record halt_value.
fn synthesize_halt_cont<M: cranelift_module::Module>(
    jmod: &mut M,
    b: &mut FunctionBuilder<'_>,
    runtime: &RuntimeRefs,
    repr: ArgRepr,
) -> ir::Value {
    let fref = jmod.declare_func_in_func(runtime.get_halt_cont_id, b.func);
    let hcb_addr = fn_addr(jmod, halt_cont_body_id_for(runtime, repr), b);
    let kind_v = b.ins().iconst(types::I32, repr.halt_kind() as i64);
    let inst = b.ins().call(fref, &[hcb_addr, kind_v]);
    b.inst_results(inst)[0]
}

/// Declare `id` in the current function and return its address as an i64.
/// Collapses the ubiquitous `declare_func_in_func` + `func_addr` pair.
pub(crate) fn fn_addr<M: cranelift_module::Module>(
    jmod: &mut M,
    id: FuncId,
    b: &mut FunctionBuilder<'_>,
) -> ir::Value {
    let fref = jmod.declare_func_in_func(id, b.func);
    b.ins().func_addr(types::I64, fref)
}

/// fz-ul4.27.22.3 — pick the halt_cont_body FuncId matching `repr`.
fn halt_cont_body_id_for(runtime: &RuntimeRefs, repr: ArgRepr) -> FuncId {
    match repr {
        ArgRepr::Tagged => runtime.halt_cont_body_tagged_id,
        ArgRepr::RawInt => runtime.halt_cont_body_i64_id,
        ArgRepr::RawF64 => runtime.halt_cont_body_f64_id,
        ArgRepr::Condition => unreachable!("Condition vars never reach halt-cont"),
    }
}

/// Per-spec entry-param ArgReprs. Length matches the spec's entry block's
/// param count.
fn build_param_reprs<T: crate::types_seam::Types>(
    t: &mut T,
    f: &crate::fz_ir::FnIr,
    ft: &crate::ir_typer::FnTypes,
) -> Vec<ArgRepr> {
    let entry = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
    entry
        .params
        .iter()
        .map(|p| {
            let ty = ft.vars.get(p).cloned().unwrap_or_else(|| t.concrete_any());
            ArgRepr::from_ty(t, &ty)
        })
        .collect()
}

/// fz-ul4.27.6.2.2 — Per-fn Cranelift Signature.
///
/// `is_native = false` → uniform `(frame_ptr: i64, host_ctx: i64) -> i64`,
/// matching the body shape produced by `compile_fn` for trampoline-driven
/// fns: frame slots for entry params, emit_return writes into the cont
/// frame and returns the cont frame ptr to the trampoline.
///
/// `is_native = true` → typed-arity signature reflecting the fn's entry
/// params + `host_ctx` + return. fz-ul4.27.13 promotes per-Descr typing:
/// each entry param's AbiParam type derives from its `ArgRepr` (RawF64 →
/// `f64`, RawInt/Tagged → `i64`); the return derives from `return_descr`
/// the same way. `host_ctx` is always `i64`.
fn build_fn_signature(
    param_reprs: &[ArgRepr],
    ret_repr: ArgRepr,
    is_native: bool,
    is_cont_fn: bool,
    closure_target_n_caps: Option<usize>,
    // fz-70q.5.5 — when the cont fn is a ReceiveMatched clause body /
    // guard, override the default 1-input shape with bound_arity. After
    // bodies set this to 0. `None` falls back to legacy `(result, self)`
    // for Term::Receive / Call / CallClosure continuations.
    cont_extras_override: Option<usize>,
) -> Signature {
    if !is_native {
        // Uniform fns always include host_ctx — the trampoline ABI is
        // fixed at `(frame_ptr, host_ctx) -> i64`; `needs_host_ctx` is
        // ignored here. (Trimming uniform sigs would require an
        // entry-harness refactor; tracked under .27.20.)
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64)); // frame_ptr
        sig.params.push(AbiParam::new(types::I64)); // host_ctx
        sig.returns.push(AbiParam::new(types::I64)); // next frame_ptr
        return sig;
    }
    // Native fns use the `Tail` calling convention so that recursive
    // tail calls can lower to `return_call` (which the SystemV ABI does
    // not permit). Without TCO, count_100k_stays_bounded blows the stack.
    // fz-ul4.27.19: append host_ctx only when this fn (or some callee
    // it forwards into) actually consumes it.
    let mut sig = Signature::new(CallConv::Tail);
    if is_cont_fn {
        // fz-ul4.27.22.3 cont fn sig per §2.1: `(result, self:i64) tail`.
        // result uses param_reprs[0]'s cl_type (RawInt=i64, RawF64=f64,
        // Tagged=i64). Producer's Term::Return sig matches via
        // return_reprs[producer_spec_id]; typer's effective_return walk
        // ensures producer and consumer agree at the seam.
        //
        // fz-70q.5.5 — ReceiveMatched body/guard fns take N typed bound
        // args up front (override default of 1). After-body fns set the
        // override to 0 — captures only, read from self+32+i*8.
        let extras = cont_extras_override.unwrap_or(1);
        for r in param_reprs.iter().take(extras) {
            sig.params.push(AbiParam::new(r.cl_type()));
        }
        sig.params.push(AbiParam::new(types::I64)); // self
    } else if let Some(n_caps) = closure_target_n_caps {
        // fz-cps.1.2 closure-target fn sig per §2.1:
        // `(args..., self:i64, cont:i64) tail`. Captures (param_reprs[0..n_caps])
        // are NOT Cranelift params — body loads them from self+24+8*i.
        // Args are param_reprs[n_caps..].
        for r in &param_reprs[n_caps..] {
            sig.params.push(AbiParam::new(r.cl_type()));
        }
        sig.params.push(AbiParam::new(types::I64)); // self
        sig.params.push(AbiParam::new(types::I64)); // cont
    } else {
        for r in param_reprs {
            sig.params.push(AbiParam::new(r.cl_type()));
        }
        // fz-cps.1.a — trailing cont:i64 per §2.1.
        sig.params.push(AbiParam::new(types::I64)); // cont
    }
    if is_native {
        // fz-cps.1.2: native fn return canonicalized to i64 regardless of
        // ret_repr. Term::Return is `return_call_indirect sig(i64,i64)->i64
        // tail`; coercion happens at the return site.
        sig.returns.push(AbiParam::new(types::I64));
    } else if closure_target_n_caps.is_some() {
        // fz-try.15 — closure-target ABI is structurally uniform Tagged.
        // The indirect-dispatch seam (stub_fp) can't carry typed return
        // info to its caller, so the wire format is fixed. Specialization
        // is body-internal; ABI is seam-external — the body coerces its
        // narrow return to Tagged at Term::Return.
        sig.returns.push(AbiParam::new(types::I64));
    } else {
        sig.returns.push(AbiParam::new(ret_repr.cl_type()));
    }
    sig
}

/// shared and the trait owns every legitimate point of variation —
/// fn linkage, per-program metadata emission, and the finalize step
/// that materializes the backend's Output.
pub trait Backend {
    type Module: cranelift_module::Module;
    /// Whatever the backend hands the user after compilation finishes.
    /// JIT returns a `CompiledModule` (in-memory, runnable); AOT returns
    /// an `AotArtifact` (object bytes + linker metadata).
    type Output;

    fn module_mut(&mut self) -> &mut Self::Module;

    /// Linkage applied to user `fz_fn_<id>` declarations. JIT keeps them
    /// `Local` (only resolved in-process). AOT exports them so the linker
    /// can see them when assembling the final binary.
    fn fn_linkage(&self) -> Linkage;

    /// Emit per-program metadata carriers (dispatch fn, frame-size fn,
    /// atom-name blob, C `main` shim). The JIT impl is a no-op — the same
    /// data lives in `CompiledModule`'s Rust HashMaps and the runtime
    /// reads them directly. AOT emits Cranelift data + fns so the linker
    /// + `fz_aot_run_main` can resolve them at runtime.
    fn emit_metadata_carriers(
        &mut self,
        fbctx: &mut FunctionBuilderContext,
        meta: &CompiledMetadata,
    ) -> Result<(), CodegenError>;

    /// Finalize the backend into its Output. JIT finalizes the JITModule
    /// and resolves fn pointers. AOT emits the object-file bytes.
    fn finalize(self, meta: CompiledMetadata) -> Result<Self::Output, CodegenError>;
}

/// Everything `compile_with_backend` collects during the shared pipeline,
/// handed to the backend's `emit_metadata_carriers` and `finalize`.
///
/// The fz user `Module` (post type-rewrite) is intentionally NOT here —
/// backends only need the codegen metadata at finalize time. They've
/// already seen the module while declaring fns and compiling bodies.
pub struct CompiledMetadata {
    pub fn_ids: HashMap<u32, FuncId>,
    pub user_schemas: std::rc::Rc<std::cell::RefCell<fz_runtime::heap::SchemaRegistry>>,
    pub frame_sizes: Vec<u32>,
    pub atom_names: Vec<String>,
    pub bs_tuple_arity1_schema: Option<u32>,
    pub bs_tuple_arity3_schema: Option<u32>,
    /// fz-ul4.38 — sorted list of tuple arities the program will allocate.
    /// JIT ignores it (its runtime shares `user_schemas`); AOT bakes it
    /// into a `.data` symbol so `fz_aot_setup` can re-register the same
    /// `Tuple{N}` schemas in matching order.
    pub tuple_arities: Vec<u32>,
    pub diagnostics: crate::diag::Diagnostics,
    /// FnId of fz user `main`, if present. AOT needs it to wire the C
    /// `main` shim; JIT keeps it as a convenience for the run path.
    pub main_fn_id: Option<FnId>,
    /// fz-cps.1.7 — zero-capture closure-target specs.
    /// `(cl_sid, fn_id, stub_func_id)` per entry. JIT finalize resolves
    /// stub_func_id to a code address; the resulting
    /// `CompiledModule.static_closure_targets` is consumed by
    /// `make_process` to populate `Process.static_closures`. AOT carries
    /// the same list as a startup-init data table (fz-cps.1.7 AOT path is
    /// out of scope until aot rebuilds; see ticket notes).
    pub static_closure_targets: Vec<(u32, u32, FuncId, u32 /* halt_kind */)>,
    /// fz-cps.1.11 — fz_resume_park scheduler-wakeup shim FuncId.
    pub resume_park_id: FuncId,
    /// fz-cps.1.11 — fz_spawn_entry scheduler-launch shim FuncId.
    pub spawn_entry_id: FuncId,
    /// fz-cps.5 — fz_main_entry scheduler-launch shim FuncId.
    pub main_entry_id: FuncId,
    /// fz-4mk.3a — fz_drain_dtor_entry scheduler-drain shim FuncId.
    pub drain_dtor_entry_id: FuncId,
    /// fz-ul4.27.22.3 — three fz_halt_cont_body fns indexed by repr
    /// kind (0=Tagged, 1=RawInt, 2=RawF64). Sigs: (Tagged|i64|f64, i64)
    /// -> i64 tail. Bodies call the matching halt_implicit_* and return 0.
    pub halt_cont_body_ids: [FuncId; 3],
    /// fz-ul4.27.22.3 — per-FnId halt-cont singleton kind (the entry
    /// fn's any-key return repr). Used by the Rust scheduler to pick
    /// the matching halt_cont_singletons slot when dispatching via
    /// fz_main_entry.
    pub fn_halt_kinds: HashMap<u32, u32>,
    /// fz-02r.5 — FuncIds for the 9 mid-flight resume shims (arg count 0..=8).
    pub mid_flight_resume_ids: [FuncId; 9],
    /// fz-70q.5.5 — single `fz_resume` SystemV shim FuncId. See
    /// `CompiledModule::resume_addr`.
    pub resume_id: FuncId,
}

/// fz-ul4.29.2 — Two-way mapping between (FnId, input-Descr-tuple) and
/// SpecId. Each compiled body has one entry; SpecIds are dense from 0.
///
/// In .29.2 every FnIr has exactly one SpecId (its any-key spec), so
/// `SpecId.0 == FnId.0` is an invariant — preserves bit-identical CLIF
/// vs. the pre-atom baseline. fz-ul4.29.2.1 admits multiple SpecIds per
/// FnId for narrow specs, at which point the invariant relaxes.
use crate::spec_registry::SpecRegistry;

/// JIT backend: wraps a JITModule pre-finalize. compile() constructs one,
/// drives codegen through the Backend trait, then unpacks to call the
/// JIT-specific finalize_definitions / get_finalized_function pair.
pub struct JitBackend {
    jmod: JITModule,
}

impl JitBackend {
    fn new() -> Self {
        let isa = host_isa();
        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        // Bind every fz runtime FFI fn pointer. JIT-specific: the linker
        // is in-process and resolves symbols by name → Rust fn pointer.
        // AOT will skip this entire block (linker resolves against the
        // fz_runtime staticlib instead).
        builder.symbol(
            "fz_print_value",
            fz_runtime::ir_runtime::fz_print_value as *const u8,
        );
        // fz-ul4.27.7 (VR.5b): typed print helpers — JIT routes here when
        // the arg Descr is monomorphic, skipping the boxing round-trip.
        builder.symbol("fz_print_i64", fz_runtime::fz_print_i64 as *const u8);
        // Linux JIT needs explicit symbol bindings; macOS happens to
        // resolve runtime crate exports via dlsym on the executable
        // image, but Linux's stricter visibility under cargo llvm-cov
        // drops them. Bind the assert family here so JIT-emitted code
        // can call them on every platform.
        builder.symbol("fz_assert", fz_runtime::fz_assert as *const u8);
        builder.symbol("fz_assert_eq", fz_runtime::fz_assert_eq as *const u8);
        builder.symbol("fz_assert_neq", fz_runtime::fz_assert_neq as *const u8);
        builder.symbol("fz_print_f64", fz_runtime::fz_print_f64 as *const u8);
        builder.symbol("fz_halt", fz_runtime::ir_runtime::fz_halt as *const u8);
        builder.symbol(
            "fz_halt_implicit",
            fz_runtime::ir_runtime::fz_halt_implicit as *const u8,
        );
        builder.symbol(
            "fz_halt_implicit_i64",
            fz_runtime::ir_runtime::fz_halt_implicit_i64 as *const u8,
        );
        builder.symbol(
            "fz_halt_implicit_f64",
            fz_runtime::ir_runtime::fz_halt_implicit_f64 as *const u8,
        );
        builder.symbol(
            "fz_alloc_frame",
            fz_runtime::ir_runtime::fz_alloc_frame as *const u8,
        );
        builder.symbol(
            "fz_alloc_list_cons",
            fz_runtime::ir_runtime::fz_alloc_list_cons as *const u8,
        );
        builder.symbol(
            "fz_alloc_struct",
            fz_runtime::ir_runtime::fz_alloc_struct as *const u8,
        );
        builder.symbol(
            "fz_bs_begin",
            fz_runtime::ir_runtime::fz_bs_begin as *const u8,
        );
        builder.symbol(
            "fz_bs_write_field",
            fz_runtime::ir_runtime::fz_bs_write_field as *const u8,
        );
        builder.symbol(
            "fz_bs_finalize",
            fz_runtime::ir_runtime::fz_bs_finalize as *const u8,
        );
        builder.symbol(
            "fz_alloc_bitstring_const",
            fz_runtime::ir_runtime::fz_alloc_bitstring_const as *const u8,
        );
        // fz-q8d.2 — static SharedBin path: codegen emits a 40-byte data
        // symbol in `.data`, then a call to this helper to wrap it in a
        // per-process ProcBin / MSO entry.
        builder.symbol(
            "fz_alloc_procbin_from_static",
            fz_runtime::ir_runtime::fz_alloc_procbin_from_static as *const u8,
        );
        // fz-q8d.2 — noop destructor address baked into each static
        // SharedBin's `destructor` field via a function-address
        // relocation. Never invoked in practice (anchor refcount stays
        // ≥ 1) but must resolve at link time.
        builder.symbol(
            "shared_bin_destructor_noop",
            fz_runtime::procbin::shared_bin_destructor_noop as *const u8,
        );
        // fz-9ss — extern binary marshal helpers.
        builder.symbol(
            "fz_binary_as_ptr",
            fz_runtime::extern_binary::fz_binary_as_ptr as *const u8,
        );
        builder.symbol(
            "fz_binary_as_cstring",
            fz_runtime::extern_binary::fz_binary_as_cstring as *const u8,
        );
        builder.symbol(
            "fz_bs_reader_init",
            fz_runtime::ir_runtime::fz_bs_reader_init as *const u8,
        );
        builder.symbol(
            "fz_bs_read_field",
            fz_runtime::ir_runtime::fz_bs_read_field as *const u8,
        );
        builder.symbol(
            "fz_map_begin",
            fz_runtime::ir_runtime::fz_map_begin as *const u8,
        );
        builder.symbol(
            "fz_map_clone",
            fz_runtime::ir_runtime::fz_map_clone as *const u8,
        );
        builder.symbol(
            "fz_map_push",
            fz_runtime::ir_runtime::fz_map_push as *const u8,
        );
        builder.symbol(
            "fz_map_finalize",
            fz_runtime::ir_runtime::fz_map_finalize as *const u8,
        );
        builder.symbol(
            "fz_map_get",
            fz_runtime::ir_runtime::fz_map_get as *const u8,
        );
        builder.symbol(
            "fz_alloc_float",
            fz_runtime::ir_runtime::fz_alloc_float as *const u8,
        );
        builder.symbol(
            "fz_promote_f64",
            fz_runtime::ir_runtime::fz_promote_f64 as *const u8,
        );
        builder.symbol("fz_fmod", fz_runtime::ir_runtime::fz_fmod as *const u8);
        builder.symbol(
            "fz_value_eq",
            fz_runtime::ir_runtime::fz_value_eq as *const u8,
        );
        builder.symbol(
            "fz_vec_begin",
            fz_runtime::ir_runtime::fz_vec_begin as *const u8,
        );
        builder.symbol(
            "fz_vec_push",
            fz_runtime::ir_runtime::fz_vec_push as *const u8,
        );
        builder.symbol(
            "fz_vec_finalize",
            fz_runtime::ir_runtime::fz_vec_finalize as *const u8,
        );
        builder.symbol(
            "fz_vec_get",
            fz_runtime::ir_runtime::fz_vec_get as *const u8,
        );
        builder.symbol(
            "fz_alloc_closure",
            fz_runtime::ir_runtime::fz_alloc_closure as *const u8,
        );
        builder.symbol("fz_spawn", fz_runtime::ir_runtime::fz_spawn as *const u8);
        builder.symbol(
            "fz_spawn_opt",
            fz_runtime::ir_runtime::fz_spawn_opt as *const u8,
        );
        builder.symbol("fz_self", fz_runtime::ir_runtime::fz_self as *const u8);
        builder.symbol(
            "fz_make_ref",
            fz_runtime::ir_runtime::fz_make_ref as *const u8,
        );
        builder.symbol("fz_send", fz_runtime::ir_runtime::fz_send as *const u8);
        // fz-swt.10 — `make_resource(value, &dtor/1)` lowers to an extern
        // call on `fz_make_resource`. The runtime symbol delegates to a
        // `MakeResourceHook` the binary installs before driving any task
        // that uses resources (see `src/runtime.rs`).
        builder.symbol(
            "fz_make_resource",
            fz_runtime::ir_runtime::fz_make_resource as *const u8,
        );
        // fz-axu.14 (R1) / .13 (S2) — utf8 brand support.
        builder.symbol(
            "fz_bitstring_valid_utf8",
            fz_runtime::ir_runtime::fz_bitstring_valid_utf8 as *const u8,
        );
        builder.symbol(
            "fz_brand_bitstring_as_utf8",
            fz_runtime::ir_runtime::fz_brand_bitstring_as_utf8 as *const u8,
        );
        // fz-swt.11 — runtime-exported fixture/test dtor. Always bound to
        // the JIT (not gated on cfg(test)) so any `fz dump --emit clif`
        // or `fz run` over a fixture that uses it resolves cleanly — the
        // golden-CLIF harness compiles every non-deferred fixture.
        builder.symbol(
            "fz_resource_test_print_dtor",
            fz_runtime::resource::fz_resource_test_print_dtor as *const u8,
        );
        // fz-swt.13 — tmpfile helper exported by the runtime crate for
        // file fixtures. Same wiring contract as the print-dtor symbol
        // above: bound unconditionally so any JIT-driven dump/run
        // resolves the name cleanly.
        builder.symbol(
            "fz_test_open_tmpfile",
            fz_runtime::resource::fz_test_open_tmpfile as *const u8,
        );
        builder.symbol(
            "fz_receive_attempt",
            fz_runtime::ir_runtime::fz_receive_attempt as *const u8,
        );
        builder.symbol(
            "fz_receive_park",
            fz_runtime::ir_runtime::fz_receive_park as *const u8,
        );
        // fz-yxs/fz-st5 — selective receive park entry. Used by B3's
        // JIT codegen at the Term::ReceiveMatched seam.
        builder.symbol(
            "fz_receive_park_matched",
            fz_runtime::ir_runtime::fz_receive_park_matched as *const u8,
        );
        builder.symbol(
            "fz_mid_flight_roots_ptr",
            fz_runtime::ir_runtime::fz_mid_flight_roots_ptr as *const u8,
        );
        // fz-70q.5.2 — cont stubs read bound args from this slab.
        builder.symbol(
            "fz_resume_args_ptr",
            fz_runtime::ir_runtime::fz_resume_args_ptr as *const u8,
        );
        builder.symbol(
            "fz_yield_back_edge",
            fz_runtime::ir_runtime::fz_yield_back_edge as *const u8,
        );
        builder.symbol(
            "fz_get_static_closure",
            fz_runtime::ir_runtime::fz_get_static_closure as *const u8,
        );
        builder.symbol(
            "fz_get_halt_cont",
            fz_runtime::ir_runtime::fz_get_halt_cont as *const u8,
        );
        // fz-02r.5 — bind the cooperative yield helpers and the yield-flag data.
        builder.symbol(
            "FZ_SHOULD_YIELD",
            (&fz_runtime::yield_flag::FZ_SHOULD_YIELD) as *const _ as *const u8,
        );
        // fz-swt.10 (test only) — register test externs (e.g. the
        // `_resource_test_dtor` counter used by the JIT-leg resource
        // lifecycle tests). Production paths see no extra symbols.
        #[cfg(test)]
        builder.symbol(
            "_resource_test_dtor",
            crate::ir_interp::tests_support_test_dtor_addr(),
        );
        Self {
            jmod: JITModule::new(builder),
        }
    }
}

impl Backend for JitBackend {
    type Module = JITModule;
    type Output = CompiledModule;

    fn module_mut(&mut self) -> &mut JITModule {
        &mut self.jmod
    }

    fn fn_linkage(&self) -> Linkage {
        Linkage::Local
    }

    fn emit_metadata_carriers(
        &mut self,
        _fbctx: &mut FunctionBuilderContext,
        _meta: &CompiledMetadata,
    ) -> Result<(), CodegenError> {
        // No-op: JIT carries per-program metadata (fn_ptrs, frame_sizes,
        // atom_names) in the returned CompiledModule's Rust HashMaps.
        // The runtime reads them directly. No Cranelift carriers needed.
        Ok(())
    }

    fn finalize(self, meta: CompiledMetadata) -> Result<CompiledModule, CodegenError> {
        let JitBackend { mut jmod } = self;
        jmod.finalize_definitions()
            .map_err(|e| CodegenError::new(format!("finalize: {}", e)))?;
        let mut fn_ptrs: HashMap<u32, *const u8> = HashMap::new();
        for (fz_fn_id, func_id) in &meta.fn_ids {
            fn_ptrs.insert(*fz_fn_id, jmod.get_finalized_function(*func_id));
        }
        // fz-cps.1.7 — resolve each zero-cap closure-target stub_func_id
        // to its finalized code address. `make_process` writes these into
        // the off-heap singleton's `code_ptr` slot at +16.
        let static_closure_targets: Vec<(u32, u32, *const u8, u32)> = meta
            .static_closure_targets
            .iter()
            .map(|(cl_sid, fn_id, stub_fid, halt_kind)| {
                let ptr = jmod.get_finalized_function(*stub_fid);
                (*cl_sid, *fn_id, ptr, *halt_kind)
            })
            .collect();
        let resume_park_addr = jmod.get_finalized_function(meta.resume_park_id);
        let spawn_entry_addr = jmod.get_finalized_function(meta.spawn_entry_id);
        let main_entry_addr = jmod.get_finalized_function(meta.main_entry_id);
        let drain_dtor_entry_addr = jmod.get_finalized_function(meta.drain_dtor_entry_id);
        let halt_cont_body_addrs = [
            jmod.get_finalized_function(meta.halt_cont_body_ids[0]),
            jmod.get_finalized_function(meta.halt_cont_body_ids[1]),
            jmod.get_finalized_function(meta.halt_cont_body_ids[2]),
        ];
        let mid_flight_resume_addrs = {
            let mut arr = [std::ptr::null::<u8>(); 9];
            for (i, fid) in meta.mid_flight_resume_ids.iter().enumerate() {
                arr[i] = jmod.get_finalized_function(*fid);
            }
            arr
        };
        let resume_addr = jmod.get_finalized_function(meta.resume_id);
        Ok(CompiledModule {
            module: jmod,
            fn_ptrs,
            user_schemas: meta.user_schemas,
            frame_sizes: meta.frame_sizes,
            atom_names: meta.atom_names,
            bs_tuple_arity1_schema: meta.bs_tuple_arity1_schema,
            bs_tuple_arity3_schema: meta.bs_tuple_arity3_schema,
            diagnostics: meta.diagnostics,
            static_closure_targets,
            resume_park_addr,
            spawn_entry_addr,
            main_entry_addr,
            drain_dtor_entry_addr,
            halt_cont_body_addrs,
            fn_halt_kinds: meta.fn_halt_kinds,
            mid_flight_resume_addrs,
            resume_addr,
        })
    }
}

/// AOT backend: wraps a cranelift_object ObjectModule. Drives the same
/// codegen as the JIT (through the Backend trait + declare_runtime_symbols)
/// but finalizes by emitting object-file bytes for a linker rather than
/// resolving fn pointers in memory. fz-ul4.23.6.1.
pub struct AotBackend {
    omod: cranelift_object::ObjectModule,
}

impl AotBackend {
    pub fn new(name: &str) -> Self {
        // AOT needs PIC for macOS — the linker rejects text relocations
        // in regular executables. PIC on x86_64-linux / aarch64-linux is
        // also conventional for distributable binaries.
        let isa = host_isa_with(true);
        let builder = cranelift_object::ObjectBuilder::new(
            isa,
            name.to_string(),
            cranelift_module::default_libcall_names(),
        )
        .expect("ObjectBuilder::new");
        Self {
            omod: cranelift_object::ObjectModule::new(builder),
        }
    }
}

impl Backend for AotBackend {
    type Module = cranelift_object::ObjectModule;
    type Output = AotArtifact;

    fn module_mut(&mut self) -> &mut cranelift_object::ObjectModule {
        &mut self.omod
    }

    fn fn_linkage(&self) -> Linkage {
        Linkage::Export
    }

    fn emit_metadata_carriers(
        &mut self,
        fbctx: &mut FunctionBuilderContext,
        meta: &CompiledMetadata,
    ) -> Result<(), CodegenError> {
        // No `main`/0 in the source → nothing to drive at startup. `fz build`
        // errors gracefully on this artifact via its main_symbol check.
        let Some(main_fn_id) = meta.main_fn_id else {
            return Ok(());
        };

        // fz-siu.6.1: AOT C-main is a thin driver around the cps-in-clif
        // SystemV→Tail-CC shims (fz_main_entry / fz_halt_cont_body) emitted
        // in compile_with_backend. Three FFI fns from fz-runtime do the
        // Process setup, static-closure registration, and run-main+teardown.
        // fz-ul4.27.22.3 — setup takes 3 halt_cont_body addrs (Tagged,
        // RawInt, RawF64) in slots 2-4.
        let setup_sig = sig1(
            &[
                types::I64,
                types::I32,
                types::I64,
                types::I64,
                types::I64,
                types::I64,
                types::I64,
            ],
            &[types::I64],
        );
        let setup_id = self
            .omod
            .declare_function("fz_aot_setup", Linkage::Import, &setup_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_setup: {}", e)))?;

        // fz-ul4.27.22.6: trailing i32 carries halt_kind.
        let reg_sig = sig1(
            &[types::I64, types::I32, types::I32, types::I64, types::I32],
            &[],
        );
        let reg_id = self
            .omod
            .declare_function("fz_aot_register_static_closure", Linkage::Import, &reg_sig)
            .map_err(|e| {
                CodegenError::new(format!("declare fz_aot_register_static_closure: {}", e))
            })?;

        let run_sig = sig1(&[types::I64, types::I64, types::I64], &[types::I32]);
        let run_id = self
            .omod
            .declare_function("fz_aot_run_main", Linkage::Import, &run_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_run_main: {}", e)))?;

        // fz-02r.7 — register mid-flight resume shims before fz_aot_run_main.
        let set_shims_sig = sig1(&[types::I64], &[]);
        let set_shims_id = self
            .omod
            .declare_function("fz_aot_set_resume_shims", Linkage::Import, &set_shims_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_set_resume_shims: {}", e)))?;

        // fz-4mk.3b — fz_aot_set_drain_dtor_entry(addr). Registers the
        // SystemV→Tail-CC `fz_drain_dtor_entry` shim so the AOT run-queue
        // loop can dispatch pending dtor closures at task-exit.
        let set_drain_sig = sig1(&[types::I64], &[]);
        let set_drain_id = self
            .omod
            .declare_function(
                "fz_aot_set_drain_dtor_entry",
                Linkage::Import,
                &set_drain_sig,
            )
            .map_err(|e| {
                CodegenError::new(format!("declare fz_aot_set_drain_dtor_entry: {}", e))
            })?;

        // fz-xx8.1 — fz_aot_set_resume_addr(addr). Registers the SystemV
        // `fz_resume(cont)` shim so the AOT run-queue loop can dispatch
        // `pending_resume_matched` (selective-receive wakeup) on parity
        // with the JIT path (src/ir_codegen.rs:335).
        let set_resume_sig = sig1(&[types::I64], &[]);
        let set_resume_id = self
            .omod
            .declare_function("fz_aot_set_resume_addr", Linkage::Import, &set_resume_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_set_resume_addr: {}", e)))?;

        // fz-ul4.38 — fz_aot_register_tuple_schemas(proc, arities_ptr, len)
        // populates the AOT process's SchemaRegistry with one Tuple{N} entry
        // per arity, in the order the array was emitted. That order matches
        // the sorted iteration in compile_with_backend, so the schema ids
        // baked into the CLIF (via tuple_schema_ids) resolve correctly.
        let reg_tuples_sig = sig1(&[types::I64, types::I64, types::I32], &[]);
        let reg_tuples_id = self
            .omod
            .declare_function(
                "fz_aot_register_tuple_schemas",
                Linkage::Import,
                &reg_tuples_sig,
            )
            .map_err(|e| {
                CodegenError::new(format!("declare fz_aot_register_tuple_schemas: {}", e))
            })?;

        let (tuple_arities_data, tuple_arities_len): (Option<DataId>, u32) =
            if meta.tuple_arities.is_empty() {
                (None, 0)
            } else {
                let mut bytes: Vec<u8> = Vec::with_capacity(meta.tuple_arities.len() * 4);
                for &a in &meta.tuple_arities {
                    bytes.extend_from_slice(&a.to_ne_bytes());
                }
                let len = meta.tuple_arities.len() as u32;
                let id = self
                    .omod
                    .declare_data("fz_aot_tuple_arities", Linkage::Local, false, false)
                    .map_err(|e| CodegenError::new(format!("declare tuple arities: {}", e)))?;
                let mut desc = DataDescription::new();
                desc.define(bytes.into_boxed_slice());
                self.omod
                    .define_data(id, &desc)
                    .map_err(|e| CodegenError::new(format!("define tuple arities: {}", e)))?;
                (Some(id), len)
            };

        let (atom_blob_data, atom_blob_len): (Option<DataId>, u32) = if meta.atom_names.is_empty() {
            (None, 0)
        } else {
            let mut blob: Vec<u8> = Vec::new();
            for name in &meta.atom_names {
                blob.extend_from_slice(name.as_bytes());
                blob.push(0);
            }
            blob.push(0);
            let len = blob.len() as u32;
            let id = self
                .omod
                .declare_data("fz_aot_atom_blob", Linkage::Local, false, false)
                .map_err(|e| CodegenError::new(format!("declare atom blob: {}", e)))?;
            let mut desc = DataDescription::new();
            desc.define(blob.into_boxed_slice());
            self.omod
                .define_data(id, &desc)
                .map_err(|e| CodegenError::new(format!("define atom blob: {}", e)))?;
            (Some(id), len)
        };

        let mut c_main_sig = Signature::new(CallConv::SystemV);
        c_main_sig.params.push(AbiParam::new(types::I32));
        c_main_sig.params.push(AbiParam::new(types::I64));
        c_main_sig.returns.push(AbiParam::new(types::I32));
        let c_main_id = self
            .omod
            .declare_function("main", Linkage::Export, &c_main_sig)
            .map_err(|e| CodegenError::new(format!("declare C main: {}", e)))?;
        emit_aot_c_main(
            &mut self.omod,
            fbctx,
            c_main_id,
            &c_main_sig,
            meta.fn_ids[&main_fn_id.0],
            meta.main_entry_id,
            meta.halt_cont_body_ids,
            meta.spawn_entry_id,
            meta.resume_park_id,
            &meta.static_closure_targets,
            atom_blob_data,
            atom_blob_len,
            setup_id,
            reg_id,
            run_id,
            &meta.mid_flight_resume_ids,
            set_shims_id,
            reg_tuples_id,
            tuple_arities_data,
            tuple_arities_len,
            set_drain_id,
            meta.drain_dtor_entry_id,
            set_resume_id,
            meta.resume_id,
        )?;
        Ok(())
    }

    fn finalize(self, meta: CompiledMetadata) -> Result<AotArtifact, CodegenError> {
        let AotBackend { omod } = self;
        // Emit the macOS platform load command (LC_BUILD_VERSION) so ld
        // doesn't warn "no platform load command found". Cranelift's
        // ObjectBuilder doesn't inject this automatically (fz-ul4.33).
        #[cfg(target_os = "macos")]
        let product = {
            let mut p = omod.finish();
            let mut ver = object::write::MachOBuildVersion::default();
            ver.platform = object::macho::PLATFORM_MACOS;
            ver.minos = 11 << 16; // 11.0.0 — first macOS on Apple Silicon
            ver.sdk = 11 << 16;
            p.object.set_macho_build_version(ver);
            p
        };
        #[cfg(not(target_os = "macos"))]
        let product = omod.finish();
        let object = product
            .emit()
            .map_err(|e| CodegenError::new(format!("object emit: {}", e)))?;
        // For programs with a fz `main`, the C-callable `main` shim is the
        // linker's entry point. Without a fz main, no shim was emitted and
        // we surface the underlying fz_fn_<id> name so `fz build` can
        // error cleanly.
        let main_symbol = if meta.main_fn_id.is_some() {
            Some("main".to_string())
        } else {
            None
        };
        Ok(AotArtifact {
            object,
            main_symbol,
            diagnostics: meta.diagnostics,
        })
    }
}

/// AOT artifact: per-module emitted object bytes plus enough metadata to
/// drive linking. fz-ul4.23.6.3 (`fz build`) consumes this.
pub struct AotArtifact {
    /// Object-file bytes (ELF on Linux, Mach-O on macOS, COFF on Windows)
    /// suitable for `cc` to link against fz_runtime + libc.
    pub object: Vec<u8>,
    /// `main` fn's symbol name as emitted in the object, or None if the
    /// source had no `main/0`. The AOT driver uses this when generating
    /// the startup shim's call site.
    pub main_symbol: Option<String>,
    pub diagnostics: crate::diag::Diagnostics,
}

/// Resolve a TailCallClosure edge to its body's (FnId, SpecId raw u32).
/// Returns None when the closure var isn't typed as a singleton closure_lit
/// or when no covering spec is registered for the resolved key.
/// Shared by the return-type fixpoint, tagged-return seeding, halt_kind
/// analysis, and TailCallClosure codegen — all four had identical inline copies.
fn resolve_tcc_body(
    closure: &crate::fz_ir::Var,
    args: &[crate::fz_ir::Var],
    ft: &crate::ir_typer::FnTypes,
    module: &crate::fz_ir::Module,
    spec_registry: &SpecRegistry,
) -> Option<(crate::fz_ir::FnId, u32)> {
    use crate::types_seam::Types;

    let mut t = crate::types_seam::ConcreteTypes;
    let (fn_id, captures) = t.concrete_closure_lit_parts(ft.vars.get(closure)?)?;
    let body_fn = module.fn_by_id(fn_id);
    let np = body_fn.block(body_fn.entry).params.len();
    let any = t.any();
    let mut key: Vec<crate::types_seam::Ty> = captures;
    for av in args {
        key.push(ft.vars.get(av).cloned().unwrap_or_else(|| any.clone()));
    }
    while key.len() < np {
        key.push(any.clone());
    }
    key.truncate(np);
    Some((fn_id, spec_registry.resolve(fn_id, &key)?.0))
}

/// Emit a single Cranelift function: make_context → set sig → build body →
/// finalize → define_function → clear_context. Eliminates the boilerplate
/// repeated for every runtime shim (fz_main_entry, fz_spawn_entry, etc.).
pub(crate) fn emit_fn_body<M: cranelift_module::Module>(
    module: &mut M,
    fbctx: &mut FunctionBuilderContext,
    sig: Signature,
    func_id: FuncId,
    body: impl FnOnce(&mut M, &mut FunctionBuilder<'_>),
) -> Result<(), Box<cranelift_module::ModuleError>> {
    let mut ctx = module.make_context();
    ctx.func.signature = sig;
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);
        body(module, &mut b);
        b.finalize();
    }
    module
        .define_function(func_id, &mut ctx)
        .map_err(Box::new)?;
    module.clear_context(&mut ctx);
    Ok(())
}

/// Drive the shared compile pipeline through any Backend impl. JIT and
/// AOT both route through here; the backend's hooks pick the legit
/// variation points (linkage, per-program metadata carriers, finalize).
///
/// fz-ul4.23.12. Before this, `compile()` and `compile_aot()` duplicated
/// ~90% of the pipeline side by side. Now they're each ~5-line wrappers
/// constructing a backend and calling here.
pub fn compile_with_backend<B: Backend, T: crate::types_seam::Types<Ty = crate::types_seam::Ty>>(
    t: &mut T,
    module: &Module,
    mut backend: B,
) -> Result<B::Output, CodegenError> {
    let runtime = declare_runtime_symbols(backend.module_mut())?;

    let mut fbctx = FunctionBuilderContext::new();

    // fz-ul4.27.22.3 — emit fz_main_entry. Generic shim: takes the
    // entry fn ptr + a halt-cont singleton ptr supplied by the Rust
    // caller (caller picks the singleton matching the entry fn's
    // return_repr kind). Body just `call_indirect Tail main_fp(halt_cl)`.
    {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(
            backend.module_mut(),
            &mut fbctx,
            sig,
            runtime.main_entry_id,
            |_m, b| {
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                b.seal_block(entry);
                let main_fp = b.block_params(entry)[0];
                let halt_cl = b.block_params(entry)[1];
                let mut main_sig = Signature::new(CallConv::Tail);
                main_sig.params.push(AbiParam::new(types::I64));
                main_sig.returns.push(AbiParam::new(types::I64));
                let sig_ref = b.func.import_signature(main_sig);
                let inst = b.ins().call_indirect(sig_ref, main_fp, &[halt_cl]);
                let r = b.inst_results(inst)[0];
                b.ins().return_(&[r]);
            },
        )
        .map_err(|e| CodegenError::new(format!("define fz_main_entry: {}", e)))?;
    }

    // fz-4mk.3a — emit fz_drain_dtor_entry. SystemV scheduler-callable
    // shim that invokes a 1-arg resource dtor closure with its payload.
    // Body: pick a Tagged halt-cont via fz_get_halt_cont, load the body
    // addr at closure+16, and Tail-CC indirect-call
    // `(closure, payload, halt_cl)`. Result is discarded by the caller.
    // Sig: `(closure:i64, payload:i64) -> i64 system_v`.
    {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(
            backend.module_mut(),
            &mut fbctx,
            sig,
            runtime.drain_dtor_entry_id,
            |m, b| {
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                b.seal_block(entry);
                let closure = b.block_params(entry)[0];
                let payload = b.block_params(entry)[1];
                // Tagged halt-cont (kind=0). Dtor return is discarded;
                // Tagged is harmless and avoids RawInt/F64 unboxing.
                let tagged_addr = fn_addr(m, runtime.halt_cont_body_tagged_id, b);
                let zero = b.ins().iconst(types::I32, 0);
                let ghc_fref = m.declare_func_in_func(runtime.get_halt_cont_id, b.func);
                let halt_inst = b.ins().call(ghc_fref, &[tagged_addr, zero]);
                let halt_cl = b.inst_results(halt_inst)[0];
                let code = b
                    .ins()
                    .load(types::I64, MemFlags::trusted(), closure, HEADER_SIZE);
                // fz-cps.1.2 §2.1 closure-target body sig: `(args..., self,
                // cont) tail -> i64`. For a 1-arg dtor wrapper that's
                // `(x, self, cont)`.
                let mut closure_sig = Signature::new(CallConv::Tail);
                closure_sig.params.push(AbiParam::new(types::I64)); // x (payload)
                closure_sig.params.push(AbiParam::new(types::I64)); // self
                closure_sig.params.push(AbiParam::new(types::I64)); // cont
                closure_sig.returns.push(AbiParam::new(types::I64));
                let sig_ref = b.func.import_signature(closure_sig);
                let inst = b
                    .ins()
                    .call_indirect(sig_ref, code, &[payload, closure, halt_cl]);
                let r = b.inst_results(inst)[0];
                b.ins().return_(&[r]);
            },
        )
        .map_err(|e| CodegenError::new(format!("define fz_drain_dtor_entry: {}", e)))?;
    }

    // fz-cps.1.11 — emit fz_spawn_entry. SystemV scheduler-callable shim
    // that invokes a zero-arg closure with a fresh halt-cont. Used by
    // `Runtime::spawn_closure` to launch the new task's first fn via
    // the closure-target sig `(self, cont) tail`. The closure body
    // tail-chains into a halt-cont; halt sets process.halt_value.
    // Sig: `(closure:i64) -> i64 system_v`.
    {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(
            backend.module_mut(),
            &mut fbctx,
            sig,
            runtime.spawn_entry_id,
            |m, b| {
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                b.seal_block(entry);
                let closure = b.block_params(entry)[0];
                // fz-ul4.27.22.6 — pick the matching halt-cont based on the
                // spawned closure's halt_kind (packed into the high 2 bits of
                // the heap header's `flags` at MakeClosure time). For
                // RawInt-returning bodies, this routes the i64 raw bits into
                // halt_cont_body_i64 instead of sshr-ing them as if they were
                // tagged FzValue. Pre-22.6 this was hardcoded Tagged.
                //
                // Closure HeapHeader layout:
                //   off 0  : kind (u16)         off 4  : size_bytes (u32)
                //   off 2  : flags (u16)        off 8  : schema_id (u32)
                //                               off 12 : _reserved (u32)
                // flags low 14 bits = captured_count; high 2 bits = halt_kind.
                let flags_u16 = b.ins().load(types::I16, MemFlags::trusted(), closure, 2);
                // Right-shift 14 to extract halt_kind (0..2), then widen to i32.
                let hk16 = b.ins().ushr_imm(flags_u16, 14);
                let kind = b.ins().uextend(types::I32, hk16);
                // Select halt_cont_body_addr by kind. Branchless via three
                // func_addrs + a tiny dispatch — keeps the spawn shim a leaf.
                let a_tagged = fn_addr(m, runtime.halt_cont_body_tagged_id, b);
                let a_i64 = fn_addr(m, runtime.halt_cont_body_i64_id, b);
                let a_f64 = fn_addr(m, runtime.halt_cont_body_f64_id, b);
                let one = b.ins().iconst(types::I32, 1);
                let two = b.ins().iconst(types::I32, 2);
                let is_i64 = b.ins().icmp(IntCC::Equal, kind, one);
                let is_f64 = b.ins().icmp(IntCC::Equal, kind, two);
                let pick_i64_or_tagged = b.ins().select(is_i64, a_i64, a_tagged);
                let hcb_addr = b.ins().select(is_f64, a_f64, pick_i64_or_tagged);
                let ghc_fref = m.declare_func_in_func(runtime.get_halt_cont_id, b.func);
                let halt_inst = b.ins().call(ghc_fref, &[hcb_addr, kind]);
                let halt_cl = b.inst_results(halt_inst)[0];
                // Load closure body addr at +16 and invoke as
                // closure-target sig `(self, cont) tail` (zero user args).
                let code = b
                    .ins()
                    .load(types::I64, MemFlags::trusted(), closure, HEADER_SIZE);
                let mut closure_sig = Signature::new(CallConv::Tail);
                closure_sig.params.push(AbiParam::new(types::I64)); // self
                closure_sig.params.push(AbiParam::new(types::I64)); // cont
                closure_sig.returns.push(AbiParam::new(types::I64));
                let sig_ref = b.func.import_signature(closure_sig);
                let inst = b.ins().call_indirect(sig_ref, code, &[closure, halt_cl]);
                let r = b.inst_results(inst)[0];
                b.ins().return_(&[r]);
            },
        )
        .map_err(|e| CodegenError::new(format!("define fz_spawn_entry: {}", e)))?;
    }

    // fz-cps.1.11 — emit fz_resume_park. SystemV scheduler-callable shim
    // that wakes a parked task: `load parked_cont+16; call_indirect Tail
    // sig_cont (msg, parked_cont); return result`. The runtime invokes
    // this when a Blocked task transitions to Ready (a message has
    // arrived). Sig: `(msg:i64, parked_cont:i64) -> i64 system_v`.
    {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(
            backend.module_mut(),
            &mut fbctx,
            sig,
            runtime.resume_park_id,
            |_m, b| {
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                b.seal_block(entry);
                let msg = b.block_params(entry)[0];
                let cont = b.block_params(entry)[1];
                let code = b
                    .ins()
                    .load(types::I64, MemFlags::trusted(), cont, HEADER_SIZE);
                let mut cont_sig = Signature::new(CallConv::Tail);
                cont_sig.params.push(AbiParam::new(types::I64));
                cont_sig.params.push(AbiParam::new(types::I64));
                cont_sig.returns.push(AbiParam::new(types::I64));
                let sig_ref = b.func.import_signature(cont_sig);
                let inst = b.ins().call_indirect(sig_ref, code, &[msg, cont]);
                let r = b.inst_results(inst)[0];
                b.ins().return_(&[r]);
            },
        )
        .map_err(|e| CodegenError::new(format!("define fz_resume_park: {}", e)))?;
    }

    // fz-ul4.27.22.3 — emit three fz_halt_cont_body fns, one per repr.
    // The producer's Term::Return uses sig (return_repr, i64); the
    // closure pointer at the chain end points at the matching body so
    // sigs agree. Tagged variant unboxes (existing semantics); RawInt
    // / RawF64 variants store the value directly.
    for (body_id, val_ty, halt_impl_id) in [
        (
            runtime.halt_cont_body_tagged_id,
            types::I64,
            runtime.halt_implicit_id,
        ),
        (
            runtime.halt_cont_body_i64_id,
            types::I64,
            runtime.halt_implicit_i64_id,
        ),
        (
            runtime.halt_cont_body_f64_id,
            types::F64,
            runtime.halt_implicit_f64_id,
        ),
    ] {
        let mut sig = Signature::new(CallConv::Tail);
        sig.params.push(AbiParam::new(val_ty));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(backend.module_mut(), &mut fbctx, sig, body_id, |m, b| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let val = b.block_params(entry)[0];
            let hi_fref = m.declare_func_in_func(halt_impl_id, b.func);
            b.ins().call(hi_fref, &[val]);
            let zero = b.ins().iconst(types::I64, 0);
            b.ins().return_(&[zero]);
        })
        .map_err(|e| CodegenError::new(format!("define halt_cont_body: {}", e)))?;
    }

    // Register a heap Schema for every tuple arity used by MakeTuple, so the
    // GC tracer can walk fields and so codegen can iconst the schema_id.
    // Also detect any bitstring prim so we can pre-register arity-1 / arity-3
    // schemas used by the reader / result tuples even if no MakeTuple uses
    // those arities directly.
    // fz-ul4.38 — BTreeSet so iteration order is deterministic. Schema ids
    // are assigned by registration order; the AOT runtime registers in the
    // same sorted order so its ids match what codegen baked into the CLIF.
    let mut tuple_arities: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
    let mut has_bs_prim = false;
    for f in &module.fns {
        for blk in &f.blocks {
            for stmt in &blk.stmts {
                let Stmt::Let(_, prim) = stmt;
                match prim {
                    Prim::MakeTuple(args) => {
                        tuple_arities.insert(args.len());
                    }
                    Prim::MakeBitstring(_)
                    | Prim::BitReaderInit(_)
                    | Prim::BitReadField { .. }
                    | Prim::BitReaderDone(_) => {
                        has_bs_prim = true;
                    }
                    // fz-ul4.36 — also register schemas for arities that
                    // appear in TypeTest tuple descriptors. The runtime
                    // check compares schema_id; without pre-registration
                    // we'd have no id to compare against.
                    Prim::TypeTest(_, descr) => {
                        let descr_ty = t.from_concrete(descr);
                        for arity in t.type_test_shape(&descr_ty).tuple_arities {
                            tuple_arities.insert(arity);
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    if has_bs_prim {
        tuple_arities.insert(1);
        tuple_arities.insert(3);
    }
    let user_schemas = std::rc::Rc::new(std::cell::RefCell::new(
        fz_runtime::heap::SchemaRegistry::new(),
    ));
    let mut tuple_schema_ids: HashMap<usize, u32> = HashMap::new();
    {
        let mut reg = user_schemas.borrow_mut();
        for &arity in &tuple_arities {
            let id = reg.register(Schema::tuple_of_arity(arity));
            tuple_schema_ids.insert(arity, id);
        }
    }
    let (bs_tuple_arity1_schema, bs_tuple_arity3_schema) = if has_bs_prim {
        (
            Some(*tuple_schema_ids.get(&1).expect("arity-1 schema registered")),
            Some(*tuple_schema_ids.get(&3).expect("arity-3 schema registered")),
        )
    } else {
        (None, None)
    };

    // frame_sizes is computed after `schemas` is built (post-spec_registry).

    // Run the typer ahead of codegen so per-fn Var->Descr info is
    // available during lowering. .11.24.5 clones first so the typed-schema
    // rewrite can swap MakeVec(I64) → MakeVec(F64) where elements are Float.
    //
    // fz-5j5.2 — one pre-rewrite typing serves both
    // rewrite_vec_kinds and rewrite_known_target_closures. The reads are
    // orthogonal (element types vs. fn_constants) and the writes are
    // orthogonal (VecKindIr mutations vs. CallClosure→Call rewrites);
    // neither rewrite invalidates what the other reads.
    let mut working = module.clone();
    let pre_types = crate::ir_typer::type_module(t, &working);
    crate::ir_typer::rewrite_vec_kinds(t, &mut working, &pre_types).map_err(CodegenError::new)?;
    // fz-ul4.29.10.3 — lower known-target CallClosure / TailCallClosure
    // to direct Call / TailCall. After this, the final type_module sees
    // direct dispatch where the closure-stub used to live, and
    // .29.12.6's any-key drop logic can remove the now-dead any-key.
    //
    // fz-5j5.2 — uses the same `pre_types` as rewrite_vec_kinds above.
    // The two rewrites are orthogonal: rewrite_vec_kinds mutates
    // `Prim::MakeVec` kind tags; `fn_constants` tracks Vars bound to
    // `Prim::Const(Value::Fn)` / `Prim::MakeClosure`, neither of which
    // is touched. So `pre_types.fn_constants` is identical to whatever
    // a re-type would produce. No separate `mid_types` call needed.
    crate::ir_typer::rewrite_known_target_closures(t, &mut working, &pre_types);
    #[cfg(not(test))]
    crate::ir_inline::inline_module(&mut working);
    #[cfg(test)]
    if !INLINE_DISABLED.with(|d| d.get()) {
        crate::ir_inline::inline_module(&mut working);
    }
    crate::ir_fuse::fuse_blocks(&mut working);
    // fz-jg5.4 (RED.3) — compile-time reducer pass. Folds calls whose
    // return is statically known; reduces If-on-bool-literal to Goto.
    // Plugs in after ir_inline + ir_fuse so it sees a cleaner call graph.
    // See docs/bodies-are-boundaries.md.
    // fz-uwq.9 — reducer returns a ReducerLog (Consumed / Stalled
    // facts). Codegen doesn't consume it directly; the dump pipeline
    // does. Codegen drives reduction only for its IR-rewriting effect.
    #[cfg(not(test))]
    let _ = crate::ir_reducer::reduce_module(t, &mut working);
    #[cfg(test)]
    if !REDUCER_DISABLED.with(|d| d.get()) {
        let _ = crate::ir_reducer::reduce_module(t, &mut working);
    }
    // fz-uwq.2 — single-use cont collapse runs pre-typer, alongside the
    // other call-shape mutations (`fuse_blocks`, `reduce_module`). The
    // `debug_assert_unique_conts` check at the end of `ir_lower` (fz-uwq.1)
    // guarantees this pass sees each continuation fn exactly once, so it
    // can be applied before the typer commits to specs. See
    // `docs/dispatch-as-typer-output.md` (Worry 1).
    crate::ir_inline::inline_single_use_conts(&mut working);
    let module_types = crate::ir_typer::type_module(t, &working);
    // fz-uwq.14 — snapshot per-fn call-shape multisets right after the
    // typer commits to specs. The post-typer passes (branch_fold, fold,
    // const_bs::fold, dce_module, dce_module_level) may FOLD calls away
    // (Direct → Return when the reducer would have done it; If → Goto
    // when a branch collapses) but must never INVENT new ones — the
    // typer's spec set wouldn't cover invented calls. The assertion at
    // the end of this pipeline pins the invariant: every fn's
    // call-shape multiset post-codegen is a subset (per-kind) of the
    // post-typer multiset.
    #[cfg(debug_assertions)]
    let call_shapes_pre = crate::ir_codegen_invariants::snapshot_call_shapes(&working);
    // fz-fyq.4 — fold one-sided-dead Ifs to Gotos; DCE below removes
    // the orphaned blocks and the now-unused TypeTest stmts.
    crate::ir_branch_fold::fold_module(&mut working, &module_types);
    crate::ir_fold::fold_module(&mut working, &module_types);
    // fz-cty.8 — fold byte-literal MakeBitstring into ConstBitstring before
    // DCE so the per-byte Const(Int) operand stmts go dead in the same pass.
    crate::ir_const_bs::fold_module(&mut working);
    crate::ir_dce::dce_module(&mut working);
    // fz-ul4.11.29: sweep IR fns unreachable from main after inlining.
    crate::ir_dce::dce_module_level(&mut working);
    #[cfg(debug_assertions)]
    crate::ir_codegen_invariants::assert_no_new_call_shapes(&working, &call_shapes_pre);
    let module = &working;

    // fz-ul4.29.2.1 — Build the SpecRegistry.
    //
    // Register any-keys first, in FnId.0 order — this preserves the
    // invariant `any-key SpecId.0 == FnId.0` so closure / Spawn / Receive
    // paths (and any other "use any-key" path) can keep using fn_id.0
    // directly as a schema_id / Cranelift func key. Narrow specs from
    // `module_types.specs` get SpecIds ≥ n_fns appended afterwards.
    let mut spec_registry = SpecRegistry::new();
    let mut fns_by_fnid: Vec<&crate::fz_ir::FnIr> = module.fns.iter().collect();
    fns_by_fnid.sort_by_key(|f| f.id.0);
    for f in &fns_by_fnid {
        let n_params = f.block(f.entry).params.len();
        let any_ty = t.concrete_any();
        let any_key = vec![any_ty; n_params];
        // fz-ul4.29.12.6 — skip registering F's any-key when the typer
        // dropped it (every callsite of F has typed coverage). The next
        // registration via `register_any_key_at` pads slot F.0 with a
        // sentinel automatically, preserving the `SpecId.0 == FnId.0`
        // invariant for the surviving any-keys.
        if !module_types.specs.contains_key(&(f.id, any_key.clone())) {
            continue;
        }
        let sid = spec_registry.register_any_key_at(f.id, any_key);
        debug_assert_eq!(sid.0, f.id.0);
    }
    // Append narrow specs in a deterministic order (FnId.0, then descr-tuple
    // bytes) so CLIF emission is reproducible across runs.
    let any_ty = t.concrete_any();
    let mut narrow_keys: Vec<(FnId, Vec<crate::types_seam::Ty>)> = module_types
        .specs
        .keys()
        .filter(|(fid, key)| {
            let n_params = module
                .fns
                .iter()
                .find(|f| f.id == *fid)
                .map(|f| f.block(f.entry).params.len())
                .unwrap_or(0);
            // Filter the any-keys (already registered).
            !(key.len() == n_params && key.iter().all(|d| d == &any_ty))
        })
        .cloned()
        .collect();
    narrow_keys.sort_by(|a, b| {
        a.0.0
            .cmp(&b.0.0)
            .then_with(|| format!("{:?}", a.1).cmp(&format!("{:?}", b.1)))
    });
    for (fid, key) in narrow_keys {
        spec_registry.register(fid, key);
    }

    let spec_count = spec_registry.len();
    let spec_keys: Vec<(FnId, Vec<crate::types_seam::Ty>)> = spec_registry
        .iter()
        .map(|(_, fid, key)| (fid, key.to_vec()))
        .collect();
    // SpecId.0 -> module.fns index (None when the SpecId is a sentinel
    // slot for a missing FnId.0 — cps_split sparsity).
    let mut idx_of: HashMap<FnId, usize> = HashMap::new();
    for (i, f) in module.fns.iter().enumerate() {
        idx_of.insert(f.id, i);
    }
    // fz-ul4.29.12.6 — treat slots whose typer FnTypes is absent as
    // sentinels too. Three cases collapse here:
    //   * cps_split sparsity: FnId not in module → `idx_of.get` = None.
    //   * Pre-existing sentinel slot (empty-key padding) for a missing
    //     FnId.0 → no entry in `module_types.specs` either.
    //   * Dropped any-key (.29.12.6): FnId exists in module but its
    //     any-key body was pruned by the typer → no entry in
    //     `module_types.specs`. Codegen must skip compilation for the
    //     slot; no consumer can index into it because `resolve` only
    //     returns SpecIds with a real registration.
    let spec_fnidx: Vec<Option<usize>> = spec_keys
        .iter()
        .map(|(fid, key)| {
            if !module_types.specs.contains_key(&(*fid, key.clone())) {
                return None;
            }
            idx_of.get(fid).copied()
        })
        .collect();
    let spec_fn_types: Vec<Option<&crate::ir_typer::FnTypes>> = spec_keys
        .iter()
        .enumerate()
        .map(|(sid, (fid, key))| {
            spec_fnidx[sid]?;
            module_types.specs.get(&(*fid, key.clone()))
        })
        .collect();

    // fz-ul4.29.12.2 — collect typed closure shapes keyed by the
    // lambda's resolved narrow SpecId. Each `Prim::MakeClosure` site
    // is inspected per *caller* spec (so closures built in different
    // caller specializations with different capture Descrs produce
    // distinct lambda SpecIds → distinct stubs). The key fed to
    // `spec_registry.resolve` is `[capture_descrs..., any, ...]` —
    // padded to the lambda's full arity. The .29.12.2 typer change
    // (in `ir_typer::type_module`'s worklist) registers a narrow
    // spec for every MakeClosure's capture-Descr tuple, so
    // exact-match resolve succeeds; the any-key remains a subsumption
    // backstop. Value = capture count (== `captured.len()`); needed
    // to split entry params into `[captures..., args...]` at stub
    // declaration / invocation.
    let mut closure_shapes: std::collections::BTreeMap<u32, usize> =
        std::collections::BTreeMap::new();
    for sid in 0..spec_count {
        let Some(idx) = spec_fnidx[sid] else {
            continue;
        };
        let f = &module.fns[idx];
        let Some(_) = spec_fn_types[sid] else {
            continue;
        };
        for blk in &f.blocks {
            for stmt in blk.stmts.iter() {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeClosure(_ident, lam_fn_id, captured) = prim {
                    // fz-try B1+B2 — the lambda body is the any-key
                    // body spec (SpecId.0 == FnId.0 via
                    // register_any_key_at). MakeClosure is construction,
                    // not dispatch — look up the body directly.
                    // When the any-key was dropped (.29.12.6), fall back
                    // to any registered narrow spec for this FnId; if
                    // none, the closure value has no live call target
                    // (every invocation got inlined to direct Call) —
                    // skip; the null-stub path in MakeClosure prim
                    // codegen handles allocation.
                    let cl_sid = if spec_fnidx
                        .get(lam_fn_id.0 as usize)
                        .copied()
                        .flatten()
                        .is_some()
                    {
                        Some(lam_fn_id.0)
                    } else {
                        spec_registry
                            .iter()
                            .find(|(s, fid, _)| {
                                *fid == *lam_fn_id && spec_fnidx[s.0 as usize].is_some()
                            })
                            .map(|(s, _, _)| s.0)
                    };
                    let Some(cl_sid) = cl_sid else {
                        continue;
                    };
                    closure_shapes.insert(cl_sid, captured.len());
                }
            }
        }
    }

    // fz-ul4.27.6.2.1 — Parking + native-callability analyses. Stored in
    // metadata; consumed at declare-time below (.6.2.2) for per-fn sigs
    // and at compile_fn / emit_call (.6.2.3-4) for ABI bifurcation.
    // fz-ul4.27.14.1: this block moved up to feed the new
    // `uniform_cont_reachable_specs` analysis that gates the schema /
    // ABI slot-0 force-Tagged decision below.
    let parking_reachable = crate::parking::parking_reachable(module);
    let mut natively_callable = crate::parking::natively_callable(module, &parking_reachable);

    // fz-cps.1.2 (fz-siu.1.2): the set of fns used as continuations.
    // A cont fn has sig `(result:i64, self:i64) tail` per
    // docs/cps-in-clif.md §2.1 — no host_ctx, no trailing cont param.
    // Its body reads captures from `self+24, +32, ...` rather than
    // from typed entry params, and its "next k" is one of its captures.
    let cont_fns: std::collections::HashSet<crate::fz_ir::FnId> = {
        use crate::fz_ir::Term;
        let mut s = std::collections::HashSet::new();
        for f in &module.fns {
            for b in &f.blocks {
                match &b.terminator {
                    Term::Call { continuation, .. }
                    | Term::CallClosure { continuation, .. }
                    | Term::Receive {
                        continuation,
                        ident: _,
                    } => {
                        s.insert(continuation.fn_id);
                    }
                    // fz-70q.5.5 — clause body / guard / after fns are
                    // dispatched (via cont stub) into their Tail-CC entry,
                    // so they must wear the cont-fn sig shape. The
                    // companion `cont_extras_count` map then overrides the
                    // single-input default with each fn's bound_arity so
                    // the sig is `(bound..., self) tail`. Captures live
                    // INSIDE the closure (read from self+32+i*8 by the
                    // entry harness), so they're not Cranelift params.
                    Term::ReceiveMatched { clauses, after, .. } => {
                        for c in clauses {
                            s.insert(c.body);
                            if let Some(g) = c.guard {
                                s.insert(g);
                            }
                        }
                        if let Some(a) = after {
                            s.insert(a.body);
                        }
                    }
                    _ => {}
                }
            }
        }
        s
    };
    let _ = &cont_fns; // fz-cps.1.2: consumed by sig builder + entry harness in next step.

    // fz-cps.1.2 — set of fns appearing as a MakeClosure target. Per
    // docs/cps-in-clif.md §2.1 these get sig `(args..., self:i64, cont:i64)
    // tail` and their body loads captures from `self+24+8*i`. Disjoint
    // from cont_fns by construction (conts are anonymous continuations
    // synthesized by the lowerer; MakeClosure targets are user lambdas
    // or top-level fns passed as values). If overlap occurs in some
    // future fz-IR, cont-fn shape wins (Receive parking would otherwise
    // misread the result slot).
    let (closure_target_fns, closure_n_captures): (
        std::collections::HashSet<crate::fz_ir::FnId>,
        std::collections::HashMap<crate::fz_ir::FnId, usize>,
    ) = {
        use crate::fz_ir::{Prim, Stmt, Term};
        let mut targets = std::collections::HashSet::new();
        let mut counts: std::collections::HashMap<crate::fz_ir::FnId, usize> =
            std::collections::HashMap::new();
        let mut direct_called = std::collections::HashSet::new();
        for f in &module.fns {
            for b in &f.blocks {
                match &b.terminator {
                    Term::Call { callee, .. } | Term::TailCall { callee, .. } => {
                        direct_called.insert(*callee);
                    }
                    _ => {}
                }
                for stmt in &b.stmts {
                    let Stmt::Let(_, prim) = stmt;
                    if let Prim::MakeClosure(_, fid, captured) = prim {
                        targets.insert(*fid);
                        let n = captured.len();
                        if let Some(prev) = counts.get(fid) {
                            debug_assert_eq!(
                                *prev, n,
                                "MakeClosure n_captures mismatch for fn {}: \
                                 {} vs {}",
                                fid.0, prev, n
                            );
                        }
                        counts.insert(*fid, n);
                    }
                }
            }
        }
        // fz-cps.1.8: closure-target sig is universal. Every MakeClosure
        // target gets `(args..., self, cont) tail` regardless of whether
        // it is also direct-called. Direct callers load the
        // per-Process static singleton (registered in fz-siu.1.7) and
        // pass it as `self`. See docs/cps-in-clif.md §8.2 acceptance:
        // both indirect calls lower to `return_call_indirect` against
        // this sig.
        //
        // Invariant: a closure-target fn that is ALSO direct-called must
        // have zero captures — direct callers have no captures to bind.
        // Asserted below.
        for fid in &targets {
            if direct_called.contains(fid) {
                debug_assert_eq!(
                    counts[fid], 0,
                    "fz-siu.1.8: fn {} is both direct-called and a non-zero-cap \
                     closure target — direct callers can't supply captures",
                    fid.0,
                );
            }
        }
        let _ = direct_called;
        (targets, counts)
    };
    let _ = (&closure_target_fns, &closure_n_captures);
    // fz-ul4.27.6.4 follow-up: heap-safe captures.
    //
    // A native cont chain routes the caller's captured vars through
    // Cranelift virtual stack slots / registers as it crosses the
    // synchronous call to the (native) callee. Those slots are
    // invisible to the GC's heap-frame tracer — safe for non-heap
    // payloads (tagged int / atom / nil / bool, which are just bits),
    // unsafe for heap pointers (boxed float, list cons, struct,
    // closure, etc.) because a GC firing inside the callee would
    // reclaim the unreachable objects.
    //
    // Stack-map emission + a stack-walking tracer would lift this
    // restriction (filed as a follow-up). Until then we shrink
    // `natively_callable` so it only admits conts whose every use
    // site has heap-safe captures. A cont removed by this pass cascades
    // through the fixed point — its callers may no longer satisfy the
    // chain's "every Term::Call cont is native" invariant.
    // fz-cps.1.2: `non_heap` / `is_non_heap_descr` removed with the
    // type-aware shrink — see (a) below. The descriptor types stay in
    // crate::types for other callers.
    // Single combined fixed point. Each iter re-enforces every invariant
    // so cascading removals don't leave an inconsistent set:
    //   (a) Term::Call's callee + cont both native, captures non-heap.
    //   (b) Term::TailCall's callee native, args non-heap.
    //   (c) Cont validity: if f is used as cont in some Term::Call, the
    //       caller's callee at that site must be native (so the site
    //       picks the native-chain branch) and captures non-heap.
    loop {
        let mut to_remove: Vec<crate::fz_ir::FnId> = Vec::new();
        // (a) and (b): body invariants.
        for f in module.fns.iter() {
            if !natively_callable.contains(&f.id) {
                continue;
            }
            let body_ok = f.blocks.iter().all(|b| match &b.terminator {
                Term::Return(_) | Term::Halt(_) | Term::Goto(_, _) | Term::If { .. } => true,
                Term::Call {
                    ident: _,
                    callee,
                    continuation,
                    ..
                } => {
                    // fz-cps.1.2: non-heap-args restriction lifted. The
                    // cont chain no longer routes args through Cranelift
                    // register slots invisible to the GC tracer — every
                    // cont is now a heap-allocated closure (§2.2), and
                    // the GC roots come from `process.parked_cont` (§7)
                    // not from a stack walk.
                    natively_callable.contains(callee)
                        && natively_callable.contains(&continuation.fn_id)
                }
                Term::TailCall { callee, .. } => natively_callable.contains(callee),
                // fz-cps.1.8 — closure-call terminators admitted; bodies
                // are Tail-CC at cl+16 with closure-target sig. Cont (if
                // any) must also be native so the cont-return chain is
                // unbroken.
                Term::CallClosure { continuation, .. } => {
                    natively_callable.contains(&continuation.fn_id)
                }
                Term::TailCallClosure { .. } => true,
                Term::Receive {
                    continuation,
                    ident: _,
                } => natively_callable.contains(&continuation.fn_id),
                // fz-70q.5.5 — admit ReceiveMatched on the same terms
                // as parking.rs's natively_callable: native iff every
                // body / guard / after fn is native. Cont-stub seam
                // bridges the Tail-CC body into the SystemV scheduler
                // resume path so the enclosing fn's ABI is unconstrained.
                Term::ReceiveMatched { clauses, after, .. } => {
                    let body_ok = clauses.iter().all(|c| {
                        natively_callable.contains(&c.body)
                            && c.guard.is_none_or(|g| natively_callable.contains(&g))
                    });
                    let after_ok = after
                        .as_ref()
                        .is_none_or(|a| natively_callable.contains(&a.body));
                    body_ok && after_ok
                }
            });
            if !body_ok {
                to_remove.push(f.id);
            }
        }
        // (c) Cont validity: cont must reach via a native Term::Call site.
        // fz-cps.1.2: capture heap-safety is no longer required (see
        // explanation in (a) above). The structural check remains: the
        // caller's callee at every cont reach site must still be native.
        for f in &module.fns {
            if !natively_callable.contains(&f.id) {
                continue;
            }
            if to_remove.contains(&f.id) {
                continue;
            }
            let mut cont_unsafe = false;
            'outer: for caller in module.fns.iter() {
                for b in &caller.blocks {
                    let Term::Call {
                        ident: _,
                        callee,
                        continuation,
                        ..
                    } = &b.terminator
                    else {
                        continue;
                    };
                    if continuation.fn_id != f.id {
                        continue;
                    }
                    if !natively_callable.contains(callee) {
                        cont_unsafe = true;
                        break 'outer;
                    }
                }
            }
            if cont_unsafe {
                to_remove.push(f.id);
            }
        }
        if to_remove.is_empty() {
            break;
        }
        for id in to_remove {
            natively_callable.remove(&id);
        }
    }

    // fz-ul4.27.22.16 — `uniform_cont_reachable_specs` deleted. The
    // analysis flagged conts reachable from uniform callees / Tagged-
    // unconditional writers so their entry slot 0 + schema kind would
    // be forced to Tagged/FzValue. Post-22.12, every callsite that
    // would have flagged a cont either:
    //   - resolves via closure_lit to a narrow body spec whose ABI
    //     already matches the cont's narrow slot 0 (direct dispatch);
    //   - flows through the unresolved indirect Tagged seam, which
    //     `tagged_slot0_cont_specs` (CallClosure / Receive branches)
    //     already covers.
    // Disabling the force changed only line numbers in
    // closure_typed_captures.clif (verified by experiment) — no
    // codegen content shifted. The analysis is dead.

    // fz-ul4.27.18 — per-FnId set: fns invoked from any fz IR site
    // (as a direct callee, a continuation, or a closure target).
    // A fn NOT in this set has no fz IR caller and can only enter via
    // the trampoline entry (which writes null into the frame's slot 0).
    // For such a fn, cont_ptr is statically null at runtime; emit_return
    // can specialize to a halt-only path, skipping the runtime
    // `load v0+16; icmp eq 0; brif` dispatch entirely.
    let mut ir_referenced_fns: std::collections::HashSet<crate::fz_ir::FnId> =
        std::collections::HashSet::new();
    for f in &module.fns {
        for blk in &f.blocks {
            match &blk.terminator {
                Term::Call {
                    ident: _,
                    callee,
                    continuation,
                    ..
                } => {
                    ir_referenced_fns.insert(*callee);
                    ir_referenced_fns.insert(continuation.fn_id);
                }
                Term::TailCall { callee, .. } => {
                    ir_referenced_fns.insert(*callee);
                }
                Term::CallClosure { continuation, .. } | Term::Receive { continuation, .. } => {
                    ir_referenced_fns.insert(continuation.fn_id);
                }
                _ => {}
            }
            for stmt in &blk.stmts {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeClosure(_, fid, _) = prim {
                    ir_referenced_fns.insert(*fid);
                }
            }
        }
    }
    // Rebind for the existing parameter name threading. The contained
    // fns are exactly the "never specializable as halt-only" set.
    let cont_target_fns = ir_referenced_fns;

    // Rebuild schemas: one entry per SpecId, refined entry-param kinds
    // from THAT spec's FnTypes. The any-key SpecId for FnId K lands at
    // index K (invariant) so any code path that uses fn_id.0 as a
    // schema_id continues to hit the right schema. Sentinel SpecIds
    // (missing-FnId slots) get a zero-field placeholder schema; they're
    // never reached at runtime.
    let mut schemas: Vec<Schema> = Vec::with_capacity(spec_count);
    for sid in 0..spec_count {
        let Some(idx) = spec_fnidx[sid] else {
            schemas.push(build_frame_schema("__sentinel", &[]));
            continue;
        };
        let f = &module.fns[idx];
        let ft = spec_fn_types[sid].expect("non-sentinel spec must have FnTypes");
        let entry_block = f.block(f.entry);
        let mut kinds: Vec<FieldKind> = entry_block
            .params
            .iter()
            .map(|_| FieldKind::FzValue)
            .collect();
        let any = t.concrete_any();
        for (j, p) in entry_block.params.iter().enumerate() {
            match ArgRepr::from_ty(t, &ft.vars.get(p).cloned().unwrap_or_else(|| any.clone())) {
                ArgRepr::RawF64 => kinds[j] = FieldKind::RawF64,
                ArgRepr::RawInt => kinds[j] = FieldKind::RawI64,
                _ => {}
            }
        }
        // fz-ul4.27.22.16 — uniform_cont_reachable slot-0 FzValue force
        // retired; tagged_slot0_cont_specs covers every case post-22.12.
        schemas.push(build_frame_schema(&f.name, &kinds));
    }

    // Per-spec frame sizes (consumed by `fz_alloc_frame_dyn` and the AOT
    // frame-size dispatch fn). Indexed by SpecId.0.
    let frame_sizes: Vec<u32> = schemas.iter().map(|s| s.size).collect();

    // fz-i82.2 — per-spec return Descr comes from the typer's LFP
    // (`module_types.effective_returns`). That walk filters by
    // `reachable_blocks` AND propagates through every exit terminator
    // including `Term::Call` / `Term::CallClosure` / `Term::Receive`
    // with a continuation; the cont side (`cont_slot0_descr`) already
    // reads from the same map. Reading it here too means the producer
    // abi and the cont's slot-0 abi agree by construction — the
    // mismatch that fz-i82 manifested cannot recur.
    //
    // Halt-only specs converge to `Descr::none()` in the LFP; substitute
    // `any` so `ArgRepr::from_descr` doesn't pick RawF64 (none is a
    // subtype of every set, including float). The value never reaches
    // anyone for a halt-only spec, but the abi must still be valid.
    let any = t.concrete_any();
    let none = t.none();
    let return_tys: Vec<crate::types_seam::Ty> = spec_keys
        .iter()
        .enumerate()
        .map(|(sid, (fid, key))| {
            if spec_fnidx[sid].is_none() {
                return any.clone();
            }
            let ret = module_types
                .effective_returns
                .get(&(*fid, key.clone()))
                .cloned()
                .unwrap_or_else(|| any.clone());
            let ret_ty = t.from_concrete(&ret);
            if t.is_subtype(&ret_ty, &none) {
                any.clone()
            } else {
                ret
            }
        })
        .collect();

    // fz-ul4.27.13 — Per-spec entry-param ArgReprs + return ArgRepr.
    // Drives both `build_fn_signature` (AbiParam types) and call-site
    // coerce (raw int / raw f64 vs tagged FzValue). Sentinel slots get
    // empty params + Tagged return; they're never declared.
    let param_reprs: Vec<Vec<ArgRepr>> = (0..spec_count)
        .map(|sid| match spec_fnidx[sid] {
            Some(idx) => {
                let f = &module.fns[idx];
                let reprs = build_param_reprs(
                    t,
                    f,
                    spec_fn_types[sid].expect("non-sentinel spec must have FnTypes"),
                );
                // fz-ul4.27.22.16 — uniform_cont_reachable slot-0 Tagged
                // force retired; tagged_slot0_cont_specs is sufficient.
                // fz-ul4.27.22.12 — arg-slot force at closure body retired.
                // The 22.5 capture-slot wins are preserved (CAPTURE slots
                // [0..n_caps) keep their per-spec narrow reprs). ARG slots
                // now also honor build_param_reprs' typed output: with
                // 22.10's closure_lit-typed MakeClosure and 22.11's direct
                // return_call dispatch, every closure-call site resolves
                // to a single body spec whose ABI the caller targets
                // exactly — no need to flatten arg slots to Tagged for
                // indirect-sig matching.
                //
                // The indirect fallback path in TailCallClosure still
                // assumes all-Tagged at the seam, so closures used
                // polymorphically (union of closure_lits, opaque arrow)
                // still go through the Tagged path correctly: the body's
                // narrow ABI on the direct path is compatible because
                // each direct callsite coerces explicitly.
                let _ = closure_n_captures;
                reprs
            }
            None => Vec::new(),
        })
        .collect();
    // fz-ntz (fz-3zx.2) — transitive closure of fns whose return is
    // Tagged-by-construction. Seeded with closure-target fns (forced
    // all-Tagged sig by fz-cps.1.8) and fns whose terminator on any
    // block is Term::TailCallClosure (return_call_indirect against the
    // closure-target sig forwards Tagged bits). Propagated through
    // Term::TailCall: if F tail-calls into a Tagged-returning callee,
    // F itself returns Tagged. The result drives BOTH the return_reprs
    // force (below) AND the tagged_slot0_cont_specs check (next block):
    // producer-side ABI and consumer-side schema stay aligned.
    // fz-ul4.27.22.12 — per-spec tagged-return tracking. Pre-22.12 the
    // set was keyed by FnId, conflating all specs of the same fn. With
    // closure_lit-driven per-spec resolution (22.10-22.11), one spec of
    // a fn can have a fully-resolved TailCallClosure (returning the
    // body's narrow repr) while a sibling spec's TailCallClosure stays
    // opaque (returning Tagged through the indirect seam). Per-spec is
    // the precise grain.
    //
    // Seed: spec has an UNRESOLVED TailCallClosure (or returns through
    // the all-Tagged indirect ABI). Resolved-via-closure_lit
    // TailCallClosure does not seed — it's structurally a typed
    // tail-call to the resolved body, equivalent to Term::TailCall.
    //
    // Propagation: spec's terminator chains into another spec that's
    // already tagged. Per-spec analysis uses each block's terminator
    // under this spec's env (spec_fn_types[sid]).
    let tagged_return_specs: std::collections::HashSet<u32> = {
        let mut set: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let tcc_sid = |sid: usize, closure: &crate::fz_ir::Var, args: &[crate::fz_ir::Var]| {
            let ft = spec_fn_types.get(sid).and_then(|o| *o)?;
            resolve_tcc_body(closure, args, ft, module, &spec_registry).map(|(_, s)| s)
        };
        // Seed: spec has an unresolved TailCallClosure.
        for (sid, &entry) in spec_fnidx.iter().enumerate() {
            let Some(idx) = entry else {
                continue;
            };
            let f = &module.fns[idx];
            for b in &f.blocks {
                if let Term::TailCallClosure {
                    closure,
                    args,
                    ident: _,
                } = &b.terminator
                    && tcc_sid(sid, closure, args).is_none()
                {
                    set.insert(sid as u32);
                    break;
                }
            }
        }
        // fz-try.15 — also seed: spec's body is a closure-target body.
        // Closure-target ABI is structurally uniform Tagged (the seam
        // can't carry typed returns); the body coerces at Term::Return,
        // and every spec of a closure-target fn that's reachable via
        // the closure-target sig returns Tagged on the wire. Direct
        // callers of zero-cap closure-targets (.siu.1.8 invariant) go
        // through the same body and receive Tagged too — they unbox
        // locally if they want narrow.
        for (sid, &entry) in spec_fnidx.iter().enumerate() {
            let Some(idx) = entry else {
                continue;
            };
            let fid = module.fns[idx].id;
            if closure_target_fns.contains(&fid) {
                set.insert(sid as u32);
            }
        }
        // Propagation: spec's terminator chains into a tagged spec.
        loop {
            let mut changed = false;
            for (sid, &entry) in spec_fnidx.iter().enumerate() {
                if set.contains(&(sid as u32)) {
                    continue;
                }
                let Some(idx) = entry else {
                    continue;
                };
                let f = &module.fns[idx];
                let propagates = f.blocks.iter().any(|b| match &b.terminator {
                    Term::TailCall { callee, args, .. } => {
                        // Resolve callee's spec sid under this spec's env.
                        let csid = (|| {
                            let ft = spec_fn_types.get(sid).and_then(|o| *o)?;
                            let any = t.concrete_any();
                            let arg_tys: Vec<crate::types_seam::Ty> = args
                                .iter()
                                .map(|av| ft.vars.get(av).cloned().unwrap_or_else(|| any.clone()))
                                .collect();
                            spec_registry.resolve(*callee, &arg_tys).map(|s| s.0)
                        })()
                        .unwrap_or(callee.0);
                        set.contains(&csid)
                    }
                    Term::TailCallClosure {
                        closure,
                        args,
                        ident: _,
                    } => {
                        match tcc_sid(sid, closure, args) {
                            Some(body_sid) => set.contains(&body_sid),
                            None => true, // unresolved is tagged by definition
                        }
                    }
                    Term::Call { continuation, .. }
                    | Term::CallClosure { continuation, .. }
                    | Term::Receive {
                        continuation,
                        ident: _,
                    } => {
                        // Cont's any-key spec id == continuation.fn_id.0.
                        set.contains(&continuation.fn_id.0)
                    }
                    _ => false,
                });
                if propagates {
                    set.insert(sid as u32);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        set
    };
    // Fn-id-level coarse view for legacy consumers (tagged_slot0_cont_specs
    // below queries by FnId). True iff ANY spec of the fn is tagged.
    let tagged_return_fns: std::collections::HashSet<crate::fz_ir::FnId> = {
        let mut s = std::collections::HashSet::new();
        for &sid in &tagged_return_specs {
            if let Some(idx) = spec_fnidx[sid as usize] {
                s.insert(module.fns[idx].id);
            }
        }
        s
    };

    // fz-ul4.27.22.3 — cont specs whose producer is a closure-target
    // (or whose producer is a Receive / CallClosure with unknown
    // target) must accept Tagged at slot 0. The producer returns
    // Tagged (forced for closure-target; opaque for unknown closure /
    // mailbox), and the cont's wire sig at the seam must agree.
    // fz-ntz extends "closure-target" to "Tagged-returning"
    // (`tagged_return_fns`) so direct-Calls into a Tagged-returning
    // fn also force the cont's slot 0 to FzValue.
    let mut tagged_slot0_cont_specs: std::collections::HashSet<u32> =
        std::collections::HashSet::new();
    // fz-uwq.8 — read the producer→cont dispatch facts from
    // `FnTypes.dispatches[Cont]` instead of re-walking terminators and
    // calling `cont_input_key` + `spec_registry.resolve`. The typer
    // already named which `(cont_fn, cont_key)` each Cont site
    // dispatches to (per spec); we just need to know which of those
    // producers are Tagged-returning, then look up the cont's SpecId.
    for sid_caller in 0..spec_count {
        let Some(caller_idx) = spec_fnidx[sid_caller] else {
            continue;
        };
        let caller = &module.fns[caller_idx];
        // Sentinel slots (closure-target floor with no typer body)
        // have no dispatches.
        let Some(caller_ft) = spec_fn_types[sid_caller] else {
            continue;
        };
        for blk in &caller.blocks {
            // Which terminators produce a Tagged value into their cont's
            // slot 0? CallClosure / Receive always (opaque closure /
            // mailbox produce Tagged); Call only when the callee is in
            // `tagged_return_fns` (fz-ntz).
            let Some(term_ident) = blk.terminator.ident() else {
                continue;
            };
            let produces_tagged_slot0 = match &blk.terminator {
                Term::Call { callee, .. } => tagged_return_fns.contains(callee),
                Term::CallClosure { .. } | Term::Receive { .. } => true,
                _ => false,
            };
            if !produces_tagged_slot0 {
                continue;
            }
            let cid = crate::fz_ir::CallsiteId {
                caller: caller.id,
                ident: term_ident.clone(),
                slot: crate::fz_ir::EmitSlot::Cont,
            };
            if let Some((cont_fn, cont_key)) = caller_ft.dispatches.get(&cid)
                && let Some(sid) = spec_registry.resolve(*cont_fn, cont_key)
            {
                tagged_slot0_cont_specs.insert(sid.0);
            }
        }
    }
    let param_reprs: Vec<Vec<ArgRepr>> = param_reprs
        .into_iter()
        .enumerate()
        .map(|(sid, mut reprs)| {
            if !reprs.is_empty() && tagged_slot0_cont_specs.contains(&(sid as u32)) {
                reprs[0] = ArgRepr::Tagged;
            }
            reprs
        })
        .collect();
    let return_reprs: Vec<ArgRepr> = return_tys
        .iter()
        .map(|ty| ArgRepr::from_ty(t, ty))
        .collect();
    // fz-cps.1.8 — closure-target spec bodies return Tagged i64, matching
    // the closure-target sig in §8.2's target clif. fz-ntz extends this
    // to every fn in `tagged_return_fns`: a fn whose only exit is
    // Term::TailCallClosure (or which TailCalls into one) forwards the
    // closure-target's Tagged return bits through its own outer sig.
    // Declaring that outer return as RawInt/RawF64 would let the
    // caller read tag-shifted bits as a raw number (e.g. 42 → 337).
    let return_reprs: Vec<ArgRepr> = return_reprs
        .into_iter()
        .enumerate()
        .map(|(sid, r)| {
            // fz-ul4.27.22.12 — per-spec override (was per-fn pre-22.12).
            // tagged_return_specs is the precise grain; specs whose
            // TailCallClosure resolves via closure_lit keep their narrow
            // return repr.
            if tagged_return_specs.contains(&(sid as u32)) {
                ArgRepr::Tagged
            } else {
                r
            }
        })
        .collect();

    // fz-70q.5.5 — collect per-cont-fn bound_arity (clause body / guard
    // / after) BEFORE fn_sigs so build_fn_signature can size the sig's
    // typed extras correctly. Same walk we'll later repeat in the
    // matcher pre-pass; cheap to duplicate, and putting it here keeps
    // the sig construction order-independent of the matcher decl.
    let mut cont_extras_count: HashMap<crate::fz_ir::FnId, usize> = HashMap::new();
    for f in &module.fns {
        for blk in &f.blocks {
            let Term::ReceiveMatched { clauses, after, .. } = &blk.terminator else {
                continue;
            };
            for c in clauses {
                let n = c.bound_names.len();
                cont_extras_count.insert(c.body, n);
                if let Some(g) = c.guard {
                    cont_extras_count.insert(g, n);
                }
            }
            if let Some(a) = after {
                cont_extras_count.insert(a.body, 0);
            }
        }
    }

    // fz-ul4.27.6.2.2/.3 — Per-spec Cranelift Signature. Native fns get
    // typed-arity i64s + host_ctx; uniform fns get (i64, i64) -> i64.
    // Sentinel slots get the uniform sig — they're never declared.
    let fn_sigs: Vec<Signature> = (0..spec_count)
        .map(|sid| match spec_fnidx[sid] {
            Some(idx) => {
                let f = &module.fns[idx];
                let is_native = natively_callable.contains(&f.id);
                build_fn_signature(
                    &param_reprs[sid],
                    return_reprs[sid],
                    is_native,
                    cont_fns.contains(&f.id),
                    // fz-cps.1.2: closure-target fn shape gated on
                    // native (uniform closure targets still go through
                    // the existing stub adapter).
                    if is_native {
                        closure_n_captures.get(&f.id).copied()
                    } else {
                        None
                    },
                    cont_extras_count.get(&f.id).copied(),
                )
            }
            None => {
                let mut sig = Signature::new(CallConv::SystemV);
                sig.params.push(AbiParam::new(types::I64));
                sig.params.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
                sig
            }
        })
        .collect();

    // Declare one Cranelift function per real SpecId, named
    // `fz_fn_{spec_id.0}`. Sentinel slots are skipped — no module
    // declaration is made. Any-key SpecId.0 == FnId.0 so the existing
    // closure / Spawn / Receive paths (which iconst fn_id.0 as the
    // schema_id) keep landing on the right entry.
    let linkage = backend.fn_linkage();
    let mut fn_ids: HashMap<u32, FuncId> = HashMap::new();
    for sid in 0..spec_count {
        if spec_fnidx[sid].is_none() {
            continue;
        }
        let name = format!("fz_fn_{}", sid);
        let id = backend
            .module_mut()
            .declare_function(&name, linkage, &fn_sigs[sid])
            .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))?;
        fn_ids.insert(sid as u32, id);
    }

    // fz-q8d.2 — per-module ConstBitstring symbol cache. Same byte payload
    // across the whole module shares one set of symbols:
    //   * `bytes_id`: the raw payload (Local, read-only).
    //   * `sharedbin_id`: present only for above-threshold payloads — a
    //     40-byte static SharedBin in `.data` with refcount=1 anchor, plus
    //     two relocations (bytes_ptr and the noop destructor). Below-
    //     threshold payloads have `None` here and continue to flow through
    //     `fz_alloc_bitstring_const` for inline / runtime-decided storage.
    let bs_const_data: std::cell::RefCell<HashMap<Vec<u8>, BsConstSyms>> =
        std::cell::RefCell::new(HashMap::new());

    // fz-ul4.42 — set of SpecIds reachable from main + closure-dispatched
    // fns. Specs not in this set get a trap-stub body instead of full
    // codegen. Closure-target specs (those in `closure_shapes`) are seeded
    // explicitly because runtime closure dispatch through `stub_fp` isn't
    // visible to the IR-body BFS. See ir_typer::reachable_specs.
    let reachable: std::collections::HashSet<u32> = crate::ir_typer::reachable_specs(
        t,
        module,
        &spec_registry,
        &module_types,
        closure_shapes.keys().copied(),
    );

    // fz-70q.3 — pre-pass over Term::ReceiveMatched sites.
    //
    //   * `matcher_fn_ids`: one matcher FuncId per site, keyed by
    //     `(fn_id.0, block_id.0)`. Declared up front so the park-site
    //     terminator arm can take a `func_addr` of an as-yet-unemitted
    //     symbol; the body is emitted in a post-fn-loop pass below.
    //   * `cont_extras_count`: per-clause-body / guard / after-body fn
    //     extras count consumed by build_entry_harness today (Tail-CC
    //     inputs ahead of `self`).
    //
    // (`cont_extras_count` is now built up-front above, before fn_sigs.)
    let mut matcher_fn_ids: HashMap<(u32, u32), FuncId> = HashMap::new();
    let mut receive_matched_sites: Vec<(crate::fz_ir::FnId, crate::fz_ir::BlockId)> = Vec::new();
    for f in &module.fns {
        for blk in &f.blocks {
            if !matches!(&blk.terminator, Term::ReceiveMatched { .. }) {
                continue;
            }
            let name = format!("fz_matcher_fn_{}_b{}", f.id.0, blk.id.0);
            let m_id = crate::ir_codegen_receive::declare_matcher(backend.module_mut(), &name)?;
            matcher_fn_ids.insert((f.id.0, blk.id.0), m_id);
            receive_matched_sites.push((f.id, blk.id));
        }
    }

    // fz-70q.5.4 — declare one cont stub per body spec used by any
    // ReceiveMatched site. The stub bridges the scheduler's SystemV
    // resume seam into the body fn's uniform `(frame, host_ctx) -> i64
    // systemv` entry. See ir_codegen_cont_stub for the body shape.
    //
    // Resolution must mirror the park-site's `resolve_body_sid` exactly
    // — same key construction (`[any; bound_arity] ++ cap_descrs`),
    // same spec_registry lookup — so the FuncId stored at closure+16
    // at park-site emission time agrees with what got emitted. Cap
    // descrs depend on the ENCLOSING caller's per-spec FnTypes, so we
    // iterate every (caller_fn × caller_spec × matched_block × clause)
    // tuple and dedup by body spec.
    //
    // Stub body emission (which needs spec frame_sizes / schema_ids) is
    // a post-fn-loop pass, alongside matcher body emission. We capture
    // (body_fid, body_spec_id, n_captures, bound_arity) here so the
    // post pass can read them back without re-resolving.
    struct ContStubDecl {
        stub_id: FuncId,
        body_spec_id: u32,
        bound_arity: u16,
    }
    let mut cont_stub_ids: HashMap<u32 /*body_spec_id*/, FuncId> = HashMap::new();
    let mut cont_stub_decls: Vec<ContStubDecl> = Vec::new();
    for (caller_fid, blk_id) in &receive_matched_sites {
        let caller_f = module.fn_by_id(*caller_fid);
        let caller_idx = module
            .fn_idx
            .get(caller_fid)
            .copied()
            .expect("caller fn missing from fn_idx");
        // Every spec of the caller may resolve to a different body spec
        // (per-capture-type narrowing). Walk them all.
        let blk = caller_f
            .blocks
            .iter()
            .find(|b| b.id == *blk_id)
            .expect("matched block missing");
        let Term::ReceiveMatched {
            clauses,
            after,
            captures,
            ..
        } = &blk.terminator
        else {
            unreachable!()
        };
        for caller_sid in 0..spec_count {
            // Skip specs that don't belong to this caller fn.
            if spec_fnidx[caller_sid] != Some(caller_idx) {
                continue;
            }
            let Some(caller_ft) = spec_fn_types[caller_sid] else {
                continue;
            };
            let any = t.concrete_any();
            let cap_tys: Vec<crate::types_seam::Ty> = captures
                .iter()
                .map(|cv| {
                    caller_ft
                        .vars
                        .get(cv)
                        .cloned()
                        .unwrap_or_else(|| any.clone())
                })
                .collect();
            let mut resolve = |body: crate::fz_ir::FnId, bound_arity: usize| {
                let body_fn = module.fn_by_id(body);
                let np = body_fn.block(body_fn.entry).params.len();
                let mut key: Vec<crate::types_seam::Ty> = vec![any.clone(); bound_arity];
                key.extend(cap_tys.iter().cloned());
                while key.len() < np {
                    key.push(any.clone());
                }
                key.truncate(np);
                let Some(body_spec_id) = spec_registry.resolve(body, &key).map(|sid| sid.0) else {
                    return;
                };
                if let std::collections::hash_map::Entry::Vacant(e) =
                    cont_stub_ids.entry(body_spec_id)
                {
                    let name = format!("fz_cont_stub_{}", body_spec_id);
                    let stub_id =
                        crate::ir_codegen_cont_stub::declare_cont_stub(backend.module_mut(), &name)
                            .map_err(CodegenError::new);
                    // Propagate decl errors up; using a small helper to
                    // bubble through the closure boundary cleanly.
                    let stub_id = stub_id.expect("cont stub decl");
                    e.insert(stub_id);
                    cont_stub_decls.push(ContStubDecl {
                        stub_id,
                        body_spec_id,
                        bound_arity: bound_arity as u16,
                    });
                }
            };
            for c in clauses {
                resolve(c.body, c.bound_names.len());
                if let Some(g) = c.guard {
                    resolve(g, c.bound_names.len());
                }
            }
            if let Some(a) = after {
                resolve(a.body, 0);
            }
        }
    }

    for sid in 0..spec_count {
        let Some(idx) = spec_fnidx[sid] else {
            continue;
        };
        let func_id = *fn_ids.get(&(sid as u32)).unwrap();
        let mut ctx = backend.module_mut().make_context();
        ctx.func.signature = fn_sigs[sid].clone();

        // fz-ul4.42 — unreached spec: emit a trap stub so the symbol exists
        // (other emitted code may name it via fz_fn_{sid}) but the body is
        // a single unreachable trap. Skip the @spec header annotation,
        // verifier, and any further per-spec analysis.
        if !reachable.contains(&(sid as u32)) {
            use cranelift_codegen::ir::TrapCode;
            use cranelift_frontend::FunctionBuilder;
            {
                let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                b.seal_block(entry);
                b.ins().trap(TrapCode::user(1).unwrap());
                b.finalize();
            }
            backend
                .module_mut()
                .define_function(func_id, &mut ctx)
                .map_err(|e| CodegenError::new(format!("define unreached fz_fn_{}: {}", sid, e)))?;
            backend.module_mut().clear_context(&mut ctx);
            continue;
        }
        let ft = spec_fn_types[sid].expect("non-sentinel spec must have FnTypes");
        // fz-ul4.43.B — per-spec fold. Clone the FnIr and fold against this
        // spec's FnTypes so dead arms (TypeTests whose subject is provably
        // inside/outside the test descr in THIS spec's env) collapse before
        // codegen. The pre-codegen `fold_module` already folds the any-key
        // case; this is the multi-spec case it bails on.
        let f_owned: crate::fz_ir::FnIr = {
            let mut clone = module.fns[idx].clone();
            crate::ir_fold::fold_fn_with_types(t, &mut clone, ft);
            // fz-ul4.43.D.1 — per-spec DCE + fuse after per-spec fold.
            // Fold rewrites Term::If→Goto when cond folds; DCE removes the
            // dead stmts and unreachable blocks; fuse_fn collapses the
            // remaining Goto-chains so inline_tail_calls_once's
            // is_pure_tail_caller predicate (single-block + TailCall) can
            // see these tiny per-spec bodies as inlinable.
            crate::ir_dce::dce_fn(&mut clone);
            crate::ir_fuse::fuse_fn(&mut clone);
            clone
        };
        let f = &f_owned;

        let want_asm = ASM_RECORD.with(|c| c.borrow().is_some());
        if want_asm {
            ctx.set_disasm(true);
        }
        let cg_env = CodegenEnv {
            runtime: &runtime,
            module,
            fn_types: ft,
            spec_registry: &spec_registry,
            fn_ids: &fn_ids,
            tuple_schema_ids: &tuple_schema_ids,
            bs_const_data: &bs_const_data,
            param_reprs: &param_reprs,
            return_reprs: &return_reprs,
            natively_callable: &natively_callable,
            cont_target_fns: &cont_target_fns,
            cont_fns: &cont_fns,
            closure_n_captures: &closure_n_captures,
            cont_extras_count: &cont_extras_count,
            matcher_fn_ids: &matcher_fn_ids,
            cont_stub_ids: &cont_stub_ids,
        };
        compile_fn(
            backend.module_mut(),
            &mut ctx,
            &mut fbctx,
            &cg_env,
            &schemas,
            f,
            sid as u32,
            &module.source,
        )?;
        // Any-key SpecId.0 == FnId.0 (invariant); use the bare fn name so
        // tests / `fz dump --emit clif` can refer to functions by source
        // name. Narrow specs append `_s{sid}` to keep names distinct.
        let display_name = if (sid as u32) == f.id.0 {
            f.name.clone()
        } else {
            format!("{}_s{}", f.name, sid)
        };
        // fz-ul4.32.1 — annotate raw CLIF with IR Descrs + ArgReprs so
        // golden_clif / `fz dump --emit clif` show what the typer
        // decided, not just what was lowered.
        IR_TEXT_RECORD.with(|c| {
            if let Some(v) = c.borrow_mut().as_mut() {
                // fz-323 — pin func.name to the real FuncId so the banner
                // `function u0:N(...)` carries the same id space as body
                // refs; cranelift_module's define_function does this
                // assignment anyway, we just need it before display().
                ctx.func.name = ir::UserFuncName::user(0, func_id.as_u32());
                let raw = ctx.func.display().to_string();
                let header = build_typer_header(
                    t,
                    f,
                    ft,
                    &spec_keys[sid].1,
                    &return_tys[sid],
                    &param_reprs[sid],
                    return_reprs[sid],
                );
                let func_names = snapshot_func_names(backend.module_mut().declarations());
                let annotated = VALUE_DESCR_RECORD.with(|vd| {
                    let b = vd.borrow();
                    match b.as_ref() {
                        Some(map) => annotate_clif_dump(&raw, map, &func_names, &header),
                        None => {
                            let empty = HashMap::new();
                            annotate_clif_dump(&raw, &empty, &func_names, &header)
                        }
                    }
                });
                v.push((display_name.clone(), annotated));
            }
        });
        let fn_span = module.source.fn_span_of(f.id);
        let flags = settings::Flags::new(settings::builder());
        cranelift_codegen::verifier::verify_function(&ctx.func, &flags).map_err(|e| {
            CodegenError::new(format!(
                "verify {}:\n{}\n--- IR ---\n{}",
                display_name,
                e,
                ctx.func.display()
            ))
            .with_span(fn_span)
        })?;
        backend
            .module_mut()
            .define_function(func_id, &mut ctx)
            .map_err(|e| {
                CodegenError::new(format!("define {}: {}", display_name, e)).with_span(fn_span)
            })?;
        if want_asm
            && let Some(cc) = ctx.compiled_code()
            && let Some(vcode) = cc.vcode.as_ref()
        {
            ASM_RECORD.with(|c| {
                if let Some(v) = c.borrow_mut().as_mut() {
                    v.push((display_name.clone(), vcode.clone()));
                }
            });
        }
        backend.module_mut().clear_context(&mut ctx);
    }

    // fz-cps.1.8 — stub compilation loop deleted alongside stub
    // registration. compile_closure_stub itself is dead code until
    // fz-siu.1.13 cleanup; left in place to avoid a noisy delete in this
    // commit.

    // fz-70q.3 — emit matcher fn bodies for every Term::ReceiveMatched
    // site discovered in the pre-pass above. Matchers were declared
    // before the fn-compilation loop so the park-site terminator arm
    // could take `func_addr` of the still-undefined symbols. Bodies are
    // pure leaf fns (no allocation, no extern) per F3; the emitter
    // refuses any clause with a guard.is_some() and points at fz-70q.2.2.
    for (fn_id, blk_id) in &receive_matched_sites {
        let f = module.fn_by_id(*fn_id);
        let blk = f.blocks.iter().find(|b| b.id == *blk_id).unwrap();
        let Term::ReceiveMatched {
            clauses, pinned, ..
        } = &blk.terminator
        else {
            unreachable!("receive_matched_sites holds only Term::ReceiveMatched terms");
        };
        let m_id = matcher_fn_ids[&(fn_id.0, blk_id.0)];
        crate::ir_codegen_receive::emit_matcher_body(
            backend.module_mut(),
            &mut fbctx,
            m_id,
            module,
            &tuple_schema_ids,
            pinned.as_slice(),
            clauses.as_slice(),
        )?;
    }

    // fz-70q.5.4 — emit cont-stub bodies for each (body_spec_id) we
    // declared in the pre-pass. Each stub does a SystemV → Tail-CC
    // bridge: read N bound args from process->resume_args via
    // fz_resume_args_ptr, then call body Tail-CC `(args..., self)`.
    // Captures stay inside the closure (loaded by body's entry harness
    // from self+32+i*8), so we don't forward them as Cranelift params.
    let cont_stub_rt = crate::ir_codegen_cont_stub::ContStubRuntimeRefs {
        resume_args_ptr_id: runtime.resume_args_ptr_id,
    };
    for decl in &cont_stub_decls {
        let body_fid = *fn_ids
            .get(&decl.body_spec_id)
            .expect("cont stub body spec must have a FuncId");
        crate::ir_codegen_cont_stub::emit_cont_stub_body(
            backend.module_mut(),
            &mut fbctx,
            decl.stub_id,
            crate::ir_codegen_cont_stub::ContStubLayout {
                bound_arity: decl.bound_arity,
            },
            cont_stub_rt,
            |m, b| {
                let body_fref = m.declare_func_in_func(body_fid, b.func);
                b.ins().func_addr(types::I64, body_fref)
            },
        )
        .map_err(CodegenError::new)?;
    }

    let main_fn_id = module.fn_by_name("main").map(|f| f.id);

    // fz-cps.1.7 — collect zero-capture closure-target specs for static
    // singletons. fz-cps.1.8 — code_ptr is the body's func_addr directly
    // (closure-target sig `(args, self, cont) tail`), not a SystemV stub.
    // The singleton acts both as `self` for direct callers (zero-cap
    // bodies ignore self) and as the closure handed to MakeClosure(fid,
    // []) sites. See docs/cps-in-clif.md §8.2.
    let static_closure_targets: Vec<(u32, u32, FuncId, u32)> = closure_shapes
        .iter()
        .filter(|(_, n_caps)| **n_caps == 0)
        .map(|(cl_sid, _)| {
            let fn_id = spec_keys[*cl_sid as usize].0;
            let body_fid = *fn_ids
                .get(cl_sid)
                .expect("zero-cap closure spec must have a body FuncId");
            // fz-ul4.27.22.6: pack halt_kind so fz_spawn_entry can pick
            // the matching halt-cont singleton at task launch.
            let halt_kind = return_reprs[*cl_sid as usize].halt_kind();
            (*cl_sid, fn_id.0, body_fid, halt_kind)
        })
        .collect();

    let diagnostics = crate::ir_typer::collect_diagnostics(t, module, &module_types);
    // fz-ul4.27.22.3 — per-spec chain analysis: for each registered
    // spec, walk its exit terminators and follow callee resolutions
    // transitively. The chain's halt-seam kind = JOIN of every Return
    // contributing along reachable paths.
    let chain_repr: Vec<ArgRepr> = {
        let join = |a: ArgRepr, b: ArgRepr| -> ArgRepr { if a == b { a } else { ArgRepr::Tagged } };
        let mut chain: Vec<Option<ArgRepr>> = vec![None; spec_count];
        let mut resolve_sid_under =
            |callee_id: FnId, caller_sid: u32, args: &[crate::fz_ir::Var]| -> Option<u32> {
                let any_sid = caller_sid as usize;
                let ft = spec_fn_types.get(any_sid).and_then(|o| *o)?;
                let any = t.concrete_any();
                let arg_tys: Vec<crate::types_seam::Ty> = args
                    .iter()
                    .map(|av| ft.vars.get(av).cloned().unwrap_or_else(|| any.clone()))
                    .collect();
                spec_registry.resolve(callee_id, &arg_tys).map(|s| s.0)
            };
        for _ in 0..(spec_count * 4 + 16) {
            let mut changed = false;
            for sid in 0..spec_count {
                let Some(idx) = spec_fnidx[sid] else {
                    continue;
                };
                let f = &module.fns[idx];
                let mut contributions: Vec<ArgRepr> = Vec::new();
                for blk in &f.blocks {
                    match &blk.terminator {
                        Term::Return(_) => {
                            contributions.push(return_reprs[sid]);
                        }
                        Term::TailCall { callee, args, .. } => {
                            let csid =
                                resolve_sid_under(*callee, sid as u32, args).unwrap_or(callee.0);
                            if let Some(c) = chain.get(csid as usize).and_then(|o| *o) {
                                contributions.push(c);
                            }
                        }
                        Term::Call { continuation, .. }
                        | Term::CallClosure { continuation, .. }
                        | Term::Receive {
                            continuation,
                            ident: _,
                        } => {
                            // Cont's chain: under the caller's per-spec
                            // env, the cont's resolved sid via the typer's
                            // cont_input_key (already done elsewhere) —
                            // here we use the cont's any-key as a sound
                            // over-approximation. JOIN refines later.
                            let cont_sid = continuation.fn_id.0;
                            if let Some(c) = chain.get(cont_sid as usize).and_then(|o| *o) {
                                contributions.push(c);
                            }
                        }
                        Term::TailCallClosure {
                            closure,
                            args,
                            ident: _,
                        } => {
                            // fz-ul4.27.22.12 — closure_lit-driven chain
                            // resolution. When this spec's env types the
                            // closure as `closure_lit(F, K)`, the resolved
                            // body's chain feeds ours. Mirrors 22.11's
                            // direct-dispatch resolution but at the
                            // pre-codegen analysis stage so halt_kind
                            // selection (fz_spawn_entry, halt-cont
                            // singletons) picks the right kind.
                            let resolved_body =
                                spec_fn_types.get(sid).and_then(|o| *o).and_then(|ft| {
                                    resolve_tcc_body(closure, args, ft, module, &spec_registry)
                                        .map(|(_, s)| s)
                                });
                            match resolved_body {
                                Some(body_sid) => {
                                    if let Some(c) = chain.get(body_sid as usize).and_then(|o| *o) {
                                        contributions.push(c);
                                    }
                                }
                                None => {
                                    // Indirect dispatch via cl+16 uses the
                                    // all-Tagged seam ABI, so anything
                                    // returning through it is Tagged.
                                    contributions.push(ArgRepr::Tagged);
                                }
                            }
                        }
                        _ => {}
                    }
                }
                if contributions.is_empty() {
                    continue;
                }
                let joined = contributions.into_iter().reduce(join).unwrap();
                if chain[sid] != Some(joined) {
                    chain[sid] = Some(joined);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        chain
            .into_iter()
            .map(|o| o.unwrap_or(ArgRepr::Tagged))
            .collect()
    };
    let fn_halt_kinds: HashMap<u32, u32> = {
        let mut m: HashMap<u32, u32> = HashMap::new();
        for f in &module.fns {
            // Use the fn's any-key spec sid for the entry-time chain.
            let sid = f.id.0 as usize;
            if let Some(r) = chain_repr.get(sid).copied() {
                m.insert(f.id.0, r.halt_kind());
            }
        }
        m
    };
    // fz-02r.5 — generate 9 mid-flight resume shims (one per arg count 0..=8).
    // Each shim is SystemV `(fn_ptr: i64) -> i64` and calls the target fn
    // via Tail-CC indirect with N args loaded from current_process.mid_flight_roots.
    let mid_flight_resume_ids: [FuncId; 9] = {
        let mut ids = [runtime.mid_flight_roots_ptr_id; 9]; // placeholder; overwritten below
        for (n, id_slot) in ids.iter_mut().enumerate() {
            let shim_name = format!("fz_mid_flight_resume_{}", n);
            let mut shim_sig = Signature::new(CallConv::SystemV);
            shim_sig.params.push(AbiParam::new(types::I64)); // fn_ptr
            shim_sig.returns.push(AbiParam::new(types::I64)); // result
            let shim_id = backend
                .module_mut()
                .declare_function(&shim_name, Linkage::Local, &shim_sig)
                .map_err(|e| CodegenError::new(format!("declare {}: {}", shim_name, e)))?;
            *id_slot = shim_id;
            let roots_ptr_id = runtime.mid_flight_roots_ptr_id;
            emit_fn_body(
                backend.module_mut(),
                &mut fbctx,
                shim_sig,
                shim_id,
                move |m, b| {
                    let entry = b.create_block();
                    b.append_block_params_for_function_params(entry);
                    b.switch_to_block(entry);
                    b.seal_block(entry);
                    let fn_ptr = b.block_params(entry)[0];
                    // Get the current process's mid_flight_roots slab ptr.
                    let roots_fref = m.declare_func_in_func(roots_ptr_id, b.func);
                    let roots_call = b.ins().call(roots_fref, &[]);
                    let roots_ptr_val = b.inst_results(roots_call)[0];
                    // Load n args from the slab.
                    let mut args: Vec<ir::Value> = Vec::with_capacity(n);
                    for i in 0..n {
                        let v = b.ins().load(
                            types::I64,
                            MemFlags::trusted(),
                            roots_ptr_val,
                            (i * 8) as i32,
                        );
                        args.push(v);
                    }
                    // Build Tail-CC sig with n i64 params.
                    let mut tail_sig = Signature::new(CallConv::Tail);
                    for _ in 0..n {
                        tail_sig.params.push(AbiParam::new(types::I64));
                    }
                    tail_sig.returns.push(AbiParam::new(types::I64));
                    let sig_ref = b.func.import_signature(tail_sig);
                    let call_inst = b.ins().call_indirect(sig_ref, fn_ptr, &args);
                    let result = b.inst_results(call_inst)[0];
                    b.ins().return_(&[result]);
                },
            )
            .map_err(|e| CodegenError::new(format!("define {}: {}", shim_name, e)))?;
        }
        ids
    };
    // fz-70q (B3 step A+B) — generate 9 selective-receive resume shims
    // (one per clause bound-arg count 0..=8). Each shim is SystemV
    // fz-70q.5.5 — single SystemV `fz_resume(cont) -> i64` shim. Replaces
    // the nine `fz_resume_matched_N` siblings. Bound args travel via the
    // runtime `resume_args` slab (written by the trampoline before
    // dispatch), not through register passing — so the shim sig is fixed
    // regardless of clause arity. Body:
    //     load cont+16    ; cont stub addr (SystemV)
    //     call_indirect SystemV(cont) -> i64
    //     return result
    // The cont stub itself (ir_codegen_cont_stub) reads resume_args via
    // fz_resume_args_ptr inside its body. Legacy Term::Receive still
    // uses fz_resume_park (Tail-CC into the cont body); migrating it to
    // share this seam is a follow-up once Receive cont bodies switch to
    // cont stubs too.
    let resume_id: FuncId = {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64)); // cont
        sig.returns.push(AbiParam::new(types::I64));
        let id = backend
            .module_mut()
            .declare_function("fz_resume", Linkage::Local, &sig)
            .map_err(|e| CodegenError::new(format!("declare fz_resume: {}", e)))?;
        emit_fn_body(backend.module_mut(), &mut fbctx, sig, id, |_m, b| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let cont = b.block_params(entry)[0];
            let code = b
                .ins()
                .load(types::I64, MemFlags::trusted(), cont, HEADER_SIZE);
            let mut stub_sig = Signature::new(CallConv::SystemV);
            stub_sig.params.push(AbiParam::new(types::I64)); // self
            stub_sig.returns.push(AbiParam::new(types::I64));
            let sig_ref = b.func.import_signature(stub_sig);
            let inst = b.ins().call_indirect(sig_ref, code, &[cont]);
            let r = b.inst_results(inst)[0];
            b.ins().return_(&[r]);
        })
        .map_err(|e| CodegenError::new(format!("define fz_resume: {}", e)))?;
        id
    };

    let metadata = CompiledMetadata {
        fn_ids,
        user_schemas,
        frame_sizes,
        atom_names: module.atom_names.clone(),
        bs_tuple_arity1_schema,
        bs_tuple_arity3_schema,
        tuple_arities: tuple_arities.iter().map(|&a| a as u32).collect(),
        diagnostics,
        main_fn_id,
        static_closure_targets,
        resume_park_id: runtime.resume_park_id,
        spawn_entry_id: runtime.spawn_entry_id,
        main_entry_id: runtime.main_entry_id,
        drain_dtor_entry_id: runtime.drain_dtor_entry_id,
        halt_cont_body_ids: [
            runtime.halt_cont_body_tagged_id,
            runtime.halt_cont_body_i64_id,
            runtime.halt_cont_body_f64_id,
        ],
        fn_halt_kinds,
        mid_flight_resume_ids,
        resume_id,
    };

    // Backend-specific metadata carriers (no-op for JIT; dispatch + main
    // shim + atom blob for AOT) emit before finalize so any data /
    // function declarations land in the same Module that finalize hands
    // off.
    backend.emit_metadata_carriers(&mut fbctx, &metadata)?;
    backend.finalize(metadata)
}

pub fn compile<T: crate::types_seam::Types<Ty = crate::types_seam::Ty>>(
    t: &mut T,
    module: &Module,
) -> Result<CompiledModule, CodegenError> {
    compile_with_backend(t, module, JitBackend::new())
}

pub fn compile_aot<T: crate::types_seam::Types<Ty = crate::types_seam::Ty>>(
    t: &mut T,
    module: &Module,
    obj_name: &str,
) -> Result<AotArtifact, CodegenError> {
    compile_with_backend(t, module, AotBackend::new(obj_name))
}

/// Emit the AOT C-callable main entry (fz-siu.6.1). Drives the cps-in-clif
/// startup: `fz_aot_setup` → per-closure `fz_aot_register_static_closure`
/// → `fz_aot_run_main`. The shim addresses (fz_main_entry,
/// fz_halt_cont_body) are taken via Cranelift `func_addr` against the
/// Local symbols emitted by compile_with_backend.
#[allow(clippy::too_many_arguments)]
fn emit_aot_c_main<M: cranelift_module::Module>(
    jmod: &mut M,
    fbctx: &mut FunctionBuilderContext,
    c_main_id: FuncId,
    c_main_sig: &Signature,
    main_fz_func_id: FuncId,
    main_entry_id: FuncId,
    halt_cont_body_ids: [FuncId; 3],
    spawn_entry_id: FuncId,
    resume_park_id: FuncId,
    static_closure_targets: &[(u32, u32, FuncId, u32 /* halt_kind */)],
    atom_blob_data: Option<DataId>,
    atom_blob_len: u32,
    setup_id: FuncId,
    reg_id: FuncId,
    run_id: FuncId,
    mid_flight_resume_ids: &[FuncId; 9],
    set_shims_id: FuncId,
    reg_tuples_id: FuncId,
    tuple_arities_data: Option<DataId>,
    tuple_arities_len: u32,
    set_drain_id: FuncId,
    drain_dtor_entry_id: FuncId,
    set_resume_id: FuncId,
    resume_id: FuncId,
) -> Result<(), CodegenError> {
    use cranelift_frontend::FunctionBuilder;

    let mut ctx = jmod.make_context();
    ctx.func.signature = c_main_sig.clone();
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);

        // Atom blob: symbol address + byte length.
        let atom_blob_addr = match atom_blob_data {
            Some(data_id) => {
                let gv = jmod.declare_data_in_func(data_id, b.func);
                b.ins().symbol_value(types::I64, gv)
            }
            None => b.ins().iconst(types::I64, 0),
        };
        let atom_blob_len_v = b.ins().iconst(types::I32, atom_blob_len as i64);

        // Shim addresses (Local symbols in this object).
        let hcb_tagged_addr = fn_addr(jmod, halt_cont_body_ids[0], &mut b);
        let hcb_i64_addr = fn_addr(jmod, halt_cont_body_ids[1], &mut b);
        let hcb_f64_addr = fn_addr(jmod, halt_cont_body_ids[2], &mut b);
        let me_addr = fn_addr(jmod, main_entry_id, &mut b);
        let se_addr = fn_addr(jmod, spawn_entry_id, &mut b);
        let rp_addr = fn_addr(jmod, resume_park_id, &mut b);
        let main_fp = fn_addr(jmod, main_fz_func_id, &mut b);

        // proc = fz_aot_setup(atom_blob, atom_blob_len,
        //                     hcb_tagged, hcb_i64, hcb_f64,
        //                     se_addr, rp_addr)
        let setup_fref = jmod.declare_func_in_func(setup_id, b.func);
        let setup_call = b.ins().call(
            setup_fref,
            &[
                atom_blob_addr,
                atom_blob_len_v,
                hcb_tagged_addr,
                hcb_i64_addr,
                hcb_f64_addr,
                se_addr,
                rp_addr,
            ],
        );
        let proc_v = b.inst_results(setup_call)[0];

        // fz-ul4.38 — register tuple schemas before any code that might
        // allocate one (static closures use AllocStruct, not MakeTuple, but
        // the order keeps schema setup adjacent to process setup).
        {
            let tuple_arities_addr = match tuple_arities_data {
                Some(data_id) => {
                    let gv = jmod.declare_data_in_func(data_id, b.func);
                    b.ins().symbol_value(types::I64, gv)
                }
                None => b.ins().iconst(types::I64, 0),
            };
            let tuple_arities_len_v = b.ins().iconst(types::I32, tuple_arities_len as i64);
            let reg_tuples_fref = jmod.declare_func_in_func(reg_tuples_id, b.func);
            b.ins().call(
                reg_tuples_fref,
                &[proc_v, tuple_arities_addr, tuple_arities_len_v],
            );
        }

        // Register each static closure target.
        for (cl_sid, fn_id, body_func_id, halt_kind) in static_closure_targets {
            let cl_sid_v = b.ins().iconst(types::I32, *cl_sid as i64);
            let fn_id_v = b.ins().iconst(types::I32, *fn_id as i64);
            let body_addr = fn_addr(jmod, *body_func_id, &mut b);
            let hk_v = b.ins().iconst(types::I32, *halt_kind as i64);
            let reg_fref = jmod.declare_func_in_func(reg_id, b.func);
            b.ins()
                .call(reg_fref, &[proc_v, cl_sid_v, fn_id_v, body_addr, hk_v]);
        }

        // fz-02r.7 — register mid-flight resume shims. Build a 9-pointer
        // stack array, fill with func_addr for each resume shim, then
        // call fz_aot_set_resume_shims(&array[0]).
        {
            use cranelift_codegen::ir::StackSlotData;
            use cranelift_codegen::ir::StackSlotKind;
            let slot = b.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                72, // 9 * 8 bytes
                3,  // log2(8) alignment
            ));
            for (i, &rid) in mid_flight_resume_ids.iter().enumerate() {
                let addr = fn_addr(jmod, rid, &mut b);
                b.ins().stack_store(addr, slot, (i * 8) as i32);
            }
            let shims_ptr = b.ins().stack_addr(types::I64, slot, 0);
            let set_fref = jmod.declare_func_in_func(set_shims_id, b.func);
            b.ins().call(set_fref, &[shims_ptr]);
        }

        // fz-4mk.3b — register the drain-dtor entry shim with the runtime
        // so the AOT run-queue loop can fire pending dtors at task-exit.
        {
            let drain_addr = fn_addr(jmod, drain_dtor_entry_id, &mut b);
            let set_drain_fref = jmod.declare_func_in_func(set_drain_id, b.func);
            b.ins().call(set_drain_fref, &[drain_addr]);
        }

        // fz-xx8.1 — register the `fz_resume` shim with the runtime so the
        // AOT run-queue loop can dispatch `pending_resume_matched` requests.
        {
            let resume_addr_v = fn_addr(jmod, resume_id, &mut b);
            let set_resume_fref = jmod.declare_func_in_func(set_resume_id, b.func);
            b.ins().call(set_resume_fref, &[resume_addr_v]);
        }

        // exit = fz_aot_run_main(proc, main_fp, main_entry_addr)
        let run_fref = jmod.declare_func_in_func(run_id, b.func);
        let run_call = b.ins().call(run_fref, &[proc_v, main_fp, me_addr]);
        let result = b.inst_results(run_call)[0];
        b.ins().return_(&[result]);

        b.seal_all_blocks();
        b.finalize();
    }
    let flags = settings::Flags::new(settings::builder());
    cranelift_codegen::verifier::verify_function(&ctx.func, &flags)
        .map_err(|e| CodegenError::new(format!("verify C main: {}", e)))?;
    jmod.define_function(c_main_id, &mut ctx)
        .map_err(|e| CodegenError::new(format!("define C main: {}", e)))?;
    jmod.clear_context(&mut ctx);
    Ok(())
}

fn sig1(params: &[ir::Type], rets: &[ir::Type]) -> Signature {
    let mut s = Signature::new(CallConv::SystemV);
    for p in params {
        s.params.push(AbiParam::new(*p));
    }
    for r in rets {
        s.returns.push(AbiParam::new(*r));
    }
    s
}

/// Declare every fz runtime FFI fn as an Import in the given Cranelift
/// Module and return the resulting FuncIds packed into a RuntimeRefs.
///
/// Generic on `M: cranelift_module::Module` so the JIT (JITModule) and a
/// future AOT driver (ObjectModule, fz-ul4.23.6) call the same fn — the
/// declarations don't care whether the underlying symbol resolves via
/// JIT-installed Rust fn pointers or via a linker-resolved staticlib.
///
/// This is the only place that knows the wire ABI of each runtime fn;
/// changing one signature requires updating both the FFI body in
/// ir_runtime.rs AND the matching entry here.
fn declare_runtime_symbols<M: cranelift_module::Module>(
    jmod: &mut M,
) -> Result<RuntimeRefs, CodegenError> {
    // fz-02r.5 — import FZ_SHOULD_YIELD as a 1-byte external data object.
    // Must be declared before the `decl` closure borrows `jmod`.
    let should_yield_data_id = jmod
        .declare_data("FZ_SHOULD_YIELD", Linkage::Import, false, false)
        .map_err(|e| CodegenError::new(format!("declare FZ_SHOULD_YIELD: {}", e)))?;
    let mut decl = |name: &str, params: &[ir::Type], rets: &[ir::Type]| {
        let sig = sig1(params, rets);
        jmod.declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))
    };

    let halt_id = decl("fz_halt", &[types::I64, types::I64], &[])?;
    let halt_implicit_id = decl("fz_halt_implicit", &[types::I64], &[])?;
    // fz-ul4.27.22.3 — typed halt-implicit variants.
    let halt_implicit_i64_id = decl("fz_halt_implicit_i64", &[types::I64], &[])?;
    let halt_implicit_f64_id = decl("fz_halt_implicit_f64", &[types::F64], &[])?;
    let alloc_id = decl("fz_alloc_frame", &[types::I32, types::I32], &[types::I64])?;
    let alloc_cons_id = decl(
        "fz_alloc_list_cons",
        &[types::I64, types::I64],
        &[types::I64],
    )?;
    let alloc_struct_id = decl("fz_alloc_struct", &[types::I32], &[types::I64])?;
    let bs_begin_id = decl("fz_bs_begin", &[], &[])?;
    let bs_write_id = decl(
        "fz_bs_write_field",
        &[
            types::I64, // value bits
            types::I32, // ty tag
            types::I32, // size_present
            types::I32, // size_value
            types::I32, // unit
            types::I32, // endian
            types::I32, // signed
        ],
        &[],
    )?;
    let bs_finalize_id = decl("fz_bs_finalize", &[], &[types::I64])?;
    // fz-cty.8 — `(payload_ptr: i64, byte_len: i64, bit_len: i64) -> i64`.
    let alloc_bitstring_const_id = decl(
        "fz_alloc_bitstring_const",
        &[types::I64, types::I64, types::I64],
        &[types::I64],
    )?;
    // fz-q8d.2 — `(static_sharedbin: i64) -> i64`. Retains the anchor on
    // the supplied static SharedBin and allocates a ProcBin on the
    // current process heap that owns the new refcount edge.
    let alloc_procbin_from_static_id =
        decl("fz_alloc_procbin_from_static", &[types::I64], &[types::I64])?;
    // fz-q8d.2 — noop destructor symbol. Imported so its address can be
    // baked into each static SharedBin's `destructor` slot via a
    // function-address relocation. Matches the runtime's `extern "C" fn
    // (*mut SharedBin)` signature exactly.
    let shared_bin_destructor_noop_id = decl("shared_bin_destructor_noop", &[types::I64], &[])?;
    // fz-9ss — extern binary marshal helpers.
    let binary_as_ptr_id = decl("fz_binary_as_ptr", &[types::I64], &[types::I64])?;
    let binary_as_cstring_id = decl("fz_binary_as_cstring", &[types::I64], &[types::I64])?;
    let bs_reader_init_id = decl("fz_bs_reader_init", &[types::I64], &[types::I64])?;
    let bs_read_field_id = decl(
        "fz_bs_read_field",
        &[
            types::I64, // reader bits
            types::I32, // ty tag
            types::I32, // size_present
            types::I32, // size_value
            types::I32, // unit
            types::I32, // endian
            types::I32, // signed
            types::I32, // is_last
        ],
        &[types::I64],
    )?;
    let map_begin_id = decl("fz_map_begin", &[], &[])?;
    let map_clone_id = decl("fz_map_clone", &[types::I64], &[])?;
    let map_push_id = decl("fz_map_push", &[types::I64, types::I64], &[])?;
    let map_finalize_id = decl("fz_map_finalize", &[], &[types::I64])?;
    let map_get_id = decl("fz_map_get", &[types::I64, types::I64], &[types::I64])?;
    let alloc_float_id = decl("fz_alloc_float", &[types::I64], &[types::I64])?;

    let arith_params: &[ir::Type] = &[types::I64, types::I64];
    let arith_ret: &[ir::Type] = &[types::I64];
    // fz-ul4.27.9: mixed-type arith/cmp slow paths are now inlined in JIT.
    // `fz_promote_f64` does the tag-aware Int|Float→f64 conversion (with the
    // same panic-on-non-numeric semantics the old fz_arith_* helpers had);
    // `fz_fmod` covers float remainder (Cranelift has no frem opcode).
    let promote_f64_id = decl("fz_promote_f64", &[types::I64], &[types::F64])?;
    let fmod_id = decl("fz_fmod", &[types::F64, types::F64], &[types::F64])?;
    let value_eq_id = decl("fz_value_eq", arith_params, arith_ret)?;

    let vec_begin_id = decl("fz_vec_begin", &[types::I32], &[])?;
    let vec_push_id = decl("fz_vec_push", &[types::I64], &[])?;
    let vec_finalize_id = decl("fz_vec_finalize", &[], &[types::I64])?;
    let alloc_closure_id = decl(
        "fz_alloc_closure",
        &[types::I32, types::I32, types::I32],
        &[types::I64],
    )?;
    // fz-cps.1.2 — receive cutover. Takes a cont closure ptr (i64),
    // stashes in Process::parked_cont, returns YIELD sentinel.
    let receive_park_id = decl("fz_receive_park", &[types::I64], &[types::I64])?;
    // fz-yxs/fz-st5/fz-70q.3 — selective-receive park entry. Args:
    //   matcher_fn_bits (i64), pinned_ptr (i64), n_pinned (i64),
    //   clause_bodies_ptr (i64), n_clauses (i64), bound_arity (i32),
    //   after_deadline_or_neg1 (i64), after_cont_bits (i64).
    // Returns YIELD sentinel (i64).
    let receive_park_matched_id = decl(
        "fz_receive_park_matched",
        &[
            types::I64,
            types::I64,
            types::I64,
            types::I64,
            types::I64,
            types::I32,
            types::I64,
            types::I64,
        ],
        &[types::I64],
    )?;
    // fz-02r.5 — mid-flight back-edge yield helpers.
    let mid_flight_roots_ptr_id = decl("fz_mid_flight_roots_ptr", &[], &[types::I64])?;
    // fz-70q.5.2 — cont-stub helper. Returns a raw `*const u64` to the
    // current process's resume_args slab (or null when empty). Cont stubs
    // (fz-70q.5.3) call this and read the first N u64s where N is the
    // body fn's compile-time bound_arity.
    let resume_args_ptr_id = decl("fz_resume_args_ptr", &[], &[types::I64])?;
    let yield_back_edge_id = decl(
        "fz_yield_back_edge",
        &[types::I64, types::I32],
        &[types::I64],
    )?;
    // fz-cps.1.7 — static zero-capture closure singleton lookup.
    // Returns the per-Process singleton pointer for the given cl_sid.
    let get_static_closure_id = decl("fz_get_static_closure", &[types::I32], &[types::I64])?;
    // fz-cps.1.11 — halt-cont singleton lookup. Returns the per-Process
    // halt-cont closure ptr; lazily initialized using the supplied
    // halt_cont_body addr (JIT pre-populates at make_process time;
    // AOT path relies on lazy init at first call).
    // fz-ul4.27.22.3 — `(addr, kind)` sig: kind selects among 3 Process
    // singletons (0=Tagged, 1=RawInt, 2=RawF64).
    let get_halt_cont_id = decl("fz_get_halt_cont", &[types::I64, types::I32], &[types::I64])?;
    // fz-ul4.27.22.3 — three fz_halt_cont_body variants, declared LOCAL
    // (bodies emitted below). Tagged: `(i64 Tagged, i64) -> i64 tail`;
    // RawInt: `(i64, i64) -> i64 tail`; RawF64: `(f64, i64) -> i64 tail`.
    let mut declare_hcb = |name: &str, val_ty: ir::Type| -> Result<FuncId, CodegenError> {
        let mut sig = Signature::new(CallConv::Tail);
        sig.params.push(AbiParam::new(val_ty));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        jmod.declare_function(name, Linkage::Local, &sig)
            .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))
    };
    let halt_cont_body_tagged_id = declare_hcb("fz_halt_cont_body_tagged", types::I64)?;
    let halt_cont_body_i64_id = declare_hcb("fz_halt_cont_body_i64", types::I64)?;
    let halt_cont_body_f64_id = declare_hcb("fz_halt_cont_body_f64", types::F64)?;
    // fz-cps.1.11 — fz_resume_park: SystemV entry the scheduler calls on
    // wakeup. Body emitted in compile_with_backend; signature `(msg:i64,
    // cont:i64) -> i64 system_v` matches Rust's extern "C" shape for FFI.
    let mut rp_sig = Signature::new(CallConv::SystemV);
    rp_sig.params.push(AbiParam::new(types::I64));
    rp_sig.params.push(AbiParam::new(types::I64));
    rp_sig.returns.push(AbiParam::new(types::I64));
    let resume_park_id = jmod
        .declare_function("fz_resume_park", Linkage::Local, &rp_sig)
        .map_err(|e| CodegenError::new(format!("declare fz_resume_park: {}", e)))?;
    // fz-cps.1.11 — fz_spawn_entry: SystemV entry the scheduler calls to
    // launch a new task's zero-arg closure. Sig: `(closure:i64) -> i64`.
    let mut se_sig = Signature::new(CallConv::SystemV);
    se_sig.params.push(AbiParam::new(types::I64));
    se_sig.returns.push(AbiParam::new(types::I64));
    let spawn_entry_id = jmod
        .declare_function("fz_spawn_entry", Linkage::Local, &se_sig)
        .map_err(|e| CodegenError::new(format!("declare fz_spawn_entry: {}", e)))?;
    // fz-ul4.27.22.3 — fz_main_entry: SystemV entry the scheduler calls
    // to launch at a known main fn. Sig: `(main_fp:i64, halt_cl:i64)
    // -> i64`. Rust caller picks halt_cl from process.halt_cont_singletons
    // by the entry fn's return_repr kind.
    let mut me_sig = Signature::new(CallConv::SystemV);
    me_sig.params.push(AbiParam::new(types::I64));
    me_sig.params.push(AbiParam::new(types::I64));
    me_sig.returns.push(AbiParam::new(types::I64));
    let main_entry_id = jmod
        .declare_function("fz_main_entry", Linkage::Local, &me_sig)
        .map_err(|e| CodegenError::new(format!("declare fz_main_entry: {}", e)))?;
    // fz-4mk.3a — fz_drain_dtor_entry: SystemV entry the scheduler calls
    // per pending dtor at task-exit. Sig: `(closure:i64, payload:i64) ->
    // i64 system_v`. Body loads closure+16 (body addr), allocates a
    // Tagged halt-cont via fz_get_halt_cont, and Tail-CC indirect-calls
    // the closure body with `(self, payload, halt_cl)`.
    let mut dd_sig = Signature::new(CallConv::SystemV);
    dd_sig.params.push(AbiParam::new(types::I64));
    dd_sig.params.push(AbiParam::new(types::I64));
    dd_sig.returns.push(AbiParam::new(types::I64));
    let drain_dtor_entry_id = jmod
        .declare_function("fz_drain_dtor_entry", Linkage::Local, &dd_sig)
        .map_err(|e| CodegenError::new(format!("declare fz_drain_dtor_entry: {}", e)))?;

    Ok(RuntimeRefs {
        halt_id,
        halt_implicit_id,
        halt_implicit_i64_id,
        halt_implicit_f64_id,
        halt_cont_body_tagged_id,
        halt_cont_body_i64_id,
        halt_cont_body_f64_id,
        alloc_id,
        alloc_cons_id,
        alloc_struct_id,
        bs_begin_id,
        bs_write_id,
        bs_finalize_id,
        alloc_bitstring_const_id,
        alloc_procbin_from_static_id,
        shared_bin_destructor_noop_id,
        binary_as_ptr_id,
        binary_as_cstring_id,
        bs_reader_init_id,
        bs_read_field_id,
        map_begin_id,
        map_clone_id,
        map_push_id,
        map_finalize_id,
        map_get_id,
        alloc_float_id,
        promote_f64_id,
        fmod_id,
        value_eq_id,
        vec_begin_id,
        vec_push_id,
        vec_finalize_id,
        alloc_closure_id,
        receive_park_id,
        receive_park_matched_id,
        get_static_closure_id,
        get_halt_cont_id,
        resume_park_id,
        spawn_entry_id,
        main_entry_id,
        drain_dtor_entry_id,
        mid_flight_roots_ptr_id,
        resume_args_ptr_id,
        yield_back_edge_id,
        should_yield_data_id,
    })
}

/// fz-q8d.2 — symbol set for one unique ConstBitstring byte payload.
#[derive(Clone, Copy)]
struct BsConstSyms {
    /// Byte payload symbol (Local data, read-only). Always present.
    bytes_id: DataId,
    /// Static `SharedBin` symbol (Local data, writable so the refcount
    /// anchor lives in .data). `Some` for above-threshold payloads,
    /// `None` for below-threshold (which keep the inline / runtime
    /// allocation path via `fz_alloc_bitstring_const`).
    sharedbin_id: Option<DataId>,
}

/// fz-q8d.2 — emit a 40-byte static `SharedBin` symbol in `.data`:
///
///   offset  0..8   refcount = 1 (LE u64, anchor — never decremented to 0)
///   offset  8..16  bit_len (LE u64)
///   offset 16..24  bytes_ptr — relocation to the bytes payload symbol
///   offset 24..32  bytes_len (LE u64)
///   offset 32..40  destructor — function-address relocation to noop
///
/// The destructor relocation is to `shared_bin_destructor_noop`, declared
/// as `Linkage::Import` so the linker resolves it to the runtime export.
fn define_static_sharedbin<M: cranelift_module::Module>(
    jmod: &mut M,
    runtime: &RuntimeRefs,
    bytes_id: DataId,
    bytes: &[u8],
    bit_len: u64,
    idx: usize,
) -> Result<DataId, CodegenError> {
    let sb_name = format!(".fz_bs_sb_{}", idx);
    let sb_id = jmod
        .declare_data(&sb_name, Linkage::Local, /*writable=*/ true, false)
        .map_err(|e| CodegenError::new(format!("declare {}: {}", sb_name, e)))?;
    let mut buf = vec![0u8; 40];
    buf[0..8].copy_from_slice(&1u64.to_le_bytes());
    buf[8..16].copy_from_slice(&bit_len.to_le_bytes());
    // bytes_ptr at 16..24 — zero placeholder; relocation patches at link.
    buf[24..32].copy_from_slice(&(bytes.len() as u64).to_le_bytes());
    // destructor at 32..40 — zero placeholder; function-addr reloc patches.
    let mut desc = DataDescription::new();
    desc.define(buf.into_boxed_slice());
    desc.set_align(8);
    let bytes_gv = jmod.declare_data_in_data(bytes_id, &mut desc);
    desc.write_data_addr(16, bytes_gv, 0);
    let dtor_fref = jmod.declare_func_in_data(runtime.shared_bin_destructor_noop_id, &mut desc);
    desc.write_function_addr(32, dtor_fref);
    jmod.define_data(sb_id, &desc)
        .map_err(|e| CodegenError::new(format!("define {}: {}", sb_name, e)))?;
    Ok(sb_id)
}

struct CodegenEnv<'a> {
    runtime: &'a RuntimeRefs,
    module: &'a crate::fz_ir::Module,
    fn_types: &'a crate::ir_typer::FnTypes,
    spec_registry: &'a SpecRegistry,
    fn_ids: &'a HashMap<u32, FuncId>,
    tuple_schema_ids: &'a HashMap<usize, u32>,
    /// fz-q8d.2 — per-payload symbol cache. Below-threshold payloads
    /// carry only `bytes_id`; above-threshold payloads additionally carry
    /// a static `SharedBin` symbol in `.data`.
    bs_const_data: &'a std::cell::RefCell<HashMap<Vec<u8>, BsConstSyms>>,
    param_reprs: &'a [Vec<ArgRepr>],
    return_reprs: &'a [ArgRepr],
    natively_callable: &'a std::collections::HashSet<crate::fz_ir::FnId>,
    cont_target_fns: &'a std::collections::HashSet<crate::fz_ir::FnId>,
    cont_fns: &'a std::collections::HashSet<crate::fz_ir::FnId>,
    closure_n_captures: &'a std::collections::HashMap<crate::fz_ir::FnId, usize>,
    /// fz-70q.3 — number of Tail-CC "extra" params (inputs before the
    /// trailing `self` closure ptr) for a cont fn that doesn't follow
    /// the default `(input, self)` shape. Populated only for cont fns
    /// emitted by `Term::ReceiveMatched` lowering:
    ///   * clause body fn → bound_arity (one per pattern-bound name).
    ///   * clause guard fn → bound_arity (same shape; guard returns Bool).
    ///   * after body fn → 0 (after takes no message; captures only).
    ///
    /// Unmapped cont fns default to 1 (single-input Receive cont).
    cont_extras_count: &'a std::collections::HashMap<crate::fz_ir::FnId, usize>,
    /// fz-70q.3 — matcher FuncId per ReceiveMatched site, keyed by
    /// `(parent_fn_id.0, block_id.0)`. Populated by the pre-pass in
    /// `compile_with_backend` and consumed by the Term::ReceiveMatched
    /// arm in `compile_block_terminator` (`fn_addr` → call site arg).
    matcher_fn_ids: &'a std::collections::HashMap<(u32, u32), FuncId>,
    /// fz-70q.5.4 — cont-stub FuncId keyed by body_spec_id. Populated
    /// alongside `matcher_fn_ids` in compile_with_backend's pre-pass.
    /// Consumed by the Term::ReceiveMatched arm to install the right
    /// stub address at each clause-body / guard / after closure's
    /// `stub_fp` slot (+16). See ir_codegen_cont_stub.
    cont_stub_ids: &'a std::collections::HashMap<u32, FuncId>,
}

/// Per-function mutable state threaded through `lower_prim` and
/// `emit_terminator`. Holds five orthogonal caches:
///
/// - `const_cache`: per-block constant deduplication (avoids redundant iconst).
/// - `raw_int_consts`: raw i64 value for RawInt vars (drives box-int const fold).
/// - `extern_funcs`: FuncRef deduplicated per extern symbol per function.
/// - `used_vars`: all var IDs that appear as operands anywhere in the function;
///   unit-return extern results whose dest ID is absent skip the nil iconst.
/// - `if_only_conds`: var IDs used exclusively as Term::If conditions; their
///   boolean prims emit ArgRepr::Condition (raw i1) instead of bool_to_fz, so
///   the tagged form is never materialised and brif consumes the i1 directly.
#[derive(Default)]
struct CodegenCache {
    /// Cranelift values for small integer/atom constants, keyed by (block, value)
    /// so entries from sibling blocks are never reused (fz-bwp).
    const_cache: HashMap<(ir::Block, i64), ir::Value>,
    /// Raw (unboxed) i64 values for integer constants keyed by Var ID (fz-zj3).
    raw_int_consts: HashMap<u32, i64>,
    /// FuncRef for each extern, deduplicated per function (fz-0uu).
    extern_funcs: HashMap<crate::fz_ir::ExternId, ir::FuncRef>,
    /// Var IDs referenced anywhere in the function's IR (fz-2tc). Unit-return
    /// extern results whose dest ID is absent here can skip the nil iconst.
    used_vars: std::collections::HashSet<u32>,
    /// Var IDs used exclusively as Term::If conditions — eligible for lazy
    /// bool_to_fz (stored as ArgRepr::Condition, materialised only if tagged_get
    /// is called) (fz-h4q).
    if_only_conds: std::collections::HashSet<u32>,
}

#[derive(Clone, Copy)]
struct RuntimeRefs {
    halt_id: FuncId,
    halt_implicit_id: FuncId,
    halt_implicit_i64_id: FuncId,
    halt_implicit_f64_id: FuncId,
    halt_cont_body_tagged_id: FuncId,
    halt_cont_body_i64_id: FuncId,
    halt_cont_body_f64_id: FuncId,
    alloc_id: FuncId,
    alloc_cons_id: FuncId,
    alloc_struct_id: FuncId,
    bs_begin_id: FuncId,
    bs_write_id: FuncId,
    bs_finalize_id: FuncId,
    // fz-cty.8 — single-shot allocation from a module-baked byte payload.
    alloc_bitstring_const_id: FuncId,
    // fz-q8d.2 — alloc a ProcBin referencing a static SharedBin in .data.
    alloc_procbin_from_static_id: FuncId,
    // fz-q8d.2 — noop destructor address relocated into static SharedBins.
    shared_bin_destructor_noop_id: FuncId,
    // fz-9ss — binary/cstring extern marshal helpers. Both have signature
    // `(i64 FzValue bits) -> i64 *const u8` from Cranelift's perspective.
    binary_as_ptr_id: FuncId,
    binary_as_cstring_id: FuncId,
    bs_reader_init_id: FuncId,
    bs_read_field_id: FuncId,
    map_begin_id: FuncId,
    map_clone_id: FuncId,
    map_push_id: FuncId,
    map_finalize_id: FuncId,
    map_get_id: FuncId,
    vec_begin_id: FuncId,
    vec_push_id: FuncId,
    vec_finalize_id: FuncId,
    alloc_float_id: FuncId,
    promote_f64_id: FuncId,
    fmod_id: FuncId,
    value_eq_id: FuncId,
    alloc_closure_id: FuncId,
    receive_park_id: FuncId,
    /// fz-70q.3 — fz_receive_park_matched FFI entry. Called from the
    /// Term::ReceiveMatched arm in compile_block_terminator.
    receive_park_matched_id: FuncId,
    get_static_closure_id: FuncId,
    get_halt_cont_id: FuncId,
    resume_park_id: FuncId,
    spawn_entry_id: FuncId,
    main_entry_id: FuncId,
    /// fz-4mk.3a — fz_drain_dtor_entry: SystemV→Tail-CC shim for invoking
    /// a resource dtor closure with its payload. Sig: `(closure:i64,
    /// payload:i64) -> i64 system_v`. Loads body addr at closure+16 and
    /// indirect-calls (closure, payload, halt_cl) via Tail-CC; result
    /// discarded. Scheduler drains `pending_dtors` through this shim at
    /// task-exit, replacing the legacy `resolve_dtor_from_closure` C
    /// extraction path.
    drain_dtor_entry_id: FuncId,
    // fz-02r.5 — mid-flight back-edge yield helpers.
    mid_flight_roots_ptr_id: FuncId,
    /// fz-70q.5.2 — `fz_resume_args_ptr() -> i64 systemv`. Cont stubs
    /// (fz-70q.5.3) call this to obtain the runtime slab pointer.
    /// fz-70q.5.4 wires it into the per-cont-fn stub emission pass and
    /// retires this allow.
    #[allow(dead_code)]
    resume_args_ptr_id: FuncId,
    yield_back_edge_id: FuncId,
    should_yield_data_id: DataId,
}

/// Pack a Span into a Cranelift SourceLoc (u32). 8 bits file_id + 24
/// bits start offset. Dummy spans become SourceLoc::default() so they
/// don't generate noise in the dump. fz-ul4.23.7.
fn span_to_srcloc(s: crate::diag::Span) -> cranelift_codegen::ir::SourceLoc {
    if s.is_dummy() {
        return cranelift_codegen::ir::SourceLoc::default();
    }
    let file = (s.file.0 & 0xFF) << 24;
    let offset = s.start & 0x00FF_FFFF;
    cranelift_codegen::ir::SourceLoc::new(file | offset)
}

struct EntryHarnessOut {
    var_env: HashMap<u32, VarBinding>,
    /// Some for uniform fns; None for native.
    frame_ptr: Option<ir::Value>,
    /// Some for uniform fns; None for native.
    host_ctx: Option<ir::Value>,
    /// Some for native fns (trailing cont SSA); None for uniform.
    cont_param: Option<ir::Value>,
}

fn build_entry_harness<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    env: &CodegenEnv<'_>,
    schemas: &[Schema],
    f: &crate::fz_ir::FnIr,
    this_spec_id: u32,
    is_native: bool,
    is_cont_fn: bool,
    closure_target_n_caps: Option<usize>,
    entry_cl: ir::Block,
) -> EntryHarnessOut {
    let runtime = env.runtime;
    let param_reprs = env.param_reprs;
    let entry_blk = f.blocks.iter().find(|blk| blk.id == f.entry).unwrap();
    let mut var_env: HashMap<u32, VarBinding> = HashMap::new();
    let my_schema = &schemas[this_spec_id as usize];

    // (frame_ptr, host_ctx) — uniform fns get both from entry block_params;
    // native fns have no frame and no frame_ptr (None). fz-ul4.27.16: the
    // 9 downstream consumer sites are each gated on `is_native` or on a
    // terminator type that natively_callable excludes from native fns,
    // so unwrapping the Option below is invariant-safe. Any future code
    // path that violates this surfaces immediately as a panic at codegen.
    // host_ctx is Some only for uniform fns (always the second block param).
    // Native fns always have host_ctx = None; they use fz_halt_implicit (TLS).
    // fz-cps.1.a (fz-siu.1.1): `cont_param` is the trailing i64 in the
    // native-tier signature. Threaded but unused in .1.1; .1.2+ consume it.
    let (frame_ptr, host_ctx, cont_param): (
        Option<ir::Value>,
        Option<ir::Value>,
        Option<ir::Value>,
    ) = if is_native {
        let params: Vec<ir::Value> = b.block_params(entry_cl).to_vec();
        let my_param_reprs = &param_reprs[this_spec_id as usize];
        if is_cont_fn {
            // fz-cps.1.2 cont fn entry harness per §2.1:
            //   params[0..N] = extras     → fz_param[0..N]
            //   params[N]    = self       → closure ptr
            // Closure layout (§2.2 + cps cutover):
            //   self+16 : code_ptr
            //   self+24 : outer_cont       (synthetic; not in fz_param)
            //   self+32 : user_cap[0]      → fz_param[N]
            //   self+40 : user_cap[1]      → fz_param[N+1]
            //   ...
            // The cont's "next k" is the synthetic outer_cont at +24.
            //
            // fz-70q.3 — extras_count defaults to 1 (single-input
            // Receive cont) but ReceiveMatched lowering overrides via
            // `cont_extras_count`: body / guard fns set it to
            // bound_arity; after-body sets 0.
            let extras_count = env.cont_extras_count.get(&f.id).copied().unwrap_or(1);
            // fz-ul4.27.22.3: cont sig matches my_param_reprs[i]'s
            // Cranelift type directly. Producer's Term::Return uses the
            // same sig (return_reprs[producer_sid] = my_param_reprs[0]
            // via the typer's cont_input_key seam agreement). No coerce
            // at entry — value already in body's expected repr.
            for (i, p) in entry_blk.params.iter().take(extras_count).enumerate() {
                var_env.insert(
                    p.0,
                    VarBinding {
                        value: params[i],
                        repr: my_param_reprs[i],
                    },
                );
            }
            let self_val = params[extras_count];
            for (i, p) in entry_blk.params.iter().enumerate().skip(extras_count) {
                // fz_param[i] = user_cap[i-extras_count] at offset
                // HEADER_SIZE + 2*SLOT_BYTES + (i-extras_count)*SLOT_BYTES.
                // fz-ul4.27.21.2 — captures are stored in their per-capture
                // repr at the builder (param_reprs[cont_sid][i]); load with
                // the matching Cranelift type. No tag/untag round-trip when
                // the capture is narrow.
                let off = HEADER_SIZE + SLOT_BYTES * 2 + ((i - extras_count) as i32) * SLOT_BYTES;
                let cl_ty = my_param_reprs[i].cl_type();
                let v = b.ins().load(cl_ty, MemFlags::trusted(), self_val, off);
                var_env.insert(
                    p.0,
                    VarBinding {
                        value: v,
                        repr: my_param_reprs[i],
                    },
                );
            }
            let host_ctx = None;
            (None, host_ctx, Some(self_val))
        } else if let Some(n_caps) = closure_target_n_caps {
            // fz-cps.1.2 closure-target fn entry harness per §2.1.
            // fz_params order (set by ir_lower / closure stub convention):
            //   fz_params[0..n_caps]            = captures      → load self+24+8*k
            //   fz_params[n_caps..n_caps+n_args] = args         → Cranelift params[0..n_args]
            // Cranelift sig: `(args..., self, cont) tail`.
            //   params[0..n_args]  = args
            //   params[n_args]     = self  (closure ptr)
            //   params[n_args+1]   = cont  (cont SSA)
            let n_args = entry_blk.params.len().saturating_sub(n_caps);
            let self_val = params[n_args];
            let cont_val = params[n_args + 1];
            // Captures: fz_params[0..n_caps] ← load from self+24+8*k.
            // fz-try.15+B1+B2 — closure capture-storage ABI is uniform
            // Tagged at the seam (same principle as the return seam:
            // every body invokable via stub_fp must agree on
            // wire-format, regardless of its typed view). The body
            // loads i64 Tagged from self+24+8*k and coerces to its
            // narrow capture repr internally.
            for (k, p) in entry_blk.params.iter().enumerate().take(n_caps) {
                let off = HEADER_SIZE + SLOT_BYTES + (k as i32) * SLOT_BYTES;
                let raw = b.ins().load(types::I64, MemFlags::trusted(), self_val, off);
                let v = coerce_to(b, jmod, runtime, raw, ArgRepr::Tagged, my_param_reprs[k]);
                var_env.insert(
                    p.0,
                    VarBinding {
                        value: v,
                        repr: my_param_reprs[k],
                    },
                );
            }
            // Args: fz_params[n_caps..] ← Cranelift params[0..n_args].
            for (j, p) in entry_blk.params.iter().enumerate().skip(n_caps) {
                let cl_idx = j - n_caps;
                var_env.insert(
                    p.0,
                    VarBinding {
                        value: params[cl_idx],
                        repr: my_param_reprs[j],
                    },
                );
            }
            let _ = self_val;
            (None, None, Some(cont_val))
        } else {
            for (i, p) in entry_blk.params.iter().enumerate() {
                var_env.insert(
                    p.0,
                    VarBinding {
                        value: params[i],
                        repr: my_param_reprs[i],
                    },
                );
            }
            let host_ctx_idx = entry_blk.params.len();
            let (host_ctx, cont_idx) = (None, host_ctx_idx);
            (None, host_ctx, Some(params[cont_idx]))
        }
    } else {
        let frame_ptr = b.block_params(entry_cl)[0];
        let host_ctx = b.block_params(entry_cl)[1];

        // Load entry params from frame slots [1..N+1] (offsets 24, 32, ...).
        // fz-ul4.27.5.2/3: RawF64 slots load as raw f64 (ArgRepr::RawF64);
        // RawI64 slots load as raw i64 (ArgRepr::RawInt — unshifted payload).
        // Everything else loads as a tagged FzValue i64 (ArgRepr::Tagged).
        for (i, p) in entry_blk.params.iter().enumerate() {
            let off = HEADER_SIZE + ((i as i32 + 1) * SLOT_BYTES);
            let slot_kind = &my_schema.fields[i + 1].kind;
            let (value, repr) = match slot_kind {
                FieldKind::RawF64 => {
                    let f = b
                        .ins()
                        .load(types::F64, MemFlags::trusted(), frame_ptr, off);
                    (f, ArgRepr::RawF64)
                }
                FieldKind::RawI64 => {
                    let n = b
                        .ins()
                        .load(types::I64, MemFlags::trusted(), frame_ptr, off);
                    (n, ArgRepr::RawInt)
                }
                _ => (
                    b.ins()
                        .load(types::I64, MemFlags::trusted(), frame_ptr, off),
                    ArgRepr::Tagged,
                ),
            };
            var_env.insert(p.0, VarBinding { value, repr });
        }
        // fz-cps.1.a: uniform fns do not yet have a cont SSA value; the
        // cont still lives in slot 0 of `frame_ptr` until fz-siu.1.5.
        (Some(frame_ptr), Some(host_ctx), None)
    };
    EntryHarnessOut {
        var_env,
        frame_ptr,
        host_ctx,
        cont_param,
    }
}

/// Resolve the outer-cont value to forward into a cont closure's +24 slot.
/// For cont fns: loaded from self+24. For non-cont native: cont_param.
/// For uniform fns without cont_param: load frame_ptr+16, brif on null to
/// allocate a halt-cont fallback closure.
fn resolve_outer_cont<M: cranelift_module::Module>(
    jmod: &mut M,
    b: &mut FunctionBuilder<'_>,
    runtime: &RuntimeRefs,
    return_reprs: &[ArgRepr],
    is_cont_fn: bool,
    cont_param: Option<ir::Value>,
    frame_ptr: Option<ir::Value>,
    cont_sid: u32,
) -> ir::Value {
    if is_cont_fn {
        // Native cont fn: `self` is the closure ptr; outer_cont sits at
        // self+24 by closure layout (HEADER_SIZE + SLOT_BYTES).
        //
        // fz-70q.5.5 — uniform cont fn (cont fn whose enclosing chain
        // forced a uniform frame ABI): there is no `self` closure ptr
        // — the caller dispatched through the legacy trampoline using a
        // heap frame. The outer_cont in that case lives in frame slot 0
        // (frame+16), same layout the entry harness already uses for
        // the uniform path. Fall through to the legacy frame-slot load
        // below so the same site can build cont closures whether it
        // got entered via the cont-stub seam or via a uniform call.
        if let Some(self_val) = cont_param {
            return b.ins().load(
                types::I64,
                MemFlags::trusted(),
                self_val,
                HEADER_SIZE + SLOT_BYTES,
            );
        }
        // else fall through to the uniform frame-slot branch below.
    }
    {
        let _ = is_cont_fn; // consumed above when cont_param was Some
        match cont_param {
            Some(c) => c,
            None => {
                let from_slot = b.ins().load(
                    types::I64,
                    MemFlags::trusted(),
                    frame_ptr.expect("uniform caller building cont closure must have frame_ptr"),
                    HEADER_SIZE,
                );
                let zero = b.ins().iconst(types::I64, 0);
                let is_null = b.ins().icmp(IntCC::Equal, from_slot, zero);
                let alloc_blk = b.create_block();
                let join_blk = b.create_block();
                b.append_block_param(join_blk, types::I64);
                b.ins().brif(
                    is_null,
                    alloc_blk,
                    &[][..],
                    join_blk,
                    &[BlockArg::Value(from_slot)],
                );
                b.switch_to_block(alloc_blk);
                b.seal_block(alloc_blk);
                let acl = jmod.declare_func_in_func(runtime.alloc_closure_id, b.func);
                let dummy_fid = b.ins().iconst(types::I32, 0);
                let n_caps0 = b.ins().iconst(types::I32, 0);
                let zero_hk = b.ins().iconst(types::I32, 0);
                let halt_alloc = b.ins().call(acl, &[dummy_fid, n_caps0, zero_hk]);
                let halt_cl = b.inst_results(halt_alloc)[0];
                let hc_repr = return_reprs[cont_sid as usize];
                let hcb_addr = fn_addr(jmod, halt_cont_body_id_for(runtime, hc_repr), b);
                b.ins()
                    .store(MemFlags::trusted(), hcb_addr, halt_cl, HEADER_SIZE);
                b.ins().jump(join_blk, &[BlockArg::Value(halt_cl)]);
                b.switch_to_block(join_blk);
                b.seal_block(join_blk);
                b.block_params(join_blk)[0]
            }
        }
    }
}

/// Allocate a cont closure, populate its code-addr, outer-cont, and user
/// captures. Returns the heap pointer to the new closure object.
///
/// `cap_bindings` is a slice of (value, from_repr) pairs for each user
/// capture; these are stored at `cl_ptr + HEADER_SIZE + 2*SLOT_BYTES + i*8`
/// coerced to `param_reprs[cont_sid][i+1]`.
/// fz-70q.3 — `captures_offset` is the index into `cont_param_reprs`
/// where the cont fn's user captures start. For a normal Receive cont
/// (`(msg, self)` Tail-CC) it's 1: slot 0 is the message input, slots
/// 1..N are captures. For a ReceiveMatched clause body
/// (`(bound_0, ..., bound_{N-1}, self)`) it's `bound_arity`: the first
/// N slots are bound vars, captures follow.
///
/// fz-70q.5.4 — when `cont_stub_fid` is `Some`, the closure's `stub_fp`
/// slot (+16) is populated with the cont-stub address rather than the
/// body fn's direct address. This is the path used by ReceiveMatched
/// clause-body / guard / after closures: the scheduler resume seam
/// dispatches them through their cont stub (SystemV), which bridges
/// into the body's uniform `(frame, host_ctx) -> i64 systemv` entry.
/// `None` keeps the legacy direct-dispatch behavior (Term::Receive
/// cont, Term::Call cont, etc.) until those paths migrate too.
#[allow(clippy::too_many_arguments)]
fn build_cont_closure<M: cranelift_module::Module>(
    jmod: &mut M,
    b: &mut FunctionBuilder<'_>,
    runtime: &RuntimeRefs,
    return_reprs: &[ArgRepr],
    param_reprs: &[Vec<ArgRepr>],
    is_cont_fn: bool,
    cont_param: Option<ir::Value>,
    frame_ptr: Option<ir::Value>,
    cont_sid: u32,
    cont_fid: FuncId,
    cap_bindings: &[(ir::Value, ArgRepr)],
    captures_offset: usize,
    cont_stub_fid: Option<FuncId>,
) -> ir::Value {
    let acl_fref = jmod.declare_func_in_func(runtime.alloc_closure_id, b.func);
    let cl_fid_v = b.ins().iconst(types::I32, cont_sid as i64);
    // +1: slot 0 is the synthetic outer_cont at +24; user captures start at +32.
    let n_caps_v = b.ins().iconst(types::I32, (cap_bindings.len() + 1) as i64);
    let zero_hk = b.ins().iconst(types::I32, 0);
    let cl_inst = b.ins().call(acl_fref, &[cl_fid_v, n_caps_v, zero_hk]);
    let cl_ptr = b.inst_results(cl_inst)[0];
    let stub_target_fid = cont_stub_fid.unwrap_or(cont_fid);
    let cont_code_addr = fn_addr(jmod, stub_target_fid, b);
    b.ins()
        .store(MemFlags::trusted(), cont_code_addr, cl_ptr, HEADER_SIZE);
    let my_outer_cont = resolve_outer_cont(
        jmod,
        b,
        runtime,
        return_reprs,
        is_cont_fn,
        cont_param,
        frame_ptr,
        cont_sid,
    );
    b.ins().store(
        MemFlags::trusted(),
        my_outer_cont,
        cl_ptr,
        HEADER_SIZE + SLOT_BYTES,
    );
    let cont_param_reprs = &param_reprs[cont_sid as usize];
    for (i, &(val, from)) in cap_bindings.iter().enumerate() {
        let to = cont_param_reprs[i + captures_offset];
        let v = coerce_to(b, jmod, runtime, val, from, to);
        let off = HEADER_SIZE + SLOT_BYTES * 2 + (i as i32) * SLOT_BYTES;
        b.ins().store(MemFlags::trusted(), v, cl_ptr, off);
    }
    cl_ptr
}

#[allow(clippy::too_many_arguments)]
fn emit_terminator<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    env: &CodegenEnv<'_>,
    schemas: &[Schema],
    var_env: &HashMap<u32, VarBinding>,
    blk: &crate::fz_ir::Block,
    block_map: &HashMap<u32, ir::Block>,
    is_native: bool,
    is_cont_fn: bool,
    this_spec_id: u32,
    caller_fn_id: crate::fz_ir::FnId,
    cont_ptr_known_null: bool,
    frame_ptr: Option<ir::Value>,
    host_ctx: Option<ir::Value>,
    cont_param: Option<ir::Value>,
    cache: &mut CodegenCache,
) -> Result<(), CodegenError> {
    let runtime = env.runtime;
    let fn_types = env.fn_types;
    let spec_registry = env.spec_registry;
    let fn_ids = env.fn_ids;
    let param_reprs = env.param_reprs;
    let return_reprs = env.return_reprs;
    let natively_callable = env.natively_callable;
    let closure_n_captures = env.closure_n_captures;
    let module = env.module;

    let callee_is_native = |id: u32| natively_callable.contains(&crate::fz_ir::FnId(id));
    // fz-uwq.5 — Cont dispatch reads from `fn_types.dispatches[cid]`
    // (per-spec dispatch fact; un-widened by fz-uwq.3+, so the SpecId
    // landed on by `spec_registry.resolve` matches what the codegen
    // recompute would land on by construction). The legacy registry-
    // recompute path is the fallback for the rare case where the
    // typer didn't record a dispatch for this cid.
    // fz-kgk + fz-uwq.12 — `fn_types.dispatches` keyed by the term's
    // intrinsic `CallsiteIdent` is the authoritative dispatch source.
    // The ident is positional-rewrite invariant (fuse moves the Term,
    // ident comes along); the legacy block_env recompute fallback is
    // gone.
    let resolve_cont_sid = |blk: &crate::fz_ir::Block, _continuation: &crate::fz_ir::Cont| -> u32 {
        let term_ident = blk
            .terminator
            .ident()
            .expect("resolve_cont_sid called on non-call-shape terminator");
        let cid = crate::fz_ir::CallsiteId {
            caller: caller_fn_id,
            ident: term_ident.clone(),
            slot: crate::fz_ir::EmitSlot::Cont,
        };
        let target = fn_types.dispatches.get(&cid).unwrap_or_else(|| {
            panic!(
                "fz-kgk: no dispatches entry for Cont at {:?} — typer-authoritative \
                 invariant violated",
                cid
            )
        });
        spec_registry
            .resolve(target.0, &target.1)
            .map(|s| s.0)
            .unwrap_or_else(|| {
                panic!(
                    "fz-kgk: dispatches[{:?}] = {:?} but no SpecId registered",
                    cid, target
                )
            })
    };
    // fz-qbg.2 — Resolve callee spec by querying with FLOW-NARROWED arg
    // Descrs from the current block's typer env (`fn_types.block_envs`),
    // not the def-site types (`fn_types.vars`). The dispatcher in
    // multi-clause (and any `if`/`case` pattern-bind narrowing) refines
    // an entry-block Var's type via per-block narrowing; the typer
    // registers callee specs keyed against that narrowing, so the
    // codegen lookup must use the same. Falls back to def-site when a
    // block env entry is absent (e.g. for Vars defined later in the
    // block — though calls in fz CPS-form only see args bound at or
    // before the terminator, so this is rare).
    let resolve_callee_sid_in = |_callee: crate::fz_ir::FnId,
                                 _args: &[crate::fz_ir::Var],
                                 _block_id: crate::fz_ir::BlockId,
                                 term_ident: &crate::fz_ir::CallsiteIdent|
     -> u32 {
        // fz-kgk + fz-uwq.12 — see resolve_cont_sid.
        let cid = crate::fz_ir::CallsiteId {
            caller: caller_fn_id,
            ident: term_ident.clone(),
            slot: crate::fz_ir::EmitSlot::Direct,
        };
        let target = fn_types.dispatches.get(&cid).unwrap_or_else(|| {
            panic!(
                "fz-kgk: no dispatches entry for Direct at {:?} — typer-authoritative \
                 invariant violated",
                cid
            )
        });
        spec_registry
            .resolve(target.0, &target.1)
            .map(|s| s.0)
            .unwrap_or_else(|| {
                panic!(
                    "fz-kgk: dispatches[{:?}] = {:?} but no SpecId registered",
                    cid, target
                )
            })
    };
    let resolve_callee_sid = |callee: crate::fz_ir::FnId, args: &[crate::fz_ir::Var]| -> u32 {
        let term_ident = blk
            .terminator
            .ident()
            .expect("resolve_callee_sid called on non-call-shape terminator");
        resolve_callee_sid_in(callee, args, blk.id, term_ident)
    };

    match &blk.terminator {
        Term::Goto(target, args) => {
            let tgt = *block_map.get(&target.0).unwrap();
            let arg_vals: Vec<BlockArg> = args
                .iter()
                .map(|v| BlockArg::Value(var_env.get(&v.0).expect("unbound goto arg").value))
                .collect();
            b.ins().jump(tgt, &arg_vals);
        }
        Term::If {
            cond: c,
            then_b: t,
            else_b: e,
            ..
        } => {
            let vb = var_env.get(&c.0).expect("unbound if cond");
            let t_b = *block_map.get(&t.0).unwrap();
            let e_b = *block_map.get(&e.0).unwrap();
            let no_args: Vec<BlockArg> = Vec::new();
            let truthy = if matches!(vb.repr, ArgRepr::Condition) {
                vb.value
            } else {
                is_truthy(b, cache, vb.value)
            };
            b.ins().brif(truthy, t_b, &no_args, e_b, &no_args);
        }
        Term::Halt(v) => {
            let val = var_env.get(&v.0).expect("unbound halt val").value;
            // fz-cps.1.2 — cont fns have no host_ctx (§2.1); their
            // Halt uses fz_halt_implicit which pulls process from TLS.
            // fz-cps.1.12 — all native fns use fz_halt_implicit too;
            // they no longer need host_ctx threading for halt.
            if is_cont_fn || is_native {
                let hi_fref = jmod.declare_func_in_func(runtime.halt_implicit_id, b.func);
                b.ins().call(hi_fref, &[val]);
            } else {
                let halt_fref = jmod.declare_func_in_func(runtime.halt_id, b.func);
                let hctx = host_ctx.expect("uniform fn always has host_ctx");
                b.ins().call(halt_fref, &[hctx, val]);
            }
            if is_native {
                // fz-ul4.27.6.4 — native fn: propagate halt via the
                // native return register. fz_halt already recorded
                // process.halt_value; the actual bits are unobservable
                // but the Cranelift sig requires a typed return.
                // fz-ul4.27.13: dead-code halt blocks (match_error etc.)
                // still need a well-typed return — iconst(0) satisfies
                // the i64 sig without depending on val's repr.
                let zero = b.ins().iconst(types::I64, 0);
                b.ins().return_(&[zero]);
            } else {
                // Uniform fn: trampoline sentinel is null.
                let null = b.ins().iconst(types::I64, 0);
                b.ins().return_(&[null]);
            }
        }
        Term::Return(v) => {
            let val = var_env.get(&v.0).expect("unbound return val").value;
            if is_native {
                // fz-ul4.27.22.3 — native Term::Return per docs/cps-in-clif.md
                // §2.1: `load cont+16; return_call_indirect sig(val, cont)`.
                // Cont fns fetch outer_cont from `self+24`; non-cont fns
                // use their cont_param SSA. Sig and val coerce match this
                // fn's narrow return_repr — the cont's body at +16 was
                // chosen at construction time to match (per fz-ul4.27.22.3
                // halt-cont typing + cont-seam narrowing in
                // build_fn_signature).
                //
                // fz-try.15 — closure-target bodies coerce to Tagged
                // unconditionally to match the seam ABI (matches
                // build_fn_signature's closure-target return = i64).
                // Cont fns retain narrow return_repr — they're not at
                // the indirect seam.
                let is_closure_target_body =
                    closure_n_captures.contains_key(&caller_fn_id) && !is_cont_fn;
                let my_return_repr = if is_closure_target_body {
                    ArgRepr::Tagged
                } else {
                    return_reprs[this_spec_id as usize]
                };
                let from = var_env.get(&v.0).map_or(ArgRepr::Tagged, |vb| vb.repr);
                let val_typed = coerce_to(b, jmod, runtime, val, from, my_return_repr);
                let cont_val = if is_cont_fn {
                    let self_val = cont_param.expect("cont fn binds self via cont_param");
                    b.ins().load(
                        types::I64,
                        MemFlags::trusted(),
                        self_val,
                        HEADER_SIZE + SLOT_BYTES,
                    )
                } else {
                    cont_param.expect("non-cont native fn has cont_param")
                };
                let code = b
                    .ins()
                    .load(types::I64, MemFlags::trusted(), cont_val, HEADER_SIZE);
                let mut sig = Signature::new(CallConv::Tail);
                sig.params.push(AbiParam::new(my_return_repr.cl_type()));
                sig.params.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
                let sigref = b.import_signature(sig);
                b.ins()
                    .return_call_indirect(sigref, code, &[val_typed, cont_val]);
            } else if cont_ptr_known_null {
                // fz-ul4.27.18: this fn is never a cont target; cont_ptr
                // is statically null. Skip the load/icmp/brif dispatch.
                emit_halt_and_return_null(
                    b,
                    jmod,
                    runtime,
                    host_ctx.expect(
                        "emit_halt_and_return_null needs host_ctx in a \
                         uniform fn (Term::Return uniform path)",
                    ),
                    val,
                );
            } else {
                emit_return(
                    b,
                    jmod,
                    runtime,
                    frame_ptr,
                    host_ctx.expect("emit_return needs host_ctx in a uniform fn"),
                    val,
                );
            }
        }
        Term::Call {
            ident: _,
            callee,
            args,
            continuation,
        } => {
            let cap_vals: Vec<ir::Value> = continuation
                .captured
                .iter()
                .map(|v| var_env.get(&v.0).expect("unbound captured val").value)
                .collect();
            // fz-ul4.29.7: resolve callee → narrow SpecId.0 (falls
            // back to any-key == callee.0 via subsumption).
            // fz-ul4.29.12.1: resolve the Cont to its narrow
            // SpecId.0 too (typer registers one per Cont site;
            // any-key is the subsumption backstop).
            let callee_sid = resolve_callee_sid(*callee, args);
            let cont_sid = resolve_cont_sid(blk, continuation);
            if callee_is_native(callee.0) {
                // fz-ul4.27.13 — coerce each arg from its current var
                // repr to the callee's param_repr. Result rides back
                // in the callee's return_repr; we then coerce it to
                // Tagged for the cont (cont is the any-key spec by
                // invariant — all-Tagged param_reprs, FzValue cont
                // frame slot 1).
                let callee_param_reprs = &param_reprs[callee_sid as usize];
                let callee_ret_repr = return_reprs[callee_sid as usize];
                let callee_fid = *fn_ids.get(&callee_sid).expect("callee fn_id missing");
                let callee_fref = jmod.declare_func_in_func(callee_fid, b.func);
                let mut native_args =
                    coerce_call_args(args, callee_param_reprs, var_env, b, jmod, runtime);
                // fz-cps.1.8 — if the callee is a closure-target fn,
                // its sig is `(args..., self, cont) tail`. Direct
                // callers load the per-Process static singleton and
                // pass it as `self`. The zero-cap invariant (asserted
                // at closure_target_fns build) means the body ignores
                // self at runtime, so a singleton with no captures is
                // valid for any direct-call site.
                if closure_n_captures.contains_key(callee) {
                    native_args.push(fetch_static_closure(jmod, b, runtime, callee.0));
                }
                // fz-cps.1.a: trailing cont arg per §2.1. Native
                // caller forwards its cont SSA; uniform caller passes
                // fz-cps.1.2 — chained-native cutover. Build the cont
                // closure BEFORE the callee call so the callee's
                // Term::Return can indirect-call through it (§2.1).
                // The closure's user captures must be stored before
                // the call too, since the cont body loads them on
                // entry. After the callee call, the chain unwinds
                // via halt-cont's regular return; the caller body
                // just returns whatever propagated.
                let cont_is_native = callee_is_native(continuation.fn_id.0);
                let cl_ptr_opt: Option<ir::Value> = if cont_is_native {
                    let cont_fid = *fn_ids.get(&cont_sid).expect("cont fn_id missing");
                    let cap_bindings: Vec<(ir::Value, ArgRepr)> = continuation
                        .captured
                        .iter()
                        .zip(cap_vals.iter())
                        .map(|(cv, &val)| {
                            let repr = var_env.get(&cv.0).map_or(ArgRepr::Tagged, |vb| vb.repr);
                            (val, repr)
                        })
                        .collect();
                    Some(build_cont_closure(
                        jmod,
                        b,
                        runtime,
                        return_reprs,
                        param_reprs,
                        is_cont_fn,
                        cont_param,
                        frame_ptr,
                        cont_sid,
                        cont_fid,
                        &cap_bindings,
                        /* captures_offset */ 1,
                        /* cont_stub_fid */ None,
                    ))
                } else {
                    None
                };
                // cont arg passed to the callee: cl_ptr for native cont,
                // else cont_param fallback (uniform-cont path). fz-cps.1.11:
                // when the cont-fn is uniform (rare; really only main's
                // halt-style cont after the parking-reachable lift) and
                // we have no cont_param, build a halt-cont closure inline
                // so the callee's Term::Return doesn't load through null+16.
                // synth_halt_cont tracks the latter: the callee chains
                // all the way into the halt-cont body, so the caller
                // must NOT execute its uniform-cont write-back after
                // the call (that would double-halt with the wrong value).
                let mut synth_halt_cont = false;
                let cont_arg = if let Some(cl_ptr) = cl_ptr_opt {
                    cl_ptr
                } else {
                    match cont_param {
                        Some(c) => c,
                        None => {
                            synth_halt_cont = true;
                            synthesize_halt_cont(jmod, b, runtime, callee_ret_repr)
                        }
                    }
                };
                native_args.push(cont_arg);

                if (cl_ptr_opt.is_some() || synth_halt_cont) && is_native {
                    // fz-cps.1.8 — native→native chained call uses
                    // return_call (TCO via Tail-CC). The callee's
                    // Term::Return tail-chains into the cont closure
                    // we built above. Matches §8.2 target clif.
                    // Repr invariant: natively_callable fixed-point guarantees
                    // return_reprs[this_spec_id] == callee_ret_repr here.
                    b.ins().return_call(callee_fref, &native_args);
                } else if cl_ptr_opt.is_some() || synth_halt_cont {
                    // Uniform caller → native callee (chained). Can't
                    // return_call across CC; synchronous call then
                    // return the chain-final value (halt_value already
                    // set by the time we get here). Call result is
                    // intentionally discarded — chain unwinds via halt-cont.
                    b.ins().call(callee_fref, &native_args);
                    let zero = b.ins().iconst(types::I64, 0);
                    b.ins().return_(&[zero]);
                } else {
                    let call_inst = b.ins().call(callee_fref, &native_args);
                    let result = b.inst_results(call_inst)[0];
                    let cont_schema = &schemas[cont_sid as usize];
                    let alloc_fref = jmod.declare_func_in_func(runtime.alloc_id, b.func);
                    let sid = b.ins().iconst(types::I32, cont_sid as i64);
                    let sz = b.ins().iconst(types::I32, cont_schema.size as i64);
                    let alloc_call = b.ins().call(alloc_fref, &[sid, sz]);
                    let cf = b.inst_results(alloc_call)[0];
                    let my_cont = b.ins().load(
                        types::I64,
                        MemFlags::trusted(),
                        frame_ptr.expect(
                            "Term::Call uniform-cont write-back reached from \
                             native-fn body — natively_callable invariant violated",
                        ),
                        HEADER_SIZE,
                    );
                    b.ins().store(MemFlags::trusted(), my_cont, cf, HEADER_SIZE);
                    // fz-ul4.29.12.1: result + captures are written
                    // into the cont's typed entry slots. `store_args
                    // _into_callee_frame` reads `cont_schema` per
                    // slot kind and unboxes from Tagged as needed.
                    let result_tagged =
                        coerce_to(b, jmod, runtime, result, callee_ret_repr, ArgRepr::Tagged);
                    let mut payload: Vec<ir::Value> =
                        Vec::with_capacity(continuation.captured.len() + 1);
                    payload.push(result_tagged);
                    for (cv, val) in continuation.captured.iter().zip(cap_vals.iter()) {
                        let from = var_env.get(&cv.0).map_or(ArgRepr::Tagged, |vb| vb.repr);
                        payload.push(coerce_to(b, jmod, runtime, *val, from, ArgRepr::Tagged));
                    }
                    store_args_into_callee_frame(b, cont_schema, cf, &payload, 1);
                    b.ins().return_(&[cf]);
                }
            } else {
                let arg_vals: Vec<ir::Value> = args
                    .iter()
                    .map(|v| var_env.get(&v.0).expect("unbound call arg").value)
                    .collect();
                emit_call(
                    b,
                    jmod,
                    runtime,
                    schemas,
                    frame_ptr,
                    callee_sid,
                    &arg_vals,
                    Some((cont_sid, &cap_vals)),
                );
            }
        }
        Term::TailCall {
            ident: _,
            callee,
            args,
            is_back_edge,
        } => {
            let callee_sid = resolve_callee_sid(*callee, args);
            if callee_is_native(callee.0) {
                // fz-ul4.27.6.2.3 / .27.13 — TailCall to a native callee.
                // Coerce each arg from its current var repr to the
                // callee's param_repr. The natively_callable fixed point
                // guarantees callee's return_repr matches mine, so
                // return_call is ABI-compatible without further coerce.
                let callee_param_reprs = &param_reprs[callee_sid as usize];
                let callee_ret_repr = return_reprs[callee_sid as usize];
                let callee_fid = *fn_ids.get(&callee_sid).expect("callee fn_id missing");
                let callee_fref = jmod.declare_func_in_func(callee_fid, b.func);
                let mut native_args =
                    coerce_call_args(args, callee_param_reprs, var_env, b, jmod, runtime);
                // fz-cps.1.8 — TailCall to a closure-target fn: insert
                // static singleton as `self` before cont. Mirror of
                // the Term::Call path; same zero-cap invariant lets
                // any singleton serve as self (body ignores it).
                if closure_n_captures.contains_key(callee) {
                    native_args.push(fetch_static_closure(jmod, b, runtime, callee.0));
                }
                // fz-cps.1.a: trailing cont arg per §2.1. fz-cps.1.11:
                // build halt-cont closure inline when uniform-tier
                // caller (cont_param=None) tail-calls native callee,
                // so the callee's Term::Return doesn't deref null.
                // fz-cps.1.12: cont fns forward outer_cont (loaded
                // from self+24); cont_param for cont fns is self.
                let mut synth_halt_cont = false;
                let tail_cont_arg = if is_cont_fn {
                    let self_val = cont_param.expect("cont fn binds self via cont_param");
                    b.ins().load(
                        types::I64,
                        MemFlags::trusted(),
                        self_val,
                        HEADER_SIZE + SLOT_BYTES,
                    )
                } else {
                    match cont_param {
                        Some(c) => c,
                        None => {
                            synth_halt_cont = true;
                            synthesize_halt_cont(jmod, b, runtime, callee_ret_repr)
                        }
                    }
                };
                native_args.push(tail_cont_arg);
                if is_native {
                    // Native-to-native TailCall: use return_call so
                    // recursive tail calls reuse the same stack frame
                    // (TCO). Without this, count_100k blows the stack.
                    //
                    // fz-02r.5 — back-edge cooperative yield check. When
                    // is_back_edge (annotated by annotate_back_edges in
                    // ir_lower), emit a 3-instruction guard: load
                    // FZ_SHOULD_YIELD, compare to zero, branch to the
                    // yield path if nonzero. The yield path writes all
                    // live args to mid_flight_roots, calls
                    // fz_yield_back_edge(spec_id, count), and returns
                    // the YIELD_PTR sentinel. On the scheduler side,
                    // gc_mid_flight forwards the slab, then a
                    // fz_mid_flight_resume_N shim re-enters the callee.
                    if *is_back_edge {
                        let yield_gv =
                            jmod.declare_data_in_func(runtime.should_yield_data_id, b.func);
                        let flag_ptr = b.ins().global_value(types::I64, yield_gv);
                        let flag = b.ins().load(types::I8, MemFlags::trusted(), flag_ptr, 0);
                        let flag64 = b.ins().uextend(types::I64, flag);
                        let zero64 = b.ins().iconst(types::I64, 0);
                        let is_set = b.ins().icmp(IntCC::NotEqual, flag64, zero64);
                        let yield_blk = b.create_block();
                        let proceed_blk = b.create_block();
                        let no_args: Vec<BlockArg> = Vec::new();
                        b.ins()
                            .brif(is_set, yield_blk, &no_args, proceed_blk, &no_args);

                        // yield block: write args to slab, call yield helper.
                        b.switch_to_block(yield_blk);
                        b.seal_block(yield_blk);
                        let roots_fref =
                            jmod.declare_func_in_func(runtime.mid_flight_roots_ptr_id, b.func);
                        let roots_call = b.ins().call(roots_fref, &[]);
                        let roots_ptr_val = b.inst_results(roots_call)[0];
                        debug_assert!(
                            native_args.len() <= 8,
                            "back-edge native_args ({}) exceeds mid_flight_roots slab (8)",
                            native_args.len()
                        );
                        for (i, &av) in native_args.iter().enumerate() {
                            b.ins()
                                .store(MemFlags::trusted(), av, roots_ptr_val, (i * 8) as i32);
                        }
                        let yield_fref =
                            jmod.declare_func_in_func(runtime.yield_back_edge_id, b.func);
                        // Pass the callee's raw code ptr (func_addr) so the
                        // scheduler can resume without a spec_id→ptr lookup.
                        let callee_ptr_v = b.ins().func_addr(types::I64, callee_fref);
                        let cnt_v = b.ins().iconst(types::I32, native_args.len() as i64);
                        let yield_inst = b.ins().call(yield_fref, &[callee_ptr_v, cnt_v]);
                        let yield_ret = b.inst_results(yield_inst)[0];
                        b.ins().return_(&[yield_ret]);

                        // proceed block: normal TCO.
                        b.switch_to_block(proceed_blk);
                        b.seal_block(proceed_blk);
                    }
                    b.ins().return_call(callee_fref, &native_args);
                } else if synth_halt_cont {
                    // fz-cps.1.11 — uniform caller + native callee
                    // with synthesized halt-cont: callee's chain runs
                    // all the way through halt_cont_body. Caller must
                    // NOT do post-call uniform write-back (would
                    // double-halt with the wrong value).
                    let _ = b.ins().call(callee_fref, &native_args);
                    let zero = b.ins().iconst(types::I64, 0);
                    b.ins().return_(&[zero]);
                } else {
                    // Uniform caller: synchronous call, then write result
                    // into MY cont's slot 1 (FzValue — cont result param
                    // stays `any` in the typer). Coerce result to Tagged.
                    let call_inst = b.ins().call(callee_fref, &native_args);
                    let result = b.inst_results(call_inst)[0];
                    let result_tagged =
                        coerce_to(b, jmod, runtime, result, callee_ret_repr, ArgRepr::Tagged);
                    let my_cont = b.ins().load(
                        types::I64,
                        MemFlags::trusted(),
                        frame_ptr.expect(
                            "Term::TailCall uniform-caller writeback reached from \
                             native-fn body — natively_callable invariant violated",
                        ),
                        HEADER_SIZE,
                    );
                    // Halt path: my_cont may be null on the top frame.
                    let zero = b.ins().iconst(types::I64, 0);
                    let is_null = b.ins().icmp(IntCC::Equal, my_cont, zero);
                    let halt_blk = b.create_block();
                    let invoke_blk = b.create_block();
                    let no_args: Vec<BlockArg> = Vec::new();
                    b.ins()
                        .brif(is_null, halt_blk, &no_args, invoke_blk, &no_args);
                    b.switch_to_block(halt_blk);
                    b.seal_block(halt_blk);
                    let halt_fref = jmod.declare_func_in_func(runtime.halt_id, b.func);
                    b.ins().call(
                        halt_fref,
                        &[
                            host_ctx.expect(
                                "TailCall uniform-caller halt branch needs \
                             host_ctx — uniform fns always have it",
                            ),
                            result_tagged,
                        ],
                    );
                    let null = b.ins().iconst(types::I64, 0);
                    b.ins().return_(&[null]);
                    b.switch_to_block(invoke_blk);
                    b.seal_block(invoke_blk);
                    b.ins().store(
                        MemFlags::trusted(),
                        result_tagged,
                        my_cont,
                        HEADER_SIZE + SLOT_BYTES,
                    );
                    b.ins().return_(&[my_cont]);
                }
            } else {
                let arg_vals: Vec<ir::Value> = args
                    .iter()
                    .map(|v| var_env.get(&v.0).expect("unbound tailcall arg").value)
                    .collect();
                emit_tail_call(
                    b,
                    jmod,
                    runtime,
                    schemas,
                    this_spec_id,
                    frame_ptr,
                    callee_sid,
                    &arg_vals,
                );
            }
        }
        Term::CallClosure {
            ident: _,
            closure,
            args,
            continuation,
        } => {
            // fz-ul4.29.5: load stub_fp from closure_ptr+16, build a
            // cont frame, then call_indirect through stub_fp. The stub
            // adapts the call into the callee's entry-frame layout.
            let cl_val = var_env
                .get(&closure.0)
                .expect("unbound callclosure closure")
                .value;
            let arg_vals: Vec<ir::Value> = args
                .iter()
                .map(|v| var_env.get(&v.0).expect("unbound callclosure arg").value)
                .collect();
            // fz-cps.1.2: build cont CLOSURE (not cont frame) per
            // §2.2. The closure-target callee's body indirect-calls
            // through cont+16 on Return, so the cont must be a
            // valid heap closure (code_ptr@+16, outer_cont@+24,
            // user captures from +32).
            let cont_sid = resolve_cont_sid(blk, continuation);
            let cont_fid = *fn_ids.get(&cont_sid).expect("cont fn_id missing");
            let cap_bindings: Vec<(ir::Value, ArgRepr)> = continuation
                .captured
                .iter()
                .map(|cv| {
                    let vb = var_env.get(&cv.0).expect("unbound captured val");
                    (vb.value, vb.repr)
                })
                .collect();
            let cf = build_cont_closure(
                jmod,
                b,
                runtime,
                return_reprs,
                param_reprs,
                is_cont_fn,
                cont_param,
                frame_ptr,
                cont_sid,
                cont_fid,
                &cap_bindings,
                /* captures_offset */ 1,
                /* cont_stub_fid */ None,
            );
            // fz-t45 — singleton closure-lit fast path for non-tail
            // closure calls. If this spec types `closure` as a single
            // closure_lit(F, K), resolve F's narrow body spec at
            // [K..., arg_descrs...] and call it directly with the
            // body's narrow ABI, threading the synthesized cont closure
            // as the callee's `cont` argument. Opaque / polymorphic
            // closures still fall back to the all-Tagged indirect seam.
            let lit_resolved: Option<(u32, FuncId, usize)> = (|| {
                let (body_fn_id, body_sid) =
                    resolve_tcc_body(closure, args, fn_types, module, spec_registry)?;
                let body_fid = *fn_ids.get(&body_sid)?;
                let n_caps = closure_n_captures.get(&body_fn_id).copied().unwrap_or(0);
                Some((body_sid, body_fid, n_caps))
            })();
            if let Some((body_sid, body_fid, n_caps)) = lit_resolved {
                let body_param_reprs = &param_reprs[body_sid as usize];
                let body_fref = jmod.declare_func_in_func(body_fid, b.func);
                let mut direct_args: Vec<ir::Value> = Vec::with_capacity(arg_vals.len() + 2);
                for (i, v) in arg_vals.iter().enumerate() {
                    let from = var_env
                        .get(&args[i].0)
                        .map_or(ArgRepr::Tagged, |vb| vb.repr);
                    let to = body_param_reprs
                        .get(n_caps + i)
                        .copied()
                        .unwrap_or(ArgRepr::Tagged);
                    direct_args.push(coerce_to(b, jmod, runtime, *v, from, to));
                }
                direct_args.push(cl_val);
                direct_args.push(cf);
                let _ = host_ctx;
                if is_native {
                    b.ins().return_call(body_fref, &direct_args);
                } else {
                    let call_inst = b.ins().call(body_fref, &direct_args);
                    let result = b.inst_results(call_inst)[0];
                    b.ins().return_(&[result]);
                }
                return Ok(());
            }
            // fz-cps.1.8 — load body's func_addr from cl+16 and Tail-CC
            // indirect-call with closure-target sig `(args..., self,
            // cont) -> i64 tail`. All-Tagged params. Native callers
            // use return_call_indirect (TCO); uniform callers use
            // call_indirect Tail (cross-CC) and return result.
            let body_fp = b
                .ins()
                .load(types::I64, MemFlags::trusted(), cl_val, HEADER_SIZE);
            let mut sig = Signature::new(CallConv::Tail);
            for _ in &arg_vals {
                sig.params.push(AbiParam::new(types::I64));
            }
            sig.params.push(AbiParam::new(types::I64)); // self
            sig.params.push(AbiParam::new(types::I64)); // cont
            sig.returns.push(AbiParam::new(types::I64));
            let sig_ref = b.func.import_signature(sig);
            let mut indirect_args: Vec<ir::Value> = Vec::with_capacity(arg_vals.len() + 2);
            for (i, v) in arg_vals.iter().enumerate() {
                let from = var_env
                    .get(&args[i].0)
                    .map_or(ArgRepr::Tagged, |vb| vb.repr);
                indirect_args.push(coerce_to(b, jmod, runtime, *v, from, ArgRepr::Tagged));
            }
            indirect_args.push(cl_val);
            indirect_args.push(cf);
            let _ = host_ctx; // no host_ctx in closure-target sig
            if is_native {
                b.ins()
                    .return_call_indirect(sig_ref, body_fp, &indirect_args);
            } else {
                let call_inst = b.ins().call_indirect(sig_ref, body_fp, &indirect_args);
                let result = b.inst_results(call_inst)[0];
                b.ins().return_(&[result]);
            }
        }
        Term::TailCallClosure {
            closure,
            args,
            ident: _,
        } => {
            // fz-cps.1.8 — Tail-CC indirect-call through cl+16 with
            // the caller's own cont (TCO via return_call_indirect).
            // Closure-target sig `(args..., self, cont) -> i64 tail`.
            // For cont fns, the forwarded cont is outer_cont from
            // self+24. For non-cont native fns, cont_param is the
            // cont SSA. Uniform callers load from frame_ptr+16.
            //
            // fz-ul4.27.22.11 — closure_lit fast path. When the closure
            // Var's per-spec Descr is a single closure_lit(F, K), resolve
            // F's narrow body spec at key [K..., arg_descrs...] and emit
            // a direct return_call. Bypasses the cl+16 indirect load and
            // uses the body's narrow ABI directly. Falls back to the
            // indirect path on union-of-lits, plain arrows, and
            // unresolved keys.
            let cl_val = var_env
                .get(&closure.0)
                .expect("unbound tailcallclosure closure")
                .value;
            let arg_vals: Vec<ir::Value> = args
                .iter()
                .map(|v| {
                    var_env
                        .get(&v.0)
                        .expect("unbound tailcallclosure arg")
                        .value
                })
                .collect();
            let my_cont = if is_cont_fn {
                let self_val = cont_param.expect("cont fn binds self via cont_param");
                b.ins().load(
                    types::I64,
                    MemFlags::trusted(),
                    self_val,
                    HEADER_SIZE + SLOT_BYTES,
                )
            } else {
                match cont_param {
                    Some(c) => c,
                    None => b.ins().load(
                        types::I64,
                        MemFlags::trusted(),
                        frame_ptr.expect("uniform TailCallClosure must have frame_ptr"),
                        HEADER_SIZE,
                    ),
                }
            };

            // fz-ul4.27.22.11 — try singleton resolution.
            let lit_resolved: Option<(u32, FuncId, usize)> = (|| {
                let (body_fn_id, body_sid) =
                    resolve_tcc_body(closure, args, fn_types, module, spec_registry)?;
                let body_fid = *fn_ids.get(&body_sid)?;
                let n_caps = closure_n_captures.get(&body_fn_id).copied().unwrap_or(0);
                Some((body_sid, body_fid, n_caps))
            })();

            if let Some((body_sid, body_fid, n_caps)) = lit_resolved {
                // Direct dispatch: build sig from body's narrow
                // param_reprs; emit return_call passing cl_val as self
                // and my_cont as cont.
                let body_param_reprs = &param_reprs[body_sid as usize];
                let mut sig = Signature::new(CallConv::Tail);
                // Closure-target sig: only arg slots [n_caps..] go on
                // the wire; capture slots live inside the closure heap
                // object and the body's entry harness loads them.
                for r in &body_param_reprs[n_caps..] {
                    sig.params.push(AbiParam::new(r.cl_type()));
                }
                sig.params.push(AbiParam::new(types::I64)); // self
                sig.params.push(AbiParam::new(types::I64)); // cont
                sig.returns.push(AbiParam::new(types::I64));
                let body_fref = jmod.declare_func_in_func(body_fid, b.func);
                let mut direct_args: Vec<ir::Value> = Vec::with_capacity(arg_vals.len() + 2);
                for (i, v) in arg_vals.iter().enumerate() {
                    let from = var_env
                        .get(&args[i].0)
                        .map_or(ArgRepr::Tagged, |vb| vb.repr);
                    let to = body_param_reprs
                        .get(n_caps + i)
                        .copied()
                        .unwrap_or(ArgRepr::Tagged);
                    direct_args.push(coerce_to(b, jmod, runtime, *v, from, to));
                }
                direct_args.push(cl_val);
                direct_args.push(my_cont);
                let _ = host_ctx;
                let _ = sig; // body_fref carries the signature implicitly.
                if is_native {
                    b.ins().return_call(body_fref, &direct_args);
                } else {
                    let call_inst = b.ins().call(body_fref, &direct_args);
                    let result = b.inst_results(call_inst)[0];
                    b.ins().return_(&[result]);
                }
            } else {
                // Existing indirect path (cl+16) for unresolved /
                // union-of-lits / plain-arrow closures.
                let body_fp = b
                    .ins()
                    .load(types::I64, MemFlags::trusted(), cl_val, HEADER_SIZE);
                let mut sig = Signature::new(CallConv::Tail);
                for _ in &arg_vals {
                    sig.params.push(AbiParam::new(types::I64));
                }
                sig.params.push(AbiParam::new(types::I64)); // self
                sig.params.push(AbiParam::new(types::I64)); // cont
                sig.returns.push(AbiParam::new(types::I64));
                let sig_ref = b.func.import_signature(sig);
                let mut indirect_args: Vec<ir::Value> = Vec::with_capacity(arg_vals.len() + 2);
                for (i, v) in arg_vals.iter().enumerate() {
                    let from = var_env
                        .get(&args[i].0)
                        .map_or(ArgRepr::Tagged, |vb| vb.repr);
                    indirect_args.push(coerce_to(b, jmod, runtime, *v, from, ArgRepr::Tagged));
                }
                indirect_args.push(cl_val);
                indirect_args.push(my_cont);
                let _ = host_ctx;
                if is_native {
                    b.ins()
                        .return_call_indirect(sig_ref, body_fp, &indirect_args);
                } else {
                    let call_inst = b.ins().call_indirect(sig_ref, body_fp, &indirect_args);
                    let result = b.inst_results(call_inst)[0];
                    b.ins().return_(&[result]);
                }
            }
        }
        Term::Receive {
            continuation,
            ident: _,
        } => {
            // fz-cps.1.2 Receive cutover per docs/cps-in-clif.md §4.
            // Build the cont closure (kind=Closure, code_ptr at +16,
            // synthetic outer_cont at +24, user captures from +32),
            // hand it to fz_receive_park which stashes the closure
            // in Process::parked_cont and returns YIELD sentinel.
            // On message arrival the scheduler will dispatch the
            // parked cont via a Cranelift thunk (fz-cps.1.2 follow-on).
            let cont_sid = resolve_cont_sid(blk, continuation);
            let cap_bindings: Vec<(ir::Value, ArgRepr)> = continuation
                .captured
                .iter()
                .map(|cv| {
                    let vb = var_env.get(&cv.0).expect("unbound receive cont capture");
                    (vb.value, vb.repr)
                })
                .collect();
            let cont_fid = *fn_ids.get(&cont_sid).expect("cont fn_id missing");
            let cl_ptr = build_cont_closure(
                jmod,
                b,
                runtime,
                return_reprs,
                param_reprs,
                is_cont_fn,
                cont_param,
                frame_ptr,
                cont_sid,
                cont_fid,
                &cap_bindings,
                /* captures_offset */ 1,
                /* cont_stub_fid */ None,
            );

            // fz_receive_park(cl_ptr) — stash + yield.
            let park_fref = jmod.declare_func_in_func(runtime.receive_park_id, b.func);
            let park_inst = b.ins().call(park_fref, &[cl_ptr]);
            let yield_sentinel = b.inst_results(park_inst)[0];
            if is_native {
                // Native body returns i64 (canonical); the yield
                // sentinel propagates back to the scheduler.
                b.ins().return_(&[yield_sentinel]);
            } else {
                // Uniform body returns next_frame ptr (here, YIELD
                // sentinel — trampoline parks the task).
                b.ins().return_(&[yield_sentinel]);
            }
        }
        // fz-70q.3 — selective-receive park-site CLIF.
        //
        // Layout, mirroring fz_runtime::park::ParkRecord:
        //   - matcher fn addr (declared/emitted by the pre-pass in
        //     compile_with_backend).
        //   - pinned[]: i64 array, one per `^name` referenced across
        //     all clauses, in source order.
        //   - clause_bodies[]: i64 array of cont-closure pointers,
        //     one per source clause; each closure's code_ptr at +16
        //     is the clause-body fn entry, captures laid out from
        //     +32 in source order (build_cont_closure handles all
        //     bookkeeping).
        //   - bound_arity: max bound-var count across clauses; sizes
        //     the `out` buffer the matcher fills on a hit.
        //   - after_deadline_or_neg1: -1 when no after clause,
        //     else the unboxed timeout in ms.
        //   - after_cont: closure ptr when after is Some, else null.
        //
        // After laying these out the arm calls fz_receive_park_matched
        // and returns the YIELD sentinel so the trampoline parks.
        Term::ReceiveMatched {
            clauses,
            after,
            pinned,
            captures,
            ident: _,
        } => {
            use cranelift_codegen::ir::{StackSlotData, StackSlotKind};

            let matcher_fid = *env
                .matcher_fn_ids
                .get(&(caller_fn_id.0, blk.id.0))
                .expect("matcher fn pre-declared by compile_with_backend pre-pass");
            let matcher_addr = fn_addr(jmod, matcher_fid, b);

            // Pinned snapshot: alloca [i64; n_pinned], store each
            // tagged value, take base addr.
            let n_pinned = pinned.len();
            let pinned_ptr = if n_pinned == 0 {
                b.ins().iconst(types::I64, 0)
            } else {
                let slot = b.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    (n_pinned * SLOT_BYTES as usize) as u32,
                    3,
                ));
                for (i, (_name, v)) in pinned.iter().enumerate() {
                    let tagged = tagged_get(var_env, b, jmod, runtime, v.0, cache);
                    b.ins().stack_store(tagged, slot, (i * 8) as i32);
                }
                b.ins().stack_addr(types::I64, slot, 0)
            };

            // Captures snapshot, shared across every clause body /
            // guard / after closure. `Term::ReceiveMatched::captures`
            // is already deduplicated by ir_lower; the cont fns'
            // capture-param slots line up with this order.
            let cap_bindings: Vec<(ir::Value, ArgRepr)> = captures
                .iter()
                .map(|cv| {
                    let vb = var_env.get(&cv.0).expect("unbound receive-matched capture");
                    (vb.value, vb.repr)
                })
                .collect();

            // bound_arity: max bound-var count across clauses (matcher
            // ABI sizes the out buffer to this).
            let bound_arity = clauses
                .iter()
                .map(|c| c.bound_names.len())
                .max()
                .unwrap_or(0);

            // clause_bodies[]: build one cont-closure per clause body
            // and stack-store its ptr.
            let n_clauses = clauses.len();
            assert!(
                n_clauses > 0,
                "ReceiveMatched with zero clauses should not reach codegen"
            );
            let bodies_slot = b.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                (n_clauses * SLOT_BYTES as usize) as u32,
                3,
            ));
            // Cap descrs for resolving clause body / after body specs
            // via spec_registry. Mirrors the typer's key construction
            // at ir_typer.rs:~1064: `[any; bound_arity] ++ cap_descrs`,
            // padded to body fn's entry-block arity. Body fns get a
            // narrow spec (not any-key) when captures carry non-any
            // Descrs, so we MUST resolve through the registry — the
            // FnId.0 == any-key SpecId invariant does not apply here.
            let any = crate::types_seam::concrete_any();
            let body_cap_tys: Vec<crate::types_seam::Ty> = captures
                .iter()
                .map(|cv| {
                    fn_types
                        .vars
                        .get(cv)
                        .cloned()
                        .unwrap_or_else(|| any.clone())
                })
                .collect();
            let resolve_body_sid = |body: crate::fz_ir::FnId, bound_arity: usize| -> u32 {
                let body_fn = env.module.fn_by_id(body);
                let np = body_fn.block(body_fn.entry).params.len();
                let mut key: Vec<crate::types_seam::Ty> = vec![any.clone(); bound_arity];
                key.extend(body_cap_tys.iter().cloned());
                while key.len() < np {
                    key.push(any.clone());
                }
                key.truncate(np);
                env.spec_registry
                    .resolve(body, &key)
                    .unwrap_or_else(|| {
                        panic!(
                            "matcher body fn_id {} key {:?} has no spec; \
                             typer emit at Term::ReceiveMatched may be missing",
                            body.0, key
                        )
                    })
                    .0
            };
            for (i, c) in clauses.iter().enumerate() {
                let cont_sid = resolve_body_sid(c.body, c.bound_names.len());
                let cont_fid = *fn_ids
                    .get(&cont_sid)
                    .expect("clause body sid has no FuncId");
                let cl_ptr = build_cont_closure(
                    jmod,
                    b,
                    runtime,
                    return_reprs,
                    param_reprs,
                    is_cont_fn,
                    cont_param,
                    frame_ptr,
                    cont_sid,
                    cont_fid,
                    &cap_bindings,
                    /* captures_offset */ c.bound_names.len(),
                    env.cont_stub_ids.get(&cont_sid).copied(),
                );
                b.ins().stack_store(cl_ptr, bodies_slot, (i * 8) as i32);
            }
            let bodies_ptr = b.ins().stack_addr(types::I64, bodies_slot, 0);

            // After: build the after closure if present and unbox the
            // timeout from its tagged Int. `-1` sentinel when no after.
            let (after_deadline_v, after_cont_v) = match after {
                Some(a) => {
                    let cont_sid = resolve_body_sid(a.body, 0);
                    let cont_fid = *fn_ids.get(&cont_sid).expect("after body sid has no FuncId");
                    let cl_ptr = build_cont_closure(
                        jmod,
                        b,
                        runtime,
                        return_reprs,
                        param_reprs,
                        is_cont_fn,
                        cont_param,
                        frame_ptr,
                        cont_sid,
                        cont_fid,
                        &cap_bindings,
                        /* captures_offset */ 0,
                        env.cont_stub_ids.get(&cont_sid).copied(),
                    );
                    // Timeout is a tagged FzValue::Int — shift right
                    // by 3 to recover the unboxed ms value.
                    let to_tagged = tagged_get(var_env, b, jmod, runtime, a.timeout.0, cache);
                    let unboxed = b.ins().sshr_imm(to_tagged, 3);
                    (unboxed, cl_ptr)
                }
                None => {
                    let neg1 = b.ins().iconst(types::I64, -1);
                    let nullp = b.ins().iconst(types::I64, 0);
                    (neg1, nullp)
                }
            };

            let n_pinned_v = b.ins().iconst(types::I64, n_pinned as i64);
            let n_clauses_v = b.ins().iconst(types::I64, n_clauses as i64);
            let bound_arity_v = b.ins().iconst(types::I32, bound_arity as i64);

            let park_fref = jmod.declare_func_in_func(runtime.receive_park_matched_id, b.func);
            let park_inst = b.ins().call(
                park_fref,
                &[
                    matcher_addr,
                    pinned_ptr,
                    n_pinned_v,
                    bodies_ptr,
                    n_clauses_v,
                    bound_arity_v,
                    after_deadline_v,
                    after_cont_v,
                ],
            );
            let yield_sentinel = b.inst_results(park_inst)[0];
            // Both native and uniform bodies return the YIELD
            // sentinel so the trampoline parks (same as Term::Receive).
            b.ins().return_(&[yield_sentinel]);
        }
    }
    Ok(())
}

fn compile_fn<M: cranelift_module::Module>(
    jmod: &mut M,
    ctx: &mut Context,
    fbctx: &mut FunctionBuilderContext,
    env: &CodegenEnv<'_>,
    schemas: &[Schema],
    f: &crate::fz_ir::FnIr,
    this_spec_id: u32,
    source: &crate::fz_ir::SourceInfo,
) -> Result<(), CodegenError> {
    let runtime = env.runtime;
    let fn_types = env.fn_types;
    let param_reprs = env.param_reprs;
    let natively_callable = env.natively_callable;
    let cont_target_fns = env.cont_target_fns;
    let cont_fns = env.cont_fns;
    let closure_n_captures = env.closure_n_captures;
    let is_native = natively_callable.contains(&f.id);
    let is_cont_fn = cont_fns.contains(&f.id);
    // fz-cps.1.2 — closure-target fn shape per §2.1: `(args..., self,
    // cont) tail`. Only takes effect for native fns; uniform fns still
    // go through the closure-stub adapter for now.
    let closure_target_n_caps: Option<usize> = if is_native && !is_cont_fn {
        closure_n_captures.get(&f.id).copied()
    } else {
        None
    };
    // fz-ul4.27.18: when this fn is never invoked from any fz IR site
    // (not a direct callee, not a continuation, not a closure target),
    // it can only enter via the trampoline entry, which writes null
    // into the frame's slot 0. cont_ptr is therefore statically null at
    // runtime; emit_return can elide the load/icmp/brif dispatch and
    // emit a halt-only path. The `cont_target_fns` parameter is the
    // upstream set of "ever referenced from fz IR" FnIds.
    let cont_ptr_known_null = !cont_target_fns.contains(&f.id);
    let callee_is_native = |id: u32| natively_callable.contains(&crate::fz_ir::FnId(id));
    let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);

    // fz-ul4.30 — reachability filter. `ir_lower` emits an unconditional
    // `fail_block` per fn (Halt with :function_clause atom) for clauses
    // whose patterns fail at runtime, and similar match-fail blocks for
    // `cond` / lambda bodies. Single-clause fns with bare-var params
    // never Goto their fail_block, leaving it as dead CLIF. Worse, the
    // dead Halt's `return` was previously typed `i64` regardless of the
    // fn's sig — under .27.13's per-Descr return type this trips the
    // Cranelift verifier (f64 sig vs i64 return). Skip emitting those
    // blocks entirely.
    let reachable_fz_blocks: std::collections::HashSet<u32> = {
        let blk_idx: HashMap<u32, &crate::fz_ir::Block> =
            f.blocks.iter().map(|b| (b.id.0, b)).collect();
        let mut reach: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let mut stack: Vec<u32> = vec![f.entry.0];
        while let Some(bid) = stack.pop() {
            if !reach.insert(bid) {
                continue;
            }
            let Some(blk) = blk_idx.get(&bid) else {
                continue;
            };
            match &blk.terminator {
                Term::Goto(t, _) => stack.push(t.0),
                Term::If { then_b, else_b, .. } => {
                    stack.push(then_b.0);
                    stack.push(else_b.0);
                }
                // Return / TailCall / Halt / Call / CallClosure /
                // TailCallClosure / Receive don't pass control to other
                // fz_ir blocks within this fn; codegen lowers them into
                // Cranelift sub-blocks owned by the lowering site itself.
                _ => {}
            }
        }
        reach
    };

    let mut block_map: HashMap<u32, ir::Block> = HashMap::new();
    for blk in &f.blocks {
        if !reachable_fz_blocks.contains(&blk.id.0) {
            continue;
        }
        let cl_blk = b.create_block();
        block_map.insert(blk.id.0, cl_blk);
    }
    let entry_cl = *block_map.get(&f.entry.0).unwrap();
    if is_native {
        // fz-ul4.27.6.2.3 / .27.13 — native fn entry: one block_param per
        // fz arg whose type matches my param_reprs[i] (F64 for raw float,
        // I64 for raw int or tagged), plus a trailing host_ctx i64. No
        // frame_ptr; native fns run synchronously inside their caller and
        // never visit the trampoline.
        let my_param_reprs = &param_reprs[this_spec_id as usize];
        if is_cont_fn {
            // fz-ul4.27.22.3 cont fn entry per §2.1: result's Cranelift
            // type matches my_param_reprs[0].cl_type() (RawInt=i64,
            // RawF64=f64, Tagged=i64). Body sees the value in its native
            // shape — no coerce at entry.
            //
            // fz-70q.3 — multi-input cont fns (ReceiveMatched clause
            // body / guard / after) override the default 1-extra shape
            // via `cont_extras_count`. Tail-CC sig becomes
            // `(extra_0, ..., extra_{N-1}, self:i64) tail`. Captures
            // never appear as Tail params — they're loaded from the
            // closure inside the body (see entry harness).
            let extras_count = env.cont_extras_count.get(&f.id).copied().unwrap_or(1);
            for r in &my_param_reprs[..extras_count] {
                b.append_block_param(entry_cl, r.cl_type());
            }
            b.append_block_param(entry_cl, types::I64); // self
        } else if let Some(n_caps) = closure_target_n_caps {
            // fz-cps.1.2 closure-target fn entry per §2.1:
            // `(args..., self:i64, cont:i64) tail`. n_args = total - n_caps.
            let n_args = my_param_reprs.len().saturating_sub(n_caps);
            for r in &my_param_reprs[..n_args] {
                b.append_block_param(entry_cl, r.cl_type());
            }
            b.append_block_param(entry_cl, types::I64); // self
            b.append_block_param(entry_cl, types::I64); // cont
        } else {
            for r in my_param_reprs {
                b.append_block_param(entry_cl, r.cl_type());
            }
            b.append_block_param(entry_cl, types::I64); // cont
        }
    } else {
        b.append_block_param(entry_cl, types::I64); // frame_ptr
        b.append_block_param(entry_cl, types::I64); // host_ctx
    }

    for blk in &f.blocks {
        if blk.id == f.entry {
            continue;
        }
        if !reachable_fz_blocks.contains(&blk.id.0) {
            continue;
        }
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        for _ in &blk.params {
            b.append_block_param(cl_blk, types::I64);
        }
    }

    b.switch_to_block(entry_cl);
    b.seal_block(entry_cl);

    let EntryHarnessOut {
        mut var_env,
        frame_ptr,
        host_ctx,
        cont_param,
    } = build_entry_harness(
        &mut b,
        jmod,
        env,
        schemas,
        f,
        this_spec_id,
        is_native,
        is_cont_fn,
        closure_target_n_caps,
        entry_cl,
    );

    let mut cache = {
        let (if_only, all_used) = crate::ir_dce::classify_var_uses(f);
        CodegenCache {
            if_only_conds: if_only.into_iter().map(|v| v.0).collect(),
            used_vars: all_used.into_iter().map(|v| v.0).collect(),
            ..CodegenCache::default()
        }
    };

    // Walk blocks in declared order with entry first. Unreachable
    // fz_ir blocks (fz-ul4.30) are filtered out — they have no
    // Cranelift counterpart.
    let mut order: Vec<&crate::fz_ir::Block> = Vec::with_capacity(f.blocks.len());
    if let Some(eb) = f.blocks.iter().find(|b| b.id == f.entry) {
        order.push(eb);
    }
    for blk in &f.blocks {
        if !reachable_fz_blocks.contains(&blk.id.0) {
            continue;
        }
        if blk.id != f.entry {
            order.push(blk);
        }
    }

    for blk in &order {
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        if blk.id != f.entry {
            b.switch_to_block(cl_blk);
            let params: Vec<ir::Value> = b.block_params(cl_blk).to_vec();
            for (p, val) in blk.params.iter().zip(params.iter()) {
                let mut types = crate::types_seam::ConcreteTypes;
                let repr = ArgRepr::for_block_param_ty(
                    &mut types,
                    &fn_types
                        .vars
                        .get(p)
                        .cloned()
                        .unwrap_or_else(crate::types_seam::concrete_any),
                );
                var_env.insert(p.0, VarBinding { value: *val, repr });
            }
        }

        // Per-stmt source location: ir_lower records spans into
        // SourceInfo.stmt_spans; encode each as a Cranelift SourceLoc so
        // `fz dump --emit clif` can render `; @file:line:col` comments.
        // fz-ul4.23.7.
        let stmt_spans = source.stmt_spans.get(&(f.id, blk.id));
        for (idx, stmt) in blk.stmts.iter().enumerate() {
            let span = stmt_spans
                .and_then(|v| v.get(idx))
                .copied()
                .unwrap_or(crate::diag::Span::DUMMY);
            b.set_srcloc(span_to_srcloc(span));
            let Stmt::Let(v, prim) = stmt;
            let out = lower_prim(
                &mut b, jmod, env, &var_env, prim, *v, &mut cache, f.id, blk.id, idx,
            )?;
            if !matches!(out, LowerOut::DeadUnit) {
                let repr = if out.is_raw_f64() {
                    ArgRepr::RawF64
                } else if out.is_raw_i64() {
                    ArgRepr::RawInt
                } else if out.is_condition() {
                    ArgRepr::Condition
                } else {
                    ArgRepr::Tagged
                };
                var_env.insert(
                    v.0,
                    VarBinding {
                        value: out.value(),
                        repr,
                    },
                );
            }
        }
        // Terminator gets its own srcloc (often the same as the last
        // stmt for Return blocks; distinct for Call/Goto).
        let term_span = source
            .term_span
            .get(&(f.id, blk.id))
            .copied()
            .unwrap_or(crate::diag::Span::DUMMY);
        b.set_srcloc(span_to_srcloc(term_span));

        // fz-ul4.27.5.2: tag the raw f64 vars that the terminator is
        // about to read. Other raw f64 vars in scope are dead past this
        // point and don't need boxing. Cross-block / cross-fn flow
        // operates on tagged FzValue (block params are i64; FzValue-kind
        // entry slots are tagged), so anything the terminator reaches
        // for must be materialised tagged first.
        let mut used_by_term: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let note = |vs: &[crate::fz_ir::Var], set: &mut std::collections::HashSet<u32>| {
            for v in vs {
                set.insert(v.0);
            }
        };
        match &blk.terminator {
            Term::Goto(_, args) => note(args, &mut used_by_term),
            Term::If { cond, .. } => {
                used_by_term.insert(cond.0);
            }
            Term::Halt(v) | Term::Return(v) => {
                used_by_term.insert(v.0);
            }
            Term::Call {
                ident: _,
                args,
                continuation,
                ..
            } => {
                note(args, &mut used_by_term);
                note(&continuation.captured, &mut used_by_term);
            }
            Term::TailCall { args, .. } => note(args, &mut used_by_term),
            Term::CallClosure {
                ident: _,
                closure,
                args,
                continuation,
            } => {
                used_by_term.insert(closure.0);
                note(args, &mut used_by_term);
                note(&continuation.captured, &mut used_by_term);
            }
            Term::TailCallClosure {
                closure,
                args,
                ident: _,
            } => {
                used_by_term.insert(closure.0);
                note(args, &mut used_by_term);
            }
            Term::Receive {
                continuation,
                ident: _,
            } => {
                note(&continuation.captured, &mut used_by_term);
            }
            // fz-yxs — every Var the matcher / clause-body shim will
            // read at runtime: pinned, captures, the timeout (if any).
            // Clause/after body FnIds are not Vars.
            Term::ReceiveMatched {
                pinned,
                captures,
                after,
                ..
            } => {
                for (_, v) in pinned {
                    used_by_term.insert(v.0);
                }
                note(captures, &mut used_by_term);
                if let Some(a) = after {
                    used_by_term.insert(a.timeout.0);
                }
            }
        }
        // fz-ul4.27.13 — Pre-terminator retag pass. Terminators that expect
        // tagged FzValue inputs across the board (Goto/If/Halt/CallClosure/
        // Receive, plus uniform Call/TailCall/Return) get their
        // used-by-term raw vars promoted here. Native Call/TailCall/Return
        // handle their own per-slot coerce inline at the branch below,
        // against the callee's `param_reprs` or this fn's own
        // `return_reprs` — skip the blanket retag for those.
        //
        // fz-ul4.27.22.12 — TailCallClosure also handles its own coerce
        // inline. On the direct-dispatch path (closure_lit-resolved), arg
        // slots match the body's narrow `param_reprs` so raw vars pass
        // through untagged. The indirect path's all-Tagged coerce runs
        // inside the else branch.
        let needs_blanket_retag = match &blk.terminator {
            Term::Return(_) => !is_native,
            Term::Call { callee, .. } => !callee_is_native(callee.0),
            Term::TailCall { callee, .. } => !callee_is_native(callee.0),
            Term::TailCallClosure { .. } => false,
            Term::Goto(..) => false, // handled per-arg below
            Term::Receive {
                continuation,
                ident: _,
            } => !callee_is_native(continuation.fn_id.0),
            _ => true,
        };
        if needs_blanket_retag {
            let mut to_retag: Vec<(u32, ArgRepr)> = var_env
                .iter()
                .filter(|(rv, vb)| {
                    used_by_term.contains(rv)
                        && vb.repr != ArgRepr::Tagged
                        && vb.repr != ArgRepr::Condition
                })
                .map(|(&rv, vb)| (rv, vb.repr))
                .collect();
            to_retag.sort_unstable_by_key(|(rv, _)| *rv);
            for (rv, repr) in to_retag {
                let raw = var_env.get(&rv).expect("raw var dropped from env").value;
                let boxed = match repr {
                    ArgRepr::RawF64 => box_float_native(&mut b, jmod, runtime, raw),
                    ArgRepr::RawInt => {
                        if let Some(&n) = cache.raw_int_consts.get(&rv) {
                            cached_iconst(&mut b, &mut cache, (n << 3) | TAG_INT)
                        } else {
                            box_int(&mut b, raw)
                        }
                    }
                    ArgRepr::Tagged | ArgRepr::Condition => {
                        unreachable!("Tagged/Condition in to_retag")
                    }
                };
                var_env.insert(
                    rv,
                    VarBinding {
                        value: boxed,
                        repr: ArgRepr::Tagged,
                    },
                );
            }
        }

        // fz-xs2 fz-ul4.rep.2: repr-aware Goto coercion.  Mirrors
        // coerce_call_args but for intra-function block edges.  Each arg is
        // coerced to the repr the target block param actually needs (derived
        // from fn_types.vars), so RawInt values flow through without a
        // box/unbox round-trip at inliner seams.
        if let Term::Goto(target, args) = &blk.terminator {
            for (param, arg) in f.block(*target).params.iter().zip(args.iter()) {
                let mut types = crate::types_seam::ConcreteTypes;
                let want = ArgRepr::for_block_param_ty(
                    &mut types,
                    &fn_types
                        .vars
                        .get(param)
                        .cloned()
                        .unwrap_or_else(crate::types_seam::concrete_any),
                );
                let vb = *var_env.get(&arg.0).expect("unbound goto arg");
                if vb.repr != want {
                    let coerced = coerce_to(&mut b, jmod, runtime, vb.value, vb.repr, want);
                    var_env.insert(
                        arg.0,
                        VarBinding {
                            value: coerced,
                            repr: want,
                        },
                    );
                }
            }
        }

        emit_terminator(
            &mut b,
            jmod,
            env,
            schemas,
            &var_env,
            blk,
            &block_map,
            is_native,
            is_cont_fn,
            this_spec_id,
            f.id,
            cont_ptr_known_null,
            frame_ptr,
            host_ctx,
            cont_param,
            &mut cache,
        )?;
    }

    for blk in &f.blocks {
        if !reachable_fz_blocks.contains(&blk.id.0) {
            continue;
        }
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        if blk.id != f.entry {
            b.seal_block(cl_blk);
        }
    }
    b.finalize();
    // fz-ul4.32.1 — publish Value -> Ty for the dump path. Only the
    // values bound to fz Vars are recorded; pure Cranelift intermediates
    // (iconst, ishl_imm, ...) stay unannotated. Pure overhead when
    // IR_TEXT_RECORD is disabled is the `with` + None-check.
    VALUE_DESCR_RECORD.with(|c| {
        if let Some(map) = c.borrow_mut().as_mut() {
            map.clear();
            for (var_id, vb) in &var_env {
                if let Some(d) = fn_types.vars.get(&crate::fz_ir::Var(*var_id)) {
                    map.insert(vb.value.as_u32(), d.clone());
                }
            }
        }
    });
    Ok(())
}

/// Term::Return: load my cont_ptr from frame[16]. If null, halt.
/// Otherwise write `val` to cont_frame[24] (continuation's "result" slot —
/// always entry param 0) and return cont_ptr.
///
/// fz-ul4.27.16: `frame_ptr` is `Option` because native fns don't have
/// a frame; the natively_callable invariant guarantees this helper is
/// never reached from a native fn body. Unwrapping with `.expect()`
/// turns any future invariant break into a loud panic at codegen time
/// rather than a silent load-from-zero.
fn emit_return<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    frame_ptr: Option<ir::Value>,
    host_ctx: ir::Value,
    val: ir::Value,
) {
    let frame_ptr = frame_ptr
        .expect("emit_return reached from native-fn body — natively_callable invariant violated");
    let cont_ptr = b
        .ins()
        .load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);
    // fz-ul4.27.17: one `iconst.i64 0` materialized in the entry block
    // serves both the null-compare and the halt-branch return sentinel.
    // SSA dominance lets the halt block reuse it; previously we emitted
    // a duplicate iconst inside the halt block.
    let zero = b.ins().iconst(types::I64, 0);
    let is_null = b.ins().icmp(IntCC::Equal, cont_ptr, zero);

    let halt_blk = b.create_block();
    let invoke_blk = b.create_block();
    let no_args: Vec<BlockArg> = Vec::new();
    b.ins()
        .brif(is_null, halt_blk, &no_args, invoke_blk, &no_args);

    // halt: fz_halt(host_ctx, val); return null (reusing `zero`).
    b.switch_to_block(halt_blk);
    b.seal_block(halt_blk);
    let halt_fref = jmod.declare_func_in_func(runtime.halt_id, b.func);
    b.ins().call(halt_fref, &[host_ctx, val]);
    b.ins().return_(&[zero]);

    // invoke: write val to cont[24], return cont_ptr.
    b.switch_to_block(invoke_blk);
    b.seal_block(invoke_blk);
    let result_off = HEADER_SIZE + SLOT_BYTES;
    b.ins()
        .store(MemFlags::trusted(), val, cont_ptr, result_off);
    b.ins().return_(&[cont_ptr]);
}

/// fz-ul4.27.18 — specialized emit_return for fns whose cont_ptr is
/// statically known to be null at runtime (i.e. fns that are never a
/// cont target anywhere in the module — they can only be invoked as
/// the trampoline entry, which writes null into slot 0). Skip the
/// `load v0+16; icmp eq 0; brif` dispatch and the dead invoke-branch
/// entirely; just `call fz_halt(host_ctx, val); return null`.
///
/// Takes no `frame_ptr` because none is read.
fn emit_halt_and_return_null<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    host_ctx: ir::Value,
    val: ir::Value,
) {
    let halt_fref = jmod.declare_func_in_func(runtime.halt_id, b.func);
    b.ins().call(halt_fref, &[host_ctx, val]);
    let null = b.ins().iconst(types::I64, 0);
    b.ins().return_(&[null]);
}

/// Term::Call: allocate continuation frame + callee frame. Continuation
/// frame = [my_cont_ptr, result_placeholder, ...captured]. Callee frame =
/// [cont_frame_ptr, ...args]. Return callee frame ptr.
fn emit_call<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    schemas: &[Schema],
    frame_ptr: Option<ir::Value>,
    callee_id: u32,
    args: &[ir::Value],
    cont: Option<(u32, &[ir::Value])>,
) {
    let frame_ptr = frame_ptr
        .expect("emit_call reached from native-fn body — natively_callable invariant violated");
    let alloc_fref = jmod.declare_func_in_func(runtime.alloc_id, b.func);

    // Read my cont_ptr from current frame[16] — this becomes the cont frame's cont_ptr.
    let my_cont = b
        .ins()
        .load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);

    let cont_frame_val = match cont {
        Some((cont_fn_id, captured)) => {
            let cont_schema = &schemas[cont_fn_id as usize];
            let sid = b.ins().iconst(types::I32, cont_fn_id as i64);
            let sz = b.ins().iconst(types::I32, cont_schema.size as i64);
            let call_inst = b.ins().call(alloc_fref, &[sid, sz]);
            let cf = b.inst_results(call_inst)[0];
            // Slot 0 (offset 16): cont_ptr = my_cont (my own continuation).
            b.ins().store(MemFlags::trusted(), my_cont, cf, HEADER_SIZE);
            // Slot 1 (offset 24) is the continuation's "result" param —
            // left uninitialized; will be filled by callee's Term::Return.
            // Slots 2..K+2: captured vars in declaration order. .5.4:
            // kind-aware store so a typed-int / typed-float captured slot
            // gets its raw payload, not a tagged FzValue.
            store_args_into_callee_frame(b, cont_schema, cf, captured, 2);
            cf
        }
        None => my_cont,
    };

    // Allocate callee frame.
    let callee_schema = &schemas[callee_id as usize];
    let sid = b.ins().iconst(types::I32, callee_id as i64);
    let sz = b.ins().iconst(types::I32, callee_schema.size as i64);
    let call_inst = b.ins().call(alloc_fref, &[sid, sz]);
    let callee_frame = b.inst_results(call_inst)[0];
    // Slot 0: cont_ptr = cont_frame_val.
    b.ins().store(
        MemFlags::trusted(),
        cont_frame_val,
        callee_frame,
        HEADER_SIZE,
    );
    // Slots 1..N+1: args. Each arg is tagged FzValue by the caller (the
    // pre-terminator tag pass in compile_fn made sure of it). If the
    // callee's slot is FieldKind::RawF64, unbox the tagged boxed-float
    // ptr to raw f64 here so the slot stores its declared kind — GC
    // tracer parity requires the slot's bytes match the schema.
    // fz-ul4.27.5.2.
    store_args_into_callee_frame(b, callee_schema, callee_frame, args, 1);

    b.ins().return_(&[callee_frame]);
}

/// Store `args` into the callee frame starting at slot index `slot_base`
/// (== 1 for normal calls — slot 0 is cont_ptr). Each arg is assumed
/// tagged FzValue (i64); the callee's slot kind drives whether to store
/// raw bytes or tagged FzValue. fz-ul4.27.5.2.
fn store_args_into_callee_frame(
    b: &mut FunctionBuilder<'_>,
    callee_schema: &Schema,
    callee_frame: ir::Value,
    args: &[ir::Value],
    slot_base: usize,
) {
    for (i, av) in args.iter().enumerate() {
        let slot_idx = slot_base + i;
        let off = HEADER_SIZE + SLOT_BYTES * (slot_idx as i32);
        match callee_schema.fields[slot_idx].kind {
            FieldKind::RawF64 => {
                // av is a tagged FzValue (heap ptr to boxed float). Read
                // the f64 payload and store it raw.
                let f = unbox_float(b, *av);
                b.ins().store(MemFlags::trusted(), f, callee_frame, off);
            }
            FieldKind::RawI64 => {
                // av is a tagged FzValue int `(n << 3) | 1`. Strip the
                // tag and store the raw i64. fz-ul4.27.5.3.
                let n = unbox_int(b, *av);
                b.ins().store(MemFlags::trusted(), n, callee_frame, off);
            }
            _ => {
                b.ins().store(MemFlags::trusted(), *av, callee_frame, off);
            }
        }
    }
}

/// Term::TailCall: if callee shares schema with caller, overwrite caller's
/// frame in place. Otherwise allocate a new frame. Either way, cont_ptr is
/// preserved (the parent's continuation).
fn emit_tail_call<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    schemas: &[Schema],
    self_id: u32,
    frame_ptr: Option<ir::Value>,
    callee_id: u32,
    args: &[ir::Value],
) {
    let frame_ptr = frame_ptr.expect(
        "emit_tail_call reached from native-fn body — natively_callable invariant violated",
    );
    let callee_schema = &schemas[callee_id as usize];

    if self_id == callee_id {
        // Same schema: overwrite slots 1..N+1 with new args. Slot 0 (cont) stays.
        store_args_into_callee_frame(b, callee_schema, frame_ptr, args, 1);
        b.ins().return_(&[frame_ptr]);
    } else {
        // Different schema: alloc fresh, copy cont_ptr, write args.
        let my_cont = b
            .ins()
            .load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);
        let alloc_fref = jmod.declare_func_in_func(runtime.alloc_id, b.func);
        let sid = b.ins().iconst(types::I32, callee_id as i64);
        let sz = b.ins().iconst(types::I32, callee_schema.size as i64);
        let call_inst = b.ins().call(alloc_fref, &[sid, sz]);
        let nf = b.inst_results(call_inst)[0];
        b.ins().store(MemFlags::trusted(), my_cont, nf, HEADER_SIZE);
        store_args_into_callee_frame(b, callee_schema, nf, args, 1);
        b.ins().return_(&[nf]);
    }
}

// fz-ul4.29.5: emit_call_closure / emit_tail_call_closure deleted.
// Term::CallClosure / TailCallClosure lower directly inline (load stub_fp
// from closure heap object, call_indirect through it). The closure cluster
// helpers (fz_closure_begin / push / finalize / arg / invoke / tail) are
// gone from the runtime; their work happens at compile time in stubs.

// fz-ul4.29.5: compile a closure stub. The stub is the adapter that
// the closure heap object's `stub_fp` points at. When CallClosure (or
// fz_spawn for the initial frame) invokes it, the stub:
//   1. Allocates the callee's entry frame (sized to the narrow spec).
//   2. Writes cont_ptr into slot 0 (offset 16).
//   3. Reads each capture as tagged FzValue from `closure_ptr + 24 + 8*k`
//      and stores it kind-aware into the callee frame's capture entry slot.
//   4. Writes each call arg into its entry slot, kind-aware.
//   5. Returns the callee frame for the trampoline.
//
// Closure-target bodies stay uniform-ABI in v1 (parking.rs:113 excludes
// `used_as_closure_target` fns from `natively_callable`). The native-
// callee branch is gated on .29.8 lifting that exclusion; for now we
// always go through the uniform frame-alloc path.

/// True when `v`'s typer-inferred Descr is a subtype of `int_top` — the
/// arithmetic dispatch elision pre-condition (.11.24.4).
fn descr_is_int(fn_types: &crate::ir_typer::FnTypes, v: crate::fz_ir::Var) -> bool {
    use crate::types_seam::Types;

    let mut t = crate::types_seam::ConcreteTypes;
    let want = t.int();
    let got = t.from_concrete_or_any(fn_types.vars.get(&v));
    t.is_subtype(&got, &want)
}

/// True when `v`'s typer-inferred Descr is a subtype of `float` — the
/// float-arithmetic dispatch elision pre-condition (fz-ul4.27.3).
fn descr_is_float(fn_types: &crate::ir_typer::FnTypes, v: crate::fz_ir::Var) -> bool {
    use crate::types_seam::Types;

    let mut t = crate::types_seam::ConcreteTypes;
    let want = t.float();
    let got = t.from_concrete_or_any(fn_types.vars.get(&v));
    t.is_subtype(&got, &want)
}

/// True when `v`'s typer-inferred Descr is a subtype of `atom_top`.
/// VR.5a: atom-monomorphic Eq/Neq lowers to a single icmp because two
/// FzValues with the same atom-id share the same bit pattern.
fn descr_is_atom(fn_types: &crate::ir_typer::FnTypes, v: crate::fz_ir::Var) -> bool {
    use crate::types_seam::Types;

    let mut t = crate::types_seam::ConcreteTypes;
    let want = t.atom();
    let got = t.from_concrete_or_any(fn_types.vars.get(&v));
    t.is_subtype(&got, &want)
}

/// True when `v` is statically nil-or-bool. Both occupy disjoint, fixed bit
/// patterns inside the tagged FzValue, so equality on them is bit-eq.
fn descr_is_nil_or_bool(fn_types: &crate::ir_typer::FnTypes, v: crate::fz_ir::Var) -> bool {
    use crate::types_seam::Types;

    let mut t = crate::types_seam::ConcreteTypes;
    let nil = t.nil();
    let bool_t = t.bool();
    let nb = t.union(nil, bool_t);
    let got = t.from_concrete_or_any(fn_types.vars.get(&v));
    t.is_subtype(&got, &nb)
}

/// True when the two operands' types have empty intersection — Eq folds to
/// false, Neq folds to true. VR.5a powers both the lowering shortcut and
/// the `type/dead-binop` diagnostic.
fn descrs_disjoint(
    fn_types: &crate::ir_typer::FnTypes,
    a: crate::fz_ir::Var,
    b: crate::fz_ir::Var,
) -> bool {
    use crate::types_seam::Types;

    let mut t = crate::types_seam::ConcreteTypes;
    match (fn_types.vars.get(&a), fn_types.vars.get(&b)) {
        (Some(da), Some(db)) => {
            let da = t.from_concrete(da);
            let db = t.from_concrete(db);
            t.is_disjoint(&da, &db)
        }
        _ => false,
    }
}

/// Output of `lower_prim`. Tagged is the common case (i64 FzValue bits);
/// RawF64 is what the typed-float fast paths return so subsequent ops on
/// the same SSA value can stay raw (fz-ul4.27.5.2). RawI64 is the same
/// idea for typed-int ops (fz-ul4.27.5.3) — the SSA value is the
/// unshifted int payload, not the `(n << 3) | TAG_INT` tagged form.
enum LowerOut {
    Tagged(ir::Value),
    RawF64(ir::Value),
    RawI64(ir::Value),
    /// Unit-return extern whose dest var is dead — no CLIF value emitted (fz-2tc).
    DeadUnit,
    /// Raw i1 from a boolean prim whose var is in `if_only_conds`; tagged form is
    /// never materialised unless tagged_get is called, which emits bool_to_fz lazily
    /// at the use site (fz-h4q).
    Condition(ir::Value),
}

impl LowerOut {
    fn value(&self) -> ir::Value {
        match self {
            LowerOut::Tagged(v)
            | LowerOut::RawF64(v)
            | LowerOut::RawI64(v)
            | LowerOut::Condition(v) => *v,
            LowerOut::DeadUnit => panic!("DeadUnit has no ir::Value"),
        }
    }
    fn is_raw_f64(&self) -> bool {
        matches!(self, LowerOut::RawF64(_))
    }
    fn is_raw_i64(&self) -> bool {
        matches!(self, LowerOut::RawI64(_))
    }
    fn is_condition(&self) -> bool {
        matches!(self, LowerOut::Condition(_))
    }
}

/// Lower collection-typed Prim variants (List, Tuple, AllocStruct, Bitstring,
/// Map, Vec) to a tagged `ir::Value`. Called by `lower_prim` for these arms.
fn lower_collection_prim<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, VarBinding>,
    prim: &Prim,
    cache: &mut CodegenCache,
) -> Result<ir::Value, CodegenError> {
    let runtime = env.runtime;
    let tuple_schema_ids = env.tuple_schema_ids;
    let v: ir::Value = match prim {
        Prim::ListCons(h, t) => {
            let hv = tagged_get(var_env, b, jmod, runtime, h.0, cache);
            let tv = tagged_get(var_env, b, jmod, runtime, t.0, cache);
            let fref = jmod.declare_func_in_func(runtime.alloc_cons_id, b.func);
            let inst = b.ins().call(fref, &[hv, tv]);
            b.inst_results(inst)[0]
        }
        Prim::ListHead(c) => {
            let cv = tagged_get(var_env, b, jmod, runtime, c.0, cache);
            b.ins().load(types::I64, MemFlags::trusted(), cv, 16)
        }
        Prim::ListTail(c) => {
            let cv = tagged_get(var_env, b, jmod, runtime, c.0, cache);
            b.ins().load(types::I64, MemFlags::trusted(), cv, 24)
        }
        Prim::MakeList(elems, tail) => {
            // fz-s9y.2 — the default tail of a list-literal is the empty
            // list (`[]`), NOT the nil atom value. They have distinct
            // runtime bit patterns now.
            let mut acc = match tail {
                Some(t) => tagged_get(var_env, b, jmod, runtime, t.0, cache),
                None => cached_iconst(b, cache, EMPTY_LIST_BITS),
            };
            let fref = jmod.declare_func_in_func(runtime.alloc_cons_id, b.func);
            for e in elems.iter().rev() {
                let ev = tagged_get(var_env, b, jmod, runtime, e.0, cache);
                let inst = b.ins().call(fref, &[ev, acc]);
                acc = b.inst_results(inst)[0];
            }
            acc
        }
        Prim::MakeTuple(elems) => {
            let arity = elems.len();
            let schema_id = *tuple_schema_ids.get(&arity).ok_or_else(|| {
                CodegenError::new(format!(
                    "tuple arity {} not pre-registered (compile() walk missed it?)",
                    arity
                ))
            })?;
            let fref = jmod.declare_func_in_func(runtime.alloc_struct_id, b.func);
            let sid = b.ins().iconst(types::I32, schema_id as i64);
            let inst = b.ins().call(fref, &[sid]);
            let p = b.inst_results(inst)[0];
            for (i, e) in elems.iter().enumerate() {
                let ev = tagged_get(var_env, b, jmod, runtime, e.0, cache);
                let off = HEADER_SIZE + (i as i32) * SLOT_BYTES;
                b.ins().store(MemFlags::trusted(), ev, p, off);
            }
            p
        }
        Prim::TupleField(c, idx) => {
            // fz-ul4.44 — `aligned` without `notrap`. Pre-fz-ben the load
            // was unconditional; `notrap` silently masked SIGSEGV-via-
            // garbage-read when the subject wasn't a tuple. Post-fz-ben
            // every TupleField is gated by a `Prim::TypeTest` (lowered at
            // `ir_lower.rs:1949`) that runtime-checks subject is a
            // matching-arity Struct heap value (fz-ul4.36 made the
            // TypeTest actually consult `descr.tuples`). The load is now
            // provably safe; SIGSEGV on a bad load would be an IR
            // integrity bug worth surfacing immediately.
            let cv = tagged_get(var_env, b, jmod, runtime, c.0, cache);
            let off = HEADER_SIZE + (*idx as i32) * SLOT_BYTES;
            let mut mf = MemFlags::new();
            mf.set_aligned();
            b.ins().load(types::I64, mf, cv, off)
        }
        Prim::AllocStruct(schema_id, fields) => {
            let fref = jmod.declare_func_in_func(runtime.alloc_struct_id, b.func);
            let sid = b.ins().iconst(types::I32, *schema_id as i64);
            let inst = b.ins().call(fref, &[sid]);
            let p = b.inst_results(inst)[0];
            for (i, fv) in fields.iter().enumerate() {
                let v = tagged_get(var_env, b, jmod, runtime, fv.0, cache);
                let off = HEADER_SIZE + (i as i32) * SLOT_BYTES;
                b.ins().store(MemFlags::trusted(), v, p, off);
            }
            p
        }
        Prim::MakeBitstring(fields) => {
            let begin = jmod.declare_func_in_func(runtime.bs_begin_id, b.func);
            b.ins().call(begin, &[]);
            let write = jmod.declare_func_in_func(runtime.bs_write_id, b.func);
            for f in fields {
                let value_v = tagged_get(var_env, b, jmod, runtime, f.value.0, cache);
                let ty_tag = b.ins().iconst(types::I32, encode_bit_type(f.ty) as i64);
                let unit = b
                    .ins()
                    .iconst(types::I32, f.unit.unwrap_or(default_unit_for(f.ty)) as i64);
                let endian = b.ins().iconst(types::I32, encode_endian(f.endian) as i64);
                let signed = b.ins().iconst(types::I32, f.signed as i64);
                let (size_present, size_value) = match &f.size {
                    None => (b.ins().iconst(types::I32, 0), b.ins().iconst(types::I32, 0)),
                    Some(crate::fz_ir::BitSizeIr::Literal(n)) => (
                        b.ins().iconst(types::I32, 1),
                        b.ins().iconst(types::I32, *n as i64),
                    ),
                    Some(crate::fz_ir::BitSizeIr::Var(v)) => {
                        let raw = tagged_get(var_env, b, jmod, runtime, v.0, cache);
                        let unb = unbox_int(b, raw);
                        let truncated = b.ins().ireduce(types::I32, unb);
                        (b.ins().iconst(types::I32, 1), truncated)
                    }
                };
                b.ins().call(
                    write,
                    &[
                        value_v,
                        ty_tag,
                        size_present,
                        size_value,
                        unit,
                        endian,
                        signed,
                    ],
                );
            }
            let fin = jmod.declare_func_in_func(runtime.bs_finalize_id, b.func);
            let inst = b.ins().call(fin, &[]);
            b.inst_results(inst)[0]
        }
        Prim::ConstBitstring(bytes, bit_len) => {
            // fz-q8d.2 — split paths by payload size:
            //   * Below threshold: intern bytes, call
            //     `fz_alloc_bitstring_const(ptr, byte_len, bit_len)`. The
            //     runtime allocates an inline HeapKind::Bitstring.
            //   * Above threshold: emit both a bytes-payload symbol and a
            //     40-byte static SharedBin symbol in `.data` (refcount=1
            //     anchor, relocs for bytes_ptr and the noop destructor),
            //     call `fz_alloc_procbin_from_static(static_ptr)`. The
            //     runtime retains the anchor and wraps a ProcBin around it.
            let above_threshold = bytes.len() > fz_runtime::heap::SHARED_BIN_THRESHOLD_BYTES;
            let syms = {
                let mut cache = env.bs_const_data.borrow_mut();
                if let Some(syms) = cache.get(bytes) {
                    // Cached. If the existing entry lacks the SharedBin
                    // symbol but this call site needs it, populate now.
                    let mut syms = *syms;
                    if above_threshold && syms.sharedbin_id.is_none() {
                        syms.sharedbin_id = Some(define_static_sharedbin(
                            jmod,
                            runtime,
                            syms.bytes_id,
                            bytes,
                            *bit_len,
                            cache.len(),
                        )?);
                        cache.insert(bytes.clone(), syms);
                    }
                    syms
                } else {
                    let idx = cache.len();
                    let bytes_name = format!(".fz_bs_const_{}", idx);
                    let bytes_id = jmod
                        .declare_data(&bytes_name, Linkage::Local, false, false)
                        .map_err(|e| CodegenError::new(format!("declare {}: {}", bytes_name, e)))?;
                    let mut desc = DataDescription::new();
                    // fz-wu9 — append invisible trailing NUL; not counted in
                    // the static SharedBin's bytes_len field. Underwrites the
                    // cstring extern marshal contract for literal binaries.
                    let mut payload: Vec<u8> = bytes.clone();
                    payload.push(0);
                    desc.define(payload.into_boxed_slice());
                    desc.set_align(1);
                    jmod.define_data(bytes_id, &desc)
                        .map_err(|e| CodegenError::new(format!("define {}: {}", bytes_name, e)))?;
                    let sharedbin_id = if above_threshold {
                        Some(define_static_sharedbin(
                            jmod, runtime, bytes_id, bytes, *bit_len, idx,
                        )?)
                    } else {
                        None
                    };
                    let syms = BsConstSyms {
                        bytes_id,
                        sharedbin_id,
                    };
                    cache.insert(bytes.clone(), syms);
                    syms
                }
            };
            if let Some(sb_id) = syms.sharedbin_id {
                let gv = jmod.declare_data_in_func(sb_id, b.func);
                let sb_ptr = b.ins().symbol_value(types::I64, gv);
                let fref = jmod.declare_func_in_func(runtime.alloc_procbin_from_static_id, b.func);
                let inst = b.ins().call(fref, &[sb_ptr]);
                b.inst_results(inst)[0]
            } else {
                let gv = jmod.declare_data_in_func(syms.bytes_id, b.func);
                let ptr_v = b.ins().symbol_value(types::I64, gv);
                let byte_len_v = b.ins().iconst(types::I64, bytes.len() as i64);
                let bit_len_v = b.ins().iconst(types::I64, *bit_len as i64);
                let fref = jmod.declare_func_in_func(runtime.alloc_bitstring_const_id, b.func);
                let inst = b.ins().call(fref, &[ptr_v, byte_len_v, bit_len_v]);
                b.inst_results(inst)[0]
            }
        }
        Prim::BitReaderInit(v) => {
            let vv = tagged_get(var_env, b, jmod, runtime, v.0, cache);
            let fref = jmod.declare_func_in_func(runtime.bs_reader_init_id, b.func);
            let inst = b.ins().call(fref, &[vv]);
            b.inst_results(inst)[0]
        }
        Prim::BitReadField {
            reader,
            ty,
            size,
            endian,
            signed,
            unit,
            is_last,
        } => {
            let rv = tagged_get(var_env, b, jmod, runtime, reader.0, cache);
            let ty_tag = b.ins().iconst(types::I32, encode_bit_type(*ty) as i64);
            let unit_v = b
                .ins()
                .iconst(types::I32, unit.unwrap_or(default_unit_for(*ty)) as i64);
            let endian_v = b.ins().iconst(types::I32, encode_endian(*endian) as i64);
            let signed_v = b.ins().iconst(types::I32, *signed as i64);
            let is_last_v = b.ins().iconst(types::I32, *is_last as i64);
            let (size_present, size_value) = match size {
                None => (b.ins().iconst(types::I32, 0), b.ins().iconst(types::I32, 0)),
                Some(crate::fz_ir::BitSizeIr::Literal(n)) => (
                    b.ins().iconst(types::I32, 1),
                    b.ins().iconst(types::I32, *n as i64),
                ),
                Some(crate::fz_ir::BitSizeIr::Var(v)) => {
                    let raw = tagged_get(var_env, b, jmod, runtime, v.0, cache);
                    let unb = unbox_int(b, raw);
                    let truncated = b.ins().ireduce(types::I32, unb);
                    (b.ins().iconst(types::I32, 1), truncated)
                }
            };
            let fref = jmod.declare_func_in_func(runtime.bs_read_field_id, b.func);
            let inst = b.ins().call(
                fref,
                &[
                    rv,
                    ty_tag,
                    size_present,
                    size_value,
                    unit_v,
                    endian_v,
                    signed_v,
                    is_last_v,
                ],
            );
            b.inst_results(inst)[0]
        }
        Prim::MakeMap(entries) => {
            let begin = jmod.declare_func_in_func(runtime.map_begin_id, b.func);
            b.ins().call(begin, &[]);
            let push = jmod.declare_func_in_func(runtime.map_push_id, b.func);
            for (k, v) in entries {
                let kv = tagged_get(var_env, b, jmod, runtime, k.0, cache);
                let vv = tagged_get(var_env, b, jmod, runtime, v.0, cache);
                b.ins().call(push, &[kv, vv]);
            }
            let fin = jmod.declare_func_in_func(runtime.map_finalize_id, b.func);
            let inst = b.ins().call(fin, &[]);
            b.inst_results(inst)[0]
        }
        Prim::MapUpdate(base, entries) => {
            let bv = tagged_get(var_env, b, jmod, runtime, base.0, cache);
            let cln = jmod.declare_func_in_func(runtime.map_clone_id, b.func);
            b.ins().call(cln, &[bv]);
            let push = jmod.declare_func_in_func(runtime.map_push_id, b.func);
            for (k, v) in entries {
                let kv = tagged_get(var_env, b, jmod, runtime, k.0, cache);
                let vv = tagged_get(var_env, b, jmod, runtime, v.0, cache);
                b.ins().call(push, &[kv, vv]);
            }
            let fin = jmod.declare_func_in_func(runtime.map_finalize_id, b.func);
            let inst = b.ins().call(fin, &[]);
            b.inst_results(inst)[0]
        }
        Prim::MapGet(m, k) => {
            let mv = tagged_get(var_env, b, jmod, runtime, m.0, cache);
            let kv = tagged_get(var_env, b, jmod, runtime, k.0, cache);
            let fref = jmod.declare_func_in_func(runtime.map_get_id, b.func);
            let inst = b.ins().call(fref, &[mv, kv]);
            b.inst_results(inst)[0]
        }
        Prim::MakeVec(kind, els) => {
            use crate::fz_ir::VecKindIr;
            use fz_runtime::fz_value::HeapKind;
            let kind_tag = match kind {
                VecKindIr::I64 => HeapKind::VecI64 as i64,
                VecKindIr::U8 => HeapKind::VecU8 as i64,
                VecKindIr::Bit => HeapKind::VecBit as i64,
                VecKindIr::F64 => {
                    return Err(CodegenError::new("MakeVec(F64) deferred to fz-ul4.11.23"));
                }
            };
            let begin = jmod.declare_func_in_func(runtime.vec_begin_id, b.func);
            let kt = b.ins().iconst(types::I32, kind_tag);
            b.ins().call(begin, &[kt]);
            let push = jmod.declare_func_in_func(runtime.vec_push_id, b.func);
            for ev in els {
                let v = tagged_get(var_env, b, jmod, runtime, ev.0, cache);
                b.ins().call(push, &[v]);
            }
            let fin = jmod.declare_func_in_func(runtime.vec_finalize_id, b.func);
            let inst = b.ins().call(fin, &[]);
            b.inst_results(inst)[0]
        }
        _ => unreachable!("lower_collection_prim: not a collection prim"),
    };
    Ok(v)
}

#[allow(clippy::too_many_arguments)]
fn lower_prim<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, VarBinding>,
    prim: &Prim,
    dest_var: crate::fz_ir::Var,
    cache: &mut CodegenCache,
    // fz-try B1+B2 — kept for call-site signature stability while we
    // route through the simplified MakeClosure lowering. The picker no
    // longer needs (caller, block, stmt) since the lambda body is
    // resolved directly by FnId.0 alignment.
    _caller_fn_id: crate::fz_ir::FnId,
    block_id: crate::fz_ir::BlockId,
    stmt_idx: usize,
) -> Result<LowerOut, CodegenError> {
    let runtime = env.runtime;
    let fn_types = env.fn_types;
    let spec_registry = env.spec_registry;
    let module = env.module;
    let fn_ids = env.fn_ids;
    let param_reprs = env.param_reprs;
    let return_reprs = env.return_reprs;
    // Helper: every consumer site below that wants a tagged FzValue uses
    // this. Sites that want a raw f64 (float fast paths only) call
    // `as_raw_f64` directly.
    //
    // The match below produces a *tagged* ir::Value for almost every prim.
    // The few prims that can produce a raw f64 (currently: typed float
    // BinOp::{Add,Sub,Mul,Div,Lt,Le,Gt,Ge,Eq,Neq}) early-return
    // `LowerOut::RawF64(_)` inside their arm. Everything else falls
    // through the match and is wrapped in `LowerOut::Tagged(_)` at the
    // bottom of the function.
    let v: ir::Value = match prim {
        Prim::Const(c) => match c {
            // fz-ul4.27.15.1: emit the raw payload when the consumer's
            // Descr is int-monomorphic. Tagged consumers retag via
            // `tagged_get` (= `box_int`) at their use site — same op
            // count as today's per-use unbox, just inverted. The wrapper
            // at the bottom of the match would otherwise wrap a tagged
            // `iconst((n<<3)|TAG_INT)` and every int-arithmetic /
            // RawInt-slot consumer would unbox via `as_raw_i64`.
            Const::Int(n) => {
                if descr_is_int(fn_types, dest_var) {
                    cache.raw_int_consts.insert(dest_var.0, *n);
                    return Ok(LowerOut::RawI64(b.ins().iconst(types::I64, *n)));
                }
                b.ins().iconst(types::I64, ((*n) << 3) | TAG_INT)
            }
            Const::True => cached_iconst(b, cache, TRUE_BITS),
            Const::False => cached_iconst(b, cache, FALSE_BITS),
            Const::Nil => cached_iconst(b, cache, NIL_BITS),
            Const::Atom(id) => cached_iconst(b, cache, ((*id as i64) << 3) | TAG_ATOM),
            Const::Float(f) => {
                // fz-ul4.27.15.2: emit a raw `f64const` when the consumer
                // is float-monomorphic. Tagged consumers heap-alloc via
                // `tagged_get` → `box_float_native` on demand. Skipping
                // the per-literal `fz_alloc_float` call when the literal
                // is consumed raw eliminates a runtime heap allocation
                // for every float literal that flows into float-arith,
                // a RawF64 slot, or `fz_print_f64`.
                if descr_is_float(fn_types, dest_var) {
                    return Ok(LowerOut::RawF64(b.ins().f64const(*f)));
                }
                // Tagged fallback: heap-alloc as before. v1 keeps const-pool
                // dedup for a future ticket — correct first.
                let bits = f.to_bits() as i64;
                let bv = b.ins().iconst(types::I64, bits);
                let fref = jmod.declare_func_in_func(runtime.alloc_float_id, b.func);
                let inst = b.ins().call(fref, &[bv]);
                b.inst_results(inst)[0]
            }
        },
        Prim::BinOp(op, a, bv) => {
            // .5.2: tagged operands are materialised lazily by `tag_a` /
            // `tag_b` below. The typed-float fast paths read raw via
            // `as_raw_f64` and never trigger the box round-trip; only the
            // tagged-path branches (int fast path, scalar Eq/Neq, dispatch
            // fallback) call `tag_a` / `tag_b` and pay the conversion.
            macro_rules! tag_a {
                () => {
                    tagged_get(var_env, b, jmod, runtime, a.0, cache)
                };
            }
            macro_rules! tag_b {
                () => {
                    tagged_get(var_env, b, jmod, runtime, bv.0, cache)
                };
            }
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    let mop = *op;
                    // Typed fast paths: float (skipped for Mod) and int.
                    if let Some(out) = try_typed_binop_fast_path(
                        fn_types,
                        *a,
                        *bv,
                        b,
                        var_env,
                        |b, af, bf| {
                            if matches!(mop, BinOp::Mod) {
                                return None;
                            }
                            Some(LowerOut::RawF64(match mop {
                                BinOp::Add => b.ins().fadd(af, bf),
                                BinOp::Sub => b.ins().fsub(af, bf),
                                BinOp::Mul => b.ins().fmul(af, bf),
                                BinOp::Div => b.ins().fdiv(af, bf),
                                _ => unreachable!(),
                            }))
                        },
                        |b, ai, bi| {
                            Some(LowerOut::RawI64(match mop {
                                BinOp::Add => b.ins().iadd(ai, bi),
                                BinOp::Sub => b.ins().isub(ai, bi),
                                BinOp::Mul => b.ins().imul(ai, bi),
                                BinOp::Div => b.ins().sdiv(ai, bi),
                                BinOp::Mod => b.ins().srem(ai, bi),
                                _ => unreachable!(),
                            }))
                        },
                    ) {
                        return Ok(out);
                    }
                    let av = tag_a!();
                    let bvv = tag_b!();
                    let fast_int = |b: &mut FunctionBuilder<'_>, av: ir::Value, bv: ir::Value| {
                        let ai = unbox_int(b, av);
                        let bi = unbox_int(b, bv);
                        let raw = match mop {
                            BinOp::Add => b.ins().iadd(ai, bi),
                            BinOp::Sub => b.ins().isub(ai, bi),
                            BinOp::Mul => b.ins().imul(ai, bi),
                            BinOp::Div => b.ins().sdiv(ai, bi),
                            BinOp::Mod => b.ins().srem(ai, bi),
                            _ => unreachable!(),
                        };
                        box_int(b, raw)
                    };
                    // fz-ul4.27.9: inlined float-arith slow path. Pre-resolve
                    // the FuncRefs the slow closure may call (jmod can't be
                    // captured into the closure). Promote both operands via
                    // fz_promote_f64, run the op natively (frem → fz_fmod
                    // since Cranelift has no native opcode), box via
                    // fz_alloc_float.
                    let pfref = jmod.declare_func_in_func(runtime.promote_f64_id, b.func);
                    let aref = jmod.declare_func_in_func(runtime.alloc_float_id, b.func);
                    let fmodref = jmod.declare_func_in_func(runtime.fmod_id, b.func);
                    let slow_arith =
                        move |b: &mut FunctionBuilder<'_>, av: ir::Value, bv: ir::Value| {
                            let i0 = b.ins().call(pfref, &[av]);
                            let af = b.inst_results(i0)[0];
                            let i1 = b.ins().call(pfref, &[bv]);
                            let bf = b.inst_results(i1)[0];
                            let raw_f = match mop {
                                BinOp::Add => b.ins().fadd(af, bf),
                                BinOp::Sub => b.ins().fsub(af, bf),
                                BinOp::Mul => b.ins().fmul(af, bf),
                                BinOp::Div => b.ins().fdiv(af, bf),
                                BinOp::Mod => {
                                    let inst = b.ins().call(fmodref, &[af, bf]);
                                    b.inst_results(inst)[0]
                                }
                                _ => unreachable!(),
                            };
                            let bits = b.ins().bitcast(types::I64, ir::MemFlags::new(), raw_f);
                            let inst = b.ins().call(aref, &[bits]);
                            b.inst_results(inst)[0]
                        };
                    emit_dispatch_binop(b, av, bvv, fast_int, slow_arith)
                }
                BinOp::Eq | BinOp::Neq => {
                    // VR.5a + .5.2.
                    let is_eq = matches!(op, BinOp::Eq);
                    let int_cc = if is_eq { IntCC::Equal } else { IntCC::NotEqual };
                    let f_cc = if is_eq {
                        FloatCC::Equal
                    } else {
                        FloatCC::NotEqual
                    };

                    // Kind-disjoint fold doesn't need either operand.
                    if descrs_disjoint(fn_types, *a, *bv) {
                        let bits = if is_eq { FALSE_BITS } else { TRUE_BITS };
                        return Ok(LowerOut::Tagged(b.ins().iconst(types::I64, bits)));
                    }
                    // Same-kind float: native fcmp on raw f64.
                    if descr_is_float(fn_types, *a) && descr_is_float(fn_types, *bv) {
                        let af = as_raw_f64(var_env, b, a.0);
                        let bf = as_raw_f64(var_env, b, bv.0);
                        let cmp = b.ins().fcmp(f_cc, af, bf);
                        if cache.if_only_conds.contains(&dest_var.0) {
                            return Ok(LowerOut::Condition(cmp));
                        }
                        return Ok(LowerOut::Tagged(bool_to_fz(b, cache, cmp)));
                    }
                    // Same-kind int: native icmp on raw i64. .5.3: must
                    // not mix raw and tagged operands — bit-eq is only
                    // correct when both are in the same encoding.
                    if descr_is_int(fn_types, *a) && descr_is_int(fn_types, *bv) {
                        let ai = as_raw_i64(var_env, b, a.0);
                        let bi = as_raw_i64(var_env, b, bv.0);
                        let cmp = b.ins().icmp(int_cc, ai, bi);
                        if cache.if_only_conds.contains(&dest_var.0) {
                            return Ok(LowerOut::Condition(cmp));
                        }
                        return Ok(LowerOut::Tagged(bool_to_fz(b, cache, cmp)));
                    }
                    let av = tag_a!();
                    let bvv = tag_b!();
                    if (descr_is_atom(fn_types, *a) && descr_is_atom(fn_types, *bv))
                        || (descr_is_nil_or_bool(fn_types, *a)
                            && descr_is_nil_or_bool(fn_types, *bv))
                    {
                        let cmp = b.ins().icmp(int_cc, av, bvv);
                        if cache.if_only_conds.contains(&dest_var.0) {
                            return Ok(LowerOut::Condition(cmp));
                        }
                        bool_to_fz(b, cache, cmp)
                    } else {
                        // Original dispatch (unchanged): both_ptr=true -> slow.
                        let cond = both_ptr(b, av, bvv);
                        let fast_blk = b.create_block();
                        let slow_blk = b.create_block();
                        let join_blk = b.create_block();
                        b.append_block_param(join_blk, types::I64);
                        let no_args: Vec<BlockArg> = Vec::new();
                        b.ins().brif(cond, slow_blk, &no_args, fast_blk, &no_args);

                        b.switch_to_block(fast_blk);
                        b.seal_block(fast_blk);
                        let cmp = b.ins().icmp(int_cc, av, bvv);
                        let fast_v = bool_to_fz(b, cache, cmp);
                        b.ins().jump(join_blk, &[BlockArg::Value(fast_v)]);

                        b.switch_to_block(slow_blk);
                        b.seal_block(slow_blk);
                        let fref = jmod.declare_func_in_func(runtime.value_eq_id, b.func);
                        let inst = b.ins().call(fref, &[av, bvv]);
                        let eq = b.inst_results(inst)[0];
                        let slow_v = if is_eq {
                            eq
                        } else {
                            b.ins().bxor_imm(eq, TRUE_BITS ^ FALSE_BITS)
                        };
                        b.ins().jump(join_blk, &[BlockArg::Value(slow_v)]);

                        b.switch_to_block(join_blk);
                        b.seal_block(join_blk);
                        b.block_params(join_blk)[0]
                    }
                }
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    let icc = match op {
                        BinOp::Lt => IntCC::SignedLessThan,
                        BinOp::Le => IntCC::SignedLessThanOrEqual,
                        BinOp::Gt => IntCC::SignedGreaterThan,
                        BinOp::Ge => IntCC::SignedGreaterThanOrEqual,
                        _ => unreachable!(),
                    };
                    let fcc = match op {
                        BinOp::Lt => FloatCC::LessThan,
                        BinOp::Le => FloatCC::LessThanOrEqual,
                        BinOp::Gt => FloatCC::GreaterThan,
                        BinOp::Ge => FloatCC::GreaterThanOrEqual,
                        _ => unreachable!(),
                    };
                    // Typed fast paths: float and int.
                    // Safety: the two closures are mutually exclusive — only the
                    // float arm fires for float operands and only the int arm fires
                    // for int operands, so the two reborrow sites never alias.
                    let dest_id = dest_var.0;
                    let cache_ptr = cache as *mut CodegenCache;
                    if let Some(out) = try_typed_binop_fast_path(
                        fn_types,
                        *a,
                        *bv,
                        b,
                        var_env,
                        |b, af, bf| {
                            let cmp = b.ins().fcmp(fcc, af, bf);
                            let cache_ref = unsafe { &mut *cache_ptr };
                            if cache_ref.if_only_conds.contains(&dest_id) {
                                return Some(LowerOut::Condition(cmp));
                            }
                            Some(LowerOut::Tagged(bool_to_fz(b, cache_ref, cmp)))
                        },
                        |b, ai, bi| {
                            let cmp = b.ins().icmp(icc, ai, bi);
                            let cache_ref = unsafe { &mut *cache_ptr };
                            if cache_ref.if_only_conds.contains(&dest_id) {
                                return Some(LowerOut::Condition(cmp));
                            }
                            Some(LowerOut::Tagged(bool_to_fz(b, cache_ref, cmp)))
                        },
                    ) {
                        return Ok(out);
                    }
                    let av = tag_a!();
                    let bvv = tag_b!();
                    // Safety: fast_int and slow_cmp run in blocks both dominated
                    // by the current block, so SSA values from the cached iconst
                    // are visible in both, and the two closures execute serially.
                    let cache_ptr = cache as *mut CodegenCache;
                    let fast_int =
                        move |b: &mut FunctionBuilder<'_>, av: ir::Value, bv: ir::Value| {
                            let ai = unbox_int(b, av);
                            let bi = unbox_int(b, bv);
                            let cmp = b.ins().icmp(icc, ai, bi);
                            bool_to_fz(b, unsafe { &mut *cache_ptr }, cmp)
                        };
                    // fz-ul4.27.9: inlined float-cmp slow path. Promote both
                    // operands to f64 and emit native fcmp.
                    let pfref = jmod.declare_func_in_func(runtime.promote_f64_id, b.func);
                    let fcc = match op {
                        BinOp::Lt => FloatCC::LessThan,
                        BinOp::Le => FloatCC::LessThanOrEqual,
                        BinOp::Gt => FloatCC::GreaterThan,
                        BinOp::Ge => FloatCC::GreaterThanOrEqual,
                        _ => unreachable!(),
                    };
                    let slow_cmp =
                        move |b: &mut FunctionBuilder<'_>, av: ir::Value, bv: ir::Value| {
                            let i0 = b.ins().call(pfref, &[av]);
                            let af = b.inst_results(i0)[0];
                            let i1 = b.ins().call(pfref, &[bv]);
                            let bf = b.inst_results(i1)[0];
                            let cmp = b.ins().fcmp(fcc, af, bf);
                            bool_to_fz(b, unsafe { &mut *cache_ptr }, cmp)
                        };
                    emit_dispatch_binop(b, av, bvv, fast_int, slow_cmp)
                }
                BinOp::And => {
                    let av = tag_a!();
                    let bvv = tag_b!();
                    let at = is_truthy(b, cache, av);
                    let bt = is_truthy(b, cache, bvv);
                    let conj = b.ins().band(at, bt);
                    if cache.if_only_conds.contains(&dest_var.0) {
                        return Ok(LowerOut::Condition(conj));
                    }
                    bool_to_fz(b, cache, conj)
                }
                BinOp::Or => {
                    let av = tag_a!();
                    let bvv = tag_b!();
                    let at = is_truthy(b, cache, av);
                    let bt = is_truthy(b, cache, bvv);
                    let disj = b.ins().bor(at, bt);
                    if cache.if_only_conds.contains(&dest_var.0) {
                        return Ok(LowerOut::Condition(disj));
                    }
                    bool_to_fz(b, cache, disj)
                }
            }
        }
        Prim::UnOp(op, x) => {
            match op {
                UnOp::Neg => {
                    // .5.3: read raw i64, native ineg, return raw — same
                    // shape as the BinOp int fast paths.
                    let xi = as_raw_i64(var_env, b, x.0);
                    return Ok(LowerOut::RawI64(b.ins().ineg(xi)));
                }
                UnOp::Not => {
                    let xv = tagged_get(var_env, b, jmod, runtime, x.0, cache);
                    let truthy = is_truthy(b, cache, xv);
                    let zero = b.ins().iconst(types::I8, 0);
                    let inv = b.ins().icmp(IntCC::Equal, truthy, zero);
                    if cache.if_only_conds.contains(&dest_var.0) {
                        return Ok(LowerOut::Condition(inv));
                    }
                    bool_to_fz(b, cache, inv)
                }
            }
        }
        Prim::Extern(eid, args) => {
            use crate::fz_ir::ExternTy;
            let decl = env.module.extern_by_id(*eid);
            let param_tys: Vec<ir::Type> = decl
                .params
                .iter()
                .map(|t| match t {
                    ExternTy::F64 => types::F64,
                    _ => types::I64,
                })
                .collect();
            let returns_value = !matches!(decl.ret, ExternTy::Unit | ExternTy::Never);
            let ret_tys: &[ir::Type] = if returns_value {
                match decl.ret {
                    ExternTy::F64 => &[types::F64],
                    _ => &[types::I64],
                }
            } else {
                &[]
            };
            let sig = sig1(&param_tys, ret_tys);
            let fref = if let Some(&cached) = cache.extern_funcs.get(eid) {
                cached
            } else {
                let func_id = jmod
                    .declare_function(&decl.symbol, Linkage::Import, &sig)
                    .map_err(|e| {
                        CodegenError::new(format!("declare extern `{}`: {}", decl.symbol, e))
                    })?;
                let fref = jmod.declare_func_in_func(func_id, b.func);
                cache.extern_funcs.insert(*eid, fref);
                fref
            };
            let param_kinds: Vec<ExternTy> = decl.params.clone();
            let arg_vals: Vec<ir::Value> = args
                .iter()
                .zip(param_kinds.iter())
                .map(|(v, ty)| match ty {
                    ExternTy::I64 => as_raw_i64(var_env, b, v.0),
                    ExternTy::F64 => as_raw_f64(var_env, b, v.0),
                    // fz-2yf — Binary/CString: call the runtime helper from
                    // [[fz-9ss]] with the tagged FzValue bits and use its
                    // returned `*const u8` as the C arg. Helper aborts on
                    // non-binary or non-byte-aligned bitstring.
                    ExternTy::Binary | ExternTy::CString => {
                        let helper_id = match ty {
                            ExternTy::CString => runtime.binary_as_cstring_id,
                            _ => runtime.binary_as_ptr_id,
                        };
                        let helper_fref = jmod.declare_func_in_func(helper_id, b.func);
                        let bits = tagged_get(var_env, b, jmod, runtime, v.0, cache);
                        let call = b.ins().call(helper_fref, &[bits]);
                        b.inst_results(call)[0]
                    }
                    _ => tagged_get(var_env, b, jmod, runtime, v.0, cache),
                })
                .collect();
            let inst = b.ins().call(fref, &arg_vals);
            if returns_value {
                let raw = b.inst_results(inst)[0];
                // fz-rb8 — `:: integer` returns a raw signed 64-bit C int;
                // box as a tagged FzValue::Int (`(n << 3) | TAG_INT`).
                let boxed = if matches!(decl.ret, ExternTy::I64) {
                    let shifted = b.ins().ishl_imm(raw, 3);
                    b.ins().bor_imm(shifted, TAG_INT)
                } else {
                    raw
                };
                return Ok(LowerOut::Tagged(boxed));
            }
            if cache.used_vars.contains(&dest_var.0) {
                return Ok(LowerOut::Tagged(cached_iconst(b, cache, NIL_BITS)));
            }
            return Ok(LowerOut::DeadUnit);
        }
        Prim::IsEmptyList(c) => {
            // fz-s9y.2 — compares to EMPTY_LIST_BITS (was NIL_BITS).
            // The empty list and the nil atom value are now distinct
            // bit patterns.
            let cv = tagged_get(var_env, b, jmod, runtime, c.0, cache);
            let empty_list_v = cached_iconst(b, cache, EMPTY_LIST_BITS);
            let cmp = b.ins().icmp(IntCC::Equal, cv, empty_list_v);
            if cache.if_only_conds.contains(&dest_var.0) {
                return Ok(LowerOut::Condition(cmp));
            }
            return Ok(LowerOut::Tagged(bool_to_fz(b, cache, cmp)));
        }
        Prim::BitReaderDone(r) => {
            let rv = tagged_get(var_env, b, jmod, runtime, r.0, cache);
            let bit_len_b = b.ins().load(types::I64, MemFlags::trusted(), rv, 24);
            let pos_b = b.ins().load(types::I64, MemFlags::trusted(), rv, 32);
            let cmp = b.ins().icmp(IntCC::Equal, bit_len_b, pos_b);
            if cache.if_only_conds.contains(&dest_var.0) {
                return Ok(LowerOut::Condition(cmp));
            }
            return Ok(LowerOut::Tagged(bool_to_fz(b, cache, cmp)));
        }
        Prim::ListCons(..)
        | Prim::ListHead(..)
        | Prim::ListTail(..)
        | Prim::MakeList(..)
        | Prim::MakeTuple(..)
        | Prim::TupleField(..)
        | Prim::AllocStruct(..)
        | Prim::MakeBitstring(..)
        | Prim::ConstBitstring(..)
        | Prim::BitReaderInit(..)
        | Prim::BitReadField { .. }
        | Prim::MakeMap(..)
        | Prim::MapUpdate(..)
        | Prim::MapGet(..)
        | Prim::MakeVec(..) => {
            return Ok(LowerOut::Tagged(lower_collection_prim(
                b, jmod, env, var_env, prim, cache,
            )?));
        }
        Prim::MakeClosure(mk_ident, fn_id, captured) => {
            // fz-ul4.29.5: alloc closure heap object via fz_alloc_closure;
            // store stub_fp at payload offset 16; write captures (tagged)
            // at offsets 24+i*8. Captures are always tagged FzValue in
            // the closure payload regardless of the callee's typed entry
            // slots — the stub handles tagged→raw conversion at invoke
            // time. fz-ul4.29.12.2: resolve this MakeClosure's narrow
            // SpecId via the lambda's full input-Descr key (captures
            // from caller's `fn_types`, args = `any`); pick the typed
            // stub keyed by that SpecId.
            let n_caps = captured.len();
            // fz-try B1+B2 — the lambda body is the any-key body spec
            // (SpecId.0 == FnId.0). Look up directly; fall back to any
            // registered narrow spec for this FnId when the any-key
            // was dropped; emit a null-stub closure when neither
            // exists (value is constructable but unreachable as a call
            // target).
            let _ = (block_id, stmt_idx, mk_ident); // fz-kgk: ident now intrinsic to the Prim.
            let cl_sid_opt = if fn_ids.contains_key(&fn_id.0) {
                Some(fn_id.0)
            } else {
                spec_registry
                    .iter()
                    .find(|(s, fid, _)| *fid == *fn_id && fn_ids.contains_key(&s.0))
                    .map(|(s, _, _)| s.0)
            };
            let Some(cl_sid) = cl_sid_opt else {
                // Null-stub closure: alloc, write null at +16, leave
                // capture slots uninitialized (the body that would read
                // them doesn't exist). halt_kind is irrelevant for an
                // un-invoked closure; pick 0.
                let alloc_fref = jmod.declare_func_in_func(runtime.alloc_closure_id, b.func);
                let fid_v = b.ins().iconst(types::I32, fn_id.0 as i64);
                let nc_v = b.ins().iconst(types::I32, n_caps as i64);
                let hk_v = b.ins().iconst(types::I32, 0);
                let inst = b.ins().call(alloc_fref, &[fid_v, nc_v, hk_v]);
                let cl_ptr = b.inst_results(inst)[0];
                let null = b.ins().iconst(types::I64, 0);
                b.ins()
                    .store(MemFlags::trusted(), null, cl_ptr, HEADER_SIZE);
                return Ok(LowerOut::Tagged(cl_ptr));
            };
            // fz-cps.1.7 — zero-capture MakeClosure: look up the
            // per-Process static singleton instead of allocating per call
            // site. fz-cps.1.8 — singleton's +16 holds the body's
            // func_addr (closure-target sig). docs/cps-in-clif.md §8.2.
            if captured.is_empty() {
                return Ok(LowerOut::Tagged(fetch_static_closure(
                    jmod, b, runtime, cl_sid,
                )));
            }
            // fz-cps.1.8 — non-zero captures: alloc closure heap object,
            // write body's func_addr at +16 (no stub), captures at +24+i*8.
            // The body has closure-target sig `(args..., self, cont) tail`
            // and loads captures from `self+24+i*8` in its entry harness.
            let body_func_id = *fn_ids.get(&cl_sid).ok_or_else(|| {
                CodegenError::new(format!(
                    "fz-cps.1.8: no body FuncId for closure SpecId({}) \
                     (FnId({}), {} captures)",
                    cl_sid, fn_id.0, n_caps
                ))
            })?;
            let alloc_fref = jmod.declare_func_in_func(runtime.alloc_closure_id, b.func);
            let fid_v = b.ins().iconst(types::I32, fn_id.0 as i64);
            let nc_v = b.ins().iconst(types::I32, n_caps as i64);
            // fz-ul4.27.22.6: halt_kind from body's return repr so
            // fz_spawn_entry can pick the matching halt-cont singleton.
            let body_return_repr = return_reprs[cl_sid as usize];
            let hk_v = b
                .ins()
                .iconst(types::I32, body_return_repr.halt_kind() as i64);
            let inst = b.ins().call(alloc_fref, &[fid_v, nc_v, hk_v]);
            let cl_ptr = b.inst_results(inst)[0];
            let body_addr = fn_addr(jmod, body_func_id, b);
            b.ins()
                .store(MemFlags::trusted(), body_addr, cl_ptr, HEADER_SIZE);
            // fz-try.15+B1+B2 — closure capture-storage ABI is uniform
            // Tagged at the seam. The body's entry harness loads i64
            // from self+24+8*k and coerces to its narrow capture repr
            // internally; storage must agree. (Same principle as the
            // return seam: bodies invokable via stub_fp can't agree on
            // narrow reprs, so the wire format is fixed.)
            let _ = &param_reprs; // capture-side now uses uniform Tagged
            for (i, cv) in captured.iter().enumerate() {
                let vb = var_env
                    .get(&cv.0)
                    .expect("MakeClosure: captured var unbound");
                let val = coerce_to(b, jmod, runtime, vb.value, vb.repr, ArgRepr::Tagged);
                let off = HEADER_SIZE + SLOT_BYTES + (i as i32) * SLOT_BYTES;
                b.ins().store(MemFlags::trusted(), val, cl_ptr, off);
            }
            cl_ptr
        }
        // fz-axu.23 (M2) — lower_program_full erases all Prim::Brand
        // before returning. If codegen sees one, ir_brand_erase didn't
        // run (or a caller injected Brand after lowering); surface it
        // loudly rather than silently lowering as identity.
        Prim::Brand(_, _) => unreachable!(
            "Prim::Brand reached codegen — erasure should run inside lower_program_full"
        ),

        Prim::TypeTest(v, descr) => {
            use crate::types::BasicBits;
            use fz_runtime::fz_value::HeapKind;
            let type_test = {
                use crate::types_seam::Types;

                let mut t = crate::types_seam::ConcreteTypes;
                let descr_ty = t.from_concrete(descr);
                t.type_test_shape(&descr_ty)
            };

            let val = tagged_get(var_env, b, jmod, runtime, v.0, cache);
            let tag3 = b.ins().band_imm(val, 7);

            // Scalar checks: safe unconditionally (no heap loads).
            let mut scalar: Option<ir::Value> = None;
            macro_rules! or_scalar {
                ($f:expr) => {
                    scalar = Some(match scalar.take() {
                        None => $f,
                        Some(p) => b.ins().bor(p, $f),
                    });
                };
            }
            // Pass 1 — scalar (tag-based) checks. Emits icmps that or-into
            // `scalar` and ignores heap-bearing axes.
            // fz-yan.2 — atoms axis covers what BasicBits::NIL and ::BOOL used
            // to cover (Descr::nil() and Descr::bool_t() are now atom literal
            // sets). For finite literal sets we icmp against each
            // (id << 3) | TAG_ATOM.
            if type_test.ints {
                let c = b.ins().icmp_imm(IntCC::Equal, tag3, TAG_INT);
                or_scalar!(c);
            }
            match &type_test.atoms {
                crate::types_seam::AtomTypeTest::None => {}
                crate::types_seam::AtomTypeTest::Any => {
                    let c = b.ins().icmp_imm(IntCC::Equal, tag3, TAG_ATOM);
                    or_scalar!(c);
                }
                crate::types_seam::AtomTypeTest::Cofinite => {
                    return Err(CodegenError::new(
                        "TypeTest: cofinite atom literal sets not yet implemented",
                    ));
                }
                crate::types_seam::AtomTypeTest::Finite(names) => {
                    let name_to_id: std::collections::HashMap<&str, u32> = module
                        .atom_names
                        .iter()
                        .enumerate()
                        .map(|(i, n)| (n.as_str(), i as u32))
                        .collect();
                    for name in names {
                        let Some(id) = name_to_id.get(name.as_str()).copied() else {
                            // Pattern wants an atom the module never interns
                            // -> no value can match; skip.
                            continue;
                        };
                        let bits = ((id as i64) << 3) | TAG_ATOM;
                        let c = b.ins().icmp_imm(IntCC::Equal, val, bits);
                        or_scalar!(c);
                    }
                }
            }

            // Pass 2 — heap-kind checks. Gated on is_ptr to avoid loading
            // header bytes from a non-pointer FzValue.
            let need_heap = type_test.floats
                || !type_test.basic.is_empty()
                || !type_test.tuple_arities.is_empty();

            let heap: Option<ir::Value> = if need_heap {
                let is_ptr = b.ins().icmp_imm(IntCC::Equal, tag3, 0i64);
                let heap_blk = b.create_block();
                let join_blk = b.create_block();
                b.append_block_param(join_blk, types::I8);
                let no_args: Vec<BlockArg> = Vec::new();
                let false8 = b.ins().iconst(types::I8, 0);
                b.ins().brif(
                    is_ptr,
                    heap_blk,
                    &no_args,
                    join_blk,
                    &[BlockArg::Value(false8)],
                );

                b.switch_to_block(heap_blk);
                b.seal_block(heap_blk);
                let kind_raw = b.ins().load(types::I16, MemFlags::trusted(), val, 0);
                let kind64 = b.ins().uextend(types::I64, kind_raw);

                let mut hf: Option<ir::Value> = None;
                macro_rules! or_heap {
                    ($f:expr) => {
                        hf = Some(match hf.take() {
                            None => $f,
                            Some(p) => b.ins().bor(p, $f),
                        });
                    };
                }
                if type_test.floats {
                    let c = b
                        .ins()
                        .icmp_imm(IntCC::Equal, kind64, HeapKind::Float as i64);
                    or_heap!(c);
                }
                for (bit, hk) in [
                    (BasicBits::VEC_I64, HeapKind::VecI64),
                    (BasicBits::VEC_F64, HeapKind::VecF64),
                    (BasicBits::VEC_U8, HeapKind::VecU8),
                    (BasicBits::VEC_BIT, HeapKind::VecBit),
                ] {
                    if type_test.basic.contains_all(bit) {
                        let c = b.ins().icmp_imm(IntCC::Equal, kind64, hk as i64);
                        or_heap!(c);
                    }
                }
                if type_test.tuple_has_negations {
                    panic!("TypeTest: negated tuple clauses not yet supported");
                }
                if !type_test.tuple_arities.is_empty() {
                    // fz-ul4.36 — tuple arity check via schema_id.
                    // size_bytes isn't arity-unique (alloc_struct aligns
                    // to 16: arity 1 & 2 -> 32, arity 3 & 4 -> 48), so
                    // the pre-registered Tuple{N} schema_id at
                    // HeapHeader offset 8 is authoritative.
                    let is_struct = b
                        .ins()
                        .icmp_imm(IntCC::Equal, kind64, HeapKind::Struct as i64);
                    let schema_raw = b.ins().load(types::I32, MemFlags::trusted(), val, 8);
                    let schema64 = b.ins().uextend(types::I64, schema_raw);
                    for arity in &type_test.tuple_arities {
                        if let Some(&sid) = env.tuple_schema_ids.get(arity) {
                            let want = b.ins().iconst(types::I64, sid as i64);
                            let schema_match = b.ins().icmp(IntCC::Equal, schema64, want);
                            let combined = b.ins().band(is_struct, schema_match);
                            or_heap!(combined);
                        }
                        // No schema id pre-registered -> no such tuple at
                        // runtime; contributes nothing.
                    }
                }
                let hr = hf.unwrap_or_else(|| b.ins().iconst(types::I8, 0));
                b.ins().jump(join_blk, &[BlockArg::Value(hr)]);

                b.switch_to_block(join_blk);
                b.seal_block(join_blk);
                Some(b.block_params(join_blk)[0])
            } else {
                None
            };

            let flag = match (scalar, heap) {
                (None, None) => b.ins().iconst(types::I8, 0),
                (Some(s), None) => s,
                (None, Some(h)) => h,
                (Some(s), Some(h)) => b.ins().bor(s, h),
            };
            if cache.if_only_conds.contains(&dest_var.0) {
                return Ok(LowerOut::Condition(flag));
            }
            bool_to_fz(b, cache, flag)
        }
    };
    Ok(LowerOut::Tagged(v))
}

/// Unbox an FzValue-tagged int (assumed Tag::Int — caller's responsibility) to
/// a raw i64 via arithmetic shift right.
fn unbox_int(b: &mut FunctionBuilder<'_>, v: ir::Value) -> ir::Value {
    b.ins().sshr_imm(v, 3)
}

#[derive(Clone, Copy)]
struct VarBinding {
    value: ir::Value,
    repr: ArgRepr,
}

/// Per-fn env: SSA value table for every Var in scope. For most Vars the
/// value is a tagged FzValue (i64). For Vars with RawF64 repr it is a raw
/// f64; RawInt is a raw i64 (the unshifted int payload). These exist so
/// arithmetic ops can chain without tag/untag round trips.
///
/// `tagged_get` is what every boundary site wants — it boxes raw vars lazily.
/// `as_raw_f64`/`as_raw_i64` are for the typed fast paths in `lower_prim`.
fn tagged_get<M: cranelift_module::Module>(
    var_env: &HashMap<u32, VarBinding>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    v: u32,
    cache: &mut CodegenCache,
) -> ir::Value {
    let vb = var_env.get(&v).expect("unbound var");
    match vb.repr {
        ArgRepr::RawF64 => box_float_native(b, jmod, runtime, vb.value),
        ArgRepr::RawInt => {
            if let Some(&n) = cache.raw_int_consts.get(&v) {
                cached_iconst(b, cache, (n << 3) | TAG_INT)
            } else {
                box_int(b, vb.value)
            }
        }
        ArgRepr::Tagged => vb.value,
        ArgRepr::Condition => bool_to_fz(b, cache, vb.value),
    }
}

/// Check if both BinOp args have narrow typed Descrs and, if so, apply
/// the matching fast-path closure. Returns Some(LowerOut) on a hit, None
/// to signal fall-through to the tagged slow path.
///
/// float_op / int_op each return Option<LowerOut> so callers can opt out
/// of a specific fast path (e.g. Mod has no float fast path → return None).
fn try_typed_binop_fast_path<F, I>(
    fn_types: &crate::ir_typer::FnTypes,
    a: crate::fz_ir::Var,
    bv: crate::fz_ir::Var,
    b: &mut FunctionBuilder<'_>,
    var_env: &HashMap<u32, VarBinding>,
    float_op: F,
    int_op: I,
) -> Option<LowerOut>
where
    F: FnOnce(&mut FunctionBuilder<'_>, ir::Value, ir::Value) -> Option<LowerOut>,
    I: FnOnce(&mut FunctionBuilder<'_>, ir::Value, ir::Value) -> Option<LowerOut>,
{
    if descr_is_float(fn_types, a) && descr_is_float(fn_types, bv) {
        let af = as_raw_f64(var_env, b, a.0);
        let bf = as_raw_f64(var_env, b, bv.0);
        if let Some(out) = float_op(b, af, bf) {
            return Some(out);
        }
    }
    if descr_is_int(fn_types, a) && descr_is_int(fn_types, bv) {
        let ai = as_raw_i64(var_env, b, a.0);
        let bi = as_raw_i64(var_env, b, bv.0);
        if let Some(out) = int_op(b, ai, bi) {
            return Some(out);
        }
    }
    None
}

fn as_raw_f64(
    var_env: &HashMap<u32, VarBinding>,
    b: &mut FunctionBuilder<'_>,
    v: u32,
) -> ir::Value {
    let vb = var_env.get(&v).expect("unbound var");
    if vb.repr == ArgRepr::RawF64 {
        vb.value
    } else {
        unbox_float(b, vb.value)
    }
}

fn as_raw_i64(
    var_env: &HashMap<u32, VarBinding>,
    b: &mut FunctionBuilder<'_>,
    v: u32,
) -> ir::Value {
    let vb = var_env.get(&v).expect("unbound var");
    if vb.repr == ArgRepr::RawInt {
        vb.value
    } else {
        unbox_int(b, vb.value)
    }
}

/// Emit `((a^1) | (b^1)) & 7 == 0` — true iff both operands are Tag::Int
/// (low 3 bits = 001). Used by arithmetic / ordered comparisons to choose
/// between the inline int fast-path and the boxed-float slow path.
fn both_int(b: &mut FunctionBuilder<'_>, av: ir::Value, bv: ir::Value) -> ir::Value {
    let xa = b.ins().bxor_imm(av, TAG_INT);
    let xb = b.ins().bxor_imm(bv, TAG_INT);
    let or_xab = b.ins().bor(xa, xb);
    let lo = b.ins().band_imm(or_xab, 7);
    b.ins().icmp_imm(IntCC::Equal, lo, 0)
}

/// Emit a tag-dispatched binary op: if both Tag::Int, run `fast`; else run
/// `slow`. fz-ul4.27.9: the slow arm is now caller-emitted (was a runtime
/// helper call), so promote+fadd+box (or promote+fcmp) lowers inline.
fn emit_dispatch_binop<F, S>(
    b: &mut FunctionBuilder<'_>,
    av: ir::Value,
    bv: ir::Value,
    fast: F,
    slow: S,
) -> ir::Value
where
    F: FnOnce(&mut FunctionBuilder<'_>, ir::Value, ir::Value) -> ir::Value,
    S: FnOnce(&mut FunctionBuilder<'_>, ir::Value, ir::Value) -> ir::Value,
{
    let cond = both_int(b, av, bv);
    let fast_blk = b.create_block();
    let slow_blk = b.create_block();
    let join_blk = b.create_block();
    b.append_block_param(join_blk, types::I64);
    let no_args: Vec<BlockArg> = Vec::new();
    b.ins().brif(cond, fast_blk, &no_args, slow_blk, &no_args);

    b.switch_to_block(fast_blk);
    b.seal_block(fast_blk);
    let fast_v = fast(b, av, bv);
    b.ins().jump(join_blk, &[BlockArg::Value(fast_v)]);

    b.switch_to_block(slow_blk);
    b.seal_block(slow_blk);
    let slow_v = slow(b, av, bv);
    b.ins().jump(join_blk, &[BlockArg::Value(slow_v)]);

    b.switch_to_block(join_blk);
    b.seal_block(join_blk);
    b.block_params(join_blk)[0]
}

/// True iff BOTH operands are Tag::Ptr (low 3 bits = 000). Used by Eq/Neq
/// to dispatch to fz_value_eq only when there's actually a heap value to
/// inspect; (Ptr, Int) and other cross-tag pairs are correctly handled by
/// raw bit-eq (always false: ptr bits never alias non-ptr tags).
fn both_ptr(b: &mut FunctionBuilder<'_>, av: ir::Value, bv: ir::Value) -> ir::Value {
    let or_ab = b.ins().bor(av, bv);
    let lo = b.ins().band_imm(or_ab, 7);
    b.ins().icmp_imm(IntCC::Equal, lo, 0)
}

/// Box a raw i64 into an FzValue-tagged int: `(n << 3) | TAG_INT`.
fn box_int(b: &mut FunctionBuilder<'_>, raw: ir::Value) -> ir::Value {
    let shifted = b.ins().ishl_imm(raw, 3);
    b.ins().bor_imm(shifted, TAG_INT)
}

/// fz-ul4.27.13 — Coerce a Cranelift value between ArgReprs. `RawInt` ↔
/// `RawF64` direct conversion is intentionally unsupported (no Descr admits
/// both; if it surfaces, the typer or call-site narrowing is wrong).
fn fetch_static_closure<M: cranelift_module::Module>(
    jmod: &mut M,
    b: &mut FunctionBuilder<'_>,
    runtime: &RuntimeRefs,
    spec_id: u32,
) -> ir::Value {
    let fref = jmod.declare_func_in_func(runtime.get_static_closure_id, b.func);
    let sid_v = b.ins().iconst(types::I32, spec_id as i64);
    let inst = b.ins().call(fref, &[sid_v]);
    b.inst_results(inst)[0]
}

fn coerce_call_args<M: cranelift_module::Module>(
    args: &[crate::fz_ir::Var],
    callee_param_reprs: &[ArgRepr],
    var_env: &HashMap<u32, VarBinding>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
) -> Vec<ir::Value> {
    let mut out: Vec<ir::Value> = Vec::with_capacity(args.len() + 1);
    for (i, av) in args.iter().enumerate() {
        let raw_val = var_env.get(&av.0).expect("unbound call arg").value;
        let from = var_env.get(&av.0).map_or(ArgRepr::Tagged, |vb| vb.repr);
        let to = callee_param_reprs[i];
        out.push(coerce_to(b, jmod, runtime, raw_val, from, to));
    }
    out
}

fn coerce_to<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    val: ir::Value,
    from: ArgRepr,
    to: ArgRepr,
) -> ir::Value {
    if from == to {
        return val;
    }
    match (from, to) {
        (ArgRepr::Tagged, ArgRepr::RawInt) => unbox_int(b, val),
        (ArgRepr::Tagged, ArgRepr::RawF64) => unbox_float(b, val),
        (ArgRepr::RawInt, ArgRepr::Tagged) => box_int(b, val),
        (ArgRepr::RawF64, ArgRepr::Tagged) => box_float_native(b, jmod, runtime, val),
        (ArgRepr::RawInt, ArgRepr::RawF64) => {
            let tagged = box_int(b, val);
            unbox_float(b, tagged)
        }
        (ArgRepr::RawF64, ArgRepr::RawInt) => {
            let tagged = box_float_native(b, jmod, runtime, val);
            unbox_int(b, tagged)
        }
        (ArgRepr::Condition, _) | (_, ArgRepr::Condition) => {
            unreachable!("Condition vars are never coerced")
        }
        (ArgRepr::Tagged, ArgRepr::Tagged)
        | (ArgRepr::RawInt, ArgRepr::RawInt)
        | (ArgRepr::RawF64, ArgRepr::RawF64) => {
            unreachable!("same-repr coerce: handled by early return")
        }
    }
}

/// Load the f64 payload of a boxed-float FzValue. The boxed-float heap
/// layout is `HeapHeader (16 bytes) + f64 payload (8 bytes)`; the tagged
/// FzValue's bits are the heap ptr (Tag::Ptr has tag bits 000). Caller
/// must already have proven Tag::Ptr+HeapKind::Float via the typer
/// (descr_is_float). fz-ul4.27.3.
fn unbox_float(b: &mut FunctionBuilder<'_>, v: ir::Value) -> ir::Value {
    b.ins().load(types::F64, MemFlags::trusted(), v, 16)
}

/// Heap-allocate a fresh boxed float from a raw f64 and return its
/// FzValue ptr-bits. Bitcasts the f64 to i64 (the wire form fz_alloc_float
/// expects) and calls fz_alloc_float. fz-ul4.27.3.
fn box_float_native<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    f: ir::Value,
) -> ir::Value {
    let bits = b.ins().bitcast(types::I64, ir::MemFlags::new(), f);
    let fref = jmod.declare_func_in_func(runtime.alloc_float_id, b.func);
    let inst = b.ins().call(fref, &[bits]);
    b.inst_results(inst)[0]
}

fn cached_iconst(b: &mut FunctionBuilder<'_>, cache: &mut CodegenCache, val: i64) -> ir::Value {
    if let Some(blk) = b.current_block() {
        if let Some(&v) = cache.const_cache.get(&(blk, val)) {
            return v;
        }
        let v = b.ins().iconst(types::I64, val);
        cache.const_cache.insert((blk, val), v);
        return v;
    }
    b.ins().iconst(types::I64, val)
}

/// Returns an i8 (0/1) indicating whether `v` is truthy: not nil and not false.
fn is_truthy(b: &mut FunctionBuilder<'_>, cache: &mut CodegenCache, v: ir::Value) -> ir::Value {
    let nil_v = cached_iconst(b, cache, NIL_BITS);
    let false_v = cached_iconst(b, cache, FALSE_BITS);
    let not_nil = b.ins().icmp(IntCC::NotEqual, v, nil_v);
    let not_false = b.ins().icmp(IntCC::NotEqual, v, false_v);
    b.ins().band(not_nil, not_false)
}

/// Convert an i8 cranelift bool to FzValue::TRUE / FzValue::FALSE.
fn bool_to_fz(b: &mut FunctionBuilder<'_>, cache: &mut CodegenCache, v: ir::Value) -> ir::Value {
    let true_v = cached_iconst(b, cache, TRUE_BITS);
    let false_v = cached_iconst(b, cache, FALSE_BITS);
    b.ins().select(v, true_v, false_v)
}

#[cfg(test)]
thread_local! {
    static INLINE_DISABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// fz-jg5.6 — disable the compile-time reducer for tests that
    /// exercise codegen infrastructure (static_closure_targets,
    /// stub_fp paths, etc.) whose triggering inputs the reducer would
    /// dissolve. Parallel to INLINE_DISABLED.
    pub(crate) static REDUCER_DISABLED: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

#[cfg(test)]
fn with_inline_disabled<F: FnOnce() -> R, R>(f: F) -> R {
    INLINE_DISABLED.with(|d| d.set(true));
    let r = f();
    INLINE_DISABLED.with(|d| d.set(false));
    r
}

#[cfg(test)]
pub(crate) fn with_reducer_disabled<F: FnOnce() -> R, R>(f: F) -> R {
    REDUCER_DISABLED.with(|d| d.set(true));
    let r = f();
    REDUCER_DISABLED.with(|d| d.set(false));
    r
}

#[cfg(test)]
#[path = "ir_codegen_tests.rs"]
mod tests;
