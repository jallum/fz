//! Split from src/ir_codegen.rs (fz-ame.7). Mechanical move only.

#![allow(unused_imports)]

use super::*;
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

/// Compiled module: persistent JITModule + per-fn ptr table + schemas. The
/// host runs a fn via `compiled.run(fn_id)` (constructs an internal default
/// Process) or `compiled.run_in(fn_id, &mut Process)` (caller-owned Process).
pub struct CompiledModule {
    pub(super) _module: JITModule,
    /// fz_fn_id -> compiled fn ptr.
    pub(super) fn_ptrs: HashMap<u32, *const u8>,
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
    /// make_process() time so any_value::debug::render can spell atoms
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
    /// `fz_drain_dtor_entry(closure, payload_ref) -> i64`. The scheduler
    /// calls this once per entry on `process.heap.pending_dtors` at
    /// task-exit; the shim Tail-CC dispatches the closure body with
    /// payload + a fresh Strict halt-cont.
    pub(crate) drain_dtor_entry_addr: *const u8,
    /// fz-ul4.27.22.3 — finalized addresses of the three Cranelift-emitted
    /// `fz_halt_cont_body_{tagged,i64,f64}` Tail-CC fns, indexed by repr
    /// kind (0=ValueRef, 1=RawInt, 2=RawF64). `make_process` seeds matching
    /// Process singletons via `init_halt_cont_singletons`. Null slots
    /// (unused reprs for this program) are pre-populated lazily by
    /// `fz_get_halt_cont` at first use.
    pub(crate) halt_cont_body_addrs: [*const u8; 3],
    /// fz-ul4.27.22.3 — per-FnId halt-cont singleton kind. When the
    /// Rust scheduler dispatches a task via `fz_main_entry`, it picks
    /// `process.halt_cont_singletons[kind]` matching the entry fn's
    /// any-key return repr. Default kind 0 (ValueRef) for fns not in
    /// the map.
    pub(crate) fn_halt_kinds: HashMap<u32, u32>,
    /// fz-70q.5.5 — single `fz_resume(cont) -> i64` SystemV shim.
    /// Reads the code pointer through the runtime closure ABI and tail-calls
    /// the continuation body with `cont` as self. Bound args live in the
    /// outcome closure env, so arity is invisible to the shim.
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
            bs_builder: None,
            frame_sizes: self.frame_sizes.clone(),
            atom_names: self.atom_names.clone(),
            bs_tuple_arity1_schema: self.bs_tuple_arity1_schema,
            bs_tuple_arity3_schema: self.bs_tuple_arity3_schema,
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
        };
        // fz-cps.1.7 — allocate one static singleton per zero-cap
        // closure-target spec. See docs/cps-in-clif.md §8.2.
        p.init_static_closures(&self.static_closure_targets);
        // fz-ul4.27.22.3 — seed all three halt-cont singletons; each
        // slot's body sig matches its repr kind (ValueRef / RawInt / RawF64).
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
        /// invokes Cheney over every scheduler-owned heap root: mailbox
        /// messages, receive templates, runnable closures, and pending
        /// entry closures. GC may rewrite those pointers to their to-space
        /// copies.
        fn park_time_gc(process: &mut Process) {
            if !process.heap.should_gc() {
                return;
            }

            fn closure_root(ptr: *mut u8) -> fz_runtime::any_value::AnyValue {
                if ptr.is_null() {
                    fz_runtime::any_value::AnyValue::null()
                } else if let Some(value) =
                    fz_runtime::any_value::AnyValue::decode_tagged_heap_bits(ptr as u64)
                {
                    value
                } else {
                    fz_runtime::any_value::AnyValue::heap_ptr(
                        ptr,
                        fz_runtime::any_value::ValueKind::CLOSURE,
                    )
                }
            }

            fn closure_bits(value: fz_runtime::any_value::AnyValue) -> *mut u8 {
                if value.kind() == fz_runtime::any_value::ValueKind::NULL {
                    std::ptr::null_mut()
                } else {
                    value.heap_addr().expect("scheduler closure root")
                }
            }

            fn push_closure_root(
                roots: &mut Vec<fz_runtime::any_value::AnyValue>,
                ptr: *mut u8,
            ) -> Option<usize> {
                if ptr.is_null() {
                    None
                } else {
                    let idx = roots.len();
                    roots.push(closure_root(ptr));
                    Some(idx)
                }
            }

            let mut mailbox_roots: Vec<fz_runtime::any_value::AnyValueRef> =
                process.mailbox.iter().copied().collect();

            let parked_clause_start = 0usize;
            let mut roots: Vec<fz_runtime::any_value::AnyValue> = Vec::new();
            if let Some(park) = process.parked_matched.as_ref() {
                roots.extend(park.clause_bodies.iter().map(|&p| closure_root(p)));
                roots.push(closure_root(park.after_cont));
            }

            let runnable_idx = push_closure_root(&mut roots, process.runnable_closure);
            let pending_closure_idx = push_closure_root(&mut roots, process.pending_closure_entry);

            let mut null_root = std::ptr::null_mut();
            process.heap.gc_with_value_and_any_value_ref_roots(
                &mut null_root,
                &mut roots,
                &mut mailbox_roots,
            );

            process.mailbox.clear();
            process.mailbox.extend(mailbox_roots);

            if let Some(park) = process.parked_matched.as_mut() {
                for (i, body) in park.clause_bodies.iter_mut().enumerate() {
                    *body = closure_bits(roots[parked_clause_start + i]);
                }
                let after_idx = parked_clause_start + park.clause_bodies.len();
                park.after_cont = closure_bits(roots[after_idx]);
            }

            if let Some(idx) = runnable_idx {
                process.runnable_closure = closure_bits(roots[idx]);
            }

            if let Some(idx) = pending_closure_idx {
                process.pending_closure_entry = closure_bits(roots[idx]);
            }

            process.heap.clear_should_gc_flag();
            // After park-time GC the process is about to park on receive,
            // so FZ_SHOULD_YIELD no longer applies to this quantum.
            fz_runtime::yield_flag::clear();
        }

        // fz-qw6 — selective-receive initial scan lifted to runtime::sched.
        // Hit sets runnable_closure + cancels after-timer (via the
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
        fn run_scheduler_closure(resume_addr: *const u8, closure: *mut u8) {
            let closure = fz_runtime::any_value::AnyValueRef::from_heap_object(
                fz_runtime::any_value::ValueKind::CLOSURE,
                closure as *const u8,
            )
            .expect("scheduler closure ref")
            .raw_word();
            type Resume = extern "C" fn(u64) -> i64;
            let f: Resume = unsafe { std::mem::transmute(resume_addr) };
            let _ = f(closure);
        }

        // fz-70q.5.5 — receive wakeup. Set by the sender-probe
        // in `send_via_current_runtime` (or the after-timer fire in
        // `drain_expired_timers`, or the initial-scan branch above)
        // when a matcher hit picked the winning clause; the message has
        // already been consumed and the bound values extracted.
        //
        // Dispatch through the single SystemV `fz_resume(cont)` shim.
        // The shim asks the runtime for the closure code pointer, then
        // call_indirects Tail(cont); bound values already live in the
        // outcome closure env.
        if let Some(closure) = process.take_runnable_closure() {
            run_scheduler_closure(self.resume_addr, closure);
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
            let halt_cl = fz_runtime::any_value::AnyValueRef::from_heap_object(
                fz_runtime::any_value::ValueKind::CLOSURE,
                process.halt_cont_singletons[kind] as *const u8,
            )
            .expect("halt continuation ref")
            .raw_word();
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
        // or Receive synchronously; on Receive it parks a matcher record
        // and the next wakeup materializes runnable_closure.
        if !process.pending_closure_entry.is_null() {
            let cl_ptr = process.pending_closure_entry;
            process.pending_closure_entry = std::ptr::null_mut();
            let cl_ref = fz_runtime::any_value::AnyValueRef::from_heap_object(
                fz_runtime::any_value::ValueKind::CLOSURE,
                cl_ptr as *const u8,
            )
            .expect("pending closure ref")
            .raw_word();
            type SpawnEntry = extern "C" fn(u64) -> i64;
            let f: SpawnEntry = unsafe { std::mem::transmute(self.spawn_entry_addr) };
            let _ = f(cl_ref);
            process.next_frame = std::ptr::null_mut();
            park_time_gc(process);
            return;
        }
        // fz-cps.5 — the trampoline loop is unreachable. All fz fns are
        // Tail-CC; dispatch flows through the three SystemV shims above
        // (receive runnable_closure, pending_main_entry, pending_closure_entry).
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
        let _current_process = fz_runtime::process::CurrentProcessGuard::install(ptr);
        self.run_internal(fn_id)
    }

    /// Run with a caller-owned Process.
    pub fn run_in(&self, fn_id: FnId, process: &mut Process) -> i64 {
        let ptr = process as *mut Process;
        let _current_process = fz_runtime::process::CurrentProcessGuard::install(ptr);
        self.run_internal(fn_id)
    }

    pub(crate) fn run_internal(&self, fn_id: FnId) -> i64 {
        let fp = self
            .fn_ptrs
            .get(&fn_id.0)
            .copied()
            .unwrap_or_else(|| panic!("no fn ptr for entry {}", fn_id.0));
        let kind = self.fn_halt_kinds.get(&fn_id.0).copied().unwrap_or(0) as usize;
        let halt_cl = fz_runtime::any_value::AnyValueRef::from_heap_object(
            fz_runtime::any_value::ValueKind::CLOSURE,
            current_process().halt_cont_singletons[kind] as *const u8,
        )
        .expect("halt continuation ref")
        .raw_word();
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
            while let Some((closure, payload_ref)) = proc_mut.heap.pending_dtors.pop_front() {
                let _ = drain(closure, payload_ref);
            }
        }
        current_process().halt_value
    }
}

// Process, PidId, ProcessState, CURRENT_PROCESS, DEFAULT_PROCESS, and
// current_process() moved to src/process.rs (fz-ul4.23.4.2). Re-exported
// here for existing downstream users (runtime.rs, ir_runtime.rs, tests)
// while consumers migrate to `fz_runtime::process::*`.
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
    /// fz-cps.1.11 — fz_spawn_entry scheduler-launch shim FuncId.
    pub spawn_entry_id: FuncId,
    /// fz-cps.5 — fz_main_entry scheduler-launch shim FuncId.
    pub main_entry_id: FuncId,
    /// fz-4mk.3a — fz_drain_dtor_entry scheduler-drain shim FuncId.
    pub drain_dtor_entry_id: FuncId,
    /// fz-ul4.27.22.3 — three fz_halt_cont_body fns indexed by repr
    /// kind (0=ValueRef, 1=RawInt, 2=RawF64). Sigs: (ValueRef|i64|f64, i64)
    /// -> i64 tail. Bodies call the matching halt_implicit_* and return 0.
    pub halt_cont_body_ids: [FuncId; 3],
    /// fz-ul4.27.22.3 — per-FnId halt-cont singleton kind (the entry
    /// fn's any-key return repr). Used by the Rust scheduler to pick
    /// the matching halt_cont_singletons slot when dispatching via
    /// fz_main_entry.
    pub fn_halt_kinds: HashMap<u32, u32>,
    /// fz-70q.5.5 — single `fz_resume` SystemV shim FuncId. See
    /// `CompiledModule::resume_addr`.
    pub resume_id: FuncId,
}
