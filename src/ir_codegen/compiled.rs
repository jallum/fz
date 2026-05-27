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
    /// User-data SchemaRegistry. Shared with every Process built by
    /// `make_process()` through its Heap.
    pub(crate) user_schemas: std::rc::Rc<std::cell::RefCell<fz_runtime::heap::SchemaRegistry>>,
    /// Per-fn frame size (bytes), indexed by FnId.0. Consumed by
    /// `fz_alloc_frame_dyn` for fns whose id is only known dynamically
    /// (closure invocation).
    pub(crate) frame_sizes: Vec<u32>,
    /// Heap-registered schema ids for the bitstring reader/result tuples.
    /// None means no bitstring prim is present in this module.
    pub(crate) bs_tuple_arity1_schema: Option<u32>,
    pub(crate) bs_tuple_arity3_schema: Option<u32>,
    /// Atom names indexed by id. Copied into each Process so
    /// `any_value::debug::render` can spell atoms as `:name`.
    pub(crate) atom_names: Vec<String>,
    pub(crate) diagnostics: crate::diag::Diagnostics,
    /// Zero-capture closure-target spec singletons resolved to code
    /// addresses at JIT-finalize time. `make_process` allocates one
    /// 24-byte off-heap closure per entry into `Process.static_closures`.
    /// See docs/cps-in-clif.md §8.2.
    pub(crate) static_closure_targets: Vec<(u32, u32, *const u8, u32 /* halt_kind */)>,
    /// SystemV→Tail-CC shim `fz_spawn_entry(closure) -> i64`. Allocates a
    /// halt-cont and indirect-calls the zero-arg closure with
    /// `(self, halt_cont)`. Used by `Runtime::spawn_closure`.
    pub(crate) spawn_entry_addr: *const u8,
    /// SystemV→Tail-CC shim `fz_main_entry(main_fp) -> i64`. Allocates a
    /// halt-cont and indirect-calls main with `(halt_cont)`. Used by
    /// `Runtime::spawn(fn_id)` / `CompiledModule::run_internal`.
    pub(crate) main_entry_addr: *const u8,
    /// SystemV→Tail-CC shim `fz_drain_dtor_entry(closure, payload_ref) -> i64`.
    /// The scheduler calls this once per entry on
    /// `process.heap.pending_dtors` at task-exit; dispatches the dtor
    /// closure with payload + a fresh Strict halt-cont.
    pub(crate) drain_dtor_entry_addr: *const u8,
    /// Finalized addresses of the three `fz_halt_cont_body_{tagged,i64,f64}`
    /// Tail-CC fns, indexed by repr kind (0=ValueRef, 1=RawInt, 2=RawF64).
    /// Null slots (unused reprs in this program) are populated lazily by
    /// `fz_get_halt_cont` at first use.
    pub(crate) halt_cont_body_addrs: [*const u8; 3],
    /// Per-FnId halt-cont singleton kind (the entry fn's any-key return
    /// repr). The Rust scheduler picks the matching
    /// `process.halt_cont_singletons[kind]` when dispatching via
    /// `fz_main_entry`. Default kind 0 (ValueRef) when absent.
    pub(crate) fn_halt_kinds: HashMap<u32, u32>,
    /// Single `fz_resume(cont) -> i64` SystemV shim. Reads the code
    /// pointer through the runtime closure ABI and tail-calls the
    /// continuation body with `cont` as self. Bound args live in the
    /// outcome closure env, so arity is invisible to the shim.
    pub(crate) resume_addr: *const u8,
}

impl CompiledModule {
    /// Typer-side diagnostics collected during `compile`. Includes both
    /// warnings and errors; drivers must route through
    /// `diag::report_or_exit` so error-severity entries actually halt.
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
            scheduler_yields: 0,
            interpreter_yields: 0,
        };
        // One static singleton per zero-cap closure-target spec.
        // See docs/cps-in-clif.md §8.2.
        p.init_static_closures(&self.static_closure_targets);
        // Seed all three halt-cont singletons; each slot's body sig
        // matches its repr kind (ValueRef / RawInt / RawF64).
        p.init_halt_cont_singletons(self.halt_cont_body_addrs);
        p.heap.reset_alloc_stats();
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
        /// shim-return boundary; if `heap.should_gc()` is set, runs
        /// Cheney over every scheduler-owned heap root (mailbox,
        /// receive templates, runnable + pending entry closures) and
        /// rewrites those pointers to their to-space copies.
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

        // Selective-receive initial scan. Hit sets runnable_closure and
        // cancels the after-timer via the scheduler hook; Miss blocks the
        // task; NotApplicable is a no-op.
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

        // One dispatch decision per quantum. Variants are listed in
        // scheduling-priority order; the classifier returns the first
        // match. Receive wakeup beats fresh main-entry beats fresh
        // closure-entry; Idle is the no-work fallthrough.
        enum Dispatch {
            // Receive wakeup: a matcher hit (from sender-probe,
            // after-timer fire, or the initial-scan above) picked the
            // winning clause and bound values into the outcome closure
            // env. Dispatch through the single SystemV `fz_resume(cont)`
            // shim.
            RunnableClosure(*mut u8),
            // Fresh main-style task entry: fn ptr queued by
            // `Runtime::spawn` or `run_internal`. Dispatch via
            // `fz_main_entry`; the body runs synchronously to halt or
            // Receive.
            MainEntry { fp: *mut u8, kind: usize },
            // Fresh task entry: closure queued by
            // `Runtime::spawn_closure`. Dispatch via `fz_spawn_entry`;
            // the body runs synchronously to halt or Receive. On Receive
            // it parks a matcher record and the next wakeup
            // materializes runnable_closure.
            ClosureEntry(*mut u8),
            // All fz fns are Tail-CC; dispatch flows through the three
            // SystemV shims above. No uniform fns exist, so no
            // frame-by-frame trampoline loop is needed.
            Idle,
        }

        let dispatch = if let Some(closure) = process.take_runnable_closure() {
            Dispatch::RunnableClosure(closure)
        } else if !process.pending_main_entry.is_null() {
            let fp = process.pending_main_entry;
            process.pending_main_entry = std::ptr::null_mut();
            // Pick the halt-cont singleton matching the entry fn's
            // return-repr kind.
            let kind = self
                .fn_halt_kinds
                .get(&process.pending_main_entry_fn_id)
                .copied()
                .unwrap_or(0) as usize;
            Dispatch::MainEntry { fp, kind }
        } else if !process.pending_closure_entry.is_null() {
            let cl_ptr = process.pending_closure_entry;
            process.pending_closure_entry = std::ptr::null_mut();
            Dispatch::ClosureEntry(cl_ptr)
        } else {
            Dispatch::Idle
        };

        match dispatch {
            Dispatch::RunnableClosure(closure) => {
                run_scheduler_closure(self.resume_addr, closure);
                process.next_frame = std::ptr::null_mut();
                park_time_gc(process);
            }
            Dispatch::MainEntry { fp, kind } => {
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
            }
            Dispatch::ClosureEntry(cl_ptr) => {
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
            }
            Dispatch::Idle => {
                process.next_frame = std::ptr::null_mut();
            }
        }
    }
}

#[cfg(test)]
impl CompiledModule {
    /// Registered zero-capture closure-target specs.
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
        // Single-shot entry path: flush surviving MSO resources and run
        // their dtor closures as fz code before returning. Mirrors the
        // task-exit drain in `Runtime::run_until_idle` and
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
    /// Sorted list of tuple arities the program will allocate. JIT ignores
    /// it (its runtime shares `user_schemas`); AOT bakes it into a `.data`
    /// symbol so `fz_aot_setup` re-registers the same `Tuple{N}` schemas in
    /// matching order.
    pub tuple_arities: Vec<u32>,
    pub diagnostics: crate::diag::Diagnostics,
    /// FnId of fz user `main`, if present. AOT needs it to wire the C
    /// `main` shim; JIT keeps it as a convenience for the run path.
    pub main_fn_id: Option<FnId>,
    /// Zero-capture closure-target specs as `(cl_sid, fn_id, stub_func_id,
    /// halt_kind)`. JIT finalize resolves stub_func_id to a code address;
    /// `make_process` populates `Process.static_closures` from the result.
    pub static_closure_targets: Vec<(u32, u32, FuncId, u32 /* halt_kind */)>,
    pub spawn_entry_id: FuncId,
    pub main_entry_id: FuncId,
    pub drain_dtor_entry_id: FuncId,
    /// Three `fz_halt_cont_body` fns indexed by repr kind (0=ValueRef,
    /// 1=RawInt, 2=RawF64). Sigs: (ValueRef|i64|f64, i64) -> i64 tail.
    /// Bodies call the matching `halt_implicit_*` and return 0.
    pub halt_cont_body_ids: [FuncId; 3],
    /// Per-FnId halt-cont singleton kind (the entry fn's any-key return
    /// repr). The Rust scheduler picks the matching halt_cont_singletons
    /// slot when dispatching via `fz_main_entry`.
    pub fn_halt_kinds: HashMap<u32, u32>,
    /// See `CompiledModule::resume_addr`.
    pub resume_id: FuncId,
}
