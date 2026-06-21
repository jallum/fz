use crate::diag::Diagnostics;
#[cfg(test)]
use crate::exec::runtime::{ProcessExitCapture, Runtime};
use crate::fz_ir::FnId;
use cranelift_jit::JITModule;
use cranelift_module::FuncId;
use fz_runtime::any_value::{AnyValue, AnyValueRef, ValueKind};
use fz_runtime::heap::SchemaRegistry;
use fz_runtime::pinned_abi::call1;
use fz_runtime::process::{CompiledModuleConsts, DEFAULT_REDUCTIONS_PER_QUANTUM, Node, Process};
use fz_runtime::sched::{ScanOutcome, initial_scan};
use std::cell::RefCell;
use std::collections::HashMap;
use std::ptr::null_mut;
use std::rc::Rc;

/// Compiled module: persistent JITModule + per-fn ptr table + schemas. The
/// host runs a program by spawning it on a `Runtime` (`Runtime::new(module)`
/// then `spawn` + `run_until_idle`); the test-only `run(fn_id)` is a thin
/// one-task wrapper over exactly that.
pub struct CompiledModule {
    pub(super) _module: JITModule,
    /// fz_fn_id -> compiled fn ptr.
    pub(super) fn_ptrs: HashMap<u32, *const u8>,
    /// User-data SchemaRegistry. Shared with every Process built by
    /// `make_process()` through its Heap.
    pub(crate) user_schemas: Rc<RefCell<SchemaRegistry>>,
    /// Heap-registered schema ids for the bitstring reader/result tuples.
    /// None means no bitstring prim is present in this module.
    pub(crate) bs_tuple_arity1_schema: Option<u32>,
    pub(crate) bs_tuple_arity3_schema: Option<u32>,
    /// Node-global state shared by every Process `make_process` builds.
    pub(crate) node: Rc<Node>,
    pub(crate) diagnostics: Diagnostics,
    /// Zero-capture closure-target spec singletons resolved to code addresses
    /// at JIT-finalize time.
    pub(crate) static_closure_targets: Vec<(u32, u32, *const u8, u32)>,
    /// Tail-CC `fz_entry_thunk(self) -> i64` body.
    pub(crate) entry_thunk_addr: *const u8,
    /// Tail-CC `fz_main_trampoline(self, cont) -> i64` body.
    pub(crate) main_trampoline_addr: *const u8,
    /// SystemV->Tail-CC shim for deferred destructor dispatch.
    pub(crate) drain_dtor_entry_addr: *const u8,
    /// Finalized addresses of `fz_halt_cont_body_{tagged,i64,f64,atom}`.
    pub(crate) halt_cont_body_addrs: [*const u8; 4],
    /// Per-FnId halt-cont singleton kind.
    pub(crate) fn_halt_kinds: HashMap<u32, u32>,
    /// Single `fz_resume(cont) -> i64` SystemV shim.
    pub(crate) resume_addr: *const u8,
}

impl CompiledModule {
    /// Typer-side diagnostics collected during `compile`.
    pub fn diagnostics(&self) -> &Diagnostics {
        &self.diagnostics
    }
}

unsafe impl Send for CompiledModule {}

impl CompiledModule {
    pub fn fn_ptr(&self, fn_id: FnId) -> Option<*const u8> {
        self.fn_ptrs.get(&fn_id.0).copied()
    }

    /// Construct a fresh Process bound to this module's compile-time data.
    pub fn make_process(&self) -> Process {
        let consts = CompiledModuleConsts {
            bs_tuple_arity1_schema: self.bs_tuple_arity1_schema,
            bs_tuple_arity3_schema: self.bs_tuple_arity3_schema,
            static_closure_targets: self.static_closure_targets.clone(),
            halt_cont_body_addrs: self.halt_cont_body_addrs,
        };
        let mut p = Process::from_consts(
            Rc::clone(&self.node),
            Rc::clone(&self.user_schemas),
            &consts,
            0,
            DEFAULT_REDUCTIONS_PER_QUANTUM,
        );
        p.heap.reset_alloc_stats();
        p
    }

    /// Run one quantum for a Process.
    pub(crate) fn run_quantum(&self, process: &mut Process) {
        fn park_time_gc(process: &mut Process) {
            if !process.needs_boundary_gc() {
                return;
            }

            fn closure_root(ptr: *mut u8) -> AnyValue {
                if ptr.is_null() {
                    AnyValue::null()
                } else if let Some(value) = AnyValue::decode_tagged_heap_bits(ptr as u64) {
                    value
                } else {
                    AnyValue::heap_ptr(ptr, ValueKind::CLOSURE)
                }
            }

            fn closure_bits(value: AnyValue) -> *mut u8 {
                if value.kind() == ValueKind::NULL {
                    null_mut()
                } else {
                    value.heap_addr().expect("scheduler closure root")
                }
            }

            fn push_closure_root(roots: &mut Vec<AnyValue>, ptr: *mut u8) -> Option<usize> {
                if ptr.is_null() {
                    None
                } else {
                    let idx = roots.len();
                    roots.push(closure_root(ptr));
                    Some(idx)
                }
            }

            let mut mailbox_roots: Vec<AnyValueRef> = process.mailbox.iter().copied().collect();

            let parked_clause_start = 0usize;
            let mut roots: Vec<AnyValue> = Vec::new();
            if let Some(park) = process.wait.as_ref() {
                roots.extend(park.clause_bodies.iter().map(|&p| closure_root(p)));
                roots.push(closure_root(park.after_cont));
            }

            let runnable_idx = push_closure_root(&mut roots, process.runnable_ptr());

            let mut null_root = null_mut();
            process
                .heap
                .gc_with_value_and_any_value_ref_roots(&mut null_root, &mut roots, &mut mailbox_roots);

            process.mailbox.clear();
            process.mailbox.extend(mailbox_roots);

            if let Some(park) = process.wait.as_mut() {
                for (i, body) in park.clause_bodies.iter_mut().enumerate() {
                    *body = closure_bits(roots[parked_clause_start + i]);
                }
                let after_idx = parked_clause_start + park.clause_bodies.len();
                park.after_cont = closure_bits(roots[after_idx]);
            }

            if let Some(idx) = runnable_idx {
                process.set_runnable_closure(closure_bits(roots[idx]));
            }

            process.heap.clear_should_gc_flag();
            process.clear_yield_reasons();
        }

        match initial_scan(process) {
            ScanOutcome::Hit => {}
            ScanOutcome::Miss => {
                process.next_frame = null_mut();
                return;
            }
            ScanOutcome::NotApplicable => {}
        }

        fn run_scheduler_closure(resume_addr: *const u8, process: &mut Process, closure: *mut u8) {
            let closure = AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure as *const u8)
                .expect("scheduler closure ref")
                .raw_word();
            let process_ptr = process as *mut Process;
            let _ = unsafe { call1(resume_addr, process_ptr, closure) };
        }

        if let Some(closure) = process.take_runnable_closure() {
            run_scheduler_closure(self.resume_addr, process, closure);
            process.next_frame = null_mut();
            park_time_gc(process);
        } else {
            process.next_frame = null_mut();
        }
    }
}

#[cfg(test)]
impl CompiledModule {
    pub fn static_closure_targets(&self) -> &[(u32, u32, *const u8, u32)] {
        &self.static_closure_targets
    }

    pub fn run(&self, tel: &dyn crate::telemetry::Telemetry, fn_id: FnId) -> i64 {
        let exits = ProcessExitCapture::new();
        tel.attach(&[], exits.handler());
        let mut rt = Runtime::new(self, 1, tel);
        let root_pid = rt.spawn(fn_id);
        rt.run_until_idle();
        exits.by_pid(root_pid).expect("root process_exited captured").halt_value
    }
}

/// Everything compiler2 native codegen collects during the shared pipeline,
/// handed to the backend's `emit_metadata_carriers` and `finalize`.
pub struct CompiledMetadata {
    pub fn_ids: HashMap<u32, FuncId>,
    pub user_schemas: Rc<RefCell<SchemaRegistry>>,
    pub frame_sizes: Vec<u32>,
    pub atom_names: Vec<String>,
    pub bs_tuple_arity1_schema: Option<u32>,
    pub bs_tuple_arity3_schema: Option<u32>,
    pub tuple_arities: Vec<u32>,
    pub named_schemas: Vec<(String, Vec<String>)>,
    pub diagnostics: Diagnostics,
    pub main_fn_id: Option<FnId>,
    pub static_closure_targets: Vec<(u32, u32, FuncId, u32)>,
    pub entry_thunk_id: FuncId,
    pub main_trampoline_id: FuncId,
    pub drain_dtor_entry_id: FuncId,
    pub halt_cont_body_ids: [FuncId; 4],
    pub fn_halt_kinds: HashMap<u32, u32>,
    pub resume_id: FuncId,
}
