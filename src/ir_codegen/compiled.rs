use crate::diag::Diagnostics;
#[cfg(test)]
use crate::exec::runtime::{ProcessExitCapture, Runtime};
use crate::fz_ir::FnId;
use cranelift_jit::JITModule;
use cranelift_module::FuncId;
use fz_runtime::any_value::{AnyValueRef, ValueKind};
use fz_runtime::heap::SchemaRegistry;
use fz_runtime::pinned_abi::call1;
use fz_runtime::process::{DEFAULT_REDUCTIONS_PER_QUANTUM, Node, Process};
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
    /// Node-global state shared by every Process `make_process` builds.
    pub(crate) node: Rc<Node>,
    pub(crate) diagnostics: Diagnostics,
    /// Tail-CC `fz_entry_thunk(self) -> i64` body.
    pub(crate) entry_thunk_addr: *const u8,
    /// Tail-CC `fz_main_trampoline(self, cont) -> i64` body.
    pub(crate) main_trampoline_addr: *const u8,
    /// C-convention to Tail-CC shim for deferred destructor dispatch.
    pub(crate) drain_dtor_entry_addr: *const u8,
    /// Per-FnId halt continuation kind.
    pub(crate) fn_halt_kinds: HashMap<u32, u32>,
    /// Single `fz_resume(cont) -> i64` shim, in the target's C convention.
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
        let mut p = Process::with_node(
            Rc::clone(&self.node),
            Rc::clone(&self.user_schemas),
            0,
            DEFAULT_REDUCTIONS_PER_QUANTUM,
        );
        p.heap.reset_alloc_stats();
        p
    }

    /// Run one quantum for a Process.
    pub(crate) fn run_quantum(&self, process: &mut Process) {
        fn run_scheduler_closure(resume_addr: *const u8, process: &mut Process, closure: *mut u8) {
            let closure = AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure as *const u8)
                .expect("scheduler closure ref")
                .raw_word();
            let process_ptr = process as *mut Process;
            let _ = unsafe { call1(resume_addr, process_ptr, closure) };
        }

        let closure = process
            .take_runnable_closure()
            .expect("a dispatched process has a runnable closure");
        run_scheduler_closure(self.resume_addr, process, closure);
        process.next_frame = null_mut();
    }
}

#[cfg(test)]
impl CompiledModule {
    /// The address of the data object the program emitted under `name`.
    pub fn data_address(&self, name: &str) -> Option<usize> {
        use cranelift_module::{FuncOrDataId, Module};
        match self._module.get_name(name)? {
            FuncOrDataId::Data(id) => Some(self._module.get_finalized_data(id).0 as usize),
            FuncOrDataId::Func(_) => None,
        }
    }

    pub fn run(&self, tel: &crate::telemetry::ConfiguredTelemetry, fn_id: FnId) -> i64 {
        self.run_with_output(tel, &fz_runtime::output::STDOUT_OUTPUT, fn_id)
    }

    pub fn run_with_output(
        &self,
        tel: &crate::telemetry::ConfiguredTelemetry,
        output: &dyn fz_runtime::output::OutputSink,
        fn_id: FnId,
    ) -> i64 {
        let exits = ProcessExitCapture::new();
        exits.install(tel);
        let mut rt = Runtime::new(self, 1, tel).with_output(output);
        let root_pid = rt.spawn(fn_id);
        rt.run_until_idle();
        exits.by_pid(root_pid).expect("root process_exited captured").halt_value
    }
}

/// Everything compiler2 native codegen collects during the shared pipeline,
/// handed to the backend's `emit_metadata_carriers` and `finalize`.
pub struct CompiledMetadata {
    pub closure_denotations: Vec<(
        fz_runtime::any_value::ClosureDenotationId,
        std::sync::Arc<fz_runtime::function_denotation::FunctionDenotation>,
    )>,
    pub fn_ids: HashMap<u32, FuncId>,
    pub user_schemas: Rc<RefCell<SchemaRegistry>>,
    pub frame_sizes: Vec<u32>,
    pub atom_names: Vec<String>,
    pub tuple_arities: Vec<u32>,
    pub named_schemas: Vec<(fz_runtime::module_name::ModuleName, Vec<String>)>,
    pub diagnostics: Diagnostics,
    pub main_fn_id: Option<FnId>,
    pub entry_thunk_id: FuncId,
    pub main_trampoline_id: FuncId,
    pub drain_dtor_entry_id: FuncId,
    pub fn_halt_kinds: HashMap<u32, u32>,
    pub resume_id: FuncId,
}
