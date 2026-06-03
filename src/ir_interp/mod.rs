//! fz-ul4.23.5.2 — IR interpreter on any value refs, heap, and runtime substrate.
//!
//! Walks a `fz_ir::Module` directly, but
//! uses the SAME heap/interchange representation and runtime FFI as the JIT.
//! Spawn/send/receive call into the same runtime.rs scheduler. Print
//! renders through typed runtime helpers. Heap allocations
//! go through the current Process's Heap.
//!
//! Scope at .5.2: minimal for fixtures/add1/input.fz —
//!   Const::{Int, Atom, Nil, True, False}
//!   BinOp::Add  (Int + Int)
//!   Term::{Call, Return, Halt}
//!
//! Subsequent atoms expand the surface fixture by fixture:
//!   .5.3 scalars + print + other arith
//!   .5.4 closures + higher-order
//!   .5.5 pattern dispatch
//!   .5.6 modules
//!   .5.7 tail recursion (TCO)
//!   .5.8 spawn/send/receive

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::exec::runtime::{ExitRecord, output_hook_thunk};
use crate::fz_ir::{FnId, Module};
use crate::ir_extern_marshal::resolve_module_types;
use crate::ir_planner::{ModulePlan, plan_module};
use crate::telemetry::{NullTelemetry, Telemetry};
use crate::types::{ConcreteTypes, RenderTypes, Ty, Types};
use fz_runtime::any_value::{ValueKind, closure_addr_from_tagged};
use fz_runtime::exec_ctx::ExecCtx;
use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema, SchemaRegistry};
use fz_runtime::procbin::mso_drop_all_deferred;
use fz_runtime::process::{CompiledModuleConsts, DEFAULT_REDUCTIONS_PER_QUANTUM, Node, Process, ProcessState};
use fz_runtime::resource::{ResourceHandle, alloc_resource, fz_resource_destructor_noop};

mod binop;
mod extern_call;
mod matcher_exec;
mod prim;
mod run;
mod scheduler;
mod value;

#[cfg(test)]
mod tests;

use binop::*;
use extern_call::*;
#[cfg(test)]
pub(crate) use extern_call::{
    tests_support_dtor_fired, tests_support_dtor_last_payload, tests_support_dtor_reset, tests_support_lock,
    tests_support_test_dtor_addr,
};
use matcher_exec::*;
use prim::*;
use run::*;
use scheduler::*;
pub(crate) use value::AnyValue;
use value::*;

use std::collections::VecDeque;

/// Per-task resume state: fn to call, captures (no message), and after-chain.
type ResumeEntry = (FnId, Vec<AnyValue>, Vec<(FnId, Vec<AnyValue>)>);

/// fz-yxs/fz-2v3 — value type for selective-receive park records.
type InterpParked = (ParkRecord, Vec<(FnId, Vec<AnyValue>)>);

/// Immutable IR interpreter code generation.
///
/// `FnId`s are module-local, so every runnable process needs the code image
/// that was current when its entry/resume was created. The REPL advances the
/// evaluator to newer images as chunks compile, while blocked children may
/// resume later against an older image.
#[derive(Clone)]
pub(crate) struct CodeImage {
    module: Rc<Module>,
    module_plan: Rc<ModulePlan>,
}

impl CodeImage {
    fn planned(module: &Module, module_plan: ModulePlan) -> Result<Self, String> {
        let mut t = ConcreteTypes;
        Self::from_plan(&mut t, module, module_plan)
    }

    fn from_module(module: &Module) -> Result<Self, String> {
        let mut t = ConcreteTypes;
        let module_plan = plan_module(&mut t, module, &NullTelemetry);
        Self::from_plan(&mut t, module, module_plan)
    }

    fn from_plan<T>(t: &mut T, module: &Module, mut module_plan: ModulePlan) -> Result<Self, String>
    where
        T: Types<Ty = Ty> + RenderTypes,
    {
        let diagnostics = resolve_module_types(t, module, &mut module_plan);
        if let Some(diagnostic) = diagnostics.into_iter().next() {
            return Err(diagnostic.message);
        }
        Ok(Self {
            module: Rc::new(module.clone()),
            module_plan: Rc::new(module_plan),
        })
    }

    fn module_plan(&self) -> &ModulePlan {
        &self.module_plan
    }

    fn module(&self) -> &Module {
        &self.module
    }
}

/// Explicit owner for IR-interpreter runtime state.
///
/// fz-elu.3 introduces the container before moving scheduler operations onto
/// methods. fz-elu.2 makes the process table, run queue, resume entries, and
/// parked selective receives runtime-owned.
pub(crate) struct IrInterpRuntime {
    tasks: HashMap<u32, Box<Process>>,
    code_images: HashMap<u32, Rc<CodeImage>>,
    next_pid: u32,
    schemas: Rc<RefCell<SchemaRegistry>>,
    tuple_schema_ids: HashMap<usize, u32>,
    run_queue: VecDeque<u32>,
    resume: HashMap<u32, ResumeEntry>,
    parked: HashMap<u32, InterpParked>,
    /// Node-global state (the atom table) shared by every task in this
    /// interpreter instance, seeded from the program module's atoms.
    node: Rc<Node>,
    /// The process executing in the current quantum. Set per-quantum in
    /// `drive_until_idle`; read by BIF call sites that allocate or touch the
    /// running process's heap/mailbox. Per-instance — replaces reads of the
    /// global `CURRENT_PROCESS` thread-local so two interpreters can be live
    /// at once on one thread.
    current_proc: *mut Process,
}

impl IrInterpRuntime {
    pub(crate) fn fresh() -> Self {
        Self {
            tasks: HashMap::new(),
            code_images: HashMap::new(),
            next_pid: 2,
            schemas: Rc::new(RefCell::new(SchemaRegistry::new())),
            tuple_schema_ids: HashMap::new(),
            run_queue: VecDeque::new(),
            resume: HashMap::new(),
            parked: HashMap::new(),
            node: Rc::new(Node::empty()),
            current_proc: std::ptr::null_mut(),
        }
    }

    /// The process running in the current quantum. Call sites that allocate or
    /// touch the running process read this instead of the global
    /// `CURRENT_PROCESS` thread-local.
    #[inline]
    pub(crate) fn cur_proc(&self) -> *mut Process {
        debug_assert!(!self.current_proc.is_null(), "cur_proc outside a quantum");
        self.current_proc
    }

    pub(crate) fn fresh_with_root(module: &Module) -> Self {
        let mut runtime = Self::fresh();
        // Seed the interpreter's shared node from the program module's atoms;
        // every task clones this Rc.
        runtime.node = Rc::new(Node::new(module.atom_names.clone(), Vec::new()));
        let user_schemas = runtime.schemas();
        let (bs_tuple_arity1_schema, bs_tuple_arity3_schema) = runtime.register_bitstring_tuple_schemas();
        let consts = CompiledModuleConsts {
            bs_tuple_arity1_schema: Some(bs_tuple_arity1_schema),
            bs_tuple_arity3_schema: Some(bs_tuple_arity3_schema),
            ..CompiledModuleConsts::empty()
        };
        let process = Box::new(Process::from_consts(
            Rc::clone(&runtime.node),
            user_schemas,
            &consts,
            1,
            DEFAULT_REDUCTIONS_PER_QUANTUM,
        ));
        runtime.insert_task(1, process);
        runtime
    }

    fn schemas(&self) -> Rc<RefCell<SchemaRegistry>> {
        self.schemas.clone()
    }

    fn register_bitstring_tuple_schemas(&mut self) -> (u32, u32) {
        let (arity1, arity3) = {
            let mut reg = self.schemas.borrow_mut();
            (
                reg.register(Schema::tuple_of_arity(1)),
                reg.register(Schema::tuple_of_arity(3)),
            )
        };
        self.tuple_schema_ids.insert(1, arity1);
        self.tuple_schema_ids.insert(3, arity3);
        (arity1, arity3)
    }

    fn tuple_schema_id(&mut self, arity: usize) -> u32 {
        if let Some(&id) = self.tuple_schema_ids.get(&arity) {
            return id;
        }
        let schema = Schema {
            name: format!("Tuple{}", arity),
            size: (arity * 8) as u32,
            fields: (0..arity)
                .map(|i| FieldDescriptor {
                    offset: (i * 8) as u32,
                    kind: FieldKind::AnyValue,
                    name: None,
                })
                .collect(),
        };
        let id = self.schemas.borrow_mut().register(schema);
        self.tuple_schema_ids.insert(arity, id);
        id
    }

    fn insert_task(&mut self, pid: u32, process: Box<Process>) {
        self.tasks.insert(pid, process);
    }

    fn set_task_code_image(&mut self, pid: u32, image: Rc<CodeImage>) {
        // Atom names live on the shared `node`, not per-task. Refresh them from
        // the image's module so a REPL chunk that introduced new compile-time
        // atoms is visible to rendering/matching (the image carries the
        // cumulative atom set).
        self.node.reset_atoms(&image.module().atom_names);
        self.code_images.insert(pid, image);
    }

    fn task_code_image(&self, pid: u32) -> Option<Rc<CodeImage>> {
        self.code_images.get(&pid).cloned()
    }

    fn enqueue_resume(&mut self, pid: u32, entry: ResumeEntry) {
        self.resume.insert(pid, entry);
        self.run_queue.push_back(pid);
    }

    fn pop_runnable(&mut self) -> Option<u32> {
        self.run_queue.pop_front()
    }

    fn take_resume(&mut self, pid: u32) -> Option<ResumeEntry> {
        self.resume.remove(&pid)
    }

    fn process_ptr(&mut self, pid: u32) -> Option<*mut Process> {
        self.tasks.get_mut(&pid).map(|p| p.as_mut() as *mut Process)
    }

    fn set_process_state(&mut self, pid: u32, state: ProcessState) {
        if let Some(process) = self.tasks.get_mut(&pid) {
            process.state = state;
        }
    }

    pub(crate) fn enqueue_entry(
        &mut self,
        module: &Module,
        pid: u32,
        fn_id: FnId,
        args: Vec<AnyValue>,
    ) -> Result<(), String> {
        if !self.tasks.contains_key(&pid) {
            return Err(format!("enqueue_entry: unknown pid {}", pid));
        }
        self.set_task_code_image(pid, Rc::new(CodeImage::from_module(module)?));
        self.enqueue_entry_with_image(pid, fn_id, args)
    }

    fn enqueue_entry_with_image(&mut self, pid: u32, fn_id: FnId, args: Vec<AnyValue>) -> Result<(), String> {
        if !self.tasks.contains_key(&pid) {
            return Err(format!("enqueue_entry: unknown pid {}", pid));
        }
        self.resume.insert(pid, (fn_id, args, vec![]));
        self.run_queue.push_back(pid);
        self.set_process_state(pid, ProcessState::Ready);
        Ok(())
    }

    pub(crate) fn drive_until_idle(
        &mut self,
        tel: &dyn Telemetry,
        keepalive_pid: Option<u32>,
    ) -> Result<Vec<(u32, AnyValue)>, String> {
        let mut completions = Vec::new();
        let mut t = ConcreteTypes;
        // Route fz output (dbg/print) to telemetry for the duration of the
        // drive — same seam the compiled scheduler uses, so dbg observability
        // is engine-uniform.

        // Per-context dispatch table for this interpreter run. The interpreter
        // is its own scheduler and handles spawn/send/timer in-engine, so the
        // BIF callbacks stay None; the scheduler handle and telemetry sink
        // identify this run, and `module` is refreshed per task below. Lives on
        // this stack frame, which outlives every quantum; each task's
        // `Process.ctx` points here and BIFs dispatch output/make_resource
        // through it.
        let mut exec_ctx = ExecCtx {
            scheduler: self as *mut Self as *mut (),
            tel: (&tel) as *const &dyn Telemetry as *const (),
            // dbg/print routes to telemetry through the same thunk the compiled
            // engine uses; the rest of the BIF callbacks are interpreter-internal.
            output: Some(output_hook_thunk),
            ..ExecCtx::empty()
        };

        'sched: while let Some(pid) = self.pop_runnable() {
            let image = self
                .task_code_image(pid)
                .ok_or_else(|| format!("pid {} has no interpreter code image", pid))?;
            let module = image.module();
            let module_types = image.module_plan();
            let (fn_id, args, mut after) = self.take_resume(pid).expect("pid in run_queue with no resume entry");
            let proc_ptr = self.process_ptr(pid).expect("pid in run_queue with no process entry");
            exec_ctx.module = module as *const Module as *const ();
            unsafe {
                (*proc_ptr).state = ProcessState::Running;
                (*proc_ptr).reset_reduction_budget();
                (*proc_ptr).ctx = &mut exec_ctx;
                (*proc_ptr).heap.set_owner(proc_ptr);
                debug_assert!(!(*proc_ptr).ctx.is_null(), "interp ctx installed");
            };
            self.current_proc = proc_ptr;
            let mut step = run_fn_typed(self, &mut t, module, tel, module_types, fn_id, args);
            loop {
                match step {
                    Ok(InterpStep::Done(val)) => {
                        if let Some((next_fn, next_caps)) = after.first().cloned() {
                            after.remove(0);
                            let mut next_args = vec![val];
                            next_args.extend(next_caps);
                            step = run_fn_typed(self, &mut t, module, tel, module_types, next_fn, next_args);
                            continue;
                        }

                        completions.push((pid, val));
                        if keepalive_pid == Some(pid) {
                            self.set_process_state(pid, ProcessState::Ready);
                            continue 'sched;
                        }

                        unsafe {
                            mso_drop_all_deferred(&mut (*proc_ptr).heap);
                        }
                        if let Err(e) = drain_pending_dtors_interp(self, &mut t, module, tel, module_types) {
                            tel.event(&["fz", "runtime", "dtor_drain_failed"], crate::metadata! { error: e });
                        }
                        // Parity with the compiled engine: record the result on
                        // the Process and emit the same process_exited event
                        // through the single shared emit site.
                        unsafe {
                            (*proc_ptr).halt_value = value_to_halt(proc_ptr, val);
                            ExitRecord::emit(tel, pid, &*proc_ptr);
                        }
                        self.set_process_state(pid, ProcessState::Exited);
                        continue 'sched;
                    }
                    Ok(InterpStep::Yielded {
                        resume_fn,
                        mut resume_args,
                        after: mut new_after,
                        remaining_reductions,
                        reason,
                    }) => {
                        new_after.extend(after);
                        let process = unsafe { &mut *proc_ptr };
                        process.finish_yield_report(remaining_reductions, reason);
                        process
                            .boundary_maintenance(|p| gc_interp_scheduler_roots(p, &mut resume_args, &mut new_after))?;
                        self.set_process_state(pid, ProcessState::Ready);
                        self.resume.insert(pid, (resume_fn, resume_args, new_after));
                        self.run_queue.push_back(pid);
                        continue 'sched;
                    }
                    Ok(InterpStep::Blocked(resume_fn, cap_vals, mut new_after)) => {
                        new_after.extend(after);
                        self.set_process_state(pid, ProcessState::Blocked);
                        self.resume.insert(pid, (resume_fn, cap_vals, new_after));
                        continue 'sched;
                    }
                    Ok(InterpStep::BlockedMatched(park, mut new_after)) => {
                        new_after.extend(after);
                        self.set_process_state(pid, ProcessState::Blocked);
                        self.parked.insert(pid, (park, new_after));
                        continue 'sched;
                    }
                    Err(e) => {
                        return Err(e);
                    }
                }
            }
        }

        Ok(completions)
    }

    #[cfg(test)]
    pub(crate) fn task(&self, pid: u32) -> Option<&Process> {
        self.tasks.get(&pid).map(Box::as_ref)
    }

    #[cfg(test)]
    pub(crate) fn task_mut(&mut self, pid: u32) -> Option<&mut Process> {
        self.tasks.get_mut(&pid).map(Box::as_mut)
    }

    pub(crate) fn read_tuple_fields(&self, pid: u32, value: AnyValue, arity: usize) -> Result<Vec<AnyValue>, String> {
        let AnyValue::Ref(value_ref) = value else {
            return Err(format!(
                "expected tuple ref, got {}",
                value.render(std::ptr::null_mut())
            ));
        };
        if value_ref.tag() != ValueKind::STRUCT {
            return Err(format!("expected tuple struct, got {:?}", value));
        }
        let addr = value_ref
            .struct_addr()
            .map_err(|err| format!("expected tuple struct: {err:?}"))?;
        let task = self
            .tasks
            .get(&pid)
            .ok_or_else(|| format!("read_tuple_fields: unknown pid {}", pid))?;
        Ok((0..arity)
            .map(|i| interp_value_from_slot(task.heap.read_field_slot(addr, (i * 8) as u32)))
            .collect())
    }

    pub(crate) fn render_value(&self, pid: u32, value: AnyValue) -> Result<String, String> {
        let task = self
            .tasks
            .get(&pid)
            .ok_or_else(|| format!("render_value: unknown pid {}", pid))?;
        let proc_ptr = task.as_ref() as *const Process as *mut Process;
        Ok(value.render(proc_ptr))
    }
}

fn gc_interp_scheduler_roots(
    process: &mut Process,
    resume_args: &mut [AnyValue],
    after: &mut [(FnId, Vec<AnyValue>)],
) -> Result<(), String> {
    let resume_len = resume_args.len();
    let mut roots: Vec<fz_runtime::any_value::AnyValue> = Vec::new();
    for value in resume_args.iter() {
        roots.push(value.value(process as *mut Process)?);
    }
    for (_, caps) in after.iter() {
        for value in caps {
            roots.push(value.value(process as *mut Process)?);
        }
    }

    process
        .heap
        .gc_any_value_roots_with_process_roots(&mut roots, &mut process.mailbox);

    for (slot, root) in resume_args.iter_mut().zip(roots.iter().take(resume_len)) {
        *slot = interp_value_from_slot(*root);
    }
    let mut idx = resume_len;
    for (_, caps) in after.iter_mut() {
        for value in caps {
            *value = interp_value_from_slot(roots[idx]);
            idx += 1;
        }
    }
    Ok(())
}

/// Run `module`'s `main` fn through the interpreter.
///
/// Drives a cooperative run-queue loop: main starts at pid=1, spawned tasks
/// are enqueued and run one quantum at a time in FIFO order. Tasks that block
/// on receive park until a send wakes them. Loop exits when the queue is empty.
#[cfg(test)]
pub fn run_main(tel: &dyn Telemetry, module: &Module) -> Result<i64, String> {
    let mut t = ConcreteTypes;
    let module_plan = plan_module(&mut t, module, &NullTelemetry);
    run_main_with_plan(tel, module, module_plan).map(|(halt, _runtime)| halt)
}

pub(crate) fn run_main_with_plan(
    tel: &dyn Telemetry,
    module: &Module,
    module_plan: ModulePlan,
) -> Result<(i64, IrInterpRuntime), String> {
    run_main_inner(tel, module, module_plan)
}

#[cfg(test)]
pub(crate) fn run_main_with_runtime(tel: &dyn Telemetry, module: &Module) -> Result<(i64, IrInterpRuntime), String> {
    let mut t = ConcreteTypes;
    let module_plan = plan_module(&mut t, module, &NullTelemetry);
    run_main_inner(tel, module, module_plan)
}

fn run_main_inner(
    tel: &dyn Telemetry,
    module: &Module,
    module_plan: ModulePlan,
) -> Result<(i64, IrInterpRuntime), String> {
    let main_id = module.fn_by_name("main").ok_or("no `main/0` fn found")?.id;
    let mut runtime = IrInterpRuntime::fresh_with_root(module);
    runtime.set_task_code_image(1, Rc::new(CodeImage::planned(module, module_plan)?));
    runtime.enqueue_entry_with_image(1, main_id, vec![])?;
    let completions = runtime.drive_until_idle(tel, None)?;
    let halt_val = completions
        .iter()
        .rev()
        .find_map(|(pid, value)| {
            (*pid == 1).then(|| {
                runtime
                    .task(*pid)
                    .map(|task| value_to_halt(task as *const Process as *mut Process, *value))
            })
        })
        .flatten()
        .unwrap_or(0);
    Ok((halt_val, runtime))
}

/// Run a single test fn (no args) through the interp on a fresh Process.
/// Used by `fz test` (src/test_runner.rs). Each test gets its own heap +
/// mailbox so state can't leak between tests in the same module.
///
/// Returns Ok(()) if the test completes without an assertion failure;
/// returns Err(msg) on any interp/runtime/assertion error.
pub fn run_test_fn(tel: &dyn Telemetry, module: &Module, fn_id: FnId) -> Result<(), String> {
    let mut runtime = IrInterpRuntime::fresh();
    runtime.node = Rc::new(Node::new(module.atom_names.clone(), Vec::new()));
    let user_schemas = runtime.schemas();
    let consts = CompiledModuleConsts::empty();
    let task = Box::new(Process::from_consts(
        Rc::clone(&runtime.node),
        user_schemas,
        &consts,
        1,
        DEFAULT_REDUCTIONS_PER_QUANTUM,
    ));
    runtime.insert_task(1, task);
    let task_ptr = runtime.process_ptr(1).expect("run_test_fn installed pid 1");
    runtime.current_proc = task_ptr;
    unsafe { (*task_ptr).heap.set_owner(task_ptr) };
    let mut t = ConcreteTypes;
    let mut module_plan = plan_module(&mut t, module, &NullTelemetry);
    let diagnostics = resolve_module_types(&mut t, module, &mut module_plan);
    if let Some(diagnostic) = diagnostics.into_iter().next() {
        return Err(diagnostic.message);
    }
    let result = run_fn_typed(&mut runtime, &mut t, module, tel, &module_plan, fn_id, Vec::new());
    // fz-4mk — shutdown drain mirrors run_main's exit path: enqueue every
    // surviving resource's dtor and dispatch each as a real fz call. The dtor
    // helpers reach this task through `runtime.current_proc` (set above).
    unsafe {
        mso_drop_all_deferred(&mut (*task_ptr).heap);
    }
    if let Err(e) = drain_pending_dtors_interp(&mut runtime, &mut t, module, tel, &module_plan) {
        tel.event(&["fz", "runtime", "dtor_drain_failed"], crate::metadata! { error: e });
    }
    match result {
        Ok(InterpStep::Done(_)) => Ok(()),
        Ok(InterpStep::Yielded { .. }) => Err("test fn yielded outside scheduler drive".to_string()),
        Ok(InterpStep::Blocked(..)) | Ok(InterpStep::BlockedMatched(..)) => {
            Err("test fn blocked on receive with empty mailbox".to_string())
        }
        Err(e) => Err(e),
    }
}

fn value_to_halt(proc: *mut Process, v: AnyValue) -> i64 {
    match v {
        AnyValue::Null => 0,
        AnyValue::Int(i) => i,
        AnyValue::Float(f) => f.to_bits() as i64,
        AnyValue::Atom(v) => v as i64,
        AnyValue::EmptyList => 0,
        AnyValue::FnRef(_) => v.value(proc).expect("materialize fn ref halt value").raw() as i64,
        AnyValue::Ref(v) => v.raw_word() as i64,
    }
}

/// fz-4mk — shared work behind both the interp `fz_make_resource` BIF and
/// the JIT/AOT `MakeResourceHook` thunk: validate the dtor closure, then
/// allocate the off-heap `Resource` + on-heap stub on the current process
/// heap. The dtor body fires as real fz code at scheduler-boundary drain
/// via `fz_drain_dtor_entry` (JIT/AOT) or `run_fn` (interp); the
/// Resource's C-side dtor slot is the no-op so refcount→0 paths that
/// bypass the drain don't double-fire.
pub(crate) fn make_resource_in_current_process(
    proc: *mut Process,
    _module: &Module,
    payload: i64,
    dtor_closure: fz_runtime::any_value::AnyValue,
) -> Result<fz_runtime::any_value::AnyValue, String> {
    if dtor_closure.kind() != ValueKind::CLOSURE {
        return Err("make_resource: dtor arg is not a closure".to_string());
    }
    dtor_closure
        .heap_object_word()
        .and_then(closure_addr_from_tagged)
        .ok_or_else(|| "make_resource: dtor arg is not a closure".to_string())?;
    let handle = ResourceHandle::new(payload as u64, fz_resource_destructor_noop);
    let heap = &mut unsafe { &mut *proc }.heap;
    let stub = alloc_resource(heap, handle, dtor_closure);
    Ok(fz_runtime::any_value::AnyValue::heap_ptr(
        stub.as_raw(),
        ValueKind::RESOURCE,
    ))
}
