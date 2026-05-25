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
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::sync::Arc;

use crate::ast::ModuleName;
use crate::code_server::{CodeImage, CodeServer, CodeServerError};
use crate::fz_ir::ExportKey;
use crate::fz_ir::{FnId, Module};
use fz_runtime::heap::SchemaRegistry;
use fz_runtime::process::Process;

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
    tests_support_dtor_fired, tests_support_dtor_last_payload, tests_support_dtor_reset,
    tests_support_lock, tests_support_test_dtor_addr,
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

type InterpCodeImage = CodeImage<Module>;

/// Explicit owner for IR-interpreter runtime state.
///
/// fz-elu.3 introduces the container before moving scheduler operations onto
/// methods. fz-elu.2 makes the process table, run queue, resume entries, and
/// parked selective receives runtime-owned.
pub(crate) struct IrInterpRuntime {
    tasks: HashMap<u32, Box<Process>>,
    code_server: CodeServer<Module>,
    source_image_cache: HashMap<(usize, u64), Arc<InterpCodeImage>>,
    code_images: HashMap<u32, Arc<InterpCodeImage>>,
    next_pid: u32,
    schemas: Rc<RefCell<SchemaRegistry>>,
    tuple_schema_ids: HashMap<usize, u32>,
    run_queue: VecDeque<u32>,
    resume: HashMap<u32, ResumeEntry>,
    parked: HashMap<u32, InterpParked>,
}

impl IrInterpRuntime {
    pub(crate) fn fresh() -> Self {
        Self {
            tasks: HashMap::new(),
            code_server: CodeServer::new(),
            source_image_cache: HashMap::new(),
            code_images: HashMap::new(),
            next_pid: 2,
            schemas: Rc::new(RefCell::new(SchemaRegistry::new())),
            tuple_schema_ids: HashMap::new(),
            run_queue: VecDeque::new(),
            resume: HashMap::new(),
            parked: HashMap::new(),
        }
    }

    pub(crate) fn fresh_with_root(module: &Module) -> Self {
        let mut runtime = Self::fresh();
        let user_schemas = runtime.schemas();
        let (bs_tuple_arity1_schema, bs_tuple_arity3_schema) =
            runtime.register_bitstring_tuple_schemas();
        let mut process = Box::new(Process::new(user_schemas));
        process.pid = 1;
        process.atom_names = module.atom_names.clone();
        process.bs_tuple_arity1_schema = Some(bs_tuple_arity1_schema);
        process.bs_tuple_arity3_schema = Some(bs_tuple_arity3_schema);
        runtime.insert_task(1, process);
        let image = runtime
            .install_module_image(module)
            .expect("fresh root module image install");
        runtime.set_task_code_image(1, image);
        runtime
    }

    fn schemas(&self) -> Rc<RefCell<SchemaRegistry>> {
        self.schemas.clone()
    }

    fn register_bitstring_tuple_schemas(&mut self) -> (u32, u32) {
        let (arity1, arity3) = {
            let mut reg = self.schemas.borrow_mut();
            (
                reg.register(fz_runtime::heap::Schema::tuple_of_arity(1)),
                reg.register(fz_runtime::heap::Schema::tuple_of_arity(3)),
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
        use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema};
        let schema = Schema {
            name: format!("Tuple{}", arity),
            size: (arity * 8) as u32,
            fields: (0..arity)
                .map(|i| FieldDescriptor {
                    offset: (i * 8) as u32,
                    kind: FieldKind::AnyValue,
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

    fn set_task_code_image(&mut self, pid: u32, image: Arc<InterpCodeImage>) {
        if let Some(process) = self.tasks.get_mut(&pid) {
            process.atom_names = image.payload().atom_names.clone();
        }
        self.code_images.insert(pid, image);
    }

    fn task_code_image(&self, pid: u32) -> Option<Arc<InterpCodeImage>> {
        self.code_images.get(&pid).cloned()
    }

    pub(super) fn resolve_export(
        &self,
        key: &ExportKey,
    ) -> Result<(Arc<InterpCodeImage>, FnId), String> {
        self.code_server
            .resolve_export(key)
            .map_err(|e| format!("resolve interpreter export: {:?}", e))
    }

    fn install_module_image(&mut self, module: &Module) -> Result<Arc<InterpCodeImage>, String> {
        let source_key = (module as *const Module as usize, module_fingerprint(module));
        if let Some(image) = self.source_image_cache.get(&source_key) {
            return Ok(image.clone());
        }
        let root = ModuleName::root();
        let root_image =
            self.load_code_image(root.clone(), export_map_for(module, &root), module.clone())?;

        let mut module_names: Vec<ModuleName> = module
            .exports
            .iter()
            .map(|e| e.key.module.clone())
            .collect();
        module_names.sort();
        module_names.dedup();
        for module_name in module_names {
            self.load_code_image(
                module_name.clone(),
                export_map_for(module, &module_name),
                module.clone(),
            )?;
        }
        self.source_image_cache
            .insert(source_key, root_image.clone());
        Ok(root_image)
    }

    fn load_code_image(
        &mut self,
        module_name: ModuleName,
        exports: HashMap<ExportKey, FnId>,
        module: Module,
    ) -> Result<Arc<InterpCodeImage>, String> {
        match self
            .code_server
            .load(module_name.clone(), exports.clone(), module.clone())
        {
            Ok(image) => Ok(image),
            Err(CodeServerError::OldImagePinned { .. }) => {
                self.code_server
                    .hard_purge_old(&module_name)
                    .map_err(|e| format!("detach old interpreter image: {:?}", e))?;
                self.code_server
                    .load(module_name, exports, module)
                    .map_err(|e| format!("install interpreter code image after detach: {:?}", e))
            }
            Err(e) => Err(format!("install interpreter code image: {:?}", e)),
        }
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

    fn set_process_state(&mut self, pid: u32, state: fz_runtime::process::ProcessState) {
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
        let image = self.install_module_image(module)?;
        self.set_task_code_image(pid, image);
        self.resume.insert(pid, (fn_id, args, vec![]));
        self.run_queue.push_back(pid);
        self.set_process_state(pid, fz_runtime::process::ProcessState::Ready);
        Ok(())
    }

    pub(crate) fn drive_until_idle(
        &mut self,
        tel: &dyn crate::telemetry::Telemetry,
        keepalive_pid: Option<u32>,
    ) -> Result<Vec<(u32, AnyValue)>, String> {
        use fz_runtime::process::ProcessState;
        let mut completions = Vec::new();
        let mut t = crate::types::ConcreteTypes;

        'sched: while let Some(pid) = self.pop_runnable() {
            let image = self
                .task_code_image(pid)
                .ok_or_else(|| format!("pid {} has no interpreter code image", pid))?;
            let module = image.payload();
            let (fn_id, args, mut after) = self
                .take_resume(pid)
                .expect("pid in run_queue with no resume entry");
            let proc_ptr = self
                .process_ptr(pid)
                .expect("pid in run_queue with no process entry");
            unsafe { (*proc_ptr).state = ProcessState::Running };
            let prev = fz_runtime::process::CURRENT_PROCESS.with(|c| c.replace(proc_ptr));
            let mut step = run_fn(self, &mut t, module, tel, fn_id, args);
            loop {
                match step {
                    Ok(InterpStep::Done(val)) => {
                        if let Some((next_fn, next_caps)) = after.first().cloned() {
                            after.remove(0);
                            let mut next_args = vec![val];
                            next_args.extend(next_caps);
                            step = run_fn(self, &mut t, module, tel, next_fn, next_args);
                            continue;
                        }

                        fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
                        completions.push((pid, val));
                        if keepalive_pid == Some(pid) {
                            self.set_process_state(pid, ProcessState::Ready);
                            continue 'sched;
                        }

                        let prev =
                            fz_runtime::process::CURRENT_PROCESS.with(|c| c.replace(proc_ptr));
                        unsafe {
                            fz_runtime::procbin::mso_drop_all_deferred(&mut (*proc_ptr).heap);
                        }
                        if let Err(e) = drain_pending_dtors_interp(self, &mut t, module, tel) {
                            tel.event(
                                &["fz", "runtime", "dtor_drain_failed"],
                                crate::metadata! { error: e },
                            );
                        }
                        fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
                        self.set_process_state(pid, ProcessState::Exited);
                        continue 'sched;
                    }
                    Ok(InterpStep::Blocked(resume_fn, cap_vals, mut new_after)) => {
                        fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
                        new_after.extend(after);
                        self.set_process_state(pid, ProcessState::Blocked);
                        self.resume.insert(pid, (resume_fn, cap_vals, new_after));
                        continue 'sched;
                    }
                    Ok(InterpStep::BlockedMatched(park, mut new_after)) => {
                        fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
                        new_after.extend(after);
                        self.set_process_state(pid, ProcessState::Blocked);
                        self.parked.insert(pid, (park, new_after));
                        continue 'sched;
                    }
                    Err(e) => {
                        fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
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

    pub(crate) fn read_tuple_fields(
        &self,
        pid: u32,
        value: AnyValue,
        arity: usize,
    ) -> Result<Vec<AnyValue>, String> {
        let AnyValue::Ref(value_ref) = value else {
            return Err(format!("expected tuple ref, got {}", value.render()));
        };
        if value_ref.tag() != fz_runtime::any_value::ValueKind::STRUCT {
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
        let prev = fz_runtime::process::CURRENT_PROCESS.with(|c| c.replace(proc_ptr));
        let rendered = value.render();
        fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
        Ok(rendered)
    }
}

fn export_map_for(module: &Module, module_name: &ModuleName) -> HashMap<ExportKey, FnId> {
    module
        .exports
        .iter()
        .filter(|export| &export.key.module == module_name)
        .map(|export| (export.key.clone(), export.local_fn))
        .collect()
}

fn module_fingerprint(module: &Module) -> u64 {
    let mut h = DefaultHasher::new();
    format!("{}", module).hash(&mut h);
    h.finish()
}

/// Run `module`'s `main` fn through the interpreter.
///
/// Drives a cooperative run-queue loop: main starts at pid=1, spawned tasks
/// are enqueued and run one quantum at a time in FIFO order. Tasks that block
/// on receive park until a send wakes them. Loop exits when the queue is empty.
pub fn run_main(tel: &dyn crate::telemetry::Telemetry, module: &Module) -> Result<i64, String> {
    run_main_inner(tel, module).map(|(halt, _runtime)| halt)
}

#[cfg(test)]
pub(crate) fn run_main_with_runtime(
    tel: &dyn crate::telemetry::Telemetry,
    module: &Module,
) -> Result<(i64, IrInterpRuntime), String> {
    run_main_inner(tel, module)
}

fn run_main_inner(
    tel: &dyn crate::telemetry::Telemetry,
    module: &Module,
) -> Result<(i64, IrInterpRuntime), String> {
    let main_id = module.fn_by_name("main").ok_or("no `main/0` fn found")?.id;
    let mut runtime = IrInterpRuntime::fresh_with_root(module);
    runtime.enqueue_entry(module, 1, main_id, vec![])?;
    let completions = runtime.drive_until_idle(tel, None)?;
    let halt_val = completions
        .iter()
        .rev()
        .find_map(|(pid, value)| (*pid == 1).then_some(value_to_halt(*value)))
        .unwrap_or(0);
    Ok((halt_val, runtime))
}

/// Run a single test fn (no args) through the interp on a fresh Process.
/// Used by `fz test` (src/test_runner.rs). Each test gets its own heap +
/// mailbox so state can't leak between tests in the same module.
///
/// Returns Ok(()) if the test completes without an assertion failure;
/// returns Err(msg) on any interp/runtime/assertion error.
pub fn run_test_fn(
    tel: &dyn crate::telemetry::Telemetry,
    module: &Module,
    fn_id: FnId,
) -> Result<(), String> {
    let mut runtime = IrInterpRuntime::fresh_with_root(module);
    runtime.enqueue_entry(module, 1, fn_id, Vec::new())?;
    let completions = runtime.drive_until_idle(tel, None)?;
    if completions.iter().any(|(pid, _)| *pid == 1) {
        Ok(())
    } else {
        Err("test fn blocked on receive with empty mailbox".to_string())
    }
}

fn value_to_halt(v: AnyValue) -> i64 {
    match v {
        AnyValue::Null => 0,
        AnyValue::Int(i) => i,
        AnyValue::Float(f) => f.to_bits() as i64,
        AnyValue::Atom(v) => v as i64,
        AnyValue::EmptyList => 0,
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
    _module: &Module,
    payload: i64,
    dtor_closure: fz_runtime::any_value::AnyValue,
) -> Result<fz_runtime::any_value::AnyValue, String> {
    use fz_runtime::any_value::ValueKind;
    if dtor_closure.kind() != ValueKind::CLOSURE {
        return Err("make_resource: dtor arg is not a closure".to_string());
    }
    dtor_closure
        .heap_object_word()
        .and_then(fz_runtime::any_value::closure_addr_from_tagged)
        .ok_or_else(|| "make_resource: dtor arg is not a closure".to_string())?;
    let handle = fz_runtime::resource::ResourceHandle::new(
        payload as u64,
        fz_runtime::resource::fz_resource_destructor_noop,
    );
    let heap = &mut fz_runtime::process::current_process().heap;
    let stub = fz_runtime::resource::alloc_resource(heap, handle, dtor_closure);
    Ok(fz_runtime::any_value::AnyValue::heap_ptr(
        stub.as_raw(),
        ValueKind::RESOURCE,
    ))
}
