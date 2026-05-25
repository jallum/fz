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

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

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
use value::*;

use std::collections::VecDeque;

/// Per-task resume state: fn to call, captures (no message), and after-chain.
type ResumeEntry = (FnId, Vec<AnyValue>, Vec<(FnId, Vec<AnyValue>)>);

thread_local! {
    pub(super) static INTERP_TASKS: RefCell<HashMap<u32, Box<Process>>> =
        RefCell::new(HashMap::new());
    pub(super) static INTERP_NEXT_PID: Cell<u32> = const { Cell::new(2) };
    /// FIFO run-queue of pids ready to execute.
    pub(super) static INTERP_RUN_QUEUE: RefCell<VecDeque<u32>> = const { RefCell::new(VecDeque::new()) };
    /// Per-task resume state: (resume_fn, cap_vals, after_chain).
    /// cap_vals holds captures only (no message); interp_send prepends the
    /// message. after_chain is the sequence of (fn_id, caps) continuations to
    /// invoke in order after resume_fn returns, passing each return value on.
    pub(super) static INTERP_RESUME: RefCell<HashMap<u32, ResumeEntry>> =
        RefCell::new(HashMap::new());
    /// fz-yxs/fz-2v3 — selective-receive park records. Keyed by pid so
    /// that `interp_send` can probe an arriving message against the
    /// receiver's parked matcher without unwinding the scheduler.
    pub(super) static INTERP_PARKED: RefCell<HashMap<u32, InterpParked>> =
        RefCell::new(HashMap::new());
}

/// fz-yxs/fz-2v3 — value type for `INTERP_PARKED`. Factored out so
/// the TLS entry doesn't trip clippy's "very complex type" lint.
type InterpParked = (ParkRecord, Vec<(FnId, Vec<AnyValue>)>);

/// Explicit owner for IR-interpreter runtime state.
///
/// fz-elu.3 introduces the container before moving scheduler operations onto
/// methods. During the migration, `install_into_tls` and `sync_from_tls` are
/// the compatibility boundary for the existing TLS-based scheduler helpers.
pub(crate) struct IrInterpRuntime {
    tasks: HashMap<u32, Box<Process>>,
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
            next_pid: 2,
            schemas: Rc::new(RefCell::new(SchemaRegistry::new())),
            tuple_schema_ids: HashMap::new(),
            run_queue: VecDeque::new(),
            resume: HashMap::new(),
            parked: HashMap::new(),
        }
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

    fn enqueue_resume(&mut self, pid: u32, entry: ResumeEntry) {
        self.resume.insert(pid, entry);
        self.run_queue.push_back(pid);
    }

    fn install_into_tls(&mut self) {
        INTERP_TASKS.with(|t| *t.borrow_mut() = std::mem::take(&mut self.tasks));
        INTERP_NEXT_PID.with(|n| n.set(self.next_pid));
        INTERP_RUN_QUEUE.with(|q| *q.borrow_mut() = std::mem::take(&mut self.run_queue));
        INTERP_RESUME.with(|r| *r.borrow_mut() = std::mem::take(&mut self.resume));
        INTERP_PARKED.with(|p| *p.borrow_mut() = std::mem::take(&mut self.parked));
    }

    fn sync_from_tls(&mut self) {
        // Compatibility: existing tests still inspect INTERP_TASKS after
        // run_main. The process table moves onto IrInterpRuntime methods in
        // the next scheduler ticket; until then, leave TLS tasks in place.
        INTERP_NEXT_PID.with(|n| self.next_pid = n.get());
        INTERP_RUN_QUEUE.with(|q| self.run_queue = q.borrow().clone());
        INTERP_RESUME.with(|r| self.resume = r.borrow().clone());
        INTERP_PARKED.with(|p| self.parked = p.borrow().clone());
    }
}

/// Run `module`'s `main` fn through the interpreter.
///
/// Drives a cooperative run-queue loop: main starts at pid=1, spawned tasks
/// are enqueued and run one quantum at a time in FIFO order. Tasks that block
/// on receive park until a send wakes them. Loop exits when the queue is empty.
pub fn run_main(tel: &dyn crate::telemetry::Telemetry, module: &Module) -> Result<i64, String> {
    use fz_runtime::process::ProcessState;
    let main_id = module.fn_by_name("main").ok_or("no `main/0` fn found")?.id;
    interp_reset_state();
    let mut runtime = IrInterpRuntime::fresh();
    let user_schemas = runtime.schemas();
    let (bs_tuple_arity1_schema, bs_tuple_arity3_schema) =
        runtime.register_bitstring_tuple_schemas();
    let mut main_process = Box::new(Process::new(user_schemas));
    main_process.pid = 1;
    main_process.atom_names = module.atom_names.clone();
    main_process.state = ProcessState::Ready;
    main_process.bs_tuple_arity1_schema = Some(bs_tuple_arity1_schema);
    main_process.bs_tuple_arity3_schema = Some(bs_tuple_arity3_schema);
    runtime.insert_task(1, main_process);
    runtime.enqueue_resume(1, (main_id, vec![], vec![]));
    runtime.install_into_tls();
    let mut t = crate::types::ConcreteTypes;

    let mut halt_val = 0i64;
    'sched: while let Some(pid) = INTERP_RUN_QUEUE.with(|q| q.borrow_mut().pop_front()) {
        let (fn_id, args, mut after) = INTERP_RESUME
            .with(|r| r.borrow_mut().remove(&pid))
            .expect("pid in run_queue with no resume entry");
        let proc_ptr = INTERP_TASKS
            .with(|t| {
                t.borrow()
                    .get(&pid)
                    .map(|b| b.as_ref() as *const _ as *mut Process)
            })
            .expect("pid in run_queue with no process entry");
        unsafe { (*proc_ptr).state = ProcessState::Running };
        let prev = fz_runtime::process::CURRENT_PROCESS.with(|c| c.replace(proc_ptr));
        let mut step = run_fn(&mut runtime, &mut t, module, tel, fn_id, args);
        // Process the after-chain: each Done value is threaded into the next fn.
        loop {
            match step {
                Ok(InterpStep::Done(val)) => {
                    if let Some((next_fn, next_caps)) = after.first().cloned() {
                        after.remove(0);
                        let mut next_args = vec![val];
                        next_args.extend(next_caps);
                        step = run_fn(&mut runtime, &mut t, module, tel, next_fn, next_args);
                        // loop continues
                    } else {
                        // fz-4mk — shutdown drain: walk the MSO chain to
                        // enqueue every still-live resource's dtor, then
                        // dispatch each as a real fz call while the process
                        // is still alive (CURRENT_PROCESS is `proc_ptr`,
                        // heap is intact, scheduler can drive callbacks
                        // into externs the dtor body invokes).
                        unsafe {
                            fz_runtime::procbin::mso_drop_all_deferred(&mut (*proc_ptr).heap);
                        }
                        if let Err(e) =
                            drain_pending_dtors_interp(&mut runtime, &mut t, module, tel)
                        {
                            tel.event(
                                &["fz", "runtime", "dtor_drain_failed"],
                                crate::metadata! { error: e },
                            );
                        }
                        fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
                        INTERP_TASKS.with(|t| {
                            if let Some(p) = t.borrow_mut().get_mut(&pid) {
                                p.state = ProcessState::Exited;
                            }
                        });
                        if pid == 1 {
                            halt_val = value_to_halt(val);
                        }
                        continue 'sched;
                    }
                }
                Ok(InterpStep::Blocked(resume_fn, cap_vals, mut new_after)) => {
                    fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
                    new_after.extend(after);
                    INTERP_TASKS.with(|t| {
                        if let Some(p) = t.borrow_mut().get_mut(&pid) {
                            p.state = ProcessState::Blocked;
                        }
                    });
                    INTERP_RESUME
                        .with(|r| r.borrow_mut().insert(pid, (resume_fn, cap_vals, new_after)));
                    continue 'sched;
                }
                // fz-yxs/fz-2v3 — park record + after-chain stashed under
                // INTERP_PARKED so the next interp_send can probe the
                // matcher against the arriving message without unwinding.
                Ok(InterpStep::BlockedMatched(park, mut new_after)) => {
                    fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
                    new_after.extend(after);
                    INTERP_TASKS.with(|t| {
                        if let Some(p) = t.borrow_mut().get_mut(&pid) {
                            p.state = ProcessState::Blocked;
                        }
                    });
                    INTERP_PARKED.with(|p| {
                        p.borrow_mut().insert(pid, (park, new_after));
                    });
                    continue 'sched;
                }
                Err(e) => {
                    fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
                    runtime.sync_from_tls();
                    return Err(e);
                }
            }
        }
    }

    runtime.sync_from_tls();
    Ok(halt_val)
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
    interp_reset_state();
    let mut runtime = IrInterpRuntime::fresh();
    let user_schemas = runtime.schemas();
    let mut task = Box::new(Process::new(user_schemas));
    task.pid = 1;
    task.atom_names = module.atom_names.clone();
    runtime.insert_task(1, task);
    runtime.install_into_tls();
    let task_ptr = INTERP_TASKS
        .with(|tasks| {
            tasks
                .borrow()
                .get(&1)
                .map(|p| p.as_ref() as *const Process as *mut Process)
        })
        .expect("run_test_fn installed pid 1");
    let prev = fz_runtime::process::CURRENT_PROCESS.with(|c| c.replace(task_ptr));
    let mut t = crate::types::ConcreteTypes;
    let result = run_fn(&mut runtime, &mut t, module, tel, fn_id, Vec::new());
    // fz-4mk — shutdown drain mirrors run_main's exit path: enqueue every
    // surviving resource's dtor and dispatch each as a real fz call while
    // CURRENT_PROCESS is still pointing at the test task's heap.
    unsafe {
        fz_runtime::procbin::mso_drop_all_deferred(&mut (*task_ptr).heap);
    }
    if let Err(e) = drain_pending_dtors_interp(&mut runtime, &mut t, module, tel) {
        tel.event(
            &["fz", "runtime", "dtor_drain_failed"],
            crate::metadata! { error: e },
        );
    }
    fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
    runtime.sync_from_tls();
    match result {
        Ok(InterpStep::Done(_)) => Ok(()),
        Ok(InterpStep::Blocked(..)) | Ok(InterpStep::BlockedMatched(..)) => {
            Err("test fn blocked on receive with empty mailbox".to_string())
        }
        Err(e) => Err(e),
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
