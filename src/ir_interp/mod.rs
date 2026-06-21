//! Backend interpreter for compiler2 programs.

use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

use crate::compiler2::transport::TransportValue;
use crate::exec::runtime::ExitRecord;
use crate::fz_ir::Module;
use fz_runtime::any_value::{ValueKind, closure_addr_from_tagged};
use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema, SchemaRegistry};
use fz_runtime::process::{CompiledModuleConsts, DEFAULT_REDUCTIONS_PER_QUANTUM, Node, Process, ProcessState};
use fz_runtime::resource::{ResourceHandle, alloc_resource, fz_resource_destructor_noop};

mod backend;
mod binop;
mod dispatch_exec;
mod extern_call;
mod prim;
mod value;

pub(crate) use backend::{encode_macro_entry_inputs, run_backend_entry_on_process, run_backend_main};
use binop::*;
#[cfg(test)]
pub(crate) use extern_call::{
    tests_support_dtor_fired, tests_support_dtor_last_payload, tests_support_dtor_reset, tests_support_lock,
    tests_support_test_dtor_addr,
};
use prim::*;
pub(crate) use value::AnyValue;
use value::*;

#[derive(Clone)]
struct BackendContinuation {
    executable: usize,
    entry: crate::compiler2::ControlEntryId,
    env: HashMap<crate::compiler2::ValueId, BackendBoundValue>,
}

type BackendBoundValue = TransportValue<AnyValue>;

enum BackendResumeEntry {
    Executable {
        executable: usize,
        args: Vec<AnyValue>,
        continuations: Vec<BackendContinuation>,
    },
    Entry {
        executable: usize,
        entry: crate::compiler2::ControlEntryId,
        env: HashMap<crate::compiler2::ValueId, BackendBoundValue>,
        continuations: Vec<BackendContinuation>,
    },
}

struct BackendParkRecord {
    executable: usize,
    clauses: Vec<crate::compiler2::ReceiveClause>,
    dispatch: crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
    bindings: crate::compiler2::DispatchBindings,
    env: HashMap<crate::compiler2::ValueId, BackendBoundValue>,
    continuations: Vec<BackendContinuation>,
}

pub(crate) struct IrInterpRuntime {
    tasks: HashMap<u32, Box<Process>>,
    next_pid: u32,
    schemas: Rc<RefCell<SchemaRegistry>>,
    tuple_schema_ids: HashMap<usize, u32>,
    run_queue: VecDeque<u32>,
    backend_resume: HashMap<u32, BackendResumeEntry>,
    backend_parked: HashMap<u32, BackendParkRecord>,
    node: Rc<Node>,
    current_proc: *mut Process,
}

impl IrInterpRuntime {
    pub(crate) fn fresh() -> Self {
        Self {
            tasks: HashMap::new(),
            next_pid: 2,
            schemas: Rc::new(RefCell::new(SchemaRegistry::new())),
            tuple_schema_ids: HashMap::new(),
            run_queue: VecDeque::new(),
            backend_resume: HashMap::new(),
            backend_parked: HashMap::new(),
            node: Rc::new(Node::empty()),
            current_proc: std::ptr::null_mut(),
        }
    }

    pub(crate) fn fresh_with_atoms(atom_names: Vec<String>) -> Self {
        let mut runtime = Self::fresh();
        runtime.node = Rc::new(Node::new(atom_names, Vec::new()));
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

    pub(crate) fn with_process(mut process: Process, atom_names: &[String]) -> Self {
        for atom in atom_names {
            process.node.intern_atom(atom);
        }
        let mut runtime = Self::fresh();
        runtime.node = Rc::clone(&process.node);
        runtime.schemas = process.heap.schemas_registry();
        let (bs_tuple_arity1_schema, bs_tuple_arity3_schema) = runtime.register_bitstring_tuple_schemas();
        process.bs_tuple_arity1_schema = Some(bs_tuple_arity1_schema);
        process.bs_tuple_arity3_schema = Some(bs_tuple_arity3_schema);
        process.pid = 1;
        process.state = ProcessState::New;
        process.detach_runtime_state();
        runtime.insert_task(1, Box::new(process));
        runtime
    }

    pub(crate) fn take_process(&mut self, pid: u32) -> Option<Process> {
        self.tasks.remove(&pid).map(|process| {
            let proc_ptr: *mut Process = (&*process) as *const Process as *mut Process;
            if self.current_proc == proc_ptr {
                self.current_proc = std::ptr::null_mut();
            }
            let mut process = *process;
            process.detach_runtime_state();
            process
        })
    }

    #[inline]
    pub(crate) fn cur_proc(&self) -> *mut Process {
        debug_assert!(!self.current_proc.is_null(), "cur_proc outside a quantum");
        self.current_proc
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

    fn pop_runnable(&mut self) -> Option<u32> {
        self.run_queue.pop_front()
    }

    fn next_pid(&mut self) -> u32 {
        let pid = self.next_pid;
        self.next_pid += 1;
        pid
    }

    fn process_ptr(&mut self, pid: u32) -> Option<*mut Process> {
        self.tasks.get_mut(&pid).map(|p| p.as_mut() as *mut Process)
    }

    fn set_process_state(&mut self, pid: u32, state: ProcessState) {
        if let Some(process) = self.tasks.get_mut(&pid) {
            process.state = state;
        }
    }

    fn process_ref(&self, pid: u32) -> Option<&Process> {
        self.tasks.get(&pid).map(Box::as_ref)
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

fn is_truthy(v: AnyValue) -> bool {
    !v.is_false() && !v.is_nil()
}

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
