//! Backend interpreter for compiler2 programs.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::compiler2::transport::BoundValue;
use fz_runtime::any_value::AnyValueRef;
use fz_runtime::heap::{Schema, SchemaRegistry};
use fz_runtime::process::{DEFAULT_REDUCTIONS_PER_QUANTUM, Node, Process, ProcessState};
use fz_runtime::sched_core::SchedulingCore;
use fz_runtime::timer::TimerId;

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
    tests_support_dtor_fired, tests_support_dtor_last_payload, tests_support_dtor_reset,
    tests_support_integer_boolean_pair_addr, tests_support_lock, tests_support_resolved_symbol_addr,
    tests_support_scalar_pair_symbols, tests_support_test_dtor_addr,
};
use prim::*;
pub(crate) use value::AnyValue;
use value::*;

struct BackendContinuation {
    executable: Rc<crate::compiler2::BackendExecutable>,
    entry: crate::compiler2::ControlEntryId,
    env: Frame,
    /// A `try` handler frame: reached by a raise, never by a value. The
    /// body pops it when it completes.
    handler: bool,
}

type BackendBoundValue = BoundValue<AnyValue>;

/// The lane words of one transported value or call, held inline up to four.
pub(crate) type Lanes = smallvec::SmallVec<[AnyValue; 4]>;

/// The values a running executable holds, one slot per value id. The slot
/// count is the lowering's value count for the executable, so every id its
/// body names is in range; an insert outside the frame panics.
#[derive(Clone)]
pub(crate) struct Frame {
    slots: Vec<Option<BackendBoundValue>>,
}

impl Frame {
    pub(crate) fn sized(count: usize) -> Self {
        let mut slots = Vec::with_capacity(count);
        slots.resize_with(count, || None);
        Self { slots }
    }

    pub(crate) fn get(&self, id: crate::compiler2::ValueId) -> Option<&BackendBoundValue> {
        self.slots.get(id.as_u32() as usize).and_then(Option::as_ref)
    }

    pub(crate) fn insert(&mut self, id: crate::compiler2::ValueId, value: BackendBoundValue) {
        let slots = self.slots.len();
        let slot = self
            .slots
            .get_mut(id.as_u32() as usize)
            .unwrap_or_else(|| panic!("value {id:?} is outside a frame of {slots} slots"));
        *slot = Some(value);
    }

    /// Removes the value held for `id`, leaving the slot empty.
    pub(crate) fn take(&mut self, id: crate::compiler2::ValueId) -> Option<BackendBoundValue> {
        self.slots.get_mut(id.as_u32() as usize).and_then(Option::take)
    }

    pub(crate) fn clear(&mut self) {
        self.slots.iter_mut().for_each(|slot| *slot = None);
    }

    pub(crate) fn values_mut(&mut self) -> impl Iterator<Item = &mut BackendBoundValue> {
        self.slots.iter_mut().flatten()
    }
}

enum BackendResumeEntry {
    Executable {
        executable: Rc<crate::compiler2::BackendExecutable>,
        args: Lanes,
        continuations: Vec<BackendContinuation>,
    },
    Entry {
        executable: Rc<crate::compiler2::BackendExecutable>,
        entry: crate::compiler2::ControlEntryId,
        env: Frame,
        continuations: Vec<BackendContinuation>,
    },
}

struct BackendParkRecord {
    executable: Rc<crate::compiler2::BackendExecutable>,
    entry: crate::compiler2::ControlEntryId,
    env: Frame,
    continuations: Vec<BackendContinuation>,
    /// The timer that wakes this receive's `after` entry; `None` when the
    /// receive has no positive timeout.
    after_timer: Option<TimerId>,
}

impl BackendParkRecord {
    /// Every heap ref this parked receive holds: its environment and each
    /// continuation's. They are the roots a collection of the parked process
    /// forwards in place.
    fn heap_refs_mut(&mut self) -> Vec<&mut AnyValueRef> {
        let continuation_envs = self.continuations.iter_mut().map(|frame| &mut frame.env);
        std::iter::once(&mut self.env)
            .chain(continuation_envs)
            .flat_map(|env| env.values_mut())
            .flat_map(|value| match value {
                BoundValue::Absent => Vec::new(),
                BoundValue::Runtime(word) => vec![word],
                BoundValue::Transport { lanes, .. } => lanes.iter_mut().collect(),
            })
            .filter_map(AnyValue::heap_ref_mut)
            .collect()
    }
}

pub(crate) struct IrInterpRuntime {
    tasks: HashMap<u32, Box<Process>>,
    next_pid: u32,
    schemas: Rc<RefCell<SchemaRegistry>>,
    tuple_schema_ids: HashMap<usize, u32>,
    /// The run queue and timer wheel.
    core: SchedulingCore,
    backend_resume: HashMap<u32, BackendResumeEntry>,
    backend_parked: HashMap<u32, BackendParkRecord>,
    node: Rc<Node>,
    current_proc: *mut Process,
    callback_error: Option<String>,
    /// Generated trampolines for C variadic calls, built on first use. They
    /// carry the machine code the interpreter calls out through, so the
    /// runtime that hands out a trampoline owns the module it lives in.
    variadic_trampolines: Option<Box<extern_call::VariadicTrampolines>>,
}

impl IrInterpRuntime {
    pub(crate) fn fresh() -> Self {
        Self {
            tasks: HashMap::new(),
            next_pid: 2,
            schemas: Rc::new(RefCell::new(SchemaRegistry::new())),
            tuple_schema_ids: HashMap::new(),
            core: SchedulingCore::new(),
            backend_resume: HashMap::new(),
            backend_parked: HashMap::new(),
            node: Rc::new(Node::empty()),
            current_proc: std::ptr::null_mut(),
            callback_error: None,
            variadic_trampolines: None,
        }
    }

    pub(crate) fn fresh_with_atoms(atom_names: Vec<String>) -> Self {
        let mut runtime = Self::fresh();
        runtime.node = Rc::new(Node::new(atom_names));
        let user_schemas = runtime.schemas();
        let process = Box::new(Process::with_node(
            Rc::clone(&runtime.node),
            user_schemas,
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

    fn variadic_trampolines(&mut self) -> &mut extern_call::VariadicTrampolines {
        self.variadic_trampolines
            .get_or_insert_with(|| Box::new(extern_call::VariadicTrampolines::new()))
    }

    #[inline]
    pub(crate) fn cur_proc(&self) -> *mut Process {
        debug_assert!(!self.current_proc.is_null(), "cur_proc outside a quantum");
        self.current_proc
    }

    fn schemas(&self) -> Rc<RefCell<SchemaRegistry>> {
        self.schemas.clone()
    }

    fn tuple_schema_id(&mut self, arity: usize) -> u32 {
        if let Some(&id) = self.tuple_schema_ids.get(&arity) {
            return id;
        }
        let schema = Schema::tuple_of_arity(arity);
        let id = self.schemas.borrow_mut().register(schema);
        self.tuple_schema_ids.insert(arity, id);
        id
    }

    fn insert_task(&mut self, pid: u32, process: Box<Process>) {
        self.tasks.insert(pid, process);
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

    /// Queue `pid` to run; the scheduling core performs its transition to Ready.
    fn make_runnable(&mut self, pid: u32) {
        if let Some(process) = self.tasks.get_mut(&pid) {
            self.core.make_runnable(pid, &mut process.state);
        }
    }

    fn process_ref(&self, pid: u32) -> Option<&Process> {
        self.tasks.get(&pid).map(Box::as_ref)
    }

    fn record_callback_error(&mut self, error: String) {
        if self.callback_error.is_none() {
            self.callback_error = Some(error);
        }
    }

    pub(super) fn take_callback_error(&mut self) -> Option<String> {
        self.callback_error.take()
    }
}

fn value_to_halt(proc: *mut Process, v: AnyValue) -> i64 {
    match v {
        AnyValue::Null => 0,
        AnyValue::Int(i) => i,
        AnyValue::Float(f) => f.to_bits() as i64,
        AnyValue::Atom(v) => v as i64,
        AnyValue::EmptyList => 0,
        AnyValue::FnRef(..) => v.value(proc).expect("materialize fn ref halt value").raw() as i64,
        AnyValue::Ref(v) => v.raw().raw_word() as i64,
    }
}
