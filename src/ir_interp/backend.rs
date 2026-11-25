use std::borrow::Cow;

use crate::literal_term::LiteralTerm;
use std::rc::Rc;

use super::binop::{eval_binop, eval_unop, unpack_callable, unpack_closure};
use super::dispatch_exec::{Dispatch, DispatchInputs, DispatchSource, dispatch_values, project_from_root};
use super::extern_call::{ExternCallValue, call_lowered_extern};
use super::prim::{interp_list_cons, interp_map_get};
use super::value::{
    AnyValue, HeapRef, binary_literal_value, interp_bool_value, interp_empty_list_value, interp_named_field,
    interp_nil_value, interp_read_bit_field, interp_value_from_ref_word, with_value_ref,
};
use super::*;
use crate::compiler2::pull::TransportCarrier;
use crate::compiler2::transport::{ShapeDescr, ShapeId, TransportLayout, TransportPosition, TransportStore};
use crate::compiler2::{
    BackendBody, BackendConstructionMemberAdapter, BackendConstructionWrapper, BackendEntry, BackendExecutable,
    BackendProgram, BackendReceive, BackendStep as ProgramStep, BackendTail, CallEdge, CallTarget, ClosureCallEdge,
    ControlDestination, ExecutableDispatch, UndefinedFunction, ValueId,
};
use crate::compiler2::{ExecutableKey, FunctionId, RunFailure};
use crate::dispatch_matrix::pattern::{LastResort, RaisedField};
use crate::exec::runtime::emit_runtime_event;
use crate::fz_ir::{BinOp as IrBinOp, FnId, Module, ModuleAtoms, UnOp as IrUnOp};
use crate::runtime_type_predicate::CallableShape;
use crate::telemetry::{Telemetry, TelemetryExt};
use crate::types::ClosureTarget;
use fz_runtime::any_value::{
    AnyValue as RuntimeAnyValue, AnyValueRef, SlotLayout, Stored, ValueKind, closure_addr_from_tagged,
};
use fz_runtime::construction::FzBsField;
use fz_runtime::delivery::Delivery;
use fz_runtime::exec_ctx::{Argv, ExecCtx, NO_ARGV, timer_cancel, timer_schedule};
use fz_runtime::heap::deep_copy_any_value_ref;
use fz_runtime::heap::{Collected, Schema};
use fz_runtime::ir_runtime::{
    fz_bs_build, fz_bs_field_spec, fz_list_reuse_or_cons_parts, fz_map_dest_begin, fz_map_dest_begin_update,
    fz_map_dest_freeze, fz_map_dest_publish, fz_map_dest_put, fz_mark_published_ref_aliased, fz_struct_get_field_ref,
    fz_struct_module, fz_struct_reuse_or_copy, fz_struct_store_ref,
};
use fz_runtime::module_name::{ModuleName, STRUCT_MODULE_FIELD};
use fz_runtime::output::{EXPAND_HOOK, OUTPUT_HOOK, OutputContext, OutputSink, WARN_HOOK};
use fz_runtime::process::{DEFAULT_REDUCTIONS_PER_QUANTUM, Disposition, Process, ProcessState};
use fz_runtime::sched::{ProbeOutcome, SendProbe, drain_in_queue, gift_match, gift_message, self_send};
use fz_runtime::sched_core::{
    MAIN_PID, Scheduler, SchedulingCore, end_quantum, halt_hook, next_runnable, timer_cancel_hook, timer_schedule_hook,
};
use fz_runtime::telemetry::{Raise, RunEnded, RuntimeEvent, report_sites};
use fz_runtime::timer::TimerId;

enum BackendRunStep {
    Done(AnyValue),
    Blocked,
    Failed,
}

enum BackendEvalState {
    Executable {
        executable: Rc<BackendExecutable>,
        args: Lanes,
        continuations: Vec<BackendContinuation>,
    },
    Entry {
        executable: Rc<BackendExecutable>,
        entry: crate::compiler2::ControlEntryId,
        env: Frame,
        continuations: Vec<BackendContinuation>,
    },
}

enum BackendEvalTransition {
    Next(BackendEvalState),
    Done(AnyValue),
    Blocked,
    /// The process failed: its line went to the fault sink, and nothing
    /// after the failure runs.
    Failed,
}

/// What an interpreter run is for, which decides where a failing process's
/// line goes and whether the entry process outlives its completion.
#[derive(Clone, Copy, PartialEq, Eq)]
enum BackendRun {
    /// A program: a failure prints its line on stderr and ends the process.
    Program,
    /// A macro expansion: a failure is a compile error, and the macro's
    /// process stays alive for the next expansion.
    Macro,
}

/// Runs one closed Compiler2 backend program through the shared interpreter
/// runtime without reopening planner or type-resolution work. Answers the
/// main process's halt value.
pub(crate) fn run_backend_main<T: Telemetry + ?Sized>(
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &T,
    output: &dyn OutputSink,
    argv: &Argv,
    program: &BackendProgram,
) -> Result<i64, RunFailure> {
    let pool_outstanding_before_run = fz_runtime::heap::pool_outstanding_blocks();
    let atoms = ModuleAtoms::from_names(program.atom_names.iter().cloned());
    let mut runtime = IrInterpRuntime::fresh_with_atoms(atoms.names().to_vec());
    runtime.register_struct_schemas(
        program
            .struct_schemas
            .entries()
            .map(|(name, fields)| (name.as_ref(), fields.as_ref())),
    );
    let module = Module {
        atoms,
        ..Module::default()
    };
    let outcome = (|| -> Result<i64, RunFailure> {
        runtime.enqueue_backend_entry(
            MAIN_PID,
            backend_executable_ref(program, types, program.entry())?,
            Lanes::new(),
        )?;
        drive_backend_until_idle(
            &mut runtime,
            types,
            transport,
            tel,
            output,
            argv,
            program,
            &module,
            BackendRun::Program,
        )?;
        RunFailure::from_main_status(runtime.core.halted().unwrap_or(0))?;
        Ok(runtime.process_ref(MAIN_PID).map_or(0, |main| main.halt_value))
    })();
    output.flush();
    let counts = runtime.counts;
    let node = Rc::clone(&runtime.node);
    drop(runtime);
    tel.raw_event1(&INTERP_RAN, &counts);
    report_sites(&node, |event| emit_runtime_event(tel, event));
    emit_runtime_event(
        tel,
        RuntimeEvent::RunEnded(RunEnded::sample(pool_outstanding_before_run)),
    );
    outcome
}

pub(crate) fn run_backend_entry_on_process<T: Telemetry + ?Sized>(
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &T,
    output: &dyn OutputSink,
    program: &BackendProgram,
    process: Process,
    args: Vec<AnyValue>,
) -> (Process, Result<AnyValue, String>) {
    let mut runtime = IrInterpRuntime::with_process(process, program.atom_names.iter());
    let atoms = ModuleAtoms::from_names(
        runtime
            .process_ref(MAIN_PID)
            .expect("macro runtime should own pid 1")
            .node
            .atom_names(),
    );
    runtime.register_struct_schemas(
        program
            .struct_schemas
            .entries()
            .map(|(name, fields)| (name.as_ref(), fields.as_ref())),
    );
    let module = Module {
        atoms,
        ..Module::default()
    };
    let result = (|| {
        runtime.enqueue_backend_entry(
            MAIN_PID,
            backend_executable_ref(program, types, program.entry())?,
            args.into(),
        )?;
        drive_backend_until_idle(
            &mut runtime,
            types,
            transport,
            tel,
            output,
            &NO_ARGV,
            program,
            &module,
            BackendRun::Macro,
        )?
        .ok_or_else(|| "backend macro entry produced no completion".to_string())
    })();
    let process = runtime
        .take_process(MAIN_PID)
        .expect("macro runtime should return its source process");
    (process, result)
}

impl IrInterpRuntime {
    fn enqueue_backend_entry(
        &mut self,
        pid: u32,
        executable: Rc<BackendExecutable>,
        args: Lanes,
    ) -> Result<(), String> {
        self.enqueue_backend_executable(pid, executable, args, Vec::new())
    }

    fn enqueue_backend_executable(
        &mut self,
        pid: u32,
        executable: Rc<BackendExecutable>,
        args: Lanes,
        continuations: Vec<BackendContinuation>,
    ) -> Result<(), String> {
        if !self.tasks.contains_key(&pid) {
            return Err(format!("enqueue_backend_entry: unknown pid {}", pid));
        }
        self.backend_resume.insert(
            pid,
            BackendResumeEntry::Executable {
                executable,
                args,
                continuations,
            },
        );
        self.make_runnable(pid);
        Ok(())
    }

    /// Record that `pid` resumes at `entry` and queue it to run.
    fn enqueue_backend_local_entry(
        &mut self,
        pid: u32,
        executable: Rc<BackendExecutable>,
        entry: crate::compiler2::ControlEntryId,
        env: Frame,
        continuations: Vec<BackendContinuation>,
    ) -> Result<(), String> {
        if !self.tasks.contains_key(&pid) {
            return Err(format!("enqueue_backend_local_entry: unknown pid {}", pid));
        }
        self.backend_resume.insert(
            pid,
            BackendResumeEntry::Entry {
                executable,
                entry,
                env,
                continuations,
            },
        );
        self.make_runnable(pid);
        Ok(())
    }

    fn take_backend_resume(&mut self, pid: u32) -> Option<BackendResumeEntry> {
        self.backend_resume.remove(&pid)
    }

    pub(super) fn spawn_backend(
        &mut self,
        sender: *mut Process,
        executable: Rc<BackendExecutable>,
        args: Lanes,
    ) -> Result<u32, String> {
        if sender.is_null() {
            return Err("spawn: no sender process".to_string());
        }
        let pid = self.next_pid();
        let user_schemas = self.schemas();
        let node = Rc::clone(&self.node);
        let mut child = Box::new(Process::with_node(
            node,
            user_schemas,
            pid,
            DEFAULT_REDUCTIONS_PER_QUANTUM,
        ));
        let sender_view = unsafe { &*sender }.heap.view();
        let args = args
            .into_iter()
            .map(|value| match value {
                AnyValue::Ref(value) => {
                    let copied = deep_copy_any_value_ref(value.raw(), &sender_view, &mut child.heap);
                    AnyValue::from_any_value_ref(copied)
                }
                value => Ok(value),
            })
            .collect::<Result<Lanes, _>>()?;
        self.insert_task(pid, child);
        self.enqueue_backend_entry(pid, executable, args)?;
        Ok(pid)
    }

    /// The `after` timer `timer` of the receive `pid` is parked on has
    /// expired: queue the receive's `after` entry. A stale timer, whose
    /// receiver a message already woke, is dropped.
    fn wake_receive_after(
        &mut self,
        transport: &TransportStore,
        program: &BackendProgram,
        pid: u32,
        timer: TimerId,
    ) -> Result<(), String> {
        let Some(receiver) = self.process_ptr(pid) else {
            return Ok(());
        };
        let delivery = unsafe { &*receiver }.delivery.lock();
        if self.backend_parked.get(&pid).and_then(|park| park.after_timer) != Some(timer) {
            return Ok(());
        }
        let park = self.backend_parked.remove(&pid).expect("checked above");
        drop(delivery);
        let receive = parked_receive(&park)?;
        let after = receive
            .after
            .as_ref()
            .ok_or_else(|| format!("backend receive entry {} has a timer but no after", park.entry.as_u32()))?;
        let after_entry = after.entry;
        let receiver = self.process_ptr(pid).ok_or_else(|| format!("unknown receiver {pid}"))?;
        self.current_proc = receiver;
        let BackendParkRecord {
            executable,
            env,
            continuations,
            ..
        } = park;
        let mut env = env;
        enter_entry(self, transport, program, &executable, &mut env, after_entry, None, &[])?;
        self.enqueue_backend_local_entry(pid, executable, after_entry, env, continuations)
    }

    pub(super) fn send_ref<T: Telemetry + ?Sized>(
        &mut self,
        types: &mut crate::compiler2::Types,
        transport: &TransportStore,
        tel: &T,
        program: &BackendProgram,
        module: &Module,
        receiver_pid: &u32,
        msg_ref: AnyValueRef,
    ) -> Result<(), String> {
        let Some(receiver) = self.tasks.get(receiver_pid) else {
            return Ok(());
        };
        if receiver.state == ProcessState::Exited {
            return Ok(());
        }
        let sender = unsafe { &mut *self.cur_proc() };
        if sender.pid == *receiver_pid {
            self_send(sender, msg_ref);
            return Ok(());
        }
        let receiver = self.process_ptr(*receiver_pid).expect("receiver checked above");
        let mut delivery = unsafe { &*receiver }.delivery.lock();
        let probe = match self.backend_parked.remove(receiver_pid) {
            Some(mut park) => {
                let outcome = self.probe_parked_receive(
                    types,
                    transport,
                    program,
                    module,
                    &mut park,
                    sender,
                    (unsafe { &*receiver }, &mut delivery),
                    msg_ref,
                )?;
                self.backend_parked.insert(*receiver_pid, park);
                outcome
            }
            None => gift_message(sender, &mut delivery, *receiver_pid, msg_ref),
        };
        drop(delivery);
        emit_runtime_event(tel, RuntimeEvent::SendProbe(&probe));
        if probe.outcome == ProbeOutcome::Hit {
            self.make_runnable(*receiver_pid);
        }
        Ok(())
    }

    /// Match `msg` against the receive `park` records, on the sender, with
    /// the receiver's delivery lock held by the caller. A hit gifts the winning
    /// clause's roots and cancels the after-timer; a miss, or a receive another sender
    /// already matched, gifts the message.
    #[allow(clippy::too_many_arguments)]
    fn probe_parked_receive(
        &mut self,
        types: &mut crate::compiler2::Types,
        transport: &TransportStore,
        program: &BackendProgram,
        module: &Module,
        park: &mut BackendParkRecord,
        sender: &mut Process,
        (receiver, delivery): (&Process, &mut Delivery),
        msg_ref: AnyValueRef,
    ) -> Result<SendProbe, String> {
        if delivery.has_pending_match() {
            return Ok(gift_message(sender, delivery, receiver.pid, msg_ref));
        }
        let receive = parked_receive(park)?;
        let msg = AnyValue::from_any_value_ref(msg_ref)?;
        let reductions_before = sender.reductions_remaining;
        let matched = match_backend_receive(
            self,
            types,
            transport,
            program,
            module,
            &receive.outcomes,
            &receive.dispatch,
            msg,
            &receive.bindings,
            &park.env,
        )?;
        let reductions = i64::from(reductions_before) - i64::from(sender.reductions_remaining);
        let Some((clause_idx, roots)) = matched else {
            return Ok(SendProbe {
                reductions,
                ..gift_message(sender, delivery, receiver.pid, msg_ref)
            });
        };
        let roots = roots
            .into_iter()
            .map(|root| root.as_any_value_ref(sender))
            .collect::<Result<Vec<_>, String>>()?;
        if let Some(timer) = park.after_timer.take() {
            timer_cancel(receiver, timer);
        }
        Ok(gift_match(
            sender,
            delivery,
            receiver.pid,
            clause_idx,
            &roots,
            reductions,
        ))
    }

    /// Graft every gift queued on `pid` into its heap and, when a sender
    /// matched its parked receive, record the winning outcome entry as the
    /// resume. Runs at the start of a dispatch, before the resume is taken.
    fn deliver_in_queue(
        &mut self,
        transport: &TransportStore,
        program: &BackendProgram,
        module: &Module,
        pid: u32,
    ) -> Result<(), String> {
        let receiver = self
            .process_ptr(pid)
            .expect("backend pid in run queue with no process entry");
        let task = unsafe { &mut *receiver };
        let mut delivery = task.delivery.lock();
        let Some((clause_idx, roots)) = drain_in_queue(&mut delivery, &mut task.heap, &mut task.mailbox) else {
            return Ok(());
        };
        let park = self
            .backend_parked
            .remove(&pid)
            .expect("a matched receive is still parked");
        drop(delivery);
        let receive = parked_receive(&park)?;
        let edge = receive
            .outcomes
            .get(clause_idx)
            .expect("receive winning outcome has one target edge");
        let target = edge.target;
        let roots = roots
            .into_iter()
            .map(AnyValue::from_any_value_ref)
            .collect::<Result<Vec<_>, String>>()?;
        let params = project_receive_arguments(receiver, module, &receive.dispatch, edge, &roots)?;
        self.current_proc = receiver;
        let BackendParkRecord {
            executable,
            env,
            continuations,
            ..
        } = park;
        let mut env = env;
        let params = whole_params(params);
        enter_entry(self, transport, program, &executable, &mut env, target, None, &params)?;
        self.backend_resume.insert(
            pid,
            BackendResumeEntry::Entry {
                executable,
                entry: target,
                env,
                continuations,
            },
        );
        Ok(())
    }
}

/// The receive tail a parked process waits in.
fn parked_receive(park: &BackendParkRecord) -> Result<&BackendReceive, String> {
    let entry = entries_for_executable(&park.executable)?
        .get(park.entry.as_u32() as usize)
        .ok_or_else(|| format!("backend parked entry {} is out of bounds", park.entry.as_u32()))?;
    let BackendTail::Receive(receive) = &entry.tail else {
        return Err(format!("backend parked entry {} is not a receive", park.entry.as_u32()));
    };
    Ok(receive)
}

/// Interpreter-side implementation of the scheduler services exposed through
/// `Process::ctx`. The adapter lives on `drive_backend_until_idle`'s stack;
/// callbacks are synchronous, so every erased pointer below remains valid for
/// the whole physical extern call and is never retained by the runtime crate.
struct BackendSchedulerAdapter<T: Telemetry + ?Sized> {
    runtime: *mut IrInterpRuntime,
    types: *mut crate::compiler2::Types,
    transport: *const TransportStore,
    tel: *const T,
    program: *const BackendProgram,
    module: *const Module,
}

impl<T: Telemetry + ?Sized> Scheduler for BackendSchedulerAdapter<T> {
    fn core(&mut self) -> &mut SchedulingCore {
        &mut unsafe { &mut *self.runtime }.core
    }

    fn wake_expired(&mut self, pid: u32, timer: TimerId) {
        let runtime = unsafe { &mut *self.runtime };
        let woke = runtime.wake_receive_after(unsafe { &*self.transport }, unsafe { &*self.program }, pid, timer);
        if let Err(error) = woke {
            runtime.record_callback_error(error);
        }
    }

    fn observe(&mut self, event: RuntimeEvent<'_>) {
        emit_runtime_event(unsafe { &*self.tel }, event);
    }

    /// Collect `process` with the heap refs of its parked receive as the
    /// transient roots, and write the forwarded refs back. Every other
    /// interpreter-held value of a process is consumed before its quantum
    /// ends, so a process that is not parked holds nothing across the
    /// boundary.
    fn collect_heap<'p>(&mut self, process: &'p mut Process) -> Collected<'p> {
        let runtime = unsafe { &mut *self.runtime };
        assert!(
            !runtime.backend_resume.contains_key(&process.pid),
            "an interpreted quantum ends with its resume consumed"
        );
        match runtime.backend_parked.get_mut(&process.pid) {
            Some(park) => process.collect(park),
            None => process.collect(&mut []),
        }
    }

    /// Interpret the destructor closure on `process`. A failure is recorded
    /// for `take_backend_callback_error`, which the run loop surfaces.
    fn run_destructor(&mut self, _process: &mut Process, closure: u64, payload: u64) {
        let runtime = unsafe { &mut *self.runtime };
        let ran = run_pending_dtor(
            runtime,
            unsafe { &mut *self.types },
            unsafe { &*self.transport },
            unsafe { &*self.tel },
            unsafe { &*self.program },
            unsafe { &*self.module },
            closure,
            payload,
        );
        if let Err(error) = ran {
            runtime.record_callback_error(error);
        }
    }
}

/// The next process to run, or `None` once the interpreter is idle. A wake
/// that failed while the core serviced a timer surfaces here as the error.
fn next_backend_runnable<T: Telemetry + ?Sized>(
    adapter: *mut BackendSchedulerAdapter<T>,
) -> Result<Option<u32>, String> {
    let adapter = unsafe { &mut *adapter };
    let next = next_runnable(adapter);
    match unsafe { &mut *adapter.runtime }.take_callback_error() {
        Some(error) => Err(error),
        None => Ok(next),
    }
}

/// The fault sink of a macro run: a failure during expansion is a compile
/// error carrying the failure's line, never the exit of a program.
unsafe extern "C" fn macro_fault_hook<T: Telemetry + ?Sized>(scheduler: *mut (), line: *const u8, len: usize) {
    let adapter = unsafe { &mut *(scheduler as *mut BackendSchedulerAdapter<T>) };
    let runtime = unsafe { &mut *adapter.runtime };
    let line = unsafe { std::slice::from_raw_parts(line, len) };
    runtime.record_callback_error(String::from_utf8_lossy(line).into_owned());
}

/// The raise hook of an interpreted run: every raise becomes a
/// `fz.runtime.raise` event on the run's telemetry.
unsafe extern "C" fn interp_raise_hook<T: Telemetry + ?Sized>(
    scheduler: *mut (),
    kind: *const u8,
    kind_len: usize,
    name: *const u8,
    name_len: usize,
    depth: usize,
    stack_bytes: usize,
) {
    let adapter = unsafe { &*(scheduler as *mut BackendSchedulerAdapter<T>) };
    let record = unsafe { Raise::from_hook_args(kind, kind_len, name, name_len, depth, stack_bytes) };
    emit_runtime_event(unsafe { &*adapter.tel }, RuntimeEvent::Raise(&record));
}

extern "C" fn interp_spawn_hook<T: Telemetry + ?Sized>(
    sender: *mut Process,
    scheduler: *mut (),
    closure_ref_word: u64,
) -> u32 {
    let adapter = unsafe { &mut *(scheduler as *mut BackendSchedulerAdapter<T>) };
    let runtime = unsafe { &mut *adapter.runtime };
    let result = (|| {
        let closure_ref = AnyValueRef::from_raw_word(closure_ref_word)
            .map_err(|error| format!("fz_spawn: invalid closure ref: {error:?}"))?;
        let closure = AnyValue::from_any_value_ref(closure_ref)?;
        let (fn_id, captures) = unpack_callable(closure, sender)?;
        let (target, inputs) = construction_wrapper_invocation(
            runtime,
            unsafe { &mut *adapter.types },
            unsafe { &*adapter.transport },
            unsafe { &*adapter.program },
            unsafe { &*adapter.module },
            fn_id,
            &captures,
            &[],
        )?;
        runtime.spawn_backend(sender, target, inputs)
    })();
    match result {
        Ok(pid) => pid,
        Err(error) => {
            runtime.record_callback_error(error);
            0
        }
    }
}

extern "C" fn interp_send_hook<T: Telemetry + ?Sized>(
    sender: *mut Process,
    scheduler: *mut (),
    receiver_pid: u32,
    msg_ref_word: u64,
) {
    let adapter = unsafe { &mut *(scheduler as *mut BackendSchedulerAdapter<T>) };
    let runtime = unsafe { &mut *adapter.runtime };
    let result = AnyValueRef::from_raw_word(msg_ref_word)
        .map_err(|error| format!("fz_send: invalid message ref: {error:?}"))
        .and_then(|msg| {
            debug_assert_eq!(sender, runtime.cur_proc(), "fz_send sender must be current process");
            runtime.send_ref(
                unsafe { &mut *adapter.types },
                unsafe { &*adapter.transport },
                unsafe { &*adapter.tel },
                unsafe { &*adapter.program },
                unsafe { &*adapter.module },
                &receiver_pid,
                msg,
            )
        });
    if let Err(error) = result {
        runtime.record_callback_error(error);
    }
}

fn drive_backend_until_idle<T: Telemetry + ?Sized>(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &T,
    output: &dyn OutputSink,
    argv: &Argv,
    program: &BackendProgram,
    module: &Module,
    run: BackendRun,
) -> Result<Option<AnyValue>, String> {
    let mut kept_completion = None;
    let output = OutputContext::new(output);
    let mut scheduler_adapter = BackendSchedulerAdapter {
        runtime,
        types,
        transport,
        tel,
        program,
        module,
    };
    let adapter: *mut BackendSchedulerAdapter<T> = &mut scheduler_adapter;
    let mut exec_ctx = ExecCtx {
        scheduler: adapter as *mut (),
        output_context: output.as_ptr(),
        spawn: Some(interp_spawn_hook::<T>),
        send: Some(interp_send_hook::<T>),
        fault: Some(match run {
            BackendRun::Program => fz_runtime::failure::STDERR_FAULT_HOOK,
            BackendRun::Macro => macro_fault_hook::<T>,
        }),
        halt: Some(halt_hook::<BackendSchedulerAdapter<T>>()),
        raise: Some(interp_raise_hook::<T>),
        output: Some(OUTPUT_HOOK),
        warn: Some(WARN_HOOK),
        expand: Some(EXPAND_HOOK),
        timer_schedule: Some(timer_schedule_hook::<BackendSchedulerAdapter<T>>()),
        timer_cancel: Some(timer_cancel_hook::<BackendSchedulerAdapter<T>>()),
        argv,
    };

    while let Some(pid) = next_backend_runnable(adapter)? {
        // Gifts queued by senders become this heap's before any code runs; a
        // matched receive becomes the resume entry here.
        runtime.deliver_in_queue(transport, program, module, pid)?;
        let resume = runtime
            .take_backend_resume(pid)
            .expect("backend pid in run queue with no backend resume");
        let proc_ptr = runtime
            .process_ptr(pid)
            .expect("backend pid in run queue with no process entry");
        unsafe {
            (*proc_ptr).state = ProcessState::Running;
            (*proc_ptr).reset_reduction_budget();
            (*proc_ptr).ctx = &mut exec_ctx;
        }
        runtime.current_proc = proc_ptr;
        let stack_marker = 0u8;
        unsafe { (*proc_ptr).stack_base = &stack_marker as *const u8 as usize };
        let step = run_backend_resume(runtime, types, transport, tel, program, module, resume);
        unsafe { (*proc_ptr).stack_base = 0 };
        match step? {
            BackendRunStep::Done(value) => {
                if run == BackendRun::Macro && pid == MAIN_PID {
                    // Lent by a caller that holds refs into its heap, so no
                    // collection may move it. Kept alive for its next entry:
                    // off the run queue until that entry queues it.
                    kept_completion = Some(value);
                    runtime.set_process_state(pid, ProcessState::Blocked);
                    continue;
                }
                unsafe { (*proc_ptr).halt_value = value_to_halt(proc_ptr, value) };
            }
            BackendRunStep::Failed => {}
            BackendRunStep::Blocked => runtime.set_process_state(pid, ProcessState::Blocked),
        }
        let disposition = unsafe { end_quantum(&mut *adapter, &mut *proc_ptr) };
        if let Some(error) = runtime.take_callback_error() {
            return Err(error);
        }
        match disposition {
            Disposition::Exited | Disposition::Parked => {}
            Disposition::Requeue => {
                return Err(format!(
                    "interpreted process {pid} yielded; the interpreter never yields"
                ));
            }
        }
    }

    Ok(kept_completion)
}

fn run_backend_resume<T: Telemetry + ?Sized>(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &T,
    program: &BackendProgram,
    module: &Module,
    resume: BackendResumeEntry,
) -> Result<BackendRunStep, String> {
    let mut state = match resume {
        BackendResumeEntry::Executable {
            executable,
            args,
            continuations,
        } => BackendEvalState::Executable {
            executable,
            args,
            continuations,
        },
        BackendResumeEntry::Entry {
            executable,
            entry,
            env,
            continuations,
        } => BackendEvalState::Entry {
            executable,
            entry,
            env,
            continuations,
        },
    };

    loop {
        let next = match state {
            BackendEvalState::Executable {
                executable,
                args,
                continuations,
            } => step_backend_executable(
                runtime,
                types,
                transport,
                tel,
                program,
                module,
                executable,
                args,
                continuations,
            )?,
            BackendEvalState::Entry {
                executable,
                entry,
                env,
                continuations,
            } => {
                let executable_ref = executable.as_ref();
                let BackendBody::Clauses { entries, .. } = &executable_ref.body else {
                    return Err(format!("backend executable {:?} is not clause-backed", executable.key));
                };
                step_eval_entry(
                    runtime,
                    types,
                    transport,
                    tel,
                    program,
                    module,
                    &executable,
                    entries,
                    entry,
                    env,
                    continuations,
                )?
            }
        };
        match next {
            BackendEvalTransition::Next(next) => state = next,
            BackendEvalTransition::Done(value) => return Ok(BackendRunStep::Done(value)),
            BackendEvalTransition::Blocked => return Ok(BackendRunStep::Blocked),
            BackendEvalTransition::Failed => return Ok(BackendRunStep::Failed),
        }
    }
}

fn continue_backend_value(
    runtime: &mut IrInterpRuntime,
    transport: &TransportStore,
    program: &BackendProgram,
    value: BackendBoundValue,
    mut continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
    let Some(frame) = continuations.pop() else {
        return Ok(BackendEvalTransition::Done(materialize_backend_value(
            transport,
            runtime.cur_proc(),
            &value,
        )?));
    };
    if frame.handler {
        return Err(format!(
            "a value reached the try handler frame of executable {:?} entry {}; the body pops it first",
            frame.executable.key,
            frame.entry.as_u32()
        ));
    }
    let executable = frame.executable.as_ref();
    let mut env = frame.env;
    enter_entry(
        runtime,
        transport,
        program,
        executable,
        &mut env,
        frame.entry,
        Some(value),
        &[],
    )
    .map_err(|error| {
        format!(
            "backend continuation delivery executable={:?} entry={}: {error}",
            frame.executable.key,
            frame.entry.as_u32()
        )
    })?;
    Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
        executable: frame.executable.clone(),
        entry: frame.entry,
        env,
        continuations,
    }))
}

fn step_backend_executable<T: Telemetry + ?Sized>(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &T,
    program: &BackendProgram,
    module: &Module,
    executable: Rc<BackendExecutable>,
    args: Lanes,
    continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
    runtime.counts.calls += 1;
    match &executable.body {
        BackendBody::Extern { signature } => step_extern_executable(
            runtime,
            types,
            transport,
            program,
            module,
            &executable,
            signature,
            None,
            &args,
            continuations,
        ),
        BackendBody::Clauses { clauses, entries, .. } => {
            let semantic_inputs = bind_executable_inputs(transport, types, runtime, &executable, &args)?;
            let Some(dispatch) = &executable.abi.materialized.entry_dispatch else {
                return Err(format!(
                    "backend executable {:?} has {} clauses but no settled entry dispatch",
                    executable.key,
                    clauses.len()
                ));
            };
            let Some(selected) = select_clause(
                runtime,
                types,
                transport,
                program,
                module,
                dispatch,
                &semantic_inputs,
                &executable,
            )?
            else {
                return raise_unmatched_entry(
                    runtime,
                    transport,
                    program,
                    &executable,
                    dispatch,
                    &semantic_inputs,
                    continuations,
                );
            };
            let clause = clauses
                .get(selected.clause)
                .ok_or_else(|| format!("backend clause {} is out of bounds", selected.clause))?;
            runtime.counts.frames += 1;
            let mut env = Frame::sized(executable.value_count);
            for (param, value) in clause.params.iter().copied().zip(semantic_inputs) {
                if let Some(value) = value {
                    env.insert(param, value);
                }
            }
            enter_entry(
                runtime,
                transport,
                program,
                &executable,
                &mut env,
                clause.entry,
                None,
                &selected.handed,
            )?;
            step_eval_entry(
                runtime,
                types,
                transport,
                tel,
                program,
                module,
                &executable,
                entries,
                clause.entry,
                env,
                continuations,
            )
        }
    }
}

/// Which clause of an executable's entry dispatch its arguments choose.
/// An extern is a function with one typed clause: its entry dispatch, when the
/// call's types leave one to ask, selects that clause or raises the arm of
/// last resort as an ordinary function's does.
fn step_extern_executable(
    runtime: &mut IrInterpRuntime,
    types: &crate::compiler2::Types,
    transport: &TransportStore,
    program: &BackendProgram,
    module: &Module,
    executable: &BackendExecutable,
    signature: &crate::compiler2::LoweredExtern,
    extern_marshals: Option<&[crate::fz_ir::ExternTy]>,
    args: &[AnyValue],
    continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
    if let Some(dispatch) = &executable.abi.materialized.entry_dispatch {
        let semantic_inputs = bind_executable_inputs(transport, types, runtime, executable, args)?;
        if select_clause(
            runtime,
            types,
            transport,
            program,
            module,
            dispatch,
            &semantic_inputs,
            executable,
        )?
        .is_none()
        {
            return raise_unmatched_entry(
                runtime,
                transport,
                program,
                executable,
                dispatch,
                &semantic_inputs,
                continuations,
            );
        }
    }
    let words = extern_argument_words(executable, signature, args)?;
    let value = call_lowered_extern(runtime, signature, extern_marshals, &words)?;
    continue_after_extern(runtime, transport, program, value, continuations)
}

/// A dispatch input in the form it is held: a cursor stays a cursor, so the
/// dispatch asks of it what it can without the binary being made, and every
/// other value is the word it is.
fn held_or_whole(
    transport: &TransportStore,
    proc: *mut Process,
    env: &Frame,
    value: ValueId,
) -> Result<BackendBoundValue, String> {
    match env_get_value(env, value)? {
        held @ BackendBoundValue::Transport { shape, .. }
            if matches!(transport.interners().shape(*shape), ShapeDescr::Cursor { .. }) =>
        {
            Ok(held.clone())
        }
        _ => env_get(transport, proc, env, value).map(BackendBoundValue::Runtime),
    }
}

/// The words an extern receives. An input that arrives as two lanes is a
/// cursor, which a `binary_cursor` parameter takes as its source and position;
/// a whole binary there is itself at position 0. Every other input is its one
/// lane.
fn extern_argument_words(
    executable: &BackendExecutable,
    signature: &crate::compiler2::LoweredExtern,
    lanes: &[AnyValue],
) -> Result<Lanes, String> {
    let mut remaining = lanes;
    let mut words = Lanes::new();
    for input in executable.abi.semantic_inputs.iter() {
        let (own, rest) = remaining.split_at(input.layout.reprs.len().min(remaining.len()));
        remaining = rest;
        let wire = signature.params.get(input.semantic_index);
        match (wire, own) {
            (Some(crate::fz_ir::ExternTy::BinaryCursor), [whole]) => words.extend([*whole, AnyValue::Int(0)]),
            (_, [word]) => words.push(*word),
            (Some(crate::fz_ir::ExternTy::BinaryCursor), [source, position]) => words.extend([*source, *position]),
            _ => {
                return Err(format!(
                    "extern `{}` argument {} arrives in {} lanes, which its wire type does not read",
                    signature.symbol,
                    input.semantic_index,
                    own.len()
                ));
            }
        }
    }
    Ok(words)
}

fn raise_unmatched_entry(
    runtime: &mut IrInterpRuntime,
    transport: &TransportStore,
    program: &BackendProgram,
    executable: &BackendExecutable,
    dispatch: &ExecutableDispatch,
    semantic_inputs: &[Option<BackendBoundValue>],
    continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
    let last_resort = dispatch.plan().last_resort.as_ref().ok_or_else(|| {
        format!(
            "internal error: executable {:?} matched no clause and its clauses raise nothing",
            executable.key
        )
    })?;
    raise_last_resort(
        runtime,
        transport,
        program,
        last_resort,
        DispatchInputs::Values(semantic_inputs),
        continuations,
    )
}

/// The clause an entry dispatch selected, and the value of each subject the
/// clause binds, which the deciding run already holds.
#[derive(Debug)]
struct SelectedClause {
    clause: usize,
    handed: Vec<(ValueId, BackendBoundValue)>,
}

/// Which clause of `clauses` the entry dispatch chooses for `args`. An extern
/// has no clauses, so selecting its one outcome hands nothing.
fn select_clause(
    runtime: &mut IrInterpRuntime,
    types: &crate::compiler2::Types,
    transport: &TransportStore,
    program: &BackendProgram,
    module: &Module,
    dispatch: &ExecutableDispatch,
    args: &[Option<BackendBoundValue>],
    executable: &BackendExecutable,
) -> Result<Option<SelectedClause>, String> {
    let clauses = match &executable.body {
        BackendBody::Clauses { clauses, .. } => clauses.as_slice(),
        BackendBody::Extern { .. } => &[],
    };
    let plan = dispatch.plan();
    refuse_omitted_required_inputs(plan, args)?;
    let values = dispatch_values(runtime.cur_proc(), transport, plan, DispatchSource::Inputs(args))?;
    // Dispatch reads an input in whatever form it arrived in: a tuple delivered
    // as lanes is questioned lane-wise, never rebuilt.
    let operands = values.over(transport, args);
    let handed = clauses
        .iter()
        .flat_map(|clause| clause.arguments.iter().map(|argument| argument.subject));
    let Some(mut decided) = Dispatch::new(runtime, types, program, module, plan, operands)
        .reading(handed)
        .run()?
    else {
        return Ok(None);
    };
    let clause = dispatch
        .clause_index(decided.outcome())
        .ok_or_else(|| format!("internal error: entry outcome {:?} names no clause", decided.outcome()))?;
    let handed = clauses
        .get(clause)
        .map(|clause| &clause.arguments[..])
        .unwrap_or_default()
        .iter()
        .map(|argument| {
            let layout = entry_param_layout(executable, argument.parameter)?;
            let value = decided
                .subject_handed(argument.subject, layout)
                .map_err(|_| format!("winning outcome lacks subject {:?}", argument.subject))?;
            Ok((argument.parameter, value))
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(Some(SelectedClause { clause, handed }))
}

/// An input the plan reads has to have arrived. The demand lattice says which
/// inputs a plan reads; a caller is free to omit any other.
fn refuse_omitted_required_inputs(
    plan: &crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
    args: &[Option<BackendBoundValue>],
) -> Result<(), String> {
    for ordinal in (0..plan.input_demand().len()).filter(|ordinal| plan.required_input(*ordinal)) {
        if args.get(ordinal).and_then(Option::as_ref).is_none() {
            return Err(format!(
                "backend clause dispatch required omitted semantic input {ordinal}"
            ));
        }
    }
    Ok(())
}

/// The CONSTRUCTION a runtime code word denotes, in the terms the type lattice
/// uses: the function it runs, and the projected capture types it closed over.
///
/// A callable value the backend built through a construction wrapper carries
/// that wrapper's synthetic identity, which is this backend's own numbering;
/// the wrapper owns the ordered source capture annotations. Every other callable
/// value carries its function's own id directly and closes over nothing a test
/// can name, so it answers as a construction over no captures.
pub(super) fn backend_callable_identity(
    types: &crate::compiler2::Types,
    transport: &TransportStore,
    program: &BackendProgram,
    code: u64,
) -> Option<CallableShape> {
    let fn_id = FnId(u32::try_from(code).ok()?);
    let Some(wrapper) = construction_wrapper_for_fn(program, fn_id) else {
        return Some(CallableShape {
            target: ClosureTarget(fn_id.0),
            captures: Vec::new(),
        });
    };
    let callable = transport.interners().callable(wrapper.callable);
    Some(CallableShape {
        target: ClosureTarget(callable.function?.as_u32()),
        captures: wrapper
            .captures
            .iter()
            .map(|capture| types.runtime_type_predicate(&capture.ty))
            .collect(),
    })
}

/// The function a runtime code word runs, unwrapping a construction wrapper.
///
/// The wrapper's word is this backend's own numbering, so it is never a
/// `FunctionId`; the program is what translates it back.
fn backend_callable_function(transport: &TransportStore, program: &BackendProgram, fn_id: FnId) -> Option<FunctionId> {
    match construction_wrapper_for_fn(program, fn_id) {
        Some(wrapper) => transport.interners().callable(wrapper.callable).function,
        None => Some(FunctionId::from_fn_id(fn_id)),
    }
}

fn step_eval_entry<T: Telemetry + ?Sized>(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &T,
    program: &BackendProgram,
    module: &Module,
    executable: &Rc<BackendExecutable>,
    entries: &[BackendEntry],
    entry_id: crate::compiler2::ControlEntryId,
    mut env: Frame,
    mut continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
    runtime.counts.entries += 1;
    let entry = entries
        .get(entry_id.as_u32() as usize)
        .ok_or_else(|| format!("backend entry {} is out of bounds", entry_id.as_u32()))?;
    eval_steps(
        runtime,
        types,
        tel,
        transport,
        program,
        module,
        executable,
        &entry.steps,
        &mut env,
        &mut continuations,
    )
    .map_err(|error| {
        format!(
            "backend executable {:?} function {} entry {} step evaluation failed: {error}",
            executable.key,
            executable.key.activation.function.as_u32(),
            entry_id.as_u32()
        )
    })?;
    if let BackendTail::DirectCall { args, .. } | BackendTail::ClosureCall { args, .. } = &entry.tail {
        for arg in args {
            if arg.ownership == crate::fz_ir::OwnershipMode::Share
                && let Some(value) = env.get(arg.value)
            {
                publish_backend_capture(runtime.cur_proc(), value)?;
            }
        }
    }
    match &entry.tail {
        BackendTail::Value { value, dest } => match dest {
            ControlDestination::Return => {
                // Zero-lane return contracts need no environment read. This is ABI
                // width, not semantic absence; decoding retains tuple/callable shape.
                let returns_no_lanes = executable.abi.return_layout.layout.publishes_no_lanes();
                let result = if returns_no_lanes && env.get(*value).is_none() {
                    decode_transport_layout(
                        transport,
                        &[],
                        TransportLayout {
                            structural: executable.abi.return_layout.layout.structural,
                            carrier: executable.abi.return_layout.layout.carrier,
                        },
                        &mut 0,
                    )?
                } else {
                    env.take(*value)
                        .ok_or_else(|| format!("backend value {} is unbound", value.as_u32()))?
                };
                continue_backend_value(runtime, transport, program, result, continuations)
            }
            // A resume that wants nothing never had the value delivered to this
            // entry, so the read waits for a resume that asks for it.
            ControlDestination::Deliver(target) => {
                let delivered = env.get(*value).cloned();
                enter_entry(
                    runtime,
                    transport,
                    program,
                    executable,
                    &mut env,
                    *target,
                    delivered,
                    &[],
                )?;
                Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                    executable: executable.clone(),
                    entry: *target,
                    env,
                    continuations,
                }))
            }
        },
        BackendTail::DirectCall {
            target,
            selector,
            args,
            dest,
            ..
        } => {
            let (callee, extern_marshals) = match target {
                CallEdge::Direct(direct) => (&direct.callee, direct.extern_marshals.as_deref()),
                CallEdge::Dispatch(dispatch) => {
                    let inputs = selector
                        .iter()
                        .copied()
                        .chain(args.iter().map(|arg| arg.value))
                        .enumerate()
                        .map(|(index, input)| {
                            let bound = if dispatch.plan.required_input(index) {
                                held_or_whole(transport, runtime.cur_proc(), &env, input).map_err(|error| {
                                    format!(
                                        "backend dispatch call requires input {index} value {}: {error}",
                                        input.as_u32()
                                    )
                                })?
                            } else {
                                BackendBoundValue::Runtime(interp_nil_value())
                            };
                            Ok(Some(bound))
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    let values = dispatch_values(
                        runtime.cur_proc(),
                        transport,
                        &dispatch.plan,
                        DispatchSource::Inputs(&inputs),
                    )?;
                    let operands = values.over(transport, &inputs);
                    let Some(decided) =
                        Dispatch::new(runtime, types, program, module, &dispatch.plan, operands).run()?
                    else {
                        let last_resort = dispatch.plan.last_resort.as_ref().ok_or_else(|| {
                            format!(
                                "backend dispatch callsite in executable {:?} missed an exhaustive dispatch",
                                executable.key
                            )
                        })?;
                        return raise_last_resort(
                            runtime,
                            transport,
                            program,
                            last_resort,
                            DispatchInputs::Values(&inputs),
                            continuations,
                        );
                    };
                    let outcome = decided.outcome();
                    let arm = dispatch
                        .arm(outcome)
                        .ok_or_else(|| format!("backend dispatch outcome {:?} has no target", outcome))?;
                    (&arm.callee, arm.extern_marshals.as_deref())
                }
                CallEdge::Indirect { .. } => {
                    return Err(format!(
                        "backend direct callsite in executable {:?} materialized as an indirect closure edge; Indirect is closure-call-only",
                        executable.key
                    ));
                }
            };
            if let CallTarget::Undefined(undefined) = callee {
                return raise_undefined_function(
                    runtime,
                    transport,
                    program,
                    undefined,
                    *selector,
                    &env,
                    continuations,
                );
            }
            eval_backend_direct_call_edge(
                runtime,
                types,
                transport,
                program,
                module,
                callee,
                args,
                extern_marshals,
                env,
                executable,
                dest.clone(),
                continuations,
            )
        }
        BackendTail::ClosureCall {
            edge,
            callsite,
            callee,
            args,
            dest,
            ..
        } => {
            let callee_value = env.get(*callee);
            // The recorded call form carries the decision the artifact layer
            // made. A direct edge names its target and the capture count that
            // target declares, and the captures come out of the callee value's
            // own lanes; a seam call goes through the boxed apply wrapper. This
            // door emits what that one answer promised, exactly as native does.
            let (executable_target, call_args) = match edge {
                ClosureCallEdge::Direct { target, capture_count } => {
                    let callee_executable = backend_executable_ref(program, types, target)?;
                    let capture_inputs_end = *capture_count;
                    let captures = match callee_value {
                        Some(BackendBoundValue::Transport { shape, lanes })
                            if matches!(transport.interners().shape(*shape), ShapeDescr::Callable(_)) =>
                        {
                            transport_field_views(transport, *shape, lanes)?
                        }
                        _ => Vec::new(),
                    };
                    let mut lanes = Lanes::new();
                    for binding in callee_executable
                        .abi
                        .semantic_inputs
                        .iter()
                        .filter(|binding| binding.semantic_index < capture_inputs_end)
                    {
                        if binding.layout.publishes_no_lanes() {
                            continue;
                        }
                        let capture = captures.get(binding.semantic_index).ok_or_else(|| {
                            format!(
                                "closure call executable={:?} function={} callsite={} calls {:?} directly, but callee value {} carries no capture {}",
                                executable.key,
                                executable.key.activation.function.as_u32(),
                                callsite.as_u32(),
                                callee_executable.key,
                                callee.as_u32(),
                                binding.semantic_index
                            )
                        })?;
                        encode_runtime_input_binding(
                            transport,
                            program,
                            runtime.cur_proc(),
                            capture,
                            binding,
                            &mut lanes,
                        )?;
                    }
                    lanes.extend(encode_call_args(
                        transport,
                        program,
                        types,
                        runtime,
                        callee_executable.as_ref(),
                        &env,
                        args,
                        capture_inputs_end,
                    )?);
                    (callee_executable, lanes)
                }
                ClosureCallEdge::Seam | ClosureCallEdge::Dead => {
                    let callee_value = callee_value.ok_or_else(|| {
                        format!(
                            "closure call executable={:?} function={} callsite={} callee_value={}: backend value {} is unbound",
                            executable.key,
                            executable.key.activation.function.as_u32(),
                            callsite.as_u32(),
                            callee.as_u32(),
                            callee.as_u32()
                        )
                    })?;
                    let materialized = materialize_backend_value(transport, runtime.cur_proc(), callee_value)?;
                    let (fn_id, capture_lanes) = match materialized {
                        AnyValue::FnRef(fn_id, _, _) => (fn_id, Vec::new()),
                        other => unpack_closure(other.value(runtime.cur_proc())?).map_err(|error| {
                            format!(
                                "closure call executable={:?} function={} callsite={} callee_value={}: {error}",
                                executable.key,
                                executable.key.activation.function.as_u32(),
                                callsite.as_u32(),
                                callee.as_u32()
                            )
                        })?,
                    };
                    let wrapper = construction_wrapper_for_fn(program, fn_id).ok_or_else(|| {
                        format!(
                            "backend closure call executable={:?} function={} callsite={} reached function {} through the apply seam, which publishes no construction wrapper",
                            executable.key,
                            executable.key.activation.function.as_u32(),
                            callsite.as_u32(),
                            fn_id.0
                        )
                    })?;
                    let arg_values = args
                        .iter()
                        .map(|arg| env_get(transport, runtime.cur_proc(), &env, arg.value))
                        .collect::<Result<Vec<_>, _>>()?;
                    let member =
                        select_construction_member(runtime, types, transport, program, module, wrapper, &arg_values)?;
                    let callee_executable = backend_executable_ref(program, types, &member.target)?;
                    let lanes = ConstructionInputEncoder {
                        runtime,
                        types,
                        transport,
                        program,
                        target: callee_executable.as_ref(),
                        wrapper,
                        member,
                    }
                    .encode(&capture_lanes, args, |arg| {
                        env_get_value(&env, arg.value).map(Cow::Borrowed)
                    })?;
                    (callee_executable, lanes)
                }
            };
            let continuations = match dest {
                ControlDestination::Return => continuations,
                ControlDestination::Deliver(target) => {
                    let mut continuations = continuations;
                    continuations.push(BackendContinuation {
                        executable: executable.clone(),
                        entry: *target,
                        env: retain_continuation_captures(transport, entries, *target, env)?,
                        handler: false,
                    });
                    continuations
                }
            };
            Ok(BackendEvalTransition::Next(BackendEvalState::Executable {
                executable: executable_target,
                args: call_args,
                continuations,
            }))
        }
        BackendTail::If {
            cond,
            then_entry,
            else_entry,
        } => {
            let target = if env_get(transport, runtime.cur_proc(), &env, *cond)?.is_truthy() {
                *then_entry
            } else {
                *else_entry
            };
            enter_entry(runtime, transport, program, executable, &mut env, target, None, &[])?;
            Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                executable: executable.clone(),
                entry: target,
                env,
                continuations,
            }))
        }
        BackendTail::Dispatch {
            inputs,
            bindings,
            dispatch,
        } => {
            // A decision reads an input in whatever form it is bound in, and an
            // input it never reads was never bound.
            let pinned_values = dispatch_values(
                runtime.cur_proc(),
                transport,
                &dispatch.plan,
                DispatchSource::Bound { env: &env, bindings },
            )?;
            let operands = pinned_values.over_frame(transport, &env, inputs);
            let run = Dispatch::new(runtime, types, program, module, &dispatch.plan, operands)
                .reading(dispatch.argument_subjects());
            let (target, params) = match run.run()? {
                Some(mut decided) => {
                    let edge = dispatch.outcome(decided.outcome());
                    // The winning outcome's arguments come off the run that
                    // decided it, which already holds the subjects it produced.
                    let params = edge
                        .arguments
                        .iter()
                        .map(|argument| {
                            let layout = entry_param_layout(executable, argument.parameter)?;
                            let value = decided
                                .subject_handed(argument.subject, layout)
                                .map_err(|_| format!("winning outcome lacks subject {:?}", argument.subject))?;
                            Ok((argument.parameter, value))
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    (edge.target, params)
                }
                None => match (dispatch.miss_entry, &dispatch.plan.last_resort) {
                    (Some(miss_entry), _) => (miss_entry, Vec::new()),
                    (None, Some(last_resort)) => {
                        return raise_last_resort(
                            runtime,
                            transport,
                            program,
                            last_resort,
                            DispatchInputs::Frame { env: &env, ids: inputs },
                            continuations,
                        );
                    }
                    (None, None) => {
                        return Err(format!(
                            "internal error: the decision at entry {} of executable {:?} reached its fail, which has no last resort",
                            entry_id.as_u32(),
                            executable.key
                        ));
                    }
                },
            };
            enter_entry(runtime, transport, program, executable, &mut env, target, None, &params)?;
            Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                executable: executable.clone(),
                entry: target,
                env,
                continuations,
            }))
        }
        BackendTail::Receive(receive) => {
            let bindings = &receive.bindings;
            let dispatch = &receive.dispatch;
            let outcomes = &receive.outcomes;
            let after = receive.after.as_ref();
            let mailbox_len = unsafe { &mut *runtime.cur_proc() }.mailbox.len();
            let mut hit = None;
            for mb_idx in 0..mailbox_len {
                let msg = {
                    let proc = unsafe { &mut *runtime.cur_proc() };
                    AnyValue::from_any_value_ref(proc.mailbox.get(mb_idx).expect("an index below the length"))?
                };
                if let Some((clause_idx, roots)) = match_backend_receive(
                    runtime, types, transport, program, module, outcomes, dispatch, msg, bindings, &env,
                )? {
                    let edge = &outcomes[clause_idx];
                    let params = project_receive_arguments(runtime.cur_proc(), module, dispatch, edge, &roots)?;
                    hit = Some((mb_idx, edge.target, params));
                    break;
                }
            }
            if let Some((mb_idx, target, params)) = hit {
                let proc = unsafe { &mut *runtime.cur_proc() };
                proc.mailbox.take(mb_idx, &mut proc.heap);
                let params = whole_params(params);
                enter_entry(runtime, transport, program, executable, &mut env, target, None, &params)?;
                return Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                    executable: executable.clone(),
                    entry: target,
                    env,
                    continuations,
                }));
            }
            let timeout_ms = match after {
                Some(after) => env_get(transport, runtime.cur_proc(), &env, after.timeout)?.as_i64(),
                None => None,
            };
            if let Some(after) = after
                && timeout_ms == Some(0)
            {
                enter_entry(
                    runtime,
                    transport,
                    program,
                    executable,
                    &mut env,
                    after.entry,
                    None,
                    &[],
                )?;
                return Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                    executable: executable.clone(),
                    entry: after.entry,
                    env,
                    continuations,
                }));
            }
            let after_timer = match timeout_ms {
                Some(ms) if ms > 0 => Some(arm_receive_timer(runtime.cur_proc(), ms as u64)?),
                _ => None,
            };
            runtime.backend_parked.insert(
                unsafe { &*runtime.cur_proc() }.pid,
                BackendParkRecord {
                    executable: executable.clone(),
                    entry: entry_id,
                    env,
                    continuations,
                    after_timer,
                },
            );
            Ok(BackendEvalTransition::Blocked)
        }
        BackendTail::Try { body, handler } => {
            let mut continuations = continuations;
            continuations.push(BackendContinuation {
                executable: executable.clone(),
                entry: *handler,
                env: handler_frame_from_captures(transport, entries, *handler, &env)?,
                handler: true,
            });
            unsafe { &mut *runtime.cur_proc() }.push_interpreter_handler();
            enter_entry(runtime, transport, program, executable, &mut env, *body, None, &[])?;
            Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                executable: executable.clone(),
                entry: *body,
                env,
                continuations,
            }))
        }
        BackendTail::Unreachable => Err(format!(
            "internal error: executable {:?} reached entry {}, which analysis proved unreachable",
            executable.key,
            entry_id.as_u32()
        )),
    }
}

/// A receive hit: the winning outcome's index and its roots, the outermost
/// subjects the outcome's arguments read, in the order of its `OutcomeRoots`.
type OutcomeMatch = (usize, Vec<AnyValue>);

fn match_backend_receive(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    program: &BackendProgram,
    module: &Module,
    outcomes: &[crate::compiler2::OutcomeEdge],
    dispatch: &crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
    msg: AnyValue,
    bindings: &crate::compiler2::DispatchBindings,
    env: &Frame,
) -> Result<Option<OutcomeMatch>, String> {
    let pinned = dispatch_values(
        runtime.cur_proc(),
        transport,
        dispatch,
        DispatchSource::Bound { env, bindings },
    )?;
    let inputs = [Some(BackendBoundValue::Runtime(msg))];
    let operands = pinned.over(transport, &inputs);
    let run = Dispatch::new(runtime, types, program, module, dispatch, operands)
        .reading(crate::compiler2::outcome_argument_subjects(outcomes));
    let Some(mut decided) = run.run()? else {
        return Ok(None);
    };
    let outcome = decided.outcome().0 as usize;
    let edge = outcomes
        .get(outcome)
        .expect("receive winning outcome has one target edge");
    let roots = receive_outcome_roots(dispatch, edge);
    let mut words = Vec::with_capacity(roots.roots.len());
    for root in &roots.roots {
        words.push(
            decided
                .subject_word(*root)
                .map_err(|_| format!("receive outcome lacks subject {root:?}"))?,
        );
    }
    Ok(Some((outcome, words)))
}

fn receive_outcome_roots(
    dispatch: &crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
    edge: &crate::compiler2::OutcomeEdge,
) -> crate::dispatch_matrix::pattern::OutcomeRoots {
    dispatch.outcome_roots(edge.arguments.iter().map(|argument| argument.subject))
}

/// The values a winning outcome binds into its target, read out of its roots
/// in `proc`'s heap.
fn project_receive_arguments(
    proc: *mut Process,
    module: &Module,
    dispatch: &crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
    edge: &crate::compiler2::OutcomeEdge,
    roots: &[AnyValue],
) -> Result<Vec<(ValueId, AnyValue)>, String> {
    let table = receive_outcome_roots(dispatch, edge);
    edge.arguments
        .iter()
        .zip(&table.arguments)
        .map(|(argument, root)| {
            let value = project_from_root(proc, module, dispatch, roots[root.root], &root.path)?;
            Ok((argument.parameter, value))
        })
        .collect()
}

fn eval_steps<T: Telemetry + ?Sized>(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    _tel: &T,
    transport: &TransportStore,
    program: &BackendProgram,
    module: &Module,
    executable: &BackendExecutable,
    steps: &[ProgramStep],
    env: &mut Frame,
    continuations: &mut Vec<BackendContinuation>,
) -> Result<(), String> {
    for step in steps {
        match step {
            ProgramStep::Omitted { value } => {
                env.insert(*value, BackendBoundValue::Absent);
            }
            ProgramStep::PopHandler => {
                unsafe { &mut *runtime.cur_proc() }.pop_handler();
                let frame = continuations
                    .pop()
                    .expect("a try body completes under the handler frame it pushed");
                assert!(frame.handler, "the frame a try body pops is its handler frame");
            }
            ProgramStep::Const { value, literal } => {
                let layout = executable.abi.value_layouts.get(value).map(|layout| TransportLayout {
                    structural: layout.structural,
                    carrier: layout.carrier,
                });
                let bound = literal_term_bound(transport, program, runtime, literal, layout)?;
                env.insert(*value, bound);
            }
            ProgramStep::Tuple { value, items } => {
                let bound = tuple_step_value(transport, program, runtime.cur_proc(), executable, env, *value, items)?;
                env.insert(*value, bound);
            }
            ProgramStep::List {
                value,
                items,
                tail,
                retention,
            } => {
                let tail_value = tail.map_or(Ok(interp_empty_list_value()), |tail| {
                    env_get(transport, runtime.cur_proc(), env, tail)
                })?;
                let acc = if items.len() == 1 {
                    let head = env_get(transport, runtime.cur_proc(), env, items[0])?;
                    if let Some(retention) = retention {
                        rebuild_backend_list_from_source(
                            transport,
                            runtime.cur_proc(),
                            env,
                            retention.source,
                            head,
                            tail_value,
                            retention.permission,
                        )?
                    } else {
                        interp_list_cons(runtime.cur_proc(), head, tail_value, "backend list")?
                    }
                } else {
                    let mut acc = tail_value;
                    for item in items.iter().rev() {
                        acc = interp_list_cons(
                            runtime.cur_proc(),
                            env_get(transport, runtime.cur_proc(), env, *item)?,
                            acc,
                            "backend list",
                        )?;
                    }
                    acc
                };
                env.insert(*value, BackendBoundValue::Runtime(acc));
            }
            ProgramStep::Map {
                value,
                entries,
                in_key_order,
            } => {
                let proc = runtime.cur_proc();
                let mut dest = fz_map_dest_begin(proc, entries.len() as u32);
                for (key, item) in entries {
                    let key = env_get(transport, proc, env, *key)?;
                    let item = env_get(transport, proc, env, *item)?;
                    dest = interp_map_dest_put(proc, dest, key, item, "backend map")?;
                }
                let map = if *in_key_order {
                    fz_map_dest_publish(proc, dest)
                } else {
                    fz_map_dest_freeze(proc, dest)
                };
                env.insert(
                    *value,
                    BackendBoundValue::Runtime(interp_value_from_ref_word(map, "backend map")?),
                );
            }
            ProgramStep::MapUpdate {
                value,
                ok,
                base,
                entries,
            } => {
                let proc = runtime.cur_proc();
                let base = env_get(transport, proc, env, *base)?;
                let entries = entries.iter().map(|(key, item)| (*key, *item));
                let updated = interp_map_update(transport, proc, env, base, entries)?;
                env.insert(
                    *ok,
                    BackendBoundValue::Runtime(AnyValue::Atom(if matches!(updated, AnyValue::Null) {
                        fz_runtime::any_value::FALSE_ATOM_ID
                    } else {
                        fz_runtime::any_value::TRUE_ATOM_ID
                    })),
                );
                env.insert(*value, BackendBoundValue::Runtime(updated));
            }
            ProgramStep::Struct {
                value,
                module_name,
                fields,
            } => {
                let schema_id = runtime.named_schema_id(module_name)?;
                let ptr = unsafe { &mut *runtime.cur_proc() }.heap.alloc_struct(schema_id);
                for (index, (_, item)) in fields.iter().enumerate() {
                    let item = env_get(transport, runtime.cur_proc(), env, *item)?;
                    let item = publish_runtime_value(runtime.cur_proc(), item)?;
                    unsafe {
                        (&mut *runtime.cur_proc()).heap.write_field_slot(
                            ptr,
                            (index as u32) * 8,
                            item.value(runtime.cur_proc())?,
                        );
                    }
                }
                let struct_ref = AnyValueRef::from_heap_object(ValueKind::STRUCT, ptr).expect("backend struct ref");
                env.insert(
                    *value,
                    BackendBoundValue::Runtime(AnyValue::Ref(HeapRef::new(struct_ref)?)),
                );
            }
            ProgramStep::Bitstring { value, fields } => {
                let mut descriptors = Vec::with_capacity(fields.len());
                for field in fields {
                    let item = env_get(transport, runtime.cur_proc(), env, field.value)?;
                    let (size_present, size) =
                        backend_bit_size_value(transport, runtime.cur_proc(), env, &field.spec.size)?;
                    let spec = fz_bs_field_spec(
                        field.spec.ty.tag(),
                        size_present,
                        field.spec.unit.unwrap_or(field.spec.ty.default_unit()),
                        field.spec.endian.tag(),
                        0,
                        0,
                    );
                    let value = if field.spec.ty == crate::ast::BitType::Float {
                        item.as_float_word()
                            .expect("a construction's check passes only a number to a float segment")
                            as u64
                    } else if field.spec.ty.writes_scalar_word() {
                        item.as_i64()
                            .expect("a construction's check passes only an integer to a scalar segment")
                            as u64
                    } else {
                        item.as_ref_word(runtime.cur_proc())?
                    };
                    descriptors.push(FzBsField { spec, size, value });
                }
                env.insert(
                    *value,
                    BackendBoundValue::Runtime(interp_value_from_ref_word(
                        fz_bs_build(runtime.cur_proc(), descriptors.as_ptr(), descriptors.len() as u64),
                        "backend bitstring",
                    )?),
                );
            }
            ProgramStep::FunctionRef {
                value,
                function,
                construction,
            } => {
                if construction.is_none() {
                    unsafe { &*runtime.cur_proc() }
                        .node
                        .register_closure_denotation(function.denotation(), types.callable_source_origin(*function));
                }
                let bound = if let Some(construction) = construction {
                    construction_callable_value(runtime.cur_proc(), program, construction, types, &[])?
                } else if executable
                    .abi
                    .materialized
                    .runtime_demand
                    .callable_flows
                    .get(value)
                    .is_some_and(|flow| !flow.escape && !flow.opaque && !flow.direct_surfaces.is_empty())
                {
                    let proc = runtime.cur_proc();
                    direct_callable_value(transport, program, executable, proc, env, *value, *function, &[])?
                } else {
                    BackendBoundValue::Runtime(AnyValue::FnRef(
                        FnId(function.as_u32()),
                        callable_value_arity(program, *function, 0),
                        function.denotation(),
                    ))
                };
                env.insert(*value, bound);
            }
            ProgramStep::Lambda {
                value,
                function,
                captures,
                construction,
            } => {
                for capture in captures {
                    if let Some(value) = env.get(*capture) {
                        publish_backend_capture(runtime.cur_proc(), value)?;
                    }
                }
                if construction.is_none() {
                    unsafe { &*runtime.cur_proc() }
                        .node
                        .register_closure_denotation(function.denotation(), types.callable_source_origin(*function));
                }
                let bound = if let Some(construction) = construction {
                    let wrapper = construction_wrapper_for_identity(program, construction, types).ok_or_else(|| {
                        format!("backend callable construction {construction:?} is missing its wrapper")
                    })?;
                    if captures.len() != wrapper.captures.len() {
                        return Err(format!(
                            "backend callable construction {construction:?} expected {} logical capture(s), got {}",
                            wrapper.captures.len(),
                            captures.len()
                        ));
                    }
                    let captures = env_values(transport, runtime.cur_proc(), env, captures)?;
                    construction_callable_value(runtime.cur_proc(), program, construction, types, &captures)?
                } else if executable
                    .abi
                    .materialized
                    .runtime_demand
                    .callable_flows
                    .get(value)
                    .is_some_and(|flow| !flow.escape && !flow.opaque && !flow.direct_surfaces.is_empty())
                {
                    let proc = runtime.cur_proc();
                    direct_callable_value(transport, program, executable, proc, env, *value, *function, captures)?
                } else {
                    BackendBoundValue::Runtime(make_closure(
                        runtime,
                        function.as_u32(),
                        function.denotation(),
                        callable_value_arity(program, *function, captures.len()),
                        env_values(transport, runtime.cur_proc(), env, captures)?,
                    )?)
                };
                env.insert(*value, bound);
            }
            ProgramStep::BinaryOp { value, op, left, right } => {
                let result = eval_binop(
                    runtime.cur_proc(),
                    backend_binop(*op)?,
                    env_get(transport, runtime.cur_proc(), env, *left)?,
                    env_get(transport, runtime.cur_proc(), env, *right)?,
                )?;
                env.insert(*value, BackendBoundValue::Runtime(result));
            }
            ProgramStep::UnaryOp { value, op, input } => {
                let result = eval_unop(backend_unop(*op)?, env_get(transport, runtime.cur_proc(), env, *input)?)?;
                env.insert(*value, BackendBoundValue::Runtime(result));
            }
            ProgramStep::MapIndex { value, base, key } => {
                let result = interp_map_get(
                    runtime.cur_proc(),
                    env_get(transport, runtime.cur_proc(), env, *base)?,
                    env_get(transport, runtime.cur_proc(), env, *key)?,
                )?;
                env.insert(*value, BackendBoundValue::Runtime(result));
            }
            ProgramStep::FieldAccess { value, base, field } => {
                let base = env_get(transport, runtime.cur_proc(), env, *base)?;
                let result = if field == STRUCT_MODULE_FIELD {
                    interp_struct_module(runtime, base)?
                } else {
                    interp_named_field(runtime.cur_proc(), module, base, field)?
                };
                env.insert(*value, BackendBoundValue::Runtime(result));
            }
            ProgramStep::StructUpdate {
                value,
                ok,
                base,
                module: struct_module,
                arity,
                stores,
                rewrite,
            } => {
                let proc = runtime.cur_proc();
                let base = env_get(transport, proc, env, *base)?;
                let updated = if interp_has_struct_layout(runtime, base, struct_module) {
                    let layout = SlotLayout::of(*arity as usize);
                    let may_rewrite = u64::from(*rewrite == crate::fz_ir::RewritePermission::Rewrite);
                    let copy = with_value_ref(proc, base, "backend struct update base", |base_ref| {
                        fz_struct_reuse_or_copy(proc, base_ref, *arity, may_rewrite)
                    })?;
                    for store in stores {
                        let slot = store.slot as usize;
                        let item = Stored::of(env_get(transport, proc, env, store.value)?.value(proc)?);
                        fz_struct_store_ref(
                            proc,
                            copy,
                            SlotLayout::slot_offset(slot) as u32,
                            layout.kind_offset(slot) as u32,
                            item.word,
                            item.kind,
                        );
                    }
                    interp_value_from_ref_word(copy, "backend struct update")?
                } else {
                    let entries = stores.iter().map(|store| (store.key, store.value));
                    interp_map_update(transport, proc, env, base, entries)?
                };
                env.insert(
                    *ok,
                    BackendBoundValue::Runtime(AnyValue::Atom(fz_runtime::any_value::TRUE_ATOM_ID)),
                );
                env.insert(*value, BackendBoundValue::Runtime(updated));
            }
            ProgramStep::StructSlot {
                value,
                base,
                module: struct_module,
                slot,
                field,
            } => {
                let base = env_get(transport, runtime.cur_proc(), env, *base)?;
                let read = if interp_has_struct_layout(runtime, base, struct_module) {
                    interp_slot(runtime, base, *slot)?
                } else {
                    interp_named_field(runtime.cur_proc(), module, base, field)?
                };
                env.insert(*value, BackendBoundValue::Runtime(read));
            }
        }
    }
    Ok(())
}

fn rebuild_backend_list_from_source(
    transport: &TransportStore,
    proc: *mut Process,
    env: &Frame,
    source_id: ValueId,
    head: AnyValue,
    tail: AnyValue,
    permission: crate::fz_ir::RewritePermission,
) -> Result<AnyValue, String> {
    let source = env_get(transport, proc, env, source_id)?;
    let source_ref = source
        .as_any_value_ref(proc)
        .map_err(|err| format!("backend list: cannot materialize reusable source ref: {err}"))?;
    let head = head
        .value(proc)
        .map_err(|err| format!("backend list: cannot materialize list head: {err}"))?;
    let tail = Stored::of(
        tail.value(proc)
            .map_err(|err| format!("backend list: cannot materialize list tail: {err}"))?,
    );
    interp_value_from_ref_word(
        fz_list_reuse_or_cons_parts(
            proc,
            source_ref.raw_word(),
            head.raw(),
            u64::from(head.kind().tag()),
            tail.word,
            tail.kind,
            u64::from(permission == crate::fz_ir::RewritePermission::Rewrite),
        ),
        "backend list",
    )
}

/// Parameters a runtime matcher hands over as whole values.
fn whole_params(params: Vec<(ValueId, AnyValue)>) -> Vec<(ValueId, BackendBoundValue)> {
    params
        .into_iter()
        .map(|(param, word)| (param, BackendBoundValue::Runtime(word)))
        .collect()
}

fn enter_entry(
    runtime: &mut IrInterpRuntime,
    transport: &TransportStore,
    program: &BackendProgram,
    executable: &BackendExecutable,
    env: &mut Frame,
    entry_id: crate::compiler2::ControlEntryId,
    delivered: Option<BackendBoundValue>,
    params: &[(ValueId, BackendBoundValue)],
) -> Result<(), String> {
    let entries = entries_for_executable(executable)?;
    let entry = entries
        .get(entry_id.as_u32() as usize)
        .ok_or_else(|| format!("backend entry {} is out of bounds", entry_id.as_u32()))?;
    if !params.iter().map(|(param, _)| *param).eq(entry.params.iter().copied()) {
        return Err(format!(
            "internal error: backend entry {} takes parameters {:?}, was handed {:?}",
            entry_id.as_u32(),
            entry.params,
            params.iter().map(|(param, _)| *param).collect::<Vec<_>>()
        ));
    }
    bind_entry_params(runtime.cur_proc(), transport, program, executable, env, entry, params)?;
    match &entry.origin {
        crate::compiler2::BackendEntryOrigin::Clause
        | crate::compiler2::BackendEntryOrigin::Branch
        | crate::compiler2::BackendEntryOrigin::ReceiveOutcome
        | crate::compiler2::BackendEntryOrigin::Handler => {}
        crate::compiler2::BackendEntryOrigin::DeliveredResume { value, layout } => {
            let bound = bind_delivered_value(
                transport,
                program,
                runtime.cur_proc(),
                entry_id,
                delivered.as_ref(),
                layout,
            )?;
            if let Some(bound) = bound {
                env.insert(*value, bound);
            }
        }
    }
    Ok(())
}

/// Binds the parameters an entry is handed, each through its layout: the
/// words handed are encoded into the lanes the layouts describe, and the
/// entry reads its parameters back out of those lanes.
fn bind_entry_params(
    proc: *mut Process,
    transport: &TransportStore,
    program: &BackendProgram,
    executable: &BackendExecutable,
    env: &mut Frame,
    entry: &BackendEntry,
    params: &[(ValueId, BackendBoundValue)],
) -> Result<(), String> {
    let mut lanes = Lanes::new();
    for (param, value) in params {
        let layout = entry_param_layout(executable, *param)?;
        encode_transport_layout(transport, program, proc, value, layout, &mut lanes)?;
    }
    let mut lane_index = 0;
    for param in &entry.params {
        let layout = entry_param_layout(executable, *param)?;
        env.insert(
            *param,
            decode_transport_layout(transport, &lanes, layout, &mut lane_index)?,
        );
    }
    if lane_index != lanes.len() {
        return Err(format!(
            "internal error: backend entry parameters read {lane_index} lane(s) of the {} handed",
            lanes.len()
        ));
    }
    Ok(())
}

fn entry_param_layout(executable: &BackendExecutable, param: ValueId) -> Result<TransportLayout, String> {
    let layout = executable
        .abi
        .value_layouts
        .get(&param)
        .ok_or_else(|| format!("internal error: entry parameter {} has no layout", param.as_u32()))?;
    Ok(TransportLayout {
        structural: layout.structural,
        carrier: layout.carrier,
    })
}

#[allow(clippy::too_many_arguments)]
fn eval_backend_direct_call_edge(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    program: &BackendProgram,
    module: &Module,
    callee: &CallTarget<ExecutableKey>,
    args: &[crate::compiler2::BackendCallArg],
    extern_marshals: Option<&[crate::fz_ir::ExternTy]>,
    env: Frame,
    caller: &Rc<BackendExecutable>,
    dest: ControlDestination,
    continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
    match callee {
        CallTarget::Local(callee) => {
            let callee = backend_executable_ref(program, types, callee)?;
            eval_direct_call(
                runtime,
                types,
                transport,
                program,
                module,
                callee,
                args,
                extern_marshals,
                env,
                caller,
                dest,
                continuations,
            )
        }
        CallTarget::ProviderBoundary(function) => Err(format!(
            "unresolved provider-boundary backend call to function {}",
            function.as_u32()
        )),
        CallTarget::Undefined(undefined) => Err(format!(
            "internal error: a call that finds no `{}/{}` raises; it has no target to enter",
            undefined.function, undefined.arity
        )),
    }
}

/// A call on the module value `selector` that found no function: raise what
/// compiled code raises at the same point, and carry on as after any raise.
fn raise_undefined_function(
    runtime: &mut IrInterpRuntime,
    transport: &TransportStore,
    program: &BackendProgram,
    undefined: &UndefinedFunction,
    selector: Option<ValueId>,
    env: &Frame,
    continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
    let selector = selector.ok_or_else(|| {
        format!(
            "internal error: a call that finds no `{}/{}` has no module value to show",
            undefined.function, undefined.arity
        )
    })?;
    for exception in ["Elixir.UndefinedFunctionError", "Elixir.ArgumentError"] {
        let module = ModuleName::from_atom_name(exception).expect("an exception's atom names a module");
        exception_fields(program, &module)?;
    }
    let proc = runtime.cur_proc();
    let receiver = env_get(transport, proc, env, selector)?.value(proc)?;
    let atom = |name: &str| fz_runtime::any_value::AnyValue::atom(runtime.node.intern_atom(name));
    let module_is_defined = undefined.modules_without.iter().any(|module| atom(module) == receiver);
    fz_runtime::failure::raise_undefined_function(
        proc,
        receiver,
        atom(&undefined.function),
        undefined.arity as i64,
        module_is_defined,
    );
    match runtime.take_callback_error() {
        Some(error) => Err(error),
        None => after_panic(runtime, transport, program, continuations),
    }
}

fn eval_direct_call(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    program: &BackendProgram,
    module: &Module,
    callee: Rc<BackendExecutable>,
    args: &[crate::compiler2::BackendCallArg],
    extern_marshals: Option<&[crate::fz_ir::ExternTy]>,
    env: Frame,
    caller: &Rc<BackendExecutable>,
    dest: ControlDestination,
    continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
    let executable = callee.as_ref();
    let call_args = encode_call_args(transport, program, types, runtime, executable, &env, args, 0)?;
    let continuations = match dest {
        ControlDestination::Return => continuations,
        ControlDestination::Deliver(target) => {
            let mut continuations = continuations;
            continuations.push(BackendContinuation {
                executable: caller.clone(),
                entry: target,
                env: retain_continuation_captures(transport, entries_for_executable(caller)?, target, env)?,
                handler: false,
            });
            continuations
        }
    };
    match &executable.body {
        BackendBody::Extern { signature } => step_extern_executable(
            runtime,
            types,
            transport,
            program,
            module,
            executable,
            signature,
            extern_marshals,
            &call_args,
            continuations,
        ),
        BackendBody::Clauses { .. } => Ok(BackendEvalTransition::Next(BackendEvalState::Executable {
            executable: callee,
            args: call_args,
            continuations,
        })),
    }
}

/// Deliver an extern call's answer to the continuation, unless the call
/// never returned: then the raise it made reaches its handler, or the
/// process has failed.
fn continue_after_extern(
    runtime: &mut IrInterpRuntime,
    transport: &TransportStore,
    program: &BackendProgram,
    result: ExternCallValue,
    continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
    match result {
        ExternCallValue::ProcessFailed => after_panic(runtime, transport, program, continuations),
        ExternCallValue::CheckedFailure(failure) => raise_last_resort(
            runtime,
            transport,
            program,
            &failure,
            DispatchInputs::Values(&[]),
            continuations,
        ),
        ExternCallValue::Scalar(value) => continue_backend_value(
            runtime,
            transport,
            program,
            BackendBoundValue::Runtime(value),
            continuations,
        ),
    }
}

/// A decision's last resort: raise the plan's exception, or continue the raise
/// a handler was delivered, through the one raise route, as compiled code does
/// at the same point, and carry on as after any raise: into the nearest
/// handler, or the process has failed. A message that shows the subject reads
/// the plan's first input; a re-raise reads its first two, the kind and the
/// value.
fn raise_last_resort(
    runtime: &mut IrInterpRuntime,
    transport: &TransportStore,
    program: &BackendProgram,
    last_resort: &LastResort,
    inputs: DispatchInputs<'_>,
    continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
    let proc = runtime.cur_proc();
    let input = move |index: usize| -> Result<_, String> {
        let input = inputs
            .get(index)
            .ok_or_else(|| format!("internal error: a last resort reads input {index}, which the plan lacks"))?;
        materialize_backend_value(transport, proc, input)?.value(proc)
    };
    match last_resort {
        LastResort::Reraise => {
            let (kind, value) = (input(0)?, input(1)?);
            let value = unsafe { &mut *proc }.heap.box_any_value_ref(value).raw_word();
            fz_runtime::failure::reraise(proc, kind, value);
        }
        LastResort::Exception { exception, .. } => {
            let module = ModuleName::from_atom_name(exception)
                .ok_or_else(|| format!("internal error: `{exception}` names no exception module"))?;
            let declared = exception_fields(program, &module)?;
            let defaults = program
                .struct_defaults(&module)
                .ok_or_else(|| format!("internal error: exception `{module}` has no defaults"))?;
            let mut values = Vec::with_capacity(declared.len());
            for (name, held) in last_resort.struct_fields(declared, defaults)? {
                if name == fz_runtime::failure::EXCEPTION_FIELD {
                    continue;
                }
                let value = match held {
                    RaisedField::Subject => input(0)?,
                    RaisedField::Literal(term) => literal_term_value(runtime, term)?
                        .value(proc)
                        .map_err(|err| format!("exception field `{name}`: {err}"))?,
                };
                values.push((name, value));
            }
            let exception = fz_runtime::any_value::AnyValue::atom(runtime.node.intern_atom(exception));
            fz_runtime::failure::raise_exception(proc, exception, &values);
        }
    }
    match runtime.take_callback_error() {
        Some(error) => Err(error),
        None => after_panic(runtime, transport, program, continuations),
    }
}

/// The fields the exception `module` declares. The program carries the
/// struct of every exception it raises, registered at load.
fn exception_fields<'a>(program: &'a BackendProgram, module: &ModuleName) -> Result<&'a Vec<String>, String> {
    program
        .schema(module)
        .ok_or_else(|| format!("internal error: exception `{module}` is raised and the program lacks its struct"))
}

/// What follows `fz_panic` in the interpreter. A raise that found a handler
/// left itself on the process; the frames above the handler frame are the
/// calls the raise unwound, and the handler entry runs with the raise's kind,
/// value and exception name as its params. With no handler the process has
/// failed and nothing after it runs.
fn after_panic(
    runtime: &mut IrInterpRuntime,
    transport: &TransportStore,
    program: &BackendProgram,
    mut continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
    let Some(raised) = unsafe { &mut *runtime.cur_proc() }.raised.take() else {
        return Ok(BackendEvalTransition::Failed);
    };
    let frame = loop {
        let frame = continuations
            .pop()
            .expect("a raise delivered to the interpreter has its handler frame");
        if frame.handler {
            break frame;
        }
    };
    let executable = frame.executable.as_ref();
    let BackendBody::Clauses { entries, .. } = &executable.body else {
        return Err(format!(
            "backend handler executable {:?} is not clause-backed",
            frame.executable.key
        ));
    };
    let entry = &entries[frame.entry.as_u32() as usize];
    let values = [raised.kind, raised.value, raised.name]
        .into_iter()
        .map(AnyValue::from_any_value_ref)
        .collect::<Result<Vec<_>, _>>()?;
    let params = whole_params(entry.params.iter().copied().zip(values).collect());
    let mut env = frame.env;
    enter_entry(
        runtime,
        transport,
        program,
        &frame.executable,
        &mut env,
        frame.entry,
        None,
        &params,
    )?;
    Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
        executable: frame.executable.clone(),
        entry: frame.entry,
        env,
        continuations,
    }))
}

/// The values entry `target` reads from its frame: its logical captures that
/// carry something, then its physical captures. A physical capture that is also
/// a logical one is listed once.
fn continuation_capture_ids(
    transport: &TransportStore,
    entries: &[BackendEntry],
    target: crate::compiler2::ControlEntryId,
) -> Result<smallvec::SmallVec<[ValueId; 8]>, String> {
    let entry = entries
        .get(target.as_u32() as usize)
        .ok_or_else(|| format!("backend entry {} is out of bounds", target.as_u32()))?;
    let mut ids: smallvec::SmallVec<[ValueId; 8]> = smallvec::SmallVec::new();
    for capture in &entry.captures {
        let absent = transport
            .interners()
            .shape(capture.layout.structural)
            .is_semantically_absent()
            && matches!(capture.layout.carrier, TransportCarrier::Absent);
        if !absent {
            ids.push(capture.value);
        }
    }
    for capture in &entry.physical_captures {
        if !ids.contains(capture) {
            ids.push(*capture);
        }
    }
    Ok(ids)
}

fn unavailable_capture(id: ValueId) -> String {
    format!("backend continuation capture value {} is unavailable", id.as_u32())
}

/// A continuation resumes at `target`, which reads only its captures; every
/// other value the frame holds is dead, so it is dropped here and a parked
/// process never roots it.
fn retain_continuation_captures(
    transport: &TransportStore,
    entries: &[BackendEntry],
    target: crate::compiler2::ControlEntryId,
    mut env: Frame,
) -> Result<Frame, String> {
    let mut kept: smallvec::SmallVec<[(ValueId, BackendBoundValue); 8]> = smallvec::SmallVec::new();
    for id in continuation_capture_ids(transport, entries, target)? {
        let value = env.take(id).ok_or_else(|| unavailable_capture(id))?;
        kept.push((id, value));
    }
    env.clear();
    for (id, value) in kept {
        env.insert(id, value);
    }
    Ok(env)
}

/// The frame a `try` handler resumes in. The body keeps running in `body`, so
/// the handler's frame is a new one that holds a copy of each capture and
/// nothing else.
fn handler_frame_from_captures(
    transport: &TransportStore,
    entries: &[BackendEntry],
    handler: crate::compiler2::ControlEntryId,
    body: &Frame,
) -> Result<Frame, String> {
    let mut frame = body.empty_like();
    for id in continuation_capture_ids(transport, entries, handler)? {
        let value = body.get(id).ok_or_else(|| unavailable_capture(id))?;
        frame.insert(id, value.clone());
    }
    Ok(frame)
}

fn publish_backend_capture(proc: *mut Process, value: &BackendBoundValue) -> Result<BackendBoundValue, String> {
    Ok(match value {
        BackendBoundValue::Absent => BackendBoundValue::Absent,
        BackendBoundValue::Runtime(value) => BackendBoundValue::Runtime(publish_runtime_value(proc, *value)?),
        BackendBoundValue::Transport { shape, lanes } => BackendBoundValue::Transport {
            shape: *shape,
            lanes: lanes
                .iter()
                .copied()
                .map(|lane| publish_runtime_value(proc, lane))
                .collect::<Result<_, _>>()?,
        },
    })
}

fn entries_for_executable(executable: &BackendExecutable) -> Result<&[BackendEntry], String> {
    let BackendBody::Clauses { entries, .. } = &executable.body else {
        return Err(format!("backend executable {:?} is not clause-backed", executable.key));
    };
    Ok(entries)
}

fn env_values(
    transport: &TransportStore,
    proc: *mut Process,
    env: &Frame,
    values: &[ValueId],
) -> Result<Vec<AnyValue>, String> {
    values
        .iter()
        .map(|value| env_get(transport, proc, env, *value))
        .collect()
}

/// Schedule the timer that wakes the current process's parked receive after
/// `after_ms`.
fn arm_receive_timer(process: *mut Process, after_ms: u64) -> Result<TimerId, String> {
    let process = unsafe { &*process };
    timer_schedule(process, process.pid, after_ms)
        .ok_or_else(|| "the execution context has no timer for a receive after".to_string())
}

pub(super) fn env_get(
    transport: &TransportStore,
    proc: *mut Process,
    env: &Frame,
    value: ValueId,
) -> Result<AnyValue, String> {
    materialize_backend_value(transport, proc, env_get_value(env, value)?)
}

fn env_get_value(env: &Frame, value: ValueId) -> Result<&BackendBoundValue, String> {
    env.get(value)
        .ok_or_else(|| format!("backend value {} is unbound", value.as_u32()))
}

fn bind_executable_inputs(
    transport: &TransportStore,
    types: &crate::compiler2::Types,
    _runtime: &mut IrInterpRuntime,
    executable: &BackendExecutable,
    args: &[AnyValue],
) -> Result<Vec<Option<BackendBoundValue>>, String> {
    let semantic_arity = executable.key.activation.input_len(types);
    let mut bound = vec![None; semantic_arity];
    let mut lane_index = 0;
    for input in &executable.abi.semantic_inputs {
        bound[input.semantic_index] = Some(
            decode_transport_layout(
                transport,
                args,
                TransportLayout {
                    structural: input.layout.structural,
                    carrier: input.layout.carrier,
                },
                &mut lane_index,
            )
            .map_err(|error| {
                format!(
                    "backend executable {} input {}: {error}",
                    executable.key.activation.function.as_u32(),
                    input.semantic_index
                )
            })?,
        );
    }
    if lane_index != args.len() {
        return Err(format!(
            "backend executable {} expected {} runtime lane(s), got {}",
            executable.key.activation.function.as_u32(),
            lane_index,
            args.len()
        ));
    }
    Ok(bound)
}

/// Builds the entry executable's runtime lane vector from macro inputs given by
/// semantic role — `semantic_values[0]` is `__CALLER__`, then the user args.
///
/// This is the inverse of [`bind_executable_inputs`] and honors input-lane
/// elision: an input the executable left `Nothing`-shaped (e.g. a `__CALLER__`
/// the macro body never uses) occupies no runtime lane and is skipped, exactly
/// as `decode_runtime_input` consumes zero lanes for it. The macro invocation is
/// thus lane-consistent with the executable the same way a generated caller is,
/// instead of asserting a fixed `[__CALLER__, args]` ABI. Macro inputs are
/// `Any` (one lane each); `bind_executable_inputs` validates the lane count.
pub(crate) fn encode_macro_entry_inputs(
    program: &BackendProgram,
    types: &crate::compiler2::Types,
    transport: &TransportStore,
    semantic_values: &[AnyValue],
) -> Result<Vec<AnyValue>, String> {
    let executable = program
        .executable(program.entry(), types)
        .ok_or_else(|| "backend macro entry is missing from its program".to_string())?;
    let mut lanes = Vec::new();
    for input in &executable.abi.semantic_inputs {
        let semantic_index = input.semantic_index;
        let shape = input.layout.structural;
        if matches!(transport.interners().shape(shape), ShapeDescr::Nothing) {
            continue;
        }
        let value = *semantic_values.get(semantic_index).ok_or_else(|| {
            format!(
                "macro entry expected a value for semantic input {semantic_index}, have {}",
                semantic_values.len()
            )
        })?;
        lanes.push(value);
    }
    Ok(lanes)
}

fn value_shape(executable: &BackendExecutable, value: ValueId) -> Result<ShapeId, String> {
    executable
        .abi
        .value_layouts
        .get(&value)
        .map(|layout| layout.structural)
        .ok_or_else(|| format!("backend executable did not publish a layout for {value:?}"))
}

#[allow(clippy::too_many_arguments)]
fn direct_callable_value(
    transport: &TransportStore,
    program: &BackendProgram,
    executable: &BackendExecutable,
    proc: *mut Process,
    env: &Frame,
    value: ValueId,
    function: FunctionId,
    captures: &[ValueId],
) -> Result<BackendBoundValue, String> {
    let shape = value_shape(executable, value)?;
    let ShapeDescr::Callable(callable) = transport.interners().shape(shape) else {
        return Err(format!(
            "backend direct callable producer {} had non-callable transport shape {shape:?}",
            value.as_u32()
        ));
    };
    let callable_id = *callable;
    let callable = transport.interners().callable(callable_id);
    if callable.function != Some(function) {
        return Err(format!(
            "backend direct callable producer {} expected function {}, got {:?}",
            value.as_u32(),
            function.as_u32(),
            callable.function
        ));
    }
    if callable.capture_layouts.len() != captures.len() {
        return Err(format!(
            "backend direct callable producer {} expected {} capture shape(s), got {} capture value(s)",
            value.as_u32(),
            callable.capture_layouts.len(),
            captures.len()
        ));
    }
    let mut lanes = Lanes::new();
    for (capture, layout) in captures.iter().copied().zip(callable.capture_layouts.iter().copied()) {
        if transport.interners().layout_width(layout) != 0 {
            let bound = env_get_value(env, capture)?;
            encode_transport_layout(transport, program, proc, bound, layout, &mut lanes)?;
        }
    }
    let expected = transport.interners().shape_width(shape);
    if lanes.len() != expected {
        return Err(format!(
            "backend direct callable producer {} expected {} capture lane(s), got {}",
            value.as_u32(),
            expected,
            lanes.len()
        ));
    }
    Ok(BackendBoundValue::Transport {
        shape,
        lanes: lanes.into_vec(),
    })
}

const CONSTRUCTION_WRAPPER_IDENTITY_BASE: u32 = 0x8000_0000;

fn backend_executable_ref(
    program: &BackendProgram,
    types: &crate::compiler2::Types,
    key: &ExecutableKey,
) -> Result<Rc<BackendExecutable>, String> {
    program
        .executable(key, types)
        .cloned()
        .ok_or_else(|| format!("backend executable {key:?} is missing from its program"))
}

fn construction_wrapper_identity_fn(index: usize) -> Result<FnId, String> {
    let index = u32::try_from(index)
        .ok()
        .filter(|index| index & CONSTRUCTION_WRAPPER_IDENTITY_BASE == 0)
        .ok_or_else(|| "backend callable construction inventory exceeds runtime identity space".to_string())?;
    Ok(FnId(CONSTRUCTION_WRAPPER_IDENTITY_BASE | index))
}

/// The user-visible parameter count of the callable value `function` produces:
/// the function's own inputs less the ones its environment supplies. This is
/// what a rendered fun reports (Elixir's `#Function<.../arity>`), and it is
/// fixed by the source regardless of how many captures survive demand.
///
/// A callable described exactly by transport carries its own `CallableDescr::
/// arity` and is read there instead. This answers for the remaining case: a
/// callable value whose flow is neither a construction nor a direct surface,
/// where the transported description may be the generic callable and so has no
/// arity of its own. The program always does.
fn callable_value_arity(program: &BackendProgram, function: FunctionId, capture_count: usize) -> u16 {
    program
        .executables()
        .iter()
        .find(|executable| executable.key.activation.function == function)
        .map(|executable| executable.abi.semantic_inputs.len().saturating_sub(capture_count) as u16)
        .unwrap_or(0)
}

fn construction_wrapper_for_fn(program: &BackendProgram, fn_id: FnId) -> Option<&BackendConstructionWrapper> {
    (fn_id.0 & CONSTRUCTION_WRAPPER_IDENTITY_BASE != 0)
        .then_some(fn_id.0 & !CONSTRUCTION_WRAPPER_IDENTITY_BASE)
        .and_then(|index| program.construction_wrappers().get(index as usize))
        .map(Rc::as_ref)
}

fn construction_wrapper_for_identity<'a>(
    program: &'a BackendProgram,
    identity: &TransportPosition,
    types: &crate::compiler2::Types,
) -> Option<&'a BackendConstructionWrapper> {
    program
        .construction_index(identity, types)
        .map(|index| program.construction_wrappers()[index].as_ref())
}

fn construction_callable_value(
    proc: *mut Process,
    program: &BackendProgram,
    identity: &TransportPosition,
    types: &crate::compiler2::Types,
    captures: &[AnyValue],
) -> Result<BackendBoundValue, String> {
    let index = program
        .construction_index(identity, types)
        .ok_or_else(|| format!("backend callable construction {identity:?} is missing its wrapper"))?;
    let wrapper = &program.construction_wrappers()[index];
    unsafe { &*proc }
        .node
        .register_closure_denotation(wrapper.denotation, std::sync::Arc::clone(&wrapper.source_origin));
    let capture_count = wrapper.captures.len();
    if captures.len() != capture_count {
        return Err(format!(
            "backend callable construction {identity:?} expected {} capture value(s), got {}",
            capture_count,
            captures.len()
        ));
    }
    let fn_id = construction_wrapper_identity_fn(index)?;
    let arity = wrapper.call_arity as u16;
    let value = if captures.is_empty() {
        AnyValue::FnRef(fn_id, arity, wrapper.denotation)
    } else {
        make_closure_on_proc(proc, fn_id.0, wrapper.denotation, arity, captures.to_vec())?
    };
    Ok(BackendBoundValue::Runtime(value))
}

fn select_construction_member<'a>(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    program: &BackendProgram,
    module: &Module,
    wrapper: &'a BackendConstructionWrapper,
    args: &[AnyValue],
) -> Result<&'a BackendConstructionMemberAdapter, String> {
    if args.len() != wrapper.call_arity {
        return Err(format!(
            "backend callable construction {:?} expected {} call arg(s), got {}",
            wrapper.identity,
            wrapper.call_arity,
            args.len()
        ));
    }
    let member = match &wrapper.selection {
        Some(selection) => {
            let inputs = args
                .iter()
                .map(|arg| Some(BackendBoundValue::Runtime(*arg)))
                .collect::<Vec<_>>();
            let values = dispatch_values(
                runtime.cur_proc(),
                transport,
                selection,
                DispatchSource::Inputs(&inputs),
            )?;
            let operands = values.over(transport, &inputs);
            let decided = Dispatch::new(runtime, types, program, module, selection, operands)
                .run()?
                .ok_or_else(|| format!("backend callable construction {:?} matched no member", wrapper.identity))?;
            selection.body_id(decided.outcome()) as usize
        }
        None if wrapper.members.len() == 1 => 0,
        None => {
            return Err(format!(
                "backend callable construction {:?} has {} members without a selection plan",
                wrapper.identity,
                wrapper.members.len()
            ));
        }
    };
    wrapper.members.get(member).ok_or_else(|| {
        format!(
            "backend callable construction {:?} selected member {} outside {} members",
            wrapper.identity,
            member,
            wrapper.members.len()
        )
    })
}

pub(super) fn construction_wrapper_invocation(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    program: &BackendProgram,
    module: &Module,
    fn_id: FnId,
    captures: &[AnyValue],
    args: &[AnyValue],
) -> Result<(Rc<BackendExecutable>, Lanes), String> {
    let wrapper = construction_wrapper_for_fn(program, fn_id)
        .ok_or_else(|| format!("backend callable {} has no construction wrapper", fn_id.0))?;
    let member = select_construction_member(runtime, types, transport, program, module, wrapper, args)?;
    let target = backend_executable_ref(program, types, &member.target)?;
    let executable = target.as_ref();
    let lanes = ConstructionInputEncoder {
        runtime,
        types,
        transport,
        program,
        target: executable,
        wrapper,
        member,
    }
    .encode(captures, args, |arg| Ok(Cow::Owned(BackendBoundValue::Runtime(*arg))))?;
    Ok((target, lanes))
}

struct ConstructionInputEncoder<'a> {
    runtime: &'a mut IrInterpRuntime,
    types: &'a crate::compiler2::Types,
    transport: &'a TransportStore,
    program: &'a BackendProgram,
    target: &'a BackendExecutable,
    wrapper: &'a BackendConstructionWrapper,
    member: &'a BackendConstructionMemberAdapter,
}

impl ConstructionInputEncoder<'_> {
    fn encode<'v, T>(
        self,
        captures: &[AnyValue],
        args: &[T],
        mut resolve_arg: impl FnMut(&T) -> Result<Cow<'v, BackendBoundValue>, String>,
    ) -> Result<Lanes, String> {
        // `target_inputs` is sparse: an input the target never reads publishes no
        // layout at all, which is why every entry carries its own
        // `semantic_index`. What must hold is that each published index addresses
        // a real input, since the lookups below are by that key and it indexes
        // `semantic_values` / `explicit_values`.
        let semantic_arity = self.target.key.activation.input_len(self.types);
        if let Some(input) = self
            .member
            .target_inputs
            .iter()
            .find(|input| input.semantic_index >= semantic_arity)
        {
            return Err(format!(
                "backend callable construction {:?} member target {:?} publishes semantic input {} for arity {}",
                self.wrapper.identity, self.target.key, input.semantic_index, semantic_arity
            ));
        }
        if self.wrapper.captures.len() != self.member.capture_semantic_inputs.len()
            || captures.len() != self.wrapper.captures.len()
            || args.len() != self.member.surface_semantic_inputs.len()
            || args.len() != self.wrapper.call_arity
        {
            return Err(format!(
                "backend callable construction {:?} member target {:?} does not match its published semantic layout",
                self.wrapper.identity, self.target.key
            ));
        }
        let mut semantic_values = vec![None; semantic_arity];
        for (&capture, &semantic_index) in captures.iter().zip(self.member.capture_semantic_inputs.iter()) {
            let slot = semantic_values.get_mut(semantic_index).ok_or_else(|| {
                format!(
                    "backend callable construction {:?} maps capture outside target {:?}",
                    self.wrapper.identity, self.target.key
                )
            })?;
            if slot.replace(capture).is_some() {
                return Err(format!(
                    "backend callable construction {:?} maps more than one capture to one target input",
                    self.wrapper.identity
                ));
            }
        }
        let mut explicit_values = vec![None; semantic_arity];
        for (arg_index, semantic_index) in self.member.surface_semantic_inputs.iter().copied().enumerate() {
            let slot = explicit_values.get_mut(semantic_index).ok_or_else(|| {
                format!(
                    "backend callable construction {:?} maps an argument outside target {:?}",
                    self.wrapper.identity, self.target.key
                )
            })?;
            if semantic_values[semantic_index].is_some() || slot.replace(arg_index).is_some() {
                return Err(format!(
                    "backend callable construction {:?} maps more than one value to target input {}",
                    self.wrapper.identity, semantic_index
                ));
            }
        }
        let mut lanes = Lanes::new();
        for binding in &self.target.abi.semantic_inputs {
            let input = self
                .member
                .target_inputs
                .iter()
                .find(|input| input.semantic_index == binding.semantic_index)
                .ok_or_else(|| {
                    format!(
                        "backend callable construction {:?} target {:?} omits semantic input {}",
                        self.wrapper.identity, self.target.key, binding.semantic_index
                    )
                })?;
            if input.layout.publishes_no_lanes() {
                continue;
            }
            let value = match semantic_values[binding.semantic_index] {
                Some(value) => Cow::Owned(BackendBoundValue::Runtime(value)),
                None => {
                    let arg_index = explicit_values[binding.semantic_index].ok_or_else(|| {
                        format!(
                            "backend callable construction {:?} cannot populate target {:?} semantic input {}",
                            self.wrapper.identity, self.target.key, binding.semantic_index
                        )
                    })?;
                    resolve_arg(&args[arg_index])?
                }
            };
            encode_runtime_input_binding(
                self.transport,
                self.program,
                self.runtime.cur_proc(),
                &value,
                binding,
                &mut lanes,
            )?;
        }
        Ok(lanes)
    }
}

fn materialize_backend_value(
    transport: &TransportStore,
    proc: *mut Process,
    value: &BackendBoundValue,
) -> Result<AnyValue, String> {
    match value {
        BackendBoundValue::Absent => Err("backend value was absent and cannot be materialized".to_string()),
        BackendBoundValue::Runtime(value) => Ok(*value),
        BackendBoundValue::Transport { shape, lanes } => materialize_transport_value(transport, proc, *shape, lanes),
    }
}

pub(super) fn materialize_transport_value(
    transport: &TransportStore,
    proc: *mut Process,
    shape: ShapeId,
    lanes: &[AnyValue],
) -> Result<AnyValue, String> {
    match transport.interners().shape(shape) {
        ShapeDescr::Nothing => Err("backend value was absent and cannot be materialized".to_string()),
        ShapeDescr::Lane(_) => lanes
            .first()
            .copied()
            .ok_or_else(|| format!("backend transport shape {shape:?} has no runtime lane")),
        ShapeDescr::Cursor { .. } => match lanes {
            [source, position] => materialize_cursor(proc, *source, *position),
            _ => Err(format!("backend cursor {shape:?} has {} lanes, not two", lanes.len())),
        },
        ShapeDescr::Tuple(_) => {
            let fields = transport_field_views(transport, shape, lanes)?;
            make_tuple_on_proc(
                proc,
                fields
                    .iter()
                    .map(|field| materialize_backend_value(transport, proc, field))
                    .collect::<Result<Vec<_>, _>>()?,
            )
        }
        ShapeDescr::Callable(callable) => {
            let callable = transport.interners().callable(*callable);
            let Some(function) = callable.function else {
                return lanes
                    .first()
                    .copied()
                    .ok_or_else(|| format!("backend generic callable shape {shape:?} has no published lane"));
            };
            if callable.capture_layouts.is_empty() {
                return Ok(AnyValue::FnRef(
                    FnId(function.as_u32()),
                    callable.arity,
                    function.denotation(),
                ));
            }
            Err("direct-only callable transport has no published runtime environment".into())
        }
    }
}

/// The bitstring a cursor stands for: the rest of its source from the position.
pub(super) fn materialize_cursor(proc: *mut Process, source: AnyValue, position: AnyValue) -> Result<AnyValue, String> {
    let position = position
        .as_i64()
        .ok_or_else(|| "a cursor position must be an integer".to_string())? as u64;
    let source_ref = source.as_ref_word(proc)?;
    let rest = fz_runtime::ir_runtime::fz_bs_field_spec(
        crate::ast::BitType::Bits.tag(),
        0,
        crate::ast::BitType::Bits.default_unit(),
        crate::ast::Endian::Big.tag(),
        0,
        1,
    );
    interp_read_bit_field(proc, source_ref, position, rest, 0, false)
}

fn encode_call_args(
    transport: &TransportStore,
    program: &BackendProgram,
    types: &crate::compiler2::Types,
    runtime: &mut IrInterpRuntime,
    executable: &BackendExecutable,
    env: &Frame,
    args: &[crate::compiler2::BackendCallArg],
    semantic_start: usize,
) -> Result<Lanes, String> {
    let expected = executable
        .key
        .activation
        .input_len(types)
        .saturating_sub(semantic_start);
    if args.len() != expected {
        return Err(format!(
            "backend executable {} expected {} semantic call arg(s), got {}",
            executable.key.activation.function.as_u32(),
            expected,
            args.len()
        ));
    }
    let mut lanes = Lanes::new();
    let bindings = &executable.abi.semantic_inputs;
    for binding in bindings
        .iter()
        .filter(|binding| binding.semantic_index >= semantic_start)
    {
        if binding.layout.publishes_no_lanes() {
            continue;
        }
        let arg_offset = binding.semantic_index - semantic_start;
        let arg = args.get(arg_offset).ok_or_else(|| {
            format!(
                "backend executable {} missing semantic call arg {} for binding {}",
                executable.key.activation.function.as_u32(),
                arg_offset,
                binding.semantic_index
            )
        })?;
        let value = env_get_value(env, arg.value).map_err(|error| {
            format!(
                "backend encode_call_args callee_fn={} semantic_index={} shape={:?} arg_value={:?}: {error}",
                executable.key.activation.function.as_u32(),
                binding.semantic_index,
                transport.interners().shape(binding.layout.structural),
                arg.value,
            )
        })?;
        encode_runtime_input_binding(transport, program, runtime.cur_proc(), value, binding, &mut lanes).map_err(
            |error| {
                format!(
                    "backend encode_call_args callee_fn={} semantic_index={} shape={:?} arg_value={:?}: {error}",
                    executable.key.activation.function.as_u32(),
                    binding.semantic_index,
                    transport.interners().shape(binding.layout.structural),
                    arg.value,
                )
            },
        )?;
    }
    Ok(lanes)
}

fn bind_delivered_value(
    transport: &TransportStore,
    program: &BackendProgram,
    proc: *mut Process,
    entry_id: crate::compiler2::ControlEntryId,
    delivered: Option<&BackendBoundValue>,
    layout: &crate::compiler2::BackendReturnLayout,
) -> Result<Option<BackendBoundValue>, String> {
    if transport
        .interners()
        .shape(layout.layout.structural)
        .is_semantically_absent()
        && matches!(layout.layout.carrier, TransportCarrier::Absent)
    {
        Ok(None)
    } else {
        let delivered = delivered.ok_or_else(|| {
            format!(
                "backend entry {} expected a delivered value but none was provided",
                entry_id.as_u32()
            )
        })?;
        Ok(Some(project_backend_value_for_contract(
            transport, program, proc, delivered, layout,
        )?))
    }
}

fn project_backend_value_for_contract(
    transport: &TransportStore,
    program: &BackendProgram,
    proc: *mut Process,
    value: &BackendBoundValue,
    layout: &crate::compiler2::BackendReturnLayout,
) -> Result<BackendBoundValue, String> {
    if matches!(layout.layout.carrier, TransportCarrier::ValueRef(_)) {
        return Ok(BackendBoundValue::Runtime(materialize_backend_value(
            transport, proc, value,
        )?));
    }
    let mut lanes = Lanes::new();
    encode_runtime_value(transport, program, proc, value, layout.layout.structural, &mut lanes)?;
    let mut lane_index = 0;
    let decoded = decode_transport_layout(
        transport,
        &lanes,
        TransportLayout::structural(layout.layout.structural),
        &mut lane_index,
    )?;
    if lane_index != lanes.len() {
        return Err(format!(
            "backend return layout decoded {} lane(s), got {}",
            lane_index,
            lanes.len()
        ));
    }
    Ok(decoded)
}

fn encode_runtime_value(
    transport: &TransportStore,
    program: &BackendProgram,
    proc: *mut Process,
    value: &BackendBoundValue,
    shape: ShapeId,
    lanes: &mut Lanes,
) -> Result<(), String> {
    if let BackendBoundValue::Transport {
        shape: value_shape,
        lanes: value_lanes,
    } = value
        && *value_shape == shape
    {
        lanes.extend(value_lanes.iter().copied());
        return Ok(());
    }
    match transport.interners().shape(shape) {
        ShapeDescr::Nothing => Ok(()),
        ShapeDescr::Lane(_) => {
            lanes.push(materialize_backend_value(transport, proc, value)?);
            Ok(())
        }
        ShapeDescr::Cursor { .. } => {
            match value {
                BackendBoundValue::Transport { shape, lanes: held }
                    if matches!(transport.interners().shape(*shape), ShapeDescr::Cursor { .. }) =>
                {
                    lanes.extend(held.iter().copied());
                }
                BackendBoundValue::Runtime(source) => lanes.extend([*source, AnyValue::Int(0)]),
                BackendBoundValue::Absent | BackendBoundValue::Transport { .. } => {
                    return Err("a cursor layout was handed a value that is neither a binary nor a cursor".to_string());
                }
            }
            Ok(())
        }
        ShapeDescr::Tuple(fields) => {
            let tuple_fields = tuple_field_values_for_encoding(transport, proc, value, fields)?;
            for (field_value, field_layout) in tuple_fields.iter().zip(fields.iter().copied()) {
                encode_transport_layout(transport, program, proc, field_value, field_layout, lanes)?;
            }
            Ok(())
        }
        ShapeDescr::Callable(callable) => {
            let callable = transport.interners().callable(*callable);
            match callable.function {
                // Direct callable: descriptor names the target, so the value
                // travels as its flat capture lanes.
                Some(_) => encode_direct_callable_captures(transport, program, proc, value, callable, lanes),
                // Generic (escaped / boundary-published) callable: the published
                // value lane is one boxed callable ref. Materialize the value into
                // that single lane instead of flattening captures.
                None => {
                    lanes.push(materialize_backend_value(transport, proc, value)?);
                    Ok(())
                }
            }
        }
    }
}

fn encode_transport_layout(
    transport: &TransportStore,
    program: &BackendProgram,
    proc: *mut Process,
    value: &BackendBoundValue,
    layout: TransportLayout,
    lanes: &mut Lanes,
) -> Result<(), String> {
    if layout.carrier.is_value_ref() {
        lanes.push(materialize_backend_value(transport, proc, value)?);
        return Ok(());
    }
    let shape = layout.structural;
    match transport.interners().shape(shape) {
        ShapeDescr::Tuple(fields) => {
            let tuple_fields = tuple_field_values_for_encoding(transport, proc, value, fields)?;
            for (field_value, field_layout) in tuple_fields.iter().zip(fields.iter().copied()) {
                encode_transport_layout(transport, program, proc, field_value, field_layout, lanes)?;
            }
            Ok(())
        }
        ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Callable(_) | ShapeDescr::Cursor { .. } => {
            encode_runtime_value(transport, program, proc, value, shape, lanes)
        }
    }
}

fn encode_runtime_input_binding(
    transport: &TransportStore,
    program: &BackendProgram,
    proc: *mut Process,
    value: &BackendBoundValue,
    input: &crate::compiler2::BackendSemanticInputLayout,
    lanes: &mut Lanes,
) -> Result<(), String> {
    if input.layout.publishes_no_lanes() {
        return Ok(());
    }
    encode_transport_layout(
        transport,
        program,
        proc,
        value,
        TransportLayout {
            structural: input.layout.structural,
            carrier: input.layout.carrier,
        },
        lanes,
    )
}

fn decode_transport_layout(
    transport: &TransportStore,
    args: &[AnyValue],
    layout: TransportLayout,
    lane_index: &mut usize,
) -> Result<BackendBoundValue, String> {
    if layout.carrier.is_value_ref() {
        return next_runtime_lane(args, lane_index).map(BackendBoundValue::Runtime);
    }
    let shape = layout.structural;
    match transport.interners().shape(shape) {
        ShapeDescr::Nothing => Ok(BackendBoundValue::Absent),
        ShapeDescr::Lane(_) => {
            let value = next_runtime_lane(args, lane_index)?;
            Ok(BackendBoundValue::Runtime(value))
        }
        ShapeDescr::Callable(_) | ShapeDescr::Tuple(_) | ShapeDescr::Cursor { .. } => {
            let width = transport.interners().shape_width(shape);
            let lanes = take_runtime_lanes(args, lane_index, width)?;
            decode_backend_value_from_lanes(transport, shape, lanes)
        }
    }
}

fn take_runtime_lanes<'a>(
    args: &'a [AnyValue],
    lane_index: &mut usize,
    width: usize,
) -> Result<&'a [AnyValue], String> {
    let end = lane_index
        .checked_add(width)
        .ok_or_else(|| "backend runtime lane offset overflow".to_string())?;
    let lanes = args
        .get(*lane_index..end)
        .ok_or_else(|| format!("backend expected runtime lane range {}..{}", *lane_index, end))?;
    *lane_index = end;
    Ok(lanes)
}

fn next_runtime_lane(args: &[AnyValue], lane_index: &mut usize) -> Result<AnyValue, String> {
    let value = *args
        .get(*lane_index)
        .ok_or_else(|| format!("backend expected runtime lane {}", *lane_index))?;
    *lane_index += 1;
    Ok(value)
}

/// A value in the lanes it occupies. Only a value that travels AS lanes -- a
/// tuple or a callable -- takes a copy of them; a word is read out of the slice
/// in place.
fn decode_backend_value_from_lanes(
    transport: &TransportStore,
    shape: ShapeId,
    lanes: &[AnyValue],
) -> Result<BackendBoundValue, String> {
    if lanes.len() != transport.interners().shape_width(shape) {
        return Err(format!(
            "backend transport shape {shape:?} expected {} lane(s), got {}",
            transport.interners().shape_width(shape),
            lanes.len()
        ));
    }
    Ok(match transport.interners().shape(shape) {
        ShapeDescr::Nothing => BackendBoundValue::Absent,
        ShapeDescr::Lane(_) => BackendBoundValue::Runtime(
            *lanes
                .first()
                .ok_or_else(|| format!("backend scalar transport shape {shape:?} has no runtime lane"))?,
        ),
        ShapeDescr::Tuple(_) | ShapeDescr::Callable(_) | ShapeDescr::Cursor { .. } => BackendBoundValue::Transport {
            shape,
            lanes: lanes.to_vec(),
        },
    })
}

/// The lane spans of a shape's fields, checked against the lanes in hand.
pub(super) fn field_spans_for<'t>(
    transport: &'t TransportStore,
    shape: ShapeId,
    lanes: &[AnyValue],
) -> Result<impl Iterator<Item = (TransportLayout, std::ops::Range<usize>)> + 't, String> {
    if lanes.len() != transport.interners().shape_width(shape) {
        return Err(format!(
            "backend transport shape {shape:?} expected {} lane(s), got {}",
            transport.interners().shape_width(shape),
            lanes.len()
        ));
    }
    transport
        .interners()
        .field_spans(shape)
        .ok_or_else(|| format!("backend transport shape {shape:?} has no fields"))
}

/// One field of a lane-form value, read out of the span it occupies.
pub(super) fn decode_field(
    transport: &TransportStore,
    shape: ShapeId,
    lanes: &[AnyValue],
    field_layout: TransportLayout,
    span: std::ops::Range<usize>,
) -> Result<BackendBoundValue, String> {
    let field_lanes = lanes
        .get(span)
        .ok_or_else(|| format!("backend transport shape {shape:?} has an invalid lane span"))?;
    if field_layout.carrier.is_value_ref() {
        field_lanes
            .first()
            .copied()
            .map(BackendBoundValue::Runtime)
            .ok_or_else(|| format!("backend ValueRef field in {shape:?} has no runtime lane"))
    } else {
        decode_backend_value_from_lanes(transport, field_layout.structural, field_lanes)
    }
}

/// The field at `index`, copying only the lanes that field occupies.
pub(super) fn transport_field_view(
    transport: &TransportStore,
    shape: ShapeId,
    lanes: &[AnyValue],
    index: usize,
) -> Result<Option<BackendBoundValue>, String> {
    let Some((field_layout, span)) = field_spans_for(transport, shape, lanes)?.nth(index) else {
        return Ok(None);
    };
    decode_field(transport, shape, lanes, field_layout, span).map(Some)
}

/// Every field of a lane-form value: a tuple's fields, or a callable's
/// captures, which occupy their lanes the same way.
pub(super) fn transport_field_views(
    transport: &TransportStore,
    shape: ShapeId,
    lanes: &[AnyValue],
) -> Result<Vec<BackendBoundValue>, String> {
    field_spans_for(transport, shape, lanes)?
        .map(|(field_layout, span)| decode_field(transport, shape, lanes, field_layout, span))
        .collect()
}

fn tuple_field_values_for_encoding(
    transport: &TransportStore,
    proc: *mut Process,
    value: &BackendBoundValue,
    fields: &[TransportLayout],
) -> Result<Vec<BackendBoundValue>, String> {
    if let BackendBoundValue::Transport {
        shape: value_shape,
        lanes,
    } = value
        && transport.interners().tuple_arity(*value_shape) == Some(fields.len())
    {
        return transport_field_views(transport, *value_shape, lanes);
    }
    let tuple = materialize_backend_value(transport, proc, value)?;
    fields
        .iter()
        .enumerate()
        .map(|(index, _)| {
            with_value_ref(proc, tuple, "backend tuple field lane", |struct_ref| {
                fz_struct_get_field_ref(proc, struct_ref, (index as u32) * 8)
            })
            .and_then(|ref_word| interp_value_from_ref_word(ref_word, "backend tuple field lane"))
            .map(BackendBoundValue::Runtime)
        })
        .collect()
}

fn encode_direct_callable_captures(
    transport: &TransportStore,
    program: &BackendProgram,
    proc: *mut Process,
    value: &BackendBoundValue,
    callable: &crate::compiler2::transport::CallableDescr,
    lanes: &mut Lanes,
) -> Result<(), String> {
    let function = callable.function.expect("direct callable names its source function");
    let captures = if let BackendBoundValue::Transport { shape, lanes } = value
        && let ShapeDescr::Callable(source) = transport.interners().shape(*shape)
    {
        let source = transport.interners().callable(*source);
        if source.function != Some(function) {
            return Err(format!(
                "backend direct-callable transport expected function {}, got {:?}",
                function.as_u32(),
                source.function
            ));
        }
        transport_field_views(transport, *shape, lanes)?
    } else {
        let materialized = materialize_backend_value(transport, proc, value)?;
        let (fn_id, words) = match materialized {
            AnyValue::FnRef(fn_id, _, _) => (fn_id, Vec::new()),
            other => unpack_closure(other.value(proc)?)?,
        };
        // The word is a CONSTRUCTION, not a function: a wrapper's word is this
        // backend's own numbering, so the program translates it back before the
        // check (fz-kdt.127).
        if backend_callable_function(transport, program, fn_id) != Some(function) {
            return Err(format!(
                "backend direct-callable transport expected function {}, got construction word {}",
                function.as_u32(),
                fn_id.0
            ));
        }
        words.into_iter().map(BackendBoundValue::Runtime).collect()
    };
    if captures.len() != callable.capture_layouts.len() {
        return Err(format!(
            "backend direct-callable transport expected {} lexical capture(s) for function {}, got {}",
            callable.capture_layouts.len(),
            function.as_u32(),
            captures.len()
        ));
    }
    for (capture, layout) in captures.iter().zip(callable.capture_layouts.iter().copied()) {
        encode_transport_layout(transport, program, proc, capture, layout, lanes)?;
    }
    Ok(())
}

/// `base` with each of `entries` replacing a key it has, or the miss when it
/// lacks one.
fn interp_map_update(
    transport: &TransportStore,
    proc: *mut Process,
    env: &Frame,
    base: AnyValue,
    entries: impl Iterator<Item = (ValueId, ValueId)>,
) -> Result<AnyValue, String> {
    let mut dest = with_value_ref(proc, base, "backend map update base", |base_ref| {
        fz_map_dest_begin_update(proc, base_ref)
    })?;
    for (key, item) in entries {
        let key = env_get(transport, proc, env, key)?;
        let item = publish_runtime_value(proc, env_get(transport, proc, env, item)?)?;
        dest = interp_map_dest_put(proc, dest, key, item, "backend map update")?;
    }
    interp_value_from_ref_word(fz_map_dest_freeze(proc, dest), "backend map update")
}

/// Put one entry in the map destination `dest`; the answer is the
/// destination the next put or the freeze takes.
fn interp_map_dest_put(
    proc: *mut Process,
    dest: u64,
    key: AnyValue,
    value: AnyValue,
    context: &str,
) -> Result<u64, String> {
    let key = key.value(proc).map_err(|err| format!("{context}: key: {err}"))?;
    let value = value.value(proc).map_err(|err| format!("{context}: value: {err}"))?;
    Ok(fz_map_dest_put(
        proc,
        dest,
        key.raw(),
        key.kind().tag() as u64,
        value.raw(),
        value.kind().tag() as u64,
    ))
}

fn publish_runtime_value(proc: *mut Process, value: AnyValue) -> Result<AnyValue, String> {
    let AnyValue::Ref(value_ref) = value else {
        return Ok(value);
    };
    interp_value_from_ref_word(
        fz_mark_published_ref_aliased(proc, value_ref.raw().raw_word()),
        "backend continuation capture",
    )
}

/// `term` as `layout` carries it. A tuple whose layout spreads its fields over
/// lanes is encoded field by field, as a tuple step is, so no tuple is built
/// only to be taken apart; every other term is built whole.
fn literal_term_bound(
    transport: &TransportStore,
    program: &BackendProgram,
    runtime: &mut IrInterpRuntime,
    term: &LiteralTerm,
    layout: Option<TransportLayout>,
) -> Result<BackendBoundValue, String> {
    let spread = layout.filter(|layout| {
        !layout.carrier.is_value_ref() && transport.interners().tuple_arity(layout.structural).is_some()
    });
    let (LiteralTerm::Tuple(items), Some(layout)) = (term, spread) else {
        return Ok(BackendBoundValue::Runtime(literal_term_value(runtime, term)?));
    };
    let fields = transport
        .interners()
        .field_layouts(layout.structural)
        .expect("a tuple shape has fields");
    if fields.len() != items.len() {
        return Err(format!(
            "a constant tuple of {} item(s) has a layout shape of {} field(s)",
            items.len(),
            fields.len()
        ));
    }
    let mut lanes = Lanes::new();
    for (item, field_layout) in items.iter().zip(fields.iter().copied()) {
        if transport.interners().layout_width(field_layout) != 0 {
            let bound = literal_term_bound(transport, program, runtime, item, Some(field_layout))?;
            encode_transport_layout(transport, program, runtime.cur_proc(), &bound, field_layout, &mut lanes)?;
        }
    }
    Ok(BackendBoundValue::Transport {
        shape: layout.structural,
        lanes: lanes.into_vec(),
    })
}

/// Builds `term` on the current process's heap.
fn literal_term_value(runtime: &mut IrInterpRuntime, term: &LiteralTerm) -> Result<AnyValue, String> {
    const CONTEXT: &str = "literal term";
    let proc = runtime.cur_proc();
    match term {
        LiteralTerm::Ground(value) => literal_value(runtime, value),
        LiteralTerm::Function { .. } => unreachable!("neither a constant nor a raised field holds a function"),
        LiteralTerm::List(items) => items.iter().rev().try_fold(interp_empty_list_value(), |tail, item| {
            interp_list_cons(proc, literal_term_value(runtime, item)?, tail, CONTEXT)
        }),
        LiteralTerm::Tuple(items) => {
            let items = items
                .iter()
                .map(|item| literal_term_value(runtime, item))
                .collect::<Result<_, _>>()?;
            make_tuple_on_proc(proc, items)
        }
        LiteralTerm::Map(entries) => {
            let in_key_order = LiteralTerm::entries_in_key_order(entries);
            let written = in_key_order.clone().unwrap_or_else(|| entries.iter().collect());
            let mut dest = fz_map_dest_begin(proc, written.len() as u32);
            for (key, value) in written {
                let (key, value) = (literal_term_value(runtime, key)?, literal_term_value(runtime, value)?);
                dest = interp_map_dest_put(proc, dest, key, value, CONTEXT)?;
            }
            let map = match in_key_order {
                Some(_) => fz_map_dest_publish(proc, dest),
                None => fz_map_dest_freeze(proc, dest),
            };
            interp_value_from_ref_word(map, CONTEXT)
        }
    }
}

fn literal_value(
    runtime: &mut IrInterpRuntime,
    literal: &crate::ground_value::GroundValue,
) -> Result<AnyValue, String> {
    use crate::ground_value::BodyLiteral;
    Ok(
        match literal
            .as_body_literal()
            .expect("literal_value only ever sees a lowered-body literal")
        {
            BodyLiteral::Int(value) => AnyValue::Int(value),
            BodyLiteral::Float(bits) => AnyValue::Float(f64::from_bits(bits)),
            BodyLiteral::Binary(value) => binary_literal_value(runtime.cur_proc(), value)?,
            BodyLiteral::Atom(name) => AnyValue::Atom(runtime.node.intern_atom(name)),
            BodyLiteral::Bool(value) => interp_bool_value(value),
            BodyLiteral::Nil => interp_nil_value(),
        },
    )
}

/// A tuple step builds a heap object only when the value's layout says the
/// tuple travels as one runtime value. Otherwise it travels as its fields'
/// lanes, which is what `BackendStep::Tuple` binds in native codegen: the
/// carrier is the one authority on representation, so both backends read it
/// rather than each deciding for themselves. Nothing is lost by staying
/// decomposed -- `materialize_backend_value` still builds the object on demand
/// for whoever genuinely needs one.
fn tuple_step_value(
    transport: &TransportStore,
    program: &BackendProgram,
    proc: *mut Process,
    executable: &BackendExecutable,
    env: &Frame,
    value: ValueId,
    items: &[crate::fz_ir::OwnershipUse<ValueId>],
) -> Result<BackendBoundValue, String> {
    for item in items {
        if item.mode == crate::fz_ir::OwnershipMode::Share
            && let Some(value) = env.get(item.value)
        {
            publish_backend_capture(proc, value)?;
        }
    }
    if let Some(layout) = executable.abi.value_layouts.get(&value)
        && !matches!(layout.carrier, TransportCarrier::ValueRef(_))
        && transport.interners().tuple_arity(layout.structural).is_some()
    {
        // Encoding needs the field layouts, not where their lanes land.
        let fields = transport
            .interners()
            .field_layouts(layout.structural)
            .expect("a tuple shape has fields");
        if fields.len() != items.len() {
            return Err(format!(
                "backend tuple step for value {} has {} item(s) but its layout shape has {} field(s)",
                value.as_u32(),
                items.len(),
                fields.len()
            ));
        }
        let mut lanes = Lanes::new();
        for (item, field_layout) in items.iter().copied().zip(fields.iter().copied()) {
            if transport.interners().layout_width(field_layout) != 0 {
                let bound = env_get_value(env, item.value)?;
                encode_transport_layout(transport, program, proc, bound, field_layout, &mut lanes)?;
            }
        }
        return Ok(BackendBoundValue::Transport {
            shape: layout.structural,
            lanes: lanes.into_vec(),
        });
    }
    let items = env_values(
        transport,
        proc,
        env,
        &items.iter().map(|item| item.value).collect::<Vec<_>>(),
    )?;
    Ok(BackendBoundValue::Runtime(make_tuple_on_proc(proc, items)?))
}

fn make_tuple_on_proc(proc: *mut Process, items: Vec<AnyValue>) -> Result<AnyValue, String> {
    let process = unsafe { &mut *proc };
    let schema_id = process.heap.register_schema(Schema::tuple_of_arity(items.len()));
    let p = process.heap.alloc_struct(schema_id);
    for (index, item) in items.iter().enumerate() {
        let item = publish_runtime_value(proc, *item)?;
        unsafe { process.heap.write_field_slot(p, (index as u32) * 8, item.value(proc)?) };
    }
    let tuple_ref = AnyValueRef::from_heap_object(ValueKind::STRUCT, p).expect("backend tuple ref");
    Ok(AnyValue::Ref(HeapRef::new(tuple_ref)?))
}

fn make_closure_on_proc(
    proc: *mut Process,
    code: u32,
    denotation: fz_runtime::any_value::ClosureDenotationId,
    arity: u16,
    captures: Vec<AnyValue>,
) -> Result<AnyValue, String> {
    let heap = &mut unsafe { &mut *proc }.heap;
    let bits = heap.alloc_closure_slots(denotation, arity, captures.len(), 0);
    let p = closure_addr_from_tagged(bits).expect("new backend closure ptr");
    unsafe { std::ptr::write(p.add(8) as *mut u64, code as u64) };
    for (index, value) in captures.iter().enumerate() {
        let value = publish_runtime_value(proc, *value)?;
        unsafe { heap.write_closure_capture_value(p, index, value.value(proc)?) };
    }
    let closure_addr = closure_addr_from_tagged(bits).expect("backend closure bits");
    let closure_ref = AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure_addr).expect("backend closure ref");
    Ok(AnyValue::Ref(HeapRef::new(closure_ref)?))
}

fn make_closure(
    runtime: &mut IrInterpRuntime,
    code: u32,
    denotation: fz_runtime::any_value::ClosureDenotationId,
    arity: u16,
    captures: Vec<AnyValue>,
) -> Result<AnyValue, String> {
    make_closure_on_proc(runtime.cur_proc(), code, denotation, arity, captures)
}

fn run_pending_dtor<T: Telemetry + ?Sized>(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &T,
    program: &BackendProgram,
    module: &Module,
    closure_bits: u64,
    payload_ref: u64,
) -> Result<(), String> {
    let closure_ref = AnyValueRef::from_raw_word(closure_bits)
        .map_err(|err| format!("backend dtor drain: invalid closure ref {closure_bits:#x}: {err:?}"))?;
    closure_ref
        .closure_addr()
        .map_err(|err| format!("backend dtor drain: ref is not a closure: {err:?}"))?;
    let closure = RuntimeAnyValue::from_ref(closure_ref)
        .map_err(|err| format!("backend dtor drain: invalid closure ref: {err:?}"))?;
    let (fn_id, captures) = unpack_pending_dtor_closure(closure)?;
    let payload = interp_value_from_ref_word(payload_ref, "backend dtor drain payload")?;
    let (target, args) =
        construction_wrapper_invocation(runtime, types, transport, program, module, fn_id, &captures, &[payload])?;
    run_backend_resume(
        runtime,
        types,
        transport,
        tel,
        program,
        module,
        BackendResumeEntry::Executable {
            executable: target,
            args,
            continuations: Vec::new(),
        },
    )?;
    Ok(())
}

fn unpack_pending_dtor_closure(closure: RuntimeAnyValue) -> Result<(FnId, Vec<AnyValue>), String> {
    unpack_closure(closure).map_err(|error| format!("backend dtor drain: invalid closure: {error}"))
}

fn backend_bit_size_value(
    transport: &TransportStore,
    proc: *mut Process,
    env: &Frame,
    size: &Option<crate::compiler2::LoweredBitSize>,
) -> Result<(u32, u64), String> {
    Ok(match size {
        None => (0, 0),
        Some(crate::compiler2::LoweredBitSize::Literal(value)) => (1, *value as u64),
        Some(crate::compiler2::LoweredBitSize::Value(value)) => {
            let size = env_get(transport, proc, env, *value)?
                .as_i64()
                .ok_or_else(|| "bit size value must be an integer".to_string())?;
            (1, size as u32 as u64)
        }
    })
}

fn interp_struct_module(runtime: &mut IrInterpRuntime, value: AnyValue) -> Result<AnyValue, String> {
    with_value_ref(runtime.cur_proc(), value, "backend struct module", |subject| {
        fz_struct_module(runtime.cur_proc(), subject)
    })
    .and_then(|ref_word| interp_value_from_ref_word(ref_word, "backend struct module"))
}

/// The `slot`th field of the struct or tuple `object`.
fn interp_slot(runtime: &mut IrInterpRuntime, object: AnyValue, slot: u32) -> Result<AnyValue, String> {
    with_value_ref(runtime.cur_proc(), object, "backend slot", |object_ref| {
        fz_struct_get_field_ref(runtime.cur_proc(), object_ref, slot * 8)
    })
    .and_then(|ref_word| interp_value_from_ref_word(ref_word, "backend slot"))
}

/// Whether `value` is in the struct layout of the struct named `module`.
/// The types say a value is that struct, not how it is laid out.
fn interp_has_struct_layout(
    runtime: &mut IrInterpRuntime,
    value: AnyValue,
    module: &fz_runtime::module_name::ModuleName,
) -> bool {
    match value {
        AnyValue::Ref(object) => unsafe { &*runtime.cur_proc() }
            .heap
            .has_struct_layout_of(object.raw(), module),
        _ => false,
    }
}

fn backend_binop(op: crate::ast::BinOp) -> Result<IrBinOp, String> {
    Ok(match op {
        crate::ast::BinOp::Eq => IrBinOp::Eq,
        crate::ast::BinOp::Neq => IrBinOp::Neq,
        crate::ast::BinOp::Lt => IrBinOp::Lt,
        crate::ast::BinOp::LtEq => IrBinOp::Le,
        crate::ast::BinOp::Gt => IrBinOp::Gt,
        crate::ast::BinOp::GtEq => IrBinOp::Ge,
        crate::ast::BinOp::And => IrBinOp::And,
        crate::ast::BinOp::Or => IrBinOp::Or,
        other => return Err(format!("backend interpreter does not support binary op {:?}", other)),
    })
}

fn backend_unop(op: crate::ast::UnOp) -> Result<IrUnOp, String> {
    Ok(match op {
        crate::ast::UnOp::Neg => IrUnOp::Neg,
        crate::ast::UnOp::Not => IrUnOp::Not,
    })
}

#[cfg(test)]
#[path = "backend_test.rs"]
mod backend_test;
