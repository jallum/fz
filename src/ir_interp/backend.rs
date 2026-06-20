use std::collections::HashMap;
use std::rc::Rc;

use super::binop::{eval_binop, eval_unop, interp_value_eq, unpack_closure};
use super::dispatch_exec::{DispatchExecState, execute_dispatch_inputs};
use super::extern_call::call_lowered_extern;
use super::prim::{interp_list_cons, interp_list_head, interp_list_tail, interp_map_get, interp_map_put};
use super::value::{
    AnyValue, interp_bool_value, interp_empty_list_value, interp_nil_value, interp_runtime_type_predicate_schema_ids,
    interp_struct_field_from_tagged_bits, interp_value_from_ref_word, with_value_ref,
};
use super::*;
use crate::compiler2::transport::{ShapeDescr, ShapeId, TransportPosition, TransportStore};
use crate::compiler2::{
    BackendBody, BackendEntry, BackendExecutable, BackendProgram, BackendStep as ProgramStep, BackendTail, CallTarget,
    ControlDestination, ExecutableDispatch, ValueId,
};
use crate::compiler2::{ExecutableNeed, FunctionId};
use crate::exec::runtime::output_hook_thunk;
use crate::fz_ir::{BinOp as IrBinOp, FnId, Module, UnOp as IrUnOp};
use crate::runtime_type_predicate::matches_runtime_type_predicate;
use crate::telemetry::Telemetry;
use fz_runtime::any_value::{
    AnyValue as RuntimeAnyValue, AnyValueRef, ValueKind, closure_addr_from_tagged, struct_schema_id,
};
use fz_runtime::exec_ctx::ExecCtx;
use fz_runtime::heap::Schema;
use fz_runtime::heap::{FieldKind, Heap, deep_copy_any_value_ref};
use fz_runtime::ir_runtime::{
    fz_bs_begin, fz_bs_finalize, fz_bs_write_field_ref, fz_list_reuse_or_cons_parts, fz_map_empty,
    fz_map_get_atom_key_ref, fz_mark_published_ref_aliased, fz_matcher_map_get_ref, fz_struct_get_field_ref,
};
use fz_runtime::procbin::mso_drop_all_deferred;
use fz_runtime::process::{CompiledModuleConsts, DEFAULT_REDUCTIONS_PER_QUANTUM, Process, ProcessState};

enum BackendRunStep {
    Done(AnyValue),
    Blocked,
}

enum BackendEvalState {
    Executable {
        executable: usize,
        args: Vec<AnyValue>,
        continuations: Vec<BackendContinuation>,
    },
    Entry {
        executable: usize,
        entry: crate::compiler2::ControlEntryId,
        env: HashMap<ValueId, BackendBoundValue>,
        continuations: Vec<BackendContinuation>,
    },
}

enum BackendEvalTransition {
    Next(BackendEvalState),
    Done(AnyValue),
    Blocked,
}

type DispatchMatch = (u32, Vec<(String, AnyValue)>);

/// Runs one closed Compiler2 backend program through the shared interpreter
/// runtime without reopening planner or type-resolution work.
pub(crate) fn run_backend_main(
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &dyn Telemetry,
    program: &BackendProgram,
) -> Result<i64, String> {
    let mut runtime = IrInterpRuntime::fresh_with_atoms(program.atom_names.clone());
    let module = Module {
        atom_names: program.atom_names.clone(),
        struct_schemas: program.struct_schemas.clone(),
        ..Module::default()
    };
    runtime.enqueue_backend_entry(1, program.entry, Vec::new())?;
    let completions = drive_backend_until_idle(&mut runtime, types, transport, tel, program, &module, None)?;
    let halt_val = completions
        .iter()
        .rev()
        .find_map(|(pid, value)| {
            (*pid == 1).then(|| {
                runtime
                    .process_ref(*pid)
                    .map(|task| value_to_halt(task as *const Process as *mut Process, *value))
            })
        })
        .flatten()
        .unwrap_or(0);
    Ok(halt_val)
}

pub(crate) fn run_backend_entry_on_process(
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &dyn Telemetry,
    program: &BackendProgram,
    process: Process,
    args: Vec<AnyValue>,
) -> (Process, Result<AnyValue, String>) {
    let mut runtime = IrInterpRuntime::with_process(process, &program.atom_names);
    let atom_names = runtime
        .process_ref(1)
        .expect("macro runtime should own pid 1")
        .node
        .atom_names();
    let module = Module {
        atom_names,
        struct_schemas: program.struct_schemas.clone(),
        ..Module::default()
    };
    let result = (|| {
        runtime.enqueue_backend_entry(1, program.entry, args)?;
        let completions = drive_backend_until_idle(&mut runtime, types, transport, tel, program, &module, Some(1))?;
        completions
            .into_iter()
            .rev()
            .find_map(|(pid, value)| (pid == 1).then_some(value))
            .ok_or_else(|| "backend macro entry produced no completion".to_string())
    })();
    let process = runtime
        .take_process(1)
        .expect("macro runtime should return its source process");
    (process, result)
}

impl IrInterpRuntime {
    fn enqueue_backend_entry(&mut self, pid: u32, executable: usize, args: Vec<AnyValue>) -> Result<(), String> {
        self.enqueue_backend_executable(pid, executable, args, Vec::new())
    }

    fn enqueue_backend_executable(
        &mut self,
        pid: u32,
        executable: usize,
        args: Vec<AnyValue>,
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
        self.run_queue.push_back(pid);
        self.set_process_state(pid, ProcessState::Ready);
        Ok(())
    }

    fn enqueue_backend_local_entry(
        &mut self,
        pid: u32,
        executable: usize,
        entry: crate::compiler2::ControlEntryId,
        env: HashMap<ValueId, BackendBoundValue>,
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
        self.run_queue.push_back(pid);
        self.set_process_state(pid, ProcessState::Ready);
        Ok(())
    }

    fn take_backend_resume(&mut self, pid: u32) -> Option<BackendResumeEntry> {
        self.backend_resume.remove(&pid)
    }

    pub(super) fn spawn_backend(&mut self, executable: usize, args: Vec<AnyValue>) -> Result<u32, String> {
        let pid = self.next_pid();
        let user_schemas = self.schemas();
        let node = Rc::clone(&self.node);
        let consts = CompiledModuleConsts::empty();
        let mut child = Box::new(Process::from_consts(
            node,
            user_schemas,
            &consts,
            pid,
            DEFAULT_REDUCTIONS_PER_QUANTUM,
        ));
        child.state = ProcessState::Ready;
        self.insert_task(pid, child);
        self.enqueue_backend_entry(pid, executable, args)?;
        Ok(pid)
    }

    pub(super) fn send_opaque(
        &mut self,
        types: &mut crate::compiler2::Types,
        transport: &TransportStore,
        tel: &dyn Telemetry,
        program: &BackendProgram,
        module: &Module,
        receiver_pid: u32,
        msg: AnyValue,
    ) -> Result<(), String> {
        let sender_heap = &unsafe { &*self.cur_proc() }.heap as *const Heap;
        if let Some(park) = self.backend_parked.remove(&receiver_pid) {
            if let Some((clause_index, bound_values)) = try_match_backend_receive(
                self,
                types,
                transport,
                module,
                &park.clauses,
                &park.dispatch,
                msg,
                &park.bindings,
                &park.env,
            )? {
                let executable = program
                    .executables
                    .get(park.executable)
                    .ok_or_else(|| format!("backend parked executable {} is out of bounds", park.executable))?;
                let BackendBody::Clauses { entries, .. } = &executable.body else {
                    return Err(format!(
                        "backend parked executable {} is not clause-backed",
                        park.executable
                    ));
                };
                let clause = park
                    .clauses
                    .get(clause_index)
                    .ok_or_else(|| format!("backend parked receive clause {} is out of bounds", clause_index))?;
                let env = delivered_env(
                    self,
                    transport,
                    program,
                    entries,
                    &park.env,
                    clause.entry,
                    None,
                    &bound_values,
                )?;
                self.enqueue_backend_local_entry(receiver_pid, park.executable, clause.entry, env, park.continuations)?;
                return Ok(());
            }
            self.backend_parked.insert(receiver_pid, park);
        }
        let msg_ref = msg.as_any_value_ref(self.cur_proc())?;
        let Some(task) = self.tasks.get_mut(&receiver_pid) else {
            tel.event(
                &["fz", "runtime", "send_to_unknown_pid"],
                crate::metadata! { pid: receiver_pid as u64 },
            );
            return Ok(());
        };

        let mut forwarding = HashMap::new();
        let copied = deep_copy_any_value_ref(msg_ref, unsafe { &*sender_heap }, &mut task.heap, &mut forwarding);
        task.mailbox.push_back(copied);
        Ok(())
    }
}

fn drive_backend_until_idle(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &dyn Telemetry,
    program: &BackendProgram,
    module: &Module,
    keepalive_pid: Option<u32>,
) -> Result<Vec<(u32, AnyValue)>, String> {
    let mut completions = Vec::new();
    let mut exec_ctx = ExecCtx {
        scheduler: runtime as *mut IrInterpRuntime as *mut (),
        tel: (&tel) as *const &dyn Telemetry as *const (),
        output: Some(output_hook_thunk),
        module: module as *const Module as *const (),
        ..ExecCtx::empty()
    };

    while let Some(pid) = runtime.pop_runnable() {
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
        match run_backend_resume(runtime, types, transport, tel, program, module, resume)? {
            BackendRunStep::Done(value) => {
                completions.push((pid, value));
                if keepalive_pid == Some(pid) {
                    runtime.set_process_state(pid, ProcessState::Ready);
                    continue;
                }
                unsafe {
                    mso_drop_all_deferred(&mut (*proc_ptr).heap);
                }
                if let Err(e) = drain_pending_dtors_backend(runtime, types, transport, tel, program, module) {
                    tel.event(&["fz", "runtime", "dtor_drain_failed"], crate::metadata! { error: e });
                }
                unsafe {
                    (*proc_ptr).halt_value = value_to_halt(proc_ptr, value);
                    ExitRecord::emit(tel, pid, &*proc_ptr);
                }
                runtime.set_process_state(pid, ProcessState::Exited);
            }
            BackendRunStep::Blocked => {
                runtime.set_process_state(pid, ProcessState::Blocked);
            }
        }
    }

    Ok(completions)
}

fn run_backend_resume(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &dyn Telemetry,
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
                let executable_ref = program
                    .executables
                    .get(executable)
                    .ok_or_else(|| format!("backend executable {} is out of bounds", executable))?;
                let BackendBody::Clauses { entries, .. } = &executable_ref.body else {
                    return Err(format!("backend executable {} is not clause-backed", executable));
                };
                step_eval_entry(
                    runtime,
                    types,
                    transport,
                    tel,
                    program,
                    module,
                    executable,
                    executable_ref,
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
    let executable = program
        .executables
        .get(frame.executable)
        .ok_or_else(|| format!("backend continuation executable {} is out of bounds", frame.executable))?;
    let BackendBody::Clauses { entries, .. } = &executable.body else {
        return Err(format!(
            "backend continuation executable {} is not clause-backed",
            frame.executable
        ));
    };
    Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
        executable: frame.executable,
        entry: frame.entry,
        env: delivered_env(
            runtime,
            transport,
            program,
            entries,
            &frame.env,
            frame.entry,
            Some(value),
            &[],
        )?,
        continuations,
    }))
}

fn step_backend_executable(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &dyn Telemetry,
    program: &BackendProgram,
    module: &Module,
    executable_index: usize,
    args: Vec<AnyValue>,
    continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
    let executable = program
        .executables
        .get(executable_index)
        .ok_or_else(|| format!("backend executable {} is out of bounds", executable_index))?;
    match &executable.body {
        BackendBody::Extern { signature } => {
            let value = call_lowered_extern(runtime, types, transport, tel, program, module, signature, None, &args)?;
            continue_backend_value(
                runtime,
                transport,
                program,
                BackendBoundValue::Runtime(value),
                continuations,
            )
        }
        BackendBody::Clauses { clauses, entries, .. } => {
            let semantic_inputs = bind_executable_inputs(transport, program, types, executable, &args)?;
            let clause_index = if clauses.len() == 1 {
                0
            } else {
                let dispatch = executable
                    .entry_dispatch
                    .as_ref()
                    .ok_or_else(|| format!("backend executable {} is missing clause dispatch", executable_index))?;
                let dispatch_inputs = semantic_inputs
                    .iter()
                    .map(|input| {
                        input
                            .as_ref()
                            .map(|value| materialize_backend_value(transport, runtime.cur_proc(), value))
                            .transpose()
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                select_clause(runtime, types, module, dispatch, &dispatch_inputs)?.ok_or_else(|| {
                    format!(
                        "function_clause: no backend entry clause matched for executable {}",
                        executable_index
                    )
                })?
            };
            let clause = clauses
                .get(clause_index)
                .ok_or_else(|| format!("backend clause {} is out of bounds", clause_index))?;
            if clause.params.len() != semantic_inputs.len() {
                return Err(format!(
                    "backend executable {} expected {} semantic input(s), got {}",
                    executable_index,
                    clause.params.len(),
                    semantic_inputs.len()
                ));
            }
            let mut env = HashMap::new();
            for (param, value) in clause.params.iter().copied().zip(semantic_inputs) {
                if let Some(value) = value {
                    env.insert(param, value);
                }
            }
            let mut reusable_cons_sources = HashMap::new();
            eval_steps(
                runtime,
                types,
                tel,
                transport,
                program,
                module,
                executable,
                &clause.projections,
                &mut reusable_cons_sources,
                &mut env,
            )
            .map_err(|error| {
                format!(
                    "backend executable {} function {} clause {} failed before entry {}: {error}",
                    executable_index,
                    executable.key.activation.function.as_u32(),
                    clause_index,
                    clause.entry.as_u32()
                )
            })?;
            step_eval_entry(
                runtime,
                types,
                transport,
                tel,
                program,
                module,
                executable_index,
                executable,
                entries,
                clause.entry,
                env,
                continuations,
            )
        }
    }
}

fn select_clause(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    module: &Module,
    dispatch: &ExecutableDispatch,
    args: &[Option<AnyValue>],
) -> Result<Option<usize>, String> {
    let required_inputs = dispatch.required_input_ordinals();
    for ordinal in required_inputs {
        if args.get(ordinal).and_then(|value| *value).is_none() {
            return Err(format!(
                "backend clause dispatch required omitted semantic input {}",
                ordinal
            ));
        }
    }
    let inputs = args
        .iter()
        .map(|value| value.unwrap_or_else(interp_nil_value))
        .collect::<Vec<_>>();
    let selected = select_dispatch_body(runtime, types, module, dispatch.plan(), &inputs, &HashMap::new())?;
    Ok(selected.and_then(|body_id| dispatch.clause_index(body_id)))
}

fn select_dispatch_body(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    module: &Module,
    plan: &crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
    args: &[AnyValue],
    pinned: &HashMap<String, AnyValue>,
) -> Result<Option<u32>, String> {
    Ok(select_dispatch_match(runtime, types, module, plan, args, pinned)?.map(|(body_id, _)| body_id))
}

fn select_dispatch_match(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    module: &Module,
    plan: &crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
    args: &[AnyValue],
    pinned: &HashMap<String, AnyValue>,
) -> Result<Option<DispatchMatch>, String> {
    let mut state = DispatchExecState::default();
    let mut type_match =
        |runtime: &mut IrInterpRuntime, module: &Module, want: &crate::compiler2::Ty, value: AnyValue| {
            let predicate = types.runtime_type_predicate(want);
            let runtime_value = value.value(runtime.cur_proc()).ok()?;
            let (tuple_schema_ids, named_schema_ids) =
                interp_runtime_type_predicate_schema_ids(runtime, module, &predicate);
            Some(matches_runtime_type_predicate(
                &predicate,
                module,
                runtime_value,
                &tuple_schema_ids,
                &named_schema_ids,
            ))
        };
    Ok(execute_dispatch_inputs(
        runtime,
        module,
        plan,
        args,
        pinned,
        &mut state,
        &mut type_match,
    ))
}

fn step_eval_entry(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &dyn Telemetry,
    program: &BackendProgram,
    module: &Module,
    executable_index: usize,
    executable: &BackendExecutable,
    entries: &[BackendEntry],
    entry_id: crate::compiler2::ControlEntryId,
    mut env: HashMap<ValueId, BackendBoundValue>,
    continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
    let entry = entries
        .get(entry_id.as_u32() as usize)
        .ok_or_else(|| format!("backend entry {} is out of bounds", entry_id.as_u32()))?;
    let mut reusable_cons_sources = entry
        .reusable_cons_captures
        .iter()
        .map(|capture| (capture.head, capture.source))
        .collect::<HashMap<_, _>>();
    eval_steps(
        runtime,
        types,
        tel,
        transport,
        program,
        module,
        executable,
        &entry.steps,
        &mut reusable_cons_sources,
        &mut env,
    )
    .map_err(|error| {
        format!(
            "backend executable {} function {} entry {} step evaluation failed: {error}",
            executable_index,
            executable.key.activation.function.as_u32(),
            entry_id.as_u32()
        )
    })?;
    match &entry.tail {
        BackendTail::Value { value, dest } => {
            let result = env_get_value(&env, *value)?;
            match dest {
                ControlDestination::Return => {
                    continue_backend_value(runtime, transport, program, result, continuations)
                }
                ControlDestination::Deliver(target) => Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                    executable: executable_index,
                    entry: *target,
                    env: delivered_env(runtime, transport, program, entries, &env, *target, Some(result), &[])?,
                    continuations,
                })),
            }
        }
        BackendTail::DirectCall {
            callee,
            args,
            extern_marshals,
            dest,
            ..
        } => match callee {
            CallTarget::Local(callee) => eval_direct_call(
                runtime,
                types,
                transport,
                tel,
                program,
                module,
                *callee,
                args,
                extern_marshals.as_deref(),
                env,
                executable_index,
                dest.clone(),
                continuations,
            ),
            CallTarget::ProviderBoundary(function) => Err(format!(
                "unresolved provider-boundary backend call to function {}",
                function.as_u32()
            )),
        },
        BackendTail::ClosureCall {
            target,
            callee,
            args,
            dest,
            ..
        } => {
            let callee_value = env_get_value(&env, *callee)?;
            let (function, capture_shape, capture_lanes) = match callee_value {
                BackendBoundValue::Transport { shape, lanes }
                    if matches!(transport.interners().shape(shape), ShapeDescr::Callable(_)) =>
                {
                    let ShapeDescr::Callable(callable) = transport.interners().shape(shape) else {
                        unreachable!();
                    };
                    let callable = transport.interners().callable(*callable);
                    let function = callable.function.ok_or_else(|| {
                        "backend closure call cannot directly invoke generic callable transport".to_string()
                    })?;
                    (function, Some(shape), lanes)
                }
                other => {
                    let materialized = materialize_backend_value(transport, runtime.cur_proc(), &other)?;
                    let (fn_id, captures) = match materialized {
                        AnyValue::FnRef(fn_id) => (fn_id, Vec::new()),
                        other => unpack_closure(other.value(runtime.cur_proc())?)?,
                    };
                    (FunctionId::from_fn_id(fn_id), None, captures)
                }
            };
            let fn_id = FnId(function.as_u32());
            let executable_target = match target {
                Some(target) => *target,
                None => {
                    let resolved_capture_values;
                    let capture_values = if let Some(shape) = capture_shape {
                        resolved_capture_values =
                            callable_capture_values(transport, runtime.cur_proc(), shape, &capture_lanes)?;
                        resolved_capture_values.as_slice()
                    } else {
                        capture_lanes.as_slice()
                    };
                    let arg_values = materialize_call_args(transport, runtime.cur_proc(), &env, args)?;
                    resolve_backend_callable_executable(
                        runtime,
                        types,
                        module,
                        program,
                        fn_id,
                        capture_values,
                        &arg_values,
                    )?
                }
            };
            let callee_executable = program
                .executables
                .get(executable_target)
                .ok_or_else(|| format!("backend executable {} is out of bounds", executable_target))?;
            // Capture lanes are already the flat ABI lanes for the callee's leading
            // capture inputs; forward them directly. The capture/arg split is the
            // callee's fact: total inputs minus the explicit call args.
            let arg_inputs_start = executable_input_shapes(program, callee_executable)?
                .len()
                .checked_sub(args.len())
                .ok_or_else(|| {
                    format!(
                        "backend executable {} has fewer inputs than call args",
                        callee_executable.key.activation.function.as_u32()
                    )
                })?;
            let mut call_args = Vec::new();
            call_args.extend(capture_lanes);
            call_args.extend(encode_call_args(
                transport,
                program,
                types,
                runtime,
                callee_executable,
                &env,
                args,
                arg_inputs_start,
            )?);
            let continuations = match dest {
                ControlDestination::Return => continuations,
                ControlDestination::Deliver(target) => {
                    let mut continuations = continuations;
                    continuations.push(BackendContinuation {
                        executable: executable_index,
                        entry: *target,
                        env: capture_backend_continuation_env(runtime.cur_proc(), entries, *target, &env)?,
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
            Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                executable: executable_index,
                entry: target,
                env: delivered_env(runtime, transport, program, entries, &env, target, None, &[])?,
                continuations,
            }))
        }
        BackendTail::Dispatch {
            inputs,
            bindings,
            dispatch,
        } => {
            let input_values = env_values(transport, runtime.cur_proc(), &env, inputs)?;
            let pinned_values = local_dispatch_pinned(transport, runtime.cur_proc(), &env, bindings, &dispatch.plan)?;
            let target =
                match select_dispatch_body(runtime, types, module, &dispatch.plan, &input_values, &pinned_values)? {
                    Some(body_id) => *dispatch
                        .arm_entries
                        .get(body_id as usize)
                        .ok_or_else(|| format!("backend local dispatch arm {} is out of bounds", body_id))?,
                    None => dispatch.miss_entry,
                };
            Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                executable: executable_index,
                entry: target,
                env: delivered_env(runtime, transport, program, entries, &env, target, None, &[])?,
                continuations,
            }))
        }
        BackendTail::Receive(receive) => {
            let bindings = &receive.bindings;
            let dispatch = &receive.dispatch;
            let clauses = &receive.clauses;
            let after = receive.after.as_ref();
            let mailbox_len = unsafe { &mut *runtime.cur_proc() }.mailbox.len();
            let mut hit = None;
            for mb_idx in 0..mailbox_len {
                let msg = {
                    let proc = unsafe { &mut *runtime.cur_proc() };
                    AnyValue::from_any_value_ref(proc.mailbox[mb_idx])?
                };
                if let Some((clause_index, bound_values)) = try_match_backend_receive(
                    runtime, types, transport, module, clauses, dispatch, msg, bindings, &env,
                )? {
                    hit = Some((mb_idx, clause_index, bound_values));
                    break;
                }
            }
            if let Some((mb_idx, clause_index, bound_values)) = hit {
                unsafe { &mut *runtime.cur_proc() }.mailbox.remove(mb_idx);
                let clause = clauses
                    .get(clause_index)
                    .ok_or_else(|| format!("backend receive clause {} is out of bounds", clause_index))?;
                return Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                    executable: executable_index,
                    entry: clause.entry,
                    env: delivered_env(
                        runtime,
                        transport,
                        program,
                        entries,
                        &env,
                        clause.entry,
                        None,
                        &bound_values,
                    )?,
                    continuations,
                }));
            }
            if let Some(after) = after
                && env_get(transport, runtime.cur_proc(), &env, after.timeout)?.as_i64() == Some(0)
            {
                return Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                    executable: executable_index,
                    entry: after.entry,
                    env: delivered_env(runtime, transport, program, entries, &env, after.entry, None, &[])?,
                    continuations,
                }));
            }
            runtime.backend_parked.insert(
                unsafe { &*runtime.cur_proc() }.pid,
                BackendParkRecord {
                    executable: executable_index,
                    clauses: receive.clauses.clone(),
                    dispatch: receive.dispatch.clone(),
                    bindings: receive.bindings.clone(),
                    env,
                    continuations,
                },
            );
            Ok(BackendEvalTransition::Blocked)
        }
        BackendTail::Halt { atom } => Err(atom.clone()),
    }
}

fn try_match_backend_receive(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    module: &Module,
    clauses: &[crate::compiler2::ReceiveClause],
    dispatch: &crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
    msg: AnyValue,
    bindings: &crate::compiler2::DispatchBindings,
    env: &HashMap<ValueId, BackendBoundValue>,
) -> Result<Option<(usize, Vec<AnyValue>)>, String> {
    let pinned = local_dispatch_pinned(transport, runtime.cur_proc(), env, bindings, dispatch)?;
    let Some((body_id, binds)) = select_dispatch_match(runtime, types, module, dispatch, &[msg], &pinned)? else {
        return Ok(None);
    };
    let clause_index = body_id as usize;
    let clause = clauses
        .get(clause_index)
        .ok_or_else(|| format!("backend receive clause {} is out of bounds", clause_index))?;
    let mut bound_values = Vec::with_capacity(clause.bound_names.len());
    for name in &clause.bound_names {
        let Some((_, value)) = binds.iter().rev().find(|(binding, _)| binding == name) else {
            return Err(format!(
                "backend receive binding `{name}` missing from dispatch outcome"
            ));
        };
        bound_values.push(*value);
    }
    Ok(Some((clause_index, bound_values)))
}

fn eval_steps(
    runtime: &mut IrInterpRuntime,
    _types: &mut crate::compiler2::Types,
    _tel: &dyn Telemetry,
    transport: &TransportStore,
    program: &BackendProgram,
    module: &Module,
    executable: &BackendExecutable,
    steps: &[ProgramStep],
    reusable_cons_sources: &mut HashMap<ValueId, ValueId>,
    env: &mut HashMap<ValueId, BackendBoundValue>,
) -> Result<(), String> {
    for step in steps {
        match step {
            ProgramStep::Omitted { value } => {
                env.insert(*value, BackendBoundValue::Absent);
            }
            ProgramStep::Const { value, literal } => {
                env.insert(*value, BackendBoundValue::Runtime(literal_value(runtime, literal)?));
            }
            ProgramStep::Tuple { value, items } => {
                let tuple = make_tuple(runtime, env_values(transport, runtime.cur_proc(), env, items)?)?;
                env.insert(*value, BackendBoundValue::Runtime(tuple));
            }
            ProgramStep::List { value, items, tail } => {
                let tail_value = tail.map_or(Ok(interp_empty_list_value()), |tail| {
                    env_get(transport, runtime.cur_proc(), env, tail)
                })?;
                let acc = if items.len() == 1 {
                    let head = env_get(transport, runtime.cur_proc(), env, items[0])?;
                    if let (Some(tail_id), Some(source_id)) = (*tail, reusable_cons_sources.get(&items[0]).copied()) {
                        rebuild_backend_list_from_source(
                            transport,
                            runtime.cur_proc(),
                            env,
                            source_id,
                            head,
                            env_get(transport, runtime.cur_proc(), env, tail_id)?,
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
            ProgramStep::Map { value, entries } => {
                let mut map_bits = if entries.is_empty() {
                    fz_map_empty(runtime.cur_proc())
                } else {
                    0
                };
                for (key, item) in entries {
                    map_bits = interp_map_put(
                        runtime.cur_proc(),
                        map_bits,
                        env_get(transport, runtime.cur_proc(), env, *key)?,
                        env_get(transport, runtime.cur_proc(), env, *item)?,
                        "backend map",
                    )?;
                }
                env.insert(
                    *value,
                    BackendBoundValue::Runtime(interp_value_from_ref_word(map_bits, "backend map")?),
                );
            }
            ProgramStep::MapUpdate { value, base, entries } => {
                let base = env_get(transport, runtime.cur_proc(), env, *base)?;
                let mut map_bits = base.value(runtime.cur_proc())?.ref_word().raw_word();
                for (key, item) in entries {
                    map_bits = interp_map_put(
                        runtime.cur_proc(),
                        map_bits,
                        env_get(transport, runtime.cur_proc(), env, *key)?,
                        env_get(transport, runtime.cur_proc(), env, *item)?,
                        "backend map update",
                    )?;
                }
                env.insert(
                    *value,
                    BackendBoundValue::Runtime(interp_value_from_ref_word(map_bits, "backend map update")?),
                );
            }
            ProgramStep::Struct {
                value,
                module_name,
                fields,
            } => {
                let schema = module
                    .struct_schemas
                    .get(module_name)
                    .cloned()
                    .ok_or_else(|| format!("backend struct `{module_name}` is missing its schema"))?;
                let schema_id = unsafe { &mut *runtime.cur_proc() }
                    .heap
                    .register_schema(Schema::named_struct(module_name.clone(), schema));
                let ptr = unsafe { &mut *runtime.cur_proc() }.heap.alloc_struct(schema_id);
                for (index, (_, item)) in fields.iter().enumerate() {
                    let item = env_get(transport, runtime.cur_proc(), env, *item)?;
                    unsafe { &mut *runtime.cur_proc() }.heap.write_field_slot(
                        ptr,
                        (index as u32) * 8,
                        item.value(runtime.cur_proc())?,
                    );
                }
                let struct_ref = AnyValueRef::from_heap_object(ValueKind::STRUCT, ptr).expect("backend struct ref");
                env.insert(*value, BackendBoundValue::Runtime(AnyValue::Ref(struct_ref)));
            }
            ProgramStep::Bitstring { value, fields } => {
                fz_bs_begin(runtime.cur_proc());
                for field in fields {
                    let item = env_get(transport, runtime.cur_proc(), env, field.value)?;
                    let (size_present, size_value) =
                        backend_bit_size_value(transport, runtime.cur_proc(), env, &field.spec.size)?;
                    fz_bs_write_field_ref(
                        runtime.cur_proc(),
                        item.as_ref_word(runtime.cur_proc())?,
                        backend_bit_type_tag(field.spec.ty),
                        size_present,
                        size_value,
                        field.spec.unit.unwrap_or(backend_default_bit_unit(field.spec.ty)),
                        backend_endian_tag(field.spec.endian),
                        field.spec.signed as u32,
                    );
                }
                env.insert(
                    *value,
                    BackendBoundValue::Runtime(interp_value_from_ref_word(
                        fz_bs_finalize(runtime.cur_proc()),
                        "backend bitstring",
                    )?),
                );
            }
            ProgramStep::FunctionRef { value, function } => {
                let bound = if executable
                    .runtime_demand
                    .callable_flows
                    .get(value)
                    .is_some_and(|flow| !flow.escape && !flow.opaque && !flow.direct_surfaces.is_empty())
                {
                    direct_callable_value(
                        transport,
                        program,
                        executable,
                        runtime.cur_proc(),
                        env,
                        *value,
                        *function,
                        &[],
                    )?
                } else {
                    BackendBoundValue::Runtime(AnyValue::FnRef(FnId(function.as_u32())))
                };
                env.insert(*value, bound);
            }
            ProgramStep::Lambda {
                value,
                function,
                captures,
            } => {
                let bound = if executable
                    .runtime_demand
                    .callable_flows
                    .get(value)
                    .is_some_and(|flow| !flow.escape && !flow.opaque && !flow.direct_surfaces.is_empty())
                {
                    direct_callable_value(
                        transport,
                        program,
                        executable,
                        runtime.cur_proc(),
                        env,
                        *value,
                        *function,
                        captures,
                    )?
                } else {
                    BackendBoundValue::Runtime(make_closure(
                        runtime,
                        function.as_u32(),
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
                let result = interp_struct_field(runtime, module, base, field)?;
                env.insert(*value, BackendBoundValue::Runtime(result));
            }
            ProgramStep::AssertLiteral { source, literal } => {
                let actual = env_get(transport, runtime.cur_proc(), env, *source)?;
                let expected = literal_value(runtime, literal)?;
                if !interp_value_eq(runtime.cur_proc(), actual, expected)? {
                    return Err(format!(
                        "match_error: literal assertion failed at value {}",
                        source.as_u32()
                    ));
                }
            }
            ProgramStep::AssertStruct { source, module_name } => {
                if !is_named_struct(
                    runtime,
                    module,
                    env_get(transport, runtime.cur_proc(), env, *source)?,
                    module_name,
                )? {
                    return Err(format!("match_error: expected struct {module_name}"));
                }
            }
            ProgramStep::RequireMapValue { value, source, key } => {
                let key = literal_value(runtime, key)?;
                let result = matcher_map_get(runtime, env_get(transport, runtime.cur_proc(), env, *source)?, key)?;
                if matches!(result, AnyValue::Null) {
                    return Err("match_error: expected map key to exist".to_string());
                }
                env.insert(*value, BackendBoundValue::Runtime(result));
            }
            ProgramStep::AssertTuple { source, arity } => {
                let source_value = env_get_value(env, *source)?;
                if transport_tuple_arity(transport, &source_value) != Some(*arity)
                    && !is_tuple_arity(
                        runtime,
                        materialize_backend_value(transport, runtime.cur_proc(), &source_value)?,
                        *arity,
                    )?
                {
                    return Err(format!("match_error: expected tuple arity {}", arity));
                }
            }
            ProgramStep::TupleField { value, source, index } => {
                let field = match env_get_value(env, *source)? {
                    BackendBoundValue::Transport { shape, lanes }
                        if matches!(transport.interners().shape(shape), ShapeDescr::Tuple(_)) =>
                    {
                        transport_field_views(transport, shape, &lanes)?
                            .get(*index)
                            .cloned()
                            .ok_or_else(|| format!("match_error: tuple-field index {} is out of bounds", index))?
                    }
                    other => {
                        let source = materialize_backend_value(transport, runtime.cur_proc(), &other)?;
                        BackendBoundValue::Runtime(
                            with_value_ref(runtime.cur_proc(), source, "backend tuple field", |struct_ref| {
                                fz_struct_get_field_ref(runtime.cur_proc(), struct_ref, (*index as u32) * 8)
                            })
                            .and_then(|ref_word| interp_value_from_ref_word(ref_word, "backend tuple field"))?,
                        )
                    }
                };
                env.insert(*value, field);
            }
            ProgramStep::AssertEmptyList { source } => {
                if !env_get(transport, runtime.cur_proc(), env, *source)?.is_empty_list() {
                    return Err("match_error: expected empty list".to_string());
                }
            }
            ProgramStep::AssertSame { source, value } => {
                if !interp_value_eq(
                    runtime.cur_proc(),
                    env_get(transport, runtime.cur_proc(), env, *source)?,
                    env_get(transport, runtime.cur_proc(), env, *value)?,
                )? {
                    return Err("match_error: pinned value mismatch".to_string());
                }
            }
            ProgramStep::SplitList { source, head, tail } => {
                let source_value = env_get(transport, runtime.cur_proc(), env, *source)?;
                let head_value = interp_list_head(runtime.cur_proc(), source_value)?;
                let tail_value = interp_list_tail(runtime.cur_proc(), source_value)?;
                env.insert(*head, BackendBoundValue::Runtime(head_value));
                env.insert(*tail, BackendBoundValue::Runtime(tail_value));
                reusable_cons_sources.insert(*head, *source);
            }
            ProgramStep::BitstringInit { reader, source } => {
                let source = env_get(transport, runtime.cur_proc(), env, *source)?;
                let source_ref = source.as_ref_word(runtime.cur_proc())?;
                let reader_ref = fz_runtime::ir_runtime::fz_bs_reader_init_ref(runtime.cur_proc(), source_ref);
                env.insert(
                    *reader,
                    BackendBoundValue::Runtime(interp_value_from_ref_word(reader_ref, "backend bitstring reader")?),
                );
            }
            ProgramStep::BitstringRead {
                ok,
                value,
                next_reader,
                reader,
                spec,
                is_last,
            } => {
                let reader_ref =
                    env_get(transport, runtime.cur_proc(), env, *reader)?.as_ref_word(runtime.cur_proc())?;
                let (size_present, size_value) =
                    backend_bit_size_value(transport, runtime.cur_proc(), env, &spec.size)?;
                let field_spec = fz_runtime::ir_runtime::fz_bs_field_spec(
                    backend_bit_type_tag(spec.ty),
                    size_present,
                    spec.unit.unwrap_or(backend_default_bit_unit(spec.ty)),
                    backend_endian_tag(spec.endian),
                    spec.signed as u32,
                    *is_last as u32,
                );
                let result = fz_runtime::ir_runtime::fz_bs_read_field_ref(
                    runtime.cur_proc(),
                    reader_ref,
                    field_spec,
                    size_value,
                );
                let ok_value =
                    interp_struct_field_from_tagged_bits(runtime.cur_proc(), result, 0, "backend bitstring ok")?;
                env.insert(*ok, BackendBoundValue::Runtime(ok_value));
                if ok_value.is_false() || ok_value.is_nil() {
                    env.insert(*value, BackendBoundValue::Runtime(AnyValue::Null));
                    env.insert(*next_reader, BackendBoundValue::Runtime(AnyValue::Null));
                } else {
                    env.insert(
                        *value,
                        BackendBoundValue::Runtime(interp_struct_field_from_tagged_bits(
                            runtime.cur_proc(),
                            result,
                            8,
                            "backend bitstring extracted",
                        )?),
                    );
                    env.insert(
                        *next_reader,
                        BackendBoundValue::Runtime(interp_struct_field_from_tagged_bits(
                            runtime.cur_proc(),
                            result,
                            16,
                            "backend bitstring next reader",
                        )?),
                    );
                }
            }
            ProgramStep::AssertBitstringDone { reader } => {
                let reader = env_get(transport, runtime.cur_proc(), env, *reader)?;
                let bit_len = interp_struct_field_from_tagged_bits(
                    runtime.cur_proc(),
                    reader.as_ref_word(runtime.cur_proc())?,
                    8,
                    "backend bitstring done bit_len",
                )?;
                let pos = interp_struct_field_from_tagged_bits(
                    runtime.cur_proc(),
                    reader.as_ref_word(runtime.cur_proc())?,
                    16,
                    "backend bitstring done pos",
                )?;
                if bit_len.as_i64() != pos.as_i64() {
                    return Err("match_error: expected bitstring reader to be fully consumed".to_string());
                }
            }
        }
    }
    Ok(())
}

fn rebuild_backend_list_from_source(
    transport: &TransportStore,
    proc: *mut Process,
    env: &HashMap<ValueId, BackendBoundValue>,
    source_id: ValueId,
    head: AnyValue,
    tail: AnyValue,
) -> Result<AnyValue, String> {
    let source = env_get(transport, proc, env, source_id)?;
    let source_ref = source
        .as_any_value_ref(proc)
        .map_err(|err| format!("backend list: cannot materialize reusable source ref: {err}"))?;
    let head = head
        .value(proc)
        .map_err(|err| format!("backend list: cannot materialize list head: {err}"))?;
    let tail_ref = tail
        .as_any_value_ref(proc)
        .map_err(|err| format!("backend list: cannot materialize list tail: {err}"))?;
    interp_value_from_ref_word(
        fz_list_reuse_or_cons_parts(
            proc,
            source_ref.raw_word(),
            head.raw(),
            u64::from(head.kind().tag()),
            tail_ref.raw_word(),
        ),
        "backend list",
    )
}

fn delivered_env(
    runtime: &mut IrInterpRuntime,
    transport: &TransportStore,
    program: &BackendProgram,
    entries: &[BackendEntry],
    env: &HashMap<ValueId, BackendBoundValue>,
    entry_id: crate::compiler2::ControlEntryId,
    delivered: Option<BackendBoundValue>,
    params: &[AnyValue],
) -> Result<HashMap<ValueId, BackendBoundValue>, String> {
    let entry = entries
        .get(entry_id.as_u32() as usize)
        .ok_or_else(|| format!("backend entry {} is out of bounds", entry_id.as_u32()))?;
    let mut next = HashMap::new();
    if entry.params.len() != params.len() {
        return Err(format!(
            "backend entry {} expected {} delivered param(s), got {}",
            entry_id.as_u32(),
            entry.params.len(),
            params.len()
        ));
    }
    for (param, value) in entry.params.iter().copied().zip(params.iter().copied()) {
        next.insert(param, BackendBoundValue::Runtime(value));
    }
    match &entry.origin {
        crate::compiler2::BackendEntryOrigin::Clause
        | crate::compiler2::BackendEntryOrigin::Branch
        | crate::compiler2::BackendEntryOrigin::ReceiveOutcome => {}
        crate::compiler2::BackendEntryOrigin::DeliveredResume { value, position } => {
            let shape = position_shape(program, position)?;
            let bound = bind_delivered_value(transport, runtime.cur_proc(), entry_id, delivered.as_ref(), shape)?;
            if let Some(bound) = bound {
                next.insert(*value, bound);
            }
        }
    }
    for capture in &entry.captures {
        next.insert(*capture, env_get_value(env, *capture)?);
    }
    for capture in &entry.reusable_cons_captures {
        next.insert(capture.source, env_get_value(env, capture.source)?);
    }
    Ok(next)
}

fn eval_direct_call(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &dyn Telemetry,
    program: &BackendProgram,
    module: &Module,
    callee: usize,
    args: &[crate::compiler2::BackendCallArg],
    extern_marshals: Option<&[crate::fz_ir::ExternTy]>,
    env: HashMap<ValueId, BackendBoundValue>,
    executable_index: usize,
    dest: ControlDestination,
    continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
    let executable = program
        .executables
        .get(callee)
        .ok_or_else(|| format!("backend direct callee {} is out of bounds", callee))?;
    let call_args = encode_call_args(transport, program, types, runtime, executable, &env, args, 0)?;
    let continuations = match dest {
        ControlDestination::Return => continuations,
        ControlDestination::Deliver(target) => {
            let mut continuations = continuations;
            continuations.push(BackendContinuation {
                executable: executable_index,
                entry: target,
                env: capture_backend_continuation_env(
                    runtime.cur_proc(),
                    entries_for_executable(program, executable_index)?,
                    target,
                    &env,
                )?,
            });
            continuations
        }
    };
    match &executable.body {
        BackendBody::Extern { signature } => call_lowered_extern(
            runtime,
            types,
            transport,
            tel,
            program,
            module,
            signature,
            extern_marshals,
            &call_args,
        )
        .and_then(|value| {
            continue_backend_value(
                runtime,
                transport,
                program,
                BackendBoundValue::Runtime(value),
                continuations,
            )
        }),
        BackendBody::Clauses { .. } => Ok(BackendEvalTransition::Next(BackendEvalState::Executable {
            executable: callee,
            args: call_args,
            continuations,
        })),
    }
}

fn capture_backend_continuation_env(
    proc: *mut Process,
    entries: &[BackendEntry],
    target: crate::compiler2::ControlEntryId,
    env: &HashMap<ValueId, BackendBoundValue>,
) -> Result<HashMap<ValueId, BackendBoundValue>, String> {
    let entry = entries
        .get(target.as_u32() as usize)
        .ok_or_else(|| format!("backend entry {} is out of bounds", target.as_u32()))?;
    let mut captured = HashMap::with_capacity(entry.captures.len() + entry.reusable_cons_captures.len());
    for capture in &entry.captures {
        captured.insert(*capture, publish_backend_capture(proc, &env_get_value(env, *capture)?)?);
    }
    for capture in &entry.reusable_cons_captures {
        captured.insert(
            capture.source,
            publish_backend_capture(proc, &env_get_value(env, capture.source)?)?,
        );
    }
    Ok(captured)
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
                .collect::<Result<Vec<_>, _>>()?,
        },
    })
}

fn entries_for_executable(program: &BackendProgram, executable_index: usize) -> Result<&[BackendEntry], String> {
    let executable = program
        .executables
        .get(executable_index)
        .ok_or_else(|| format!("backend executable {} is out of bounds", executable_index))?;
    let BackendBody::Clauses { entries, .. } = &executable.body else {
        return Err(format!("backend executable {} is not clause-backed", executable_index));
    };
    Ok(entries)
}

fn env_values(
    transport: &TransportStore,
    proc: *mut Process,
    env: &HashMap<ValueId, BackendBoundValue>,
    values: &[ValueId],
) -> Result<Vec<AnyValue>, String> {
    values
        .iter()
        .map(|value| env_get(transport, proc, env, *value))
        .collect()
}

fn local_dispatch_pinned(
    transport: &TransportStore,
    proc: *mut Process,
    env: &HashMap<ValueId, BackendBoundValue>,
    bindings: &crate::compiler2::DispatchBindings,
    plan: &crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
) -> Result<HashMap<String, AnyValue>, String> {
    let mut pinned = HashMap::new();
    for (index, value_id) in bindings.pinned.iter().copied().enumerate() {
        let Some(pin) = plan.pinned.get(index) else {
            return Err(format!("backend local dispatch pinned {} is out of bounds", index));
        };
        if pin.input.is_none() {
            pinned.insert(pin.name.clone(), env_get(transport, proc, env, value_id)?);
        }
    }
    for (index, value_id) in bindings.prepared.iter().copied().enumerate() {
        pinned.insert(
            crate::dispatch_matrix::pattern::prepared_key_name(index),
            env_get(transport, proc, env, value_id)?,
        );
    }
    Ok(pinned)
}

fn env_get(
    transport: &TransportStore,
    proc: *mut Process,
    env: &HashMap<ValueId, BackendBoundValue>,
    value: ValueId,
) -> Result<AnyValue, String> {
    let value = env_get_value(env, value)?;
    materialize_backend_value(transport, proc, &value)
}

fn env_get_value(env: &HashMap<ValueId, BackendBoundValue>, value: ValueId) -> Result<BackendBoundValue, String> {
    env.get(&value)
        .cloned()
        .ok_or_else(|| format!("backend value {} is unbound", value.as_u32()))
}

fn bind_executable_inputs(
    transport: &TransportStore,
    program: &BackendProgram,
    types: &crate::compiler2::Types,
    executable: &BackendExecutable,
    args: &[AnyValue],
) -> Result<Vec<Option<BackendBoundValue>>, String> {
    let semantic_arity = executable.key.activation.input_len(types);
    let mut bound = vec![None; semantic_arity];
    let mut lane_index = 0;
    for (semantic_index, shape) in executable_input_shapes(program, executable)? {
        let value = decode_runtime_input(transport, executable, args, shape, &mut lane_index)?;
        bound[semantic_index] = value;
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
    transport: &TransportStore,
    semantic_values: &[AnyValue],
) -> Result<Vec<AnyValue>, String> {
    let executable = program
        .executables
        .get(program.entry)
        .ok_or_else(|| format!("macro entry executable {} is out of bounds", program.entry))?;
    let mut lanes = Vec::new();
    for (semantic_index, shape) in executable_input_shapes(program, executable)? {
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

fn position_shape(program: &BackendProgram, position: &TransportPosition) -> Result<ShapeId, String> {
    program
        .transport
        .position_shapes
        .iter()
        .find_map(|(candidate, shape)| (candidate == position).then_some(*shape))
        .ok_or_else(|| format!("backend transport handoff did not publish shape for {position:?}"))
}

fn executable_input_shapes(
    program: &BackendProgram,
    executable: &BackendExecutable,
) -> Result<Vec<(usize, ShapeId)>, String> {
    let mut inputs = executable
        .transport
        .input_positions
        .iter()
        .filter_map(|position| {
            let TransportPosition::ExecutableInput { semantic_index, .. } = position else {
                return None;
            };
            Some(position_shape(program, position).map(|shape| (*semantic_index, shape)))
        })
        .collect::<Result<Vec<_>, _>>()?;
    inputs.sort_by_key(|(semantic_index, _)| *semantic_index);
    Ok(inputs)
}

fn value_shape(program: &BackendProgram, executable: &BackendExecutable, value: ValueId) -> Result<ShapeId, String> {
    maybe_value_shape(program, executable, value)
        .ok_or_else(|| format!("backend transport handoff did not publish value position for {value:?}"))
}

fn maybe_value_shape(program: &BackendProgram, executable: &BackendExecutable, value: ValueId) -> Option<ShapeId> {
    let position = executable.transport.value_positions.iter().find(
        |position| matches!(position, TransportPosition::Value { value: candidate, .. } if *candidate == value),
    )?;
    position_shape(program, position).ok()
}

fn direct_callable_value(
    transport: &TransportStore,
    program: &BackendProgram,
    executable: &BackendExecutable,
    proc: *mut Process,
    env: &HashMap<ValueId, BackendBoundValue>,
    value: ValueId,
    function: FunctionId,
    captures: &[ValueId],
) -> Result<BackendBoundValue, String> {
    let shape = value_shape(program, executable, value)?;
    let ShapeDescr::Callable(callable) = transport.interners().shape(shape) else {
        return Err(format!(
            "backend direct callable producer {} had non-callable transport shape {shape:?}",
            value.as_u32()
        ));
    };
    let callable = transport.interners().callable(*callable);
    if callable.function != Some(function) {
        return Err(format!(
            "backend direct callable producer {} expected function {}, got {:?}",
            value.as_u32(),
            function.as_u32(),
            callable.function
        ));
    }
    if callable.capture_shapes.len() != captures.len() {
        return Err(format!(
            "backend direct callable producer {} expected {} capture shape(s), got {} capture value(s)",
            value.as_u32(),
            callable.capture_shapes.len(),
            captures.len()
        ));
    }
    let mut lanes = Vec::new();
    for (capture, shape) in captures.iter().copied().zip(callable.capture_shapes.iter().copied()) {
        let bound = env_get_value(env, capture)?;
        encode_runtime_value(transport, proc, &bound, shape, &mut lanes)?;
    }
    if lanes.len() != callable.capture_lanes.len() {
        return Err(format!(
            "backend direct callable producer {} expected {} capture lane(s), got {}",
            value.as_u32(),
            callable.capture_lanes.len(),
            lanes.len()
        ));
    }
    Ok(BackendBoundValue::Transport { shape, lanes })
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

fn materialize_transport_value(
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
            if lanes.len() != callable.capture_lanes.len() {
                return Err(format!(
                    "backend callable shape {shape:?} expected {} capture lane(s), got {}",
                    callable.capture_lanes.len(),
                    lanes.len()
                ));
            }
            if lanes.is_empty() {
                Ok(AnyValue::FnRef(FnId(function.as_u32())))
            } else {
                make_closure_on_proc(proc, function.as_u32(), lanes.to_vec())
            }
        }
    }
}

fn materialize_call_args(
    transport: &TransportStore,
    proc: *mut Process,
    env: &HashMap<ValueId, BackendBoundValue>,
    args: &[crate::compiler2::BackendCallArg],
) -> Result<Vec<AnyValue>, String> {
    args.iter()
        .map(|arg| env_get(transport, proc, env, arg.value))
        .collect()
}

fn encode_call_args(
    transport: &TransportStore,
    program: &BackendProgram,
    types: &crate::compiler2::Types,
    runtime: &mut IrInterpRuntime,
    executable: &BackendExecutable,
    env: &HashMap<ValueId, BackendBoundValue>,
    args: &[crate::compiler2::BackendCallArg],
    semantic_start: usize,
) -> Result<Vec<AnyValue>, String> {
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
    let mut lanes = Vec::new();
    for (arg, (_, shape)) in args.iter().zip(
        executable_input_shapes(program, executable)?
            .into_iter()
            .skip(semantic_start),
    ) {
        let value = env_get_value(env, arg.value)?;
        encode_runtime_value(transport, runtime.cur_proc(), &value, shape, &mut lanes)?;
    }
    Ok(lanes)
}

fn bind_delivered_value(
    transport: &TransportStore,
    proc: *mut Process,
    entry_id: crate::compiler2::ControlEntryId,
    delivered: Option<&BackendBoundValue>,
    shape: ShapeId,
) -> Result<Option<BackendBoundValue>, String> {
    match transport.interners().shape(shape) {
        ShapeDescr::Nothing => Ok(None),
        _ => {
            let delivered = delivered.ok_or_else(|| {
                format!(
                    "backend entry {} expected a delivered value but none was provided",
                    entry_id.as_u32()
                )
            })?;
            Ok(Some(project_backend_value(transport, proc, delivered, shape)?))
        }
    }
}

fn decode_runtime_input(
    transport: &TransportStore,
    executable: &BackendExecutable,
    args: &[AnyValue],
    shape: ShapeId,
    lane_index: &mut usize,
) -> Result<Option<BackendBoundValue>, String> {
    match transport.interners().shape(shape) {
        ShapeDescr::Nothing => Ok(None),
        _ => decode_runtime_value(transport, executable, args, shape, lane_index).map(Some),
    }
}

fn decode_runtime_value(
    transport: &TransportStore,
    executable: &BackendExecutable,
    args: &[AnyValue],
    shape: ShapeId,
    lane_index: &mut usize,
) -> Result<BackendBoundValue, String> {
    let width = backend_shape_width(transport, shape);
    let end = lane_index.checked_add(width).ok_or_else(|| {
        format!(
            "backend executable {} runtime lane offset overflow",
            executable.key.activation.function.as_u32()
        )
    })?;
    let lanes = args.get(*lane_index..end).ok_or_else(|| {
        format!(
            "backend executable {} expected runtime lane range {}..{}",
            executable.key.activation.function.as_u32(),
            *lane_index,
            end
        )
    })?;
    *lane_index = end;
    decode_backend_value_from_lanes(transport, shape, lanes.to_vec())
}

fn project_backend_value(
    transport: &TransportStore,
    proc: *mut Process,
    value: &BackendBoundValue,
    shape: ShapeId,
) -> Result<BackendBoundValue, String> {
    if let BackendBoundValue::Transport {
        shape: value_shape,
        lanes,
    } = value
        && *value_shape == shape
    {
        return Ok(BackendBoundValue::Transport {
            shape,
            lanes: lanes.clone(),
        });
    }
    let mut lanes = Vec::new();
    encode_runtime_value(transport, proc, value, shape, &mut lanes)?;
    decode_backend_value_from_lanes(transport, shape, lanes)
}

fn encode_runtime_value(
    transport: &TransportStore,
    proc: *mut Process,
    value: &BackendBoundValue,
    shape: ShapeId,
    lanes: &mut Vec<AnyValue>,
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
        ShapeDescr::Tuple(fields) => {
            let tuple_fields = tuple_field_values_for_shape(transport, proc, value, shape, fields)?;
            for (field_value, field_shape) in tuple_fields.iter().zip(fields.iter().copied()) {
                encode_runtime_value(transport, proc, field_value, field_shape, lanes)?;
            }
            Ok(())
        }
        ShapeDescr::Callable(callable) => {
            let callable = transport.interners().callable(*callable);
            match callable.function {
                // Direct callable: descriptor names the target, so the value
                // travels as its flat capture lanes.
                Some(function) => {
                    let extracted =
                        direct_callable_capture_lanes(transport, proc, value, function, callable.capture_lanes.len())?;
                    lanes.extend(extracted);
                    Ok(())
                }
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

fn backend_shape_width(transport: &TransportStore, shape: ShapeId) -> usize {
    match transport.interners().shape(shape) {
        ShapeDescr::Callable(callable) if transport.interners().callable(*callable).function.is_none() => 1,
        _ => transport.interners().shape_width(shape),
    }
}

fn decode_backend_value_from_lanes(
    transport: &TransportStore,
    shape: ShapeId,
    lanes: Vec<AnyValue>,
) -> Result<BackendBoundValue, String> {
    if lanes.len() != backend_shape_width(transport, shape) {
        return Err(format!(
            "backend transport shape {shape:?} expected {} lane(s), got {}",
            backend_shape_width(transport, shape),
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
        ShapeDescr::Callable(callable) if transport.interners().callable(*callable).function.is_none() => {
            BackendBoundValue::Runtime(
                *lanes.first().ok_or_else(|| {
                    format!("backend generic callable transport shape {shape:?} has no published lane")
                })?,
            )
        }
        ShapeDescr::Tuple(_) | ShapeDescr::Callable(_) => BackendBoundValue::Transport { shape, lanes },
    })
}

fn transport_tuple_arity(transport: &TransportStore, value: &BackendBoundValue) -> Option<usize> {
    let BackendBoundValue::Transport { shape, .. } = value else {
        return None;
    };
    match transport.interners().shape(*shape) {
        ShapeDescr::Tuple(fields) => Some(fields.len()),
        ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Callable(_) => None,
    }
}

fn transport_field_views(
    transport: &TransportStore,
    shape: ShapeId,
    lanes: &[AnyValue],
) -> Result<Vec<BackendBoundValue>, String> {
    if lanes.len() != transport.interners().shape_width(shape) {
        return Err(format!(
            "backend tuple transport shape {shape:?} expected {} lane(s), got {}",
            transport.interners().shape_width(shape),
            lanes.len()
        ));
    }
    let spans = transport
        .interners()
        .tuple_field_spans(shape)
        .ok_or_else(|| format!("backend transport shape {shape:?} is not a tuple"))?;
    spans
        .into_iter()
        .map(|(field_shape, span)| {
            let field_lanes = lanes
                .get(span)
                .ok_or_else(|| format!("backend tuple transport shape {shape:?} has an invalid lane span"))?
                .to_vec();
            decode_backend_value_from_lanes(transport, field_shape, field_lanes)
        })
        .collect()
}

fn tuple_field_values_for_shape(
    transport: &TransportStore,
    proc: *mut Process,
    value: &BackendBoundValue,
    shape: ShapeId,
    fields: &[ShapeId],
) -> Result<Vec<BackendBoundValue>, String> {
    if let BackendBoundValue::Transport {
        shape: value_shape,
        lanes,
    } = value
        && *value_shape == shape
    {
        return transport_field_views(transport, shape, lanes);
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

fn callable_capture_values(
    transport: &TransportStore,
    proc: *mut Process,
    shape: ShapeId,
    lanes: &[AnyValue],
) -> Result<Vec<AnyValue>, String> {
    let ShapeDescr::Callable(callable) = transport.interners().shape(shape) else {
        return Err(format!("backend transport shape {shape:?} is not callable"));
    };
    let callable = transport.interners().callable(*callable);
    let mut offset = 0_usize;
    callable
        .capture_shapes
        .iter()
        .copied()
        .map(|capture_shape| {
            let width = transport.interners().shape_width(capture_shape);
            let end = offset
                .checked_add(width)
                .ok_or_else(|| format!("backend callable shape {shape:?} capture lane offset overflow"))?;
            let capture_lanes = lanes
                .get(offset..end)
                .ok_or_else(|| format!("backend callable shape {shape:?} has an invalid capture lane span"))?
                .to_vec();
            offset = end;
            let bound = decode_backend_value_from_lanes(transport, capture_shape, capture_lanes)?;
            materialize_backend_value(transport, proc, &bound)
        })
        .collect()
}

fn direct_callable_capture_lanes(
    transport: &TransportStore,
    proc: *mut Process,
    value: &BackendBoundValue,
    function: FunctionId,
    lane_count: usize,
) -> Result<Vec<AnyValue>, String> {
    let lanes = match value {
        BackendBoundValue::Transport { shape, lanes }
            if matches!(transport.interners().shape(*shape), ShapeDescr::Callable(_)) =>
        {
            let ShapeDescr::Callable(callable) = transport.interners().shape(*shape) else {
                unreachable!();
            };
            let callable = transport.interners().callable(*callable);
            if callable.function != Some(function) {
                return Err(format!(
                    "backend direct-callable transport expected function {}, got {:?}",
                    function.as_u32(),
                    callable.function
                ));
            }
            lanes.clone()
        }
        other => {
            let materialized = materialize_backend_value(transport, proc, other)?;
            let (fn_id, words) = match materialized {
                AnyValue::FnRef(fn_id) => (fn_id, Vec::new()),
                other => unpack_closure(other.value(proc)?)?,
            };
            if FunctionId::from_fn_id(fn_id) != function {
                return Err(format!(
                    "backend direct-callable transport expected function {}, got {}",
                    function.as_u32(),
                    fn_id.0
                ));
            }
            words
        }
    };
    if lanes.len() != lane_count {
        return Err(format!(
            "backend direct-callable transport expected {} lane(s) for function {}, got {}",
            lane_count,
            function.as_u32(),
            lanes.len()
        ));
    }
    Ok(lanes)
}

fn publish_runtime_value(proc: *mut Process, value: AnyValue) -> Result<AnyValue, String> {
    let AnyValue::Ref(value_ref) = value else {
        return Ok(value);
    };
    interp_value_from_ref_word(
        fz_mark_published_ref_aliased(proc, value_ref.raw_word()),
        "backend continuation capture",
    )
}

fn literal_value(runtime: &mut IrInterpRuntime, literal: &crate::compiler2::Literal) -> Result<AnyValue, String> {
    Ok(match literal {
        crate::compiler2::Literal::Int(value) => AnyValue::Int(*value),
        crate::compiler2::Literal::Float(value) => AnyValue::Float(*value),
        crate::compiler2::Literal::Binary(value) => {
            let ref_word = fz_runtime::ir_runtime::fz_alloc_bitstring_const(
                runtime.cur_proc(),
                value.as_ptr() as u64,
                value.len() as u64,
                (value.len() * 8) as u64,
            );
            interp_value_from_ref_word(ref_word, "backend binary literal")?
        }
        crate::compiler2::Literal::Atom(name) => AnyValue::Atom(runtime.node.intern_atom(name)),
        crate::compiler2::Literal::Bool(value) => interp_bool_value(*value),
        crate::compiler2::Literal::Nil => interp_nil_value(),
    })
}

fn make_tuple(runtime: &mut IrInterpRuntime, items: Vec<AnyValue>) -> Result<AnyValue, String> {
    make_tuple_on_proc(runtime.cur_proc(), items)
}

fn make_tuple_on_proc(proc: *mut Process, items: Vec<AnyValue>) -> Result<AnyValue, String> {
    let process = unsafe { &mut *proc };
    let schema_id = process.heap.register_schema(Schema::tuple_of_arity(items.len()));
    let p = process.heap.alloc_struct(schema_id);
    for (index, item) in items.iter().enumerate() {
        process.heap.write_field_slot(p, (index as u32) * 8, item.value(proc)?);
    }
    Ok(AnyValue::Ref(
        AnyValueRef::from_heap_object(ValueKind::STRUCT, p).expect("backend tuple ref"),
    ))
}

fn make_closure_on_proc(proc: *mut Process, code: u32, captures: Vec<AnyValue>) -> Result<AnyValue, String> {
    let heap = &mut unsafe { &mut *proc }.heap;
    let bits = heap.alloc_closure_slots(code, captures.len(), 0);
    let p = closure_addr_from_tagged(bits).expect("new backend closure ptr");
    unsafe { std::ptr::write(p.add(8) as *mut u64, code as u64) };
    for (index, value) in captures.iter().enumerate() {
        unsafe { heap.write_closure_capture_value(p, index, value.value(proc)?) };
    }
    let closure_addr = closure_addr_from_tagged(bits).expect("backend closure bits");
    Ok(AnyValue::Ref(
        AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure_addr).expect("backend closure ref"),
    ))
}

fn make_closure(runtime: &mut IrInterpRuntime, code: u32, captures: Vec<AnyValue>) -> Result<AnyValue, String> {
    make_closure_on_proc(runtime.cur_proc(), code, captures)
}

fn drain_pending_dtors_backend(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &dyn Telemetry,
    program: &BackendProgram,
    module: &Module,
) -> Result<(), String> {
    loop {
        let entry = {
            let process = unsafe { &mut *runtime.cur_proc() };
            process.heap.pending_dtors.pop_front()
        };
        let Some((closure_bits, payload_ref)) = entry else {
            break;
        };
        let closure_ref = AnyValueRef::from_raw_word(closure_bits)
            .map_err(|err| format!("backend dtor drain: invalid closure ref {closure_bits:#x}: {err:?}"))?;
        let closure = RuntimeAnyValue::heap_ptr(
            closure_ref
                .closure_addr()
                .map_err(|err| format!("backend dtor drain: ref is not a closure: {err:?}"))?,
            ValueKind::CLOSURE,
        );
        let (fn_id, captures) = match unpack_closure(closure) {
            Ok(parts) => parts,
            Err(err) => {
                tel.event(&["fz", "runtime", "bad_dtor_closure"], crate::metadata! { error: err });
                continue;
            }
        };
        let payload = interp_value_from_ref_word(payload_ref, "backend dtor drain payload")?;
        let target =
            resolve_backend_callable_executable(runtime, types, module, program, fn_id, &captures, &[payload])?;
        let mut args = captures;
        args.push(payload);
        let _ = run_backend_resume(
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
    }
    Ok(())
}

/// Resolves one runtime callable value against the closed backend inventory.
///
/// Callable identity comes from the published closure body + capture shape.
/// Dynamic arg types only break ties when more than one closed executable
/// matches that identity.
pub(super) fn resolve_backend_callable_executable(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    module: &Module,
    program: &BackendProgram,
    fn_id: FnId,
    captures: &[AnyValue],
    args: &[AnyValue],
) -> Result<usize, String> {
    let candidates = program
        .callable_entries
        .iter()
        .filter_map(|entry| {
            let executable = &program.executables[entry.target];
            (executable.key.need == ExecutableNeed::Value
                && executable.key.activation.function == FunctionId::from_fn_id(fn_id)
                && entry.capture_count == captures.len()
                && executable.key.activation.input_len(types) == captures.len() + args.len())
            .then_some(entry.target)
        })
        .collect::<Vec<_>>();

    if let [target] = candidates.as_slice() {
        return Ok(*target);
    }

    let mut actual_types = Vec::with_capacity(captures.len() + args.len());
    for value in captures.iter().chain(args.iter()) {
        actual_types.push(dynamic_value_ty(runtime, types, module, *value)?);
    }

    let mut matches = candidates
        .into_iter()
        .filter(|target| {
            let executable = &program.executables[*target];
            let expected_inputs = executable.key.activation.inputs(types);
            actual_types
                .iter()
                .zip(expected_inputs.iter())
                .all(|(&actual, &expected)| {
                    let overlap = types.intersect(actual, expected);
                    !types.is_empty(&overlap)
                })
        })
        .collect::<Vec<_>>();
    matches.sort_unstable();
    matches.dedup();

    match matches.as_slice() {
        [target] => Ok(*target),
        [] => Err(format!(
            "backend callable {} with {} capture(s) and {} arg(s) has no settled callable entry",
            fn_id.0,
            captures.len(),
            args.len()
        )),
        _ => Err(format!(
            "backend callable {} with {} capture(s) and {} arg(s) is ambiguous across callable entries {:?}",
            fn_id.0,
            captures.len(),
            args.len(),
            matches
        )),
    }
}

fn is_tuple_arity(runtime: &mut IrInterpRuntime, value: AnyValue, arity: usize) -> Result<bool, String> {
    let slot = value.value(runtime.cur_proc())?;
    Ok(slot.kind() == ValueKind::STRUCT
        && slot
            .heap_addr()
            .is_some_and(|p| unsafe { struct_schema_id(p) } == interp_tuple_schema_id(runtime, arity)))
}

fn dynamic_value_ty(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    module: &Module,
    value: AnyValue,
) -> Result<crate::compiler2::Ty, String> {
    match value {
        AnyValue::Null => Ok(types.any()),
        AnyValue::Int(value) => Ok(types.int_lit(value)),
        AnyValue::Float(value) => Ok(types.float_lit(value)),
        AnyValue::Atom(id) => {
            let Some(name) = module.atom_names.get(id as usize) else {
                return Ok(types.atom());
            };
            Ok(types.atom_lit(name))
        }
        AnyValue::EmptyList => Ok(types.empty_list()),
        AnyValue::FnRef(_) => Ok(types.any()),
        AnyValue::Ref(value_ref) => dynamic_ref_ty(runtime, types, module, value_ref),
    }
}

fn dynamic_ref_ty(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    module: &Module,
    value_ref: AnyValueRef,
) -> Result<crate::compiler2::Ty, String> {
    let value = RuntimeAnyValue::from_ref(value_ref).map_err(|err| format!("backend dynamic ref type: {err:?}"))?;
    match value.kind() {
        ValueKind::LIST => {
            let mut current = AnyValue::Ref(value_ref);
            let mut elems = Vec::new();
            while !current.is_empty_list() {
                let slot = current.value(runtime.cur_proc())?;
                if !interp_is_list_cons(slot) {
                    let any = types.any();
                    return Ok(types.list(any));
                }
                let head = interp_list_head(runtime.cur_proc(), current)?;
                elems.push(dynamic_value_ty(runtime, types, module, head)?);
                current = interp_list_tail(runtime.cur_proc(), current)?;
            }
            if elems.is_empty() {
                Ok(types.empty_list())
            } else {
                let elem_ty = elems
                    .into_iter()
                    .reduce(|lhs, rhs| types.union(lhs, rhs))
                    .unwrap_or_else(|| types.any());
                Ok(types.non_empty_list(elem_ty))
            }
        }
        ValueKind::STRUCT => {
            let Some(struct_ptr) = value.heap_addr() else {
                return Ok(types.any());
            };
            let schema_id = unsafe { struct_schema_id(struct_ptr) };
            let schema = runtime.schemas.borrow().get(schema_id).clone();
            if !schema.name.starts_with("Tuple") {
                return Ok(types.any());
            }
            let mut fields = Vec::new();
            for field in schema.fields {
                if field.kind != FieldKind::AnyValue {
                    continue;
                }
                let field_value = with_value_ref(
                    runtime.cur_proc(),
                    AnyValue::Ref(value_ref),
                    "backend tuple ty",
                    |struct_ref| fz_struct_get_field_ref(runtime.cur_proc(), struct_ref, field.offset),
                )
                .and_then(|ref_word| interp_value_from_ref_word(ref_word, "backend tuple ty"))?;
                fields.push(dynamic_value_ty(runtime, types, module, field_value)?);
            }
            Ok(types.tuple(&fields))
        }
        ValueKind::MAP => Ok(types.map_top()),
        ValueKind::BITSTRING | ValueKind::PROCBIN => Ok(types.str_t()),
        ValueKind::RESOURCE | ValueKind::CLOSURE => Ok(types.any()),
        ValueKind::NULL | ValueKind::INT | ValueKind::FLOAT | ValueKind::ATOM => Ok(types.any()),
        _ => Ok(types.any()),
    }
}

fn backend_bit_type_tag(ty: crate::ast::BitType) -> u32 {
    match ty {
        crate::ast::BitType::Integer => 0,
        crate::ast::BitType::Float => 1,
        crate::ast::BitType::Binary => 2,
        crate::ast::BitType::Bits => 3,
        crate::ast::BitType::Utf8 => 4,
        crate::ast::BitType::Utf16 => 5,
        crate::ast::BitType::Utf32 => 6,
    }
}

fn backend_default_bit_unit(ty: crate::ast::BitType) -> u32 {
    match ty {
        crate::ast::BitType::Integer | crate::ast::BitType::Float | crate::ast::BitType::Bits => 1,
        crate::ast::BitType::Binary => 8,
        crate::ast::BitType::Utf8 | crate::ast::BitType::Utf16 | crate::ast::BitType::Utf32 => 1,
    }
}

fn backend_endian_tag(endian: crate::ast::Endian) -> u32 {
    match endian {
        crate::ast::Endian::Big => 0,
        crate::ast::Endian::Little => 1,
        crate::ast::Endian::Native => 2,
    }
}

fn backend_bit_size_value(
    transport: &TransportStore,
    proc: *mut Process,
    env: &HashMap<ValueId, BackendBoundValue>,
    size: &Option<crate::compiler2::LoweredBitSize>,
) -> Result<(u32, u32), String> {
    Ok(match size {
        None => (0, 0),
        Some(crate::compiler2::LoweredBitSize::Literal(value)) => (1, *value),
        Some(crate::compiler2::LoweredBitSize::Value(value)) => {
            let size = env_get(transport, proc, env, *value)?
                .as_i64()
                .ok_or_else(|| "bit size value must be an integer".to_string())?;
            (1, size as u32)
        }
    })
}

fn interp_struct_field(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    value: AnyValue,
    field: &str,
) -> Result<AnyValue, String> {
    let slot = value.value(runtime.cur_proc())?;
    if slot.kind() == ValueKind::MAP {
        let atom_id = module
            .atom_names
            .iter()
            .position(|name| name == field)
            .ok_or_else(|| format!("field atom `{field}` not interned"))?;
        let map = value.as_ref_word(runtime.cur_proc())?;
        return interp_value_from_ref_word(
            fz_map_get_atom_key_ref(runtime.cur_proc(), map, atom_id as u64),
            "backend field access",
        );
    }
    if slot.kind() != ValueKind::STRUCT {
        return Err("StructField: subject is not a map or Struct".to_string());
    }
    with_value_ref(runtime.cur_proc(), value, "backend struct field", |struct_ref_word| {
        let struct_ref = AnyValueRef::from_raw_word(struct_ref_word).expect("backend struct ref");
        unsafe { &*runtime.cur_proc() }
            .heap
            .read_struct_named_field_ref(struct_ref, field)
            .map(|value| value.raw_word())
            .map_err(|err| format!("{err:?}"))
    })?
    .and_then(|ref_word| interp_value_from_ref_word(ref_word, "backend struct field"))
}

fn matcher_map_get(runtime: &mut IrInterpRuntime, map: AnyValue, key: AnyValue) -> Result<AnyValue, String> {
    let map_slot = map.value(runtime.cur_proc())?;
    if map_slot.kind() != ValueKind::MAP {
        return Err("MatcherMapGet expects a map".to_string());
    }
    let value = with_value_ref(runtime.cur_proc(), map, "MatcherMapGet map", |map_ref| {
        with_value_ref(runtime.cur_proc(), key, "MatcherMapGet key", |key_ref| {
            fz_matcher_map_get_ref(runtime.cur_proc(), map_ref, key_ref)
        })
    })??;
    interp_value_from_ref_word(value, "MatcherMapGet")
}

fn is_named_struct(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    value: AnyValue,
    name: &str,
) -> Result<bool, String> {
    let slot = value.value(runtime.cur_proc())?;
    if slot.kind() != ValueKind::STRUCT {
        return Ok(false);
    }
    let Some(fields) = module.struct_schemas.get(name).cloned() else {
        return Ok(false);
    };
    let Some(ptr) = slot.heap_addr() else {
        return Ok(false);
    };
    let actual_schema = unsafe { struct_schema_id(ptr) };
    let want_schema = unsafe { &mut *runtime.cur_proc() }
        .heap
        .register_schema(Schema::named_struct(name.to_string(), fields));
    Ok(actual_schema == want_schema)
}

fn backend_binop(op: crate::ast::BinOp) -> Result<IrBinOp, String> {
    Ok(match op {
        crate::ast::BinOp::Add => IrBinOp::Add,
        crate::ast::BinOp::Sub => IrBinOp::Sub,
        crate::ast::BinOp::Mul => IrBinOp::Mul,
        crate::ast::BinOp::Div => IrBinOp::Div,
        crate::ast::BinOp::Rem => IrBinOp::Mod,
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
