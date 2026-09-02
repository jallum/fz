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
use crate::compiler2::FunctionId;
use crate::compiler2::pull::TransportCarrier;
use crate::compiler2::transport::{ShapeDescr, ShapeId, TransportStore};
use crate::compiler2::{
    BackendBody, BackendConstructionMemberAdapter, BackendConstructionWrapper, BackendEntry, BackendExecutable,
    BackendProgram, BackendStep as ProgramStep, BackendTail, CallEdge, CallTarget, ControlDestination,
    ExecutableDispatch, ValueId, required_dispatch_input_ordinals,
};
use crate::fz_ir::{BinOp as IrBinOp, FnId, Module, UnOp as IrUnOp};
use crate::runtime_type_predicate::{RuntimeValueReader, matches_runtime_type_predicate, surface_membership};
use crate::telemetry::{Telemetry, TelemetryExt as _};
use crate::types::ClosureTarget;
use fz_runtime::any_value::{
    AnyValue as RuntimeAnyValue, AnyValueRef, ValueKind, closure_addr_from_tagged, struct_schema_id,
};
use fz_runtime::exec_ctx::ExecCtx;
use fz_runtime::heap::Schema;
use fz_runtime::heap::{Heap, deep_copy_any_value_ref};
use fz_runtime::ir_runtime::{
    fz_bs_begin, fz_bs_finalize, fz_bs_write_field_ref, fz_list_head_ref, fz_list_reuse_or_cons_parts, fz_map_empty,
    fz_map_get_atom_key_ref, fz_mark_published_ref_aliased, fz_matcher_map_get_ref, fz_struct_get_field_ref,
    fz_struct_get_named_field_ref,
};
use fz_runtime::output::{OUTPUT_HOOK, OutputContext, OutputSink};
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
pub(crate) fn run_backend_main<T: Telemetry + ?Sized>(
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &T,
    output: &dyn OutputSink,
    program: &BackendProgram,
) -> Result<i64, String> {
    let mut runtime = IrInterpRuntime::fresh_with_atoms(program.atom_names.clone());
    let module = Module {
        atom_names: program.atom_names.clone(),
        struct_schemas: program.struct_schemas.clone(),
        ..Module::default()
    };
    runtime.enqueue_backend_entry(1, program.entry, Vec::new())?;
    let completions = drive_backend_until_idle(&mut runtime, types, transport, tel, output, program, &module, None)?;
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

pub(crate) fn run_backend_entry_on_process<T: Telemetry + ?Sized>(
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &T,
    output: &dyn OutputSink,
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
        let completions =
            drive_backend_until_idle(&mut runtime, types, transport, tel, output, program, &module, Some(1))?;
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

    pub(super) fn send_opaque<T: Telemetry + ?Sized>(
        &mut self,
        types: &mut crate::compiler2::Types,
        transport: &TransportStore,
        tel: &T,
        program: &BackendProgram,
        module: &Module,
        receiver_pid: &u32,
        msg: AnyValue,
    ) -> Result<(), String> {
        let sender_heap = &unsafe { &*self.cur_proc() }.heap as *const Heap;
        if let Some(park) = self.backend_parked.remove(receiver_pid) {
            if let Some((clause_index, bound_values)) = try_match_backend_receive(
                self,
                types,
                transport,
                program,
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
                let env = delivered_env(self, transport, entries, &park.env, clause.entry, None, &bound_values)?;
                self.enqueue_backend_local_entry(
                    *receiver_pid,
                    park.executable,
                    clause.entry,
                    env,
                    park.continuations,
                )?;
                return Ok(());
            }
            self.backend_parked.insert(*receiver_pid, park);
        }
        let msg_ref = msg.as_any_value_ref(self.cur_proc())?;
        let Some(task) = self.tasks.get_mut(receiver_pid) else {
            tel.raw_event1(&["fz", "runtime", "send_to_unknown_pid"], receiver_pid);
            return Ok(());
        };

        let mut forwarding = HashMap::new();
        let copied = deep_copy_any_value_ref(msg_ref, unsafe { &*sender_heap }, &mut task.heap, &mut forwarding);
        task.mailbox.push_back(copied);
        Ok(())
    }
}

fn drive_backend_until_idle<T: Telemetry + ?Sized>(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &T,
    output: &dyn OutputSink,
    program: &BackendProgram,
    module: &Module,
    keepalive_pid: Option<u32>,
) -> Result<Vec<(u32, AnyValue)>, String> {
    let mut completions = Vec::new();
    let output = OutputContext::new(output);
    let mut exec_ctx = ExecCtx {
        scheduler: runtime as *mut IrInterpRuntime as *mut (),
        output_context: output.as_ptr(),
        output: Some(OUTPUT_HOOK),
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
                drain_pending_dtors_backend(runtime, types, transport, tel, program, module)?;
                unsafe {
                    (*proc_ptr).halt_value = value_to_halt(proc_ptr, value);
                    ExitRecord::emit(tel, &pid, &*proc_ptr);
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
        env: delivered_env(runtime, transport, entries, &frame.env, frame.entry, Some(value), &[]).map_err(
            |error| {
                format!(
                    "backend continuation delivery executable={} entry={}: {error}",
                    frame.executable,
                    frame.entry.as_u32()
                )
            },
        )?,
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
            let semantic_inputs = bind_executable_inputs(transport, types, runtime, executable, &args)?;
            let clause_index = match &executable.entry_dispatch {
                None => 0,
                Some(dispatch) => {
                    let dispatch_inputs = semantic_inputs
                        .iter()
                        .map(|input| {
                            input
                                .as_ref()
                                .map(|value| materialize_backend_value(transport, runtime.cur_proc(), value))
                                .transpose()
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    select_clause(runtime, types, transport, program, module, dispatch, &dispatch_inputs)?.ok_or_else(
                        || {
                            format!(
                                "function_clause: no backend entry clause matched for executable {}",
                                executable_index
                            )
                        },
                    )?
                }
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
    transport: &TransportStore,
    program: &BackendProgram,
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
    let selected = select_dispatch_body(
        runtime,
        types,
        transport,
        program,
        module,
        dispatch.plan(),
        &inputs,
        &HashMap::new(),
    )?;
    Ok(selected.and_then(|body_id| dispatch.clause_index(body_id)))
}

fn select_dispatch_body(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    program: &BackendProgram,
    module: &Module,
    plan: &crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
    args: &[AnyValue],
    pinned: &HashMap<String, AnyValue>,
) -> Result<Option<u32>, String> {
    Ok(
        select_dispatch_match(runtime, types, transport, program, module, plan, args, pinned)?
            .map(|(body_id, _)| body_id),
    )
}

/// The callable a runtime code word denotes, in the terms the type lattice uses.
///
/// A callable value the backend built through a construction wrapper carries
/// that wrapper's synthetic identity, which is this backend's own numbering;
/// the wrapper knows the callable behind it. Every other callable value carries
/// its function's own id directly.
fn backend_callable_identity(transport: &TransportStore, program: &BackendProgram, code: u64) -> Option<ClosureTarget> {
    let fn_id = FnId(u32::try_from(code).ok()?);
    match construction_wrapper_for_fn(program, fn_id) {
        Some(wrapper) => transport
            .interners()
            .callable(wrapper.callable)
            .function
            .map(|function| ClosureTarget(function.as_u32())),
        None => Some(ClosureTarget(fn_id.0)),
    }
}

fn select_dispatch_match(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    program: &BackendProgram,
    module: &Module,
    plan: &crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
    args: &[AnyValue],
    pinned: &HashMap<String, AnyValue>,
) -> Result<Option<DispatchMatch>, String> {
    let mut state = DispatchExecState::default();
    let callables = |code: u64| backend_callable_identity(transport, program, code);
    let mut type_match =
        |runtime: &mut IrInterpRuntime, module: &Module, want: &crate::compiler2::Ty, value: AnyValue| {
            let predicate = types.runtime_type_predicate(want);
            let runtime_value = value.value(runtime.cur_proc()).ok()?;
            let (tuple_schema_ids, named_schema_ids) =
                interp_runtime_type_predicate_schema_ids(runtime, module, &predicate);
            // The representation's owner answers what only it can: which
            // callable a code word denotes, and what a tuple's field holds.
            let proc = runtime.cur_proc();
            let fields = |value: RuntimeAnyValue, index: usize| {
                let field = fz_struct_get_field_ref(proc, value.ref_word().raw_word(), (index as u32) * 8);
                interp_value_from_ref_word(field, "tuple shape field")
                    .ok()
                    .and_then(|value| value.value(proc).ok())
            };
            let list_head = |value: RuntimeAnyValue| {
                let head = fz_list_head_ref(value.ref_word().raw_word());
                interp_value_from_ref_word(head, "list head")
                    .ok()
                    .and_then(|value| value.value(proc).ok())
            };
            let reader = RuntimeValueReader {
                module,
                tuple_schema_ids: &tuple_schema_ids,
                named_schema_ids: &named_schema_ids,
                callables: &callables,
                fields: &fields,
                list_head: &list_head,
            };
            let matched = matches_runtime_type_predicate(&predicate, &reader, runtime_value);
            if matched {
                surface_membership::observe(&predicate, &reader, runtime_value);
            }
            Some(matched)
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

fn step_eval_entry<T: Telemetry + ?Sized>(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &T,
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
    let transition = match &entry.tail {
        BackendTail::Value { value, dest } => {
            // fz-kdt.111: honor the return contract's own absence proof, the way
            // native's `return_lane_vars` does. Transport publishes no lane for a
            // demand-ignored input, so `bind_executable_inputs` leaves it out of
            // the env entirely; returning it is only ever reached when the return
            // contract publishes no lanes either, so there is nothing to encode
            // and nothing to read. Any other env miss is still a real fault.
            let returns_no_lanes =
                matches!(dest, ControlDestination::Return) && executable.return_layout.layout.reprs.is_empty();
            let result = if returns_no_lanes && !env.contains_key(value) {
                BackendBoundValue::Absent
            } else {
                env_get_value(&env, *value)?
            };
            match dest {
                ControlDestination::Return => {
                    continue_backend_value(runtime, transport, program, result, continuations)
                }
                ControlDestination::Deliver(target) => Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                    executable: executable_index,
                    entry: *target,
                    env: delivered_env(runtime, transport, entries, &env, *target, Some(result), &[])?,
                    continuations,
                })),
            }
        }
        BackendTail::DirectCall { target, args, dest, .. } => {
            let (callee, extern_marshals) = match target {
                CallEdge::Direct(direct) => (&direct.callee, direct.extern_marshals.as_deref()),
                CallEdge::Dispatch(dispatch) => {
                    let required_inputs = required_dispatch_input_ordinals(&dispatch.plan);
                    let input_values = args
                        .iter()
                        .enumerate()
                        .map(|(index, arg)| {
                            if required_inputs.contains(&index) {
                                env_get(transport, runtime.cur_proc(), &env, arg.value).map_err(|error| {
                                    format!(
                                        "backend dispatch call requires semantic argument {index} value {}: {error}",
                                        arg.value.as_u32()
                                    )
                                })
                            } else {
                                Ok(interp_nil_value())
                            }
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    let body_id = select_dispatch_body(
                        runtime,
                        types,
                        transport,
                        program,
                        module,
                        &dispatch.plan,
                        &input_values,
                        &HashMap::new(),
                    )?
                    .ok_or_else(|| {
                        format!(
                            "backend dispatch callsite in executable {} missed an exhaustive dispatch",
                            executable_index
                        )
                    })?;
                    let arm = dispatch
                        .arms
                        .iter()
                        .find(|arm| arm.body_id == body_id)
                        .ok_or_else(|| format!("backend dispatch call arm {} is out of bounds", body_id))?;
                    (&arm.callee, arm.extern_marshals.as_deref())
                }
                CallEdge::Indirect { .. } => {
                    return Err(format!(
                        "backend direct callsite in executable {executable_index} materialized as an indirect closure edge; Indirect is closure-call-only"
                    ));
                }
            };
            eval_backend_direct_call_edge(
                runtime,
                types,
                transport,
                tel,
                program,
                module,
                callee,
                args,
                extern_marshals,
                env,
                executable_index,
                dest.clone(),
                continuations,
            )
        }
        BackendTail::ClosureCall {
            target,
            callsite,
            callee,
            args,
            dest,
            ..
        } => {
            let callee_value = env_get_value(&env, *callee);
            let missing_direct_callee = callee_value.is_err();
            let (fn_id, _capture_shape, capture_lanes) = match callee_value {
                Ok(BackendBoundValue::Transport { shape, lanes })
                    if matches!(transport.interners().shape(shape), ShapeDescr::Callable(_)) =>
                {
                    let ShapeDescr::Callable(callable) = transport.interners().shape(shape) else {
                        unreachable!();
                    };
                    let callable = transport.interners().callable(*callable);
                    let function = callable.function.ok_or_else(|| {
                        "backend closure call cannot directly invoke generic callable transport".to_string()
                    })?;
                    (FnId(function.as_u32()), Some(shape), lanes)
                }
                Ok(other) => {
                    let materialized = materialize_backend_value(transport, runtime.cur_proc(), &other)?;
                    let (fn_id, captures) = match materialized {
                        AnyValue::FnRef(fn_id, _) => (fn_id, Vec::new()),
                        other => unpack_closure(other.value(runtime.cur_proc())?).map_err(|error| {
                            format!(
                                "closure call executable={} function={} callsite={} callee_value={}: {error}",
                                executable_index,
                                executable.key.activation.function.as_u32(),
                                callsite.as_u32(),
                                callee.as_u32()
                            )
                        })?,
                    };
                    (fn_id, None, captures)
                }
                Err(error) => {
                    let Some(target) = target else {
                        return Err(format!(
                            "closure call executable={} function={} callsite={} callee_value={}: {error}",
                            executable_index,
                            executable.key.activation.function.as_u32(),
                            callsite.as_u32(),
                            callee.as_u32()
                        ));
                    };
                    let callee_executable = program
                        .executables
                        .get(*target)
                        .ok_or_else(|| format!("backend executable {} is out of bounds", target))?;
                    (
                        FnId(callee_executable.key.activation.function.as_u32()),
                        None,
                        Vec::new(),
                    )
                }
            };
            let wrapper = construction_wrapper_for_fn(program, fn_id);
            let executable_target = if let Some(wrapper) = wrapper {
                let args = args
                    .iter()
                    .map(|arg| env_get(transport, runtime.cur_proc(), &env, arg.value))
                    .collect::<Result<Vec<_>, _>>()?;
                select_construction_member(runtime, types, transport, program, module, wrapper, &args)?.target
            } else if let Some(target) = target {
                *target
            } else {
                return Err(format!(
                    "backend closure call executable={} function={} callsite={} has no construction wrapper or direct target",
                    executable_index,
                    executable.key.activation.function.as_u32(),
                    callsite.as_u32()
                ));
            };
            let callee_executable = program
                .executables
                .get(executable_target)
                .ok_or_else(|| format!("backend executable {} is out of bounds", executable_target))?;
            let capture_inputs_end = callee_executable
                .key
                .activation
                .input_len(types)
                .checked_sub(args.len())
                .ok_or_else(|| {
                    format!(
                        "backend executable {} has fewer inputs than closure call args",
                        callee_executable.key.activation.function.as_u32()
                    )
                })?;
            if missing_direct_callee
                && callee_executable
                    .semantic_inputs
                    .iter()
                    .any(|input| input.semantic_index < capture_inputs_end && !input.layout.reprs.is_empty())
            {
                return Err(format!(
                    "closure call executable={} function={} callsite={} omitted callee value {} but target {} needs semantic inputs",
                    executable_index,
                    executable.key.activation.function.as_u32(),
                    callsite.as_u32(),
                    callee.as_u32(),
                    executable_target
                ));
            }
            let call_args = if let Some(wrapper) = wrapper {
                let member = select_construction_member(
                    runtime,
                    types,
                    transport,
                    program,
                    module,
                    wrapper,
                    &args
                        .iter()
                        .map(|arg| env_get(transport, runtime.cur_proc(), &env, arg.value))
                        .collect::<Result<Vec<_>, _>>()?,
                )?;
                ConstructionInputEncoder {
                    runtime,
                    types,
                    transport,
                    target: callee_executable,
                    target_index: executable_target,
                    wrapper,
                    member,
                }
                .encode(&capture_lanes, args, |arg| env_get_value(&env, arg.value))?
            } else {
                let mut lanes = capture_lanes;
                lanes.extend(encode_call_args(
                    transport,
                    types,
                    runtime,
                    callee_executable,
                    &env,
                    args,
                    capture_inputs_end,
                )?);
                lanes
            };
            let continuations = match dest {
                ControlDestination::Return => continuations,
                ControlDestination::Deliver(target) => {
                    let mut continuations = continuations;
                    let proc = runtime.cur_proc();
                    continuations.push(BackendContinuation {
                        executable: executable_index,
                        entry: *target,
                        env: capture_backend_continuation_env(proc, entries, *target, &env)?,
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
                env: delivered_env(runtime, transport, entries, &env, target, None, &[])?,
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
            let target = match select_dispatch_body(
                runtime,
                types,
                transport,
                program,
                module,
                &dispatch.plan,
                &input_values,
                &pinned_values,
            )? {
                Some(body_id) => *dispatch
                    .arm_entries
                    .get(body_id as usize)
                    .ok_or_else(|| format!("backend local dispatch arm {} is out of bounds", body_id))?,
                None => dispatch.miss_entry,
            };
            Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                executable: executable_index,
                entry: target,
                env: delivered_env(runtime, transport, entries, &env, target, None, &[])?,
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
                    runtime, types, transport, program, module, clauses, dispatch, msg, bindings, &env,
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
                    env: delivered_env(runtime, transport, entries, &env, clause.entry, None, &bound_values)?,
                    continuations,
                }));
            }
            if let Some(after) = after
                && env_get(transport, runtime.cur_proc(), &env, after.timeout)?.as_i64() == Some(0)
            {
                return Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                    executable: executable_index,
                    entry: after.entry,
                    env: delivered_env(runtime, transport, entries, &env, after.entry, None, &[])?,
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
    };
    transition.map_err(|error| {
        format!(
            "backend executable {} function {} entry {} tail failed: {error}",
            executable_index,
            executable.key.activation.function.as_u32(),
            entry_id.as_u32()
        )
    })
}

fn try_match_backend_receive(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    program: &BackendProgram,
    module: &Module,
    clauses: &[crate::compiler2::ReceiveClause],
    dispatch: &crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
    msg: AnyValue,
    bindings: &crate::compiler2::DispatchBindings,
    env: &HashMap<ValueId, BackendBoundValue>,
) -> Result<Option<(usize, Vec<AnyValue>)>, String> {
    let pinned = local_dispatch_pinned(transport, runtime.cur_proc(), env, bindings, dispatch)?;
    let Some((body_id, binds)) =
        select_dispatch_match(runtime, types, transport, program, module, dispatch, &[msg], &pinned)?
    else {
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

fn eval_steps<T: Telemetry + ?Sized>(
    runtime: &mut IrInterpRuntime,
    _types: &mut crate::compiler2::Types,
    _tel: &T,
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
                let bound = tuple_step_value(transport, runtime.cur_proc(), executable, env, *value, items)?;
                env.insert(*value, bound);
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
            ProgramStep::FunctionRef {
                value,
                function,
                construction,
            } => {
                let bound = if let Some(construction) = construction {
                    construction_callable_value(runtime.cur_proc(), program, *construction, &[])?
                } else if executable
                    .runtime_demand
                    .callable_flows
                    .get(value)
                    .is_some_and(|flow| !flow.escape && !flow.opaque && !flow.direct_surfaces.is_empty())
                {
                    let proc = runtime.cur_proc();
                    direct_callable_value(transport, executable, proc, env, *value, *function, &[])?
                } else {
                    BackendBoundValue::Runtime(AnyValue::FnRef(
                        FnId(function.as_u32()),
                        callable_value_arity(program, *function, 0),
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
                let bound = if let Some(construction) = construction {
                    let wrapper = construction_wrapper_for_identity(program, *construction).ok_or_else(|| {
                        format!("backend callable construction {construction} is missing its wrapper")
                    })?;
                    if captures.len() != wrapper.captures.len() {
                        return Err(format!(
                            "backend callable construction {construction} expected {} logical capture(s), got {}",
                            wrapper.captures.len(),
                            captures.len()
                        ));
                    }
                    let physical_captures = captures
                        .iter()
                        .copied()
                        .zip(wrapper.captures.iter())
                        .filter(|(_, capture)| !capture.layout.reprs.is_empty())
                        .map(|(capture, _)| env_get(transport, runtime.cur_proc(), env, capture))
                        .collect::<Result<Vec<_>, _>>()?;
                    construction_callable_value(runtime.cur_proc(), program, *construction, &physical_captures)?
                } else if executable
                    .runtime_demand
                    .callable_flows
                    .get(value)
                    .is_some_and(|flow| !flow.escape && !flow.opaque && !flow.direct_surfaces.is_empty())
                {
                    let proc = runtime.cur_proc();
                    direct_callable_value(transport, executable, proc, env, *value, *function, captures)?
                } else {
                    BackendBoundValue::Runtime(make_closure(
                        runtime,
                        function.as_u32(),
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
        crate::compiler2::BackendEntryOrigin::DeliveredResume { value, layout } => {
            let bound = bind_delivered_value(transport, runtime.cur_proc(), entry_id, delivered.as_ref(), layout)?;
            if let Some(bound) = bound {
                next.insert(*value, bound);
            }
        }
    }
    for capture in &entry.captures {
        if capture.layout.reprs.is_empty() {
            continue;
        }
        next.insert(capture.value, env_get_value(env, capture.value)?);
    }
    for capture in &entry.reusable_cons_captures {
        next.insert(capture.source, env_get_value(env, capture.source)?);
    }
    Ok(next)
}

#[allow(clippy::too_many_arguments)]
fn eval_backend_direct_call_edge<T: Telemetry + ?Sized>(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &T,
    program: &BackendProgram,
    module: &Module,
    callee: &CallTarget<usize>,
    args: &[crate::compiler2::BackendCallArg],
    extern_marshals: Option<&[crate::fz_ir::ExternTy]>,
    env: HashMap<ValueId, BackendBoundValue>,
    executable_index: usize,
    dest: ControlDestination,
    continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
    match callee {
        CallTarget::Local(callee) => eval_direct_call(
            runtime,
            types,
            transport,
            tel,
            program,
            module,
            *callee,
            args,
            extern_marshals,
            env,
            executable_index,
            dest,
            continuations,
        ),
        CallTarget::ProviderBoundary(function) => Err(format!(
            "unresolved provider-boundary backend call to function {}",
            function.as_u32()
        )),
    }
}

fn eval_direct_call<T: Telemetry + ?Sized>(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &T,
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
    let call_args = encode_call_args(transport, types, runtime, executable, &env, args, 0)?;
    let continuations = match dest {
        ControlDestination::Return => continuations,
        ControlDestination::Deliver(target) => {
            let mut continuations = continuations;
            continuations.push(BackendContinuation {
                executable: executable_index,
                entry: target,
                env: {
                    let proc = runtime.cur_proc();
                    capture_backend_continuation_env(
                        proc,
                        entries_for_executable(program, executable_index)?,
                        target,
                        &env,
                    )?
                },
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

#[allow(clippy::too_many_arguments)]
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
        if capture.layout.reprs.is_empty() {
            continue;
        }
        let value = env_get_value(env, capture.value).map_err(|error| {
            format!(
                "backend continuation capture value {} is unavailable: {error}",
                capture.value.as_u32(),
            )
        })?;
        captured.insert(capture.value, publish_backend_capture(proc, &value)?);
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
    types: &crate::compiler2::Types,
    runtime: &mut IrInterpRuntime,
    executable: &BackendExecutable,
    args: &[AnyValue],
) -> Result<Vec<Option<BackendBoundValue>>, String> {
    let semantic_arity = executable.key.activation.input_len(types);
    let mut bound = vec![None; semantic_arity];
    let mut lane_index = 0;
    let proc = runtime.cur_proc();
    for input in &executable.semantic_inputs {
        let value = if input.layout.reprs.is_empty() {
            None
        } else {
            Some(decode_runtime_value_with_carrier(
                transport,
                proc,
                args,
                input.layout.structural,
                input.layout.carrier,
                &mut lane_index,
            )?)
        };
        bound[input.semantic_index] = value;
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
    for input in &executable.semantic_inputs {
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
        .value_layouts
        .get(&value)
        .map(|layout| layout.structural)
        .ok_or_else(|| format!("backend executable did not publish a layout for {value:?}"))
}

#[allow(clippy::too_many_arguments)]
fn direct_callable_value(
    transport: &TransportStore,
    executable: &BackendExecutable,
    proc: *mut Process,
    env: &HashMap<ValueId, BackendBoundValue>,
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
    if callable.capture_shapes.len() != captures.len() {
        return Err(format!(
            "backend direct callable producer {} expected {} capture shape(s), got {} capture value(s)",
            value.as_u32(),
            callable.capture_shapes.len(),
            captures.len()
        ));
    }
    // The callable descriptor's `capture_lanes` is the one authority on how
    // many lanes the construction carries, and it can be wider than the sum
    // of the captures' structural widths: a capture whose structural shape is
    // width 0 may still own one descriptor lane, carrying the value boxed
    // (native's construction lowering assigns those extra lanes to width-0
    // captures greedily in capture order). A width-0 capture that owns no
    // lane is fully erased -- its value may legitimately be unbound (its own
    // input published no layout), so it must be skipped without ever reading
    // the environment.
    let structural_width: usize = callable
        .capture_shapes
        .iter()
        .map(|shape| transport.interners().shape_width(*shape))
        .sum();
    let mut extra_lanes = callable.capture_lanes.len().saturating_sub(structural_width);
    let mut lanes = Vec::new();
    for (capture, capture_shape) in captures.iter().copied().zip(callable.capture_shapes.iter().copied()) {
        if transport.interners().shape_width(capture_shape) == 0 {
            if extra_lanes == 0 {
                continue;
            }
            extra_lanes -= 1;
            let bound = env_get_value(env, capture)?;
            lanes.push(materialize_backend_value(transport, proc, &bound)?);
        } else {
            let bound = env_get_value(env, capture)?;
            encode_runtime_value(transport, proc, &bound, capture_shape, &mut lanes)?;
        }
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

const CONSTRUCTION_WRAPPER_IDENTITY_BASE: u32 = 0x8000_0000;

fn construction_wrapper_identity_fn(identity: u32) -> FnId {
    FnId(CONSTRUCTION_WRAPPER_IDENTITY_BASE | identity)
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
        .executables
        .iter()
        .find(|executable| executable.key.activation.function == function)
        .map(|executable| executable.semantic_inputs.len().saturating_sub(capture_count) as u16)
        .unwrap_or(0)
}

fn construction_wrapper_for_fn(program: &BackendProgram, fn_id: FnId) -> Option<&BackendConstructionWrapper> {
    (fn_id.0 & CONSTRUCTION_WRAPPER_IDENTITY_BASE != 0)
        .then_some(fn_id.0 & !CONSTRUCTION_WRAPPER_IDENTITY_BASE)
        .and_then(|identity| construction_wrapper_for_identity(program, identity))
}

fn construction_wrapper_for_identity(program: &BackendProgram, identity: u32) -> Option<&BackendConstructionWrapper> {
    program
        .construction_wrappers
        .iter()
        .find(|wrapper| wrapper.identity == identity)
}

fn construction_callable_value(
    proc: *mut Process,
    program: &BackendProgram,
    identity: u32,
    captures: &[AnyValue],
) -> Result<BackendBoundValue, String> {
    let wrapper = construction_wrapper_for_identity(program, identity)
        .ok_or_else(|| format!("backend callable construction {identity} is missing its wrapper"))?;
    let capture_count = wrapper
        .captures
        .iter()
        .filter(|capture| !capture.layout.reprs.is_empty())
        .count();
    if captures.len() != capture_count {
        return Err(format!(
            "backend callable construction {identity} expected {} capture value(s), got {}",
            capture_count,
            captures.len()
        ));
    }
    let fn_id = construction_wrapper_identity_fn(identity);
    let arity = wrapper.call_arity as u16;
    let value = if captures.is_empty() {
        AnyValue::FnRef(fn_id, arity)
    } else {
        make_closure_on_proc(proc, fn_id.0, arity, captures.to_vec())?
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
            "backend callable construction {} expected {} call arg(s), got {}",
            wrapper.identity,
            wrapper.call_arity,
            args.len()
        ));
    }
    let member = match &wrapper.selection {
        Some(selection) => select_dispatch_body(
            runtime,
            types,
            transport,
            program,
            module,
            selection,
            args,
            &HashMap::new(),
        )?
        .ok_or_else(|| format!("backend callable construction {} matched no member", wrapper.identity))?
            as usize,
        None if wrapper.members.len() == 1 => 0,
        None => {
            return Err(format!(
                "backend callable construction {} has {} members without a selection plan",
                wrapper.identity,
                wrapper.members.len()
            ));
        }
    };
    wrapper.members.get(member).ok_or_else(|| {
        format!(
            "backend callable construction {} selected member {} outside {} members",
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
) -> Result<(usize, Vec<AnyValue>), String> {
    let wrapper = construction_wrapper_for_fn(program, fn_id)
        .ok_or_else(|| format!("backend callable {} has no construction wrapper", fn_id.0))?;
    let member = select_construction_member(runtime, types, transport, program, module, wrapper, args)?;
    let target = member.target;
    let executable = program.executables.get(target).ok_or_else(|| {
        format!(
            "backend callable construction {} target {} is out of bounds",
            wrapper.identity, target
        )
    })?;
    let lanes = ConstructionInputEncoder {
        runtime,
        types,
        transport,
        target: executable,
        target_index: target,
        wrapper,
        member,
    }
    .encode(captures, args, |arg| Ok(BackendBoundValue::Runtime(*arg)))?;
    Ok((target, lanes))
}

struct ConstructionInputEncoder<'a> {
    runtime: &'a mut IrInterpRuntime,
    types: &'a crate::compiler2::Types,
    transport: &'a TransportStore,
    target: &'a BackendExecutable,
    target_index: usize,
    wrapper: &'a BackendConstructionWrapper,
    member: &'a BackendConstructionMemberAdapter,
}

impl ConstructionInputEncoder<'_> {
    fn encode<T>(
        self,
        captures: &[AnyValue],
        args: &[T],
        mut resolve_arg: impl FnMut(&T) -> Result<BackendBoundValue, String>,
    ) -> Result<Vec<AnyValue>, String> {
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
                "backend callable construction {} member target {} publishes semantic input {} for arity {}",
                self.wrapper.identity, self.target_index, input.semantic_index, semantic_arity
            ));
        }
        let physical_capture_count = self
            .wrapper
            .captures
            .iter()
            .filter(|capture| !capture.layout.reprs.is_empty())
            .count();
        if self.wrapper.captures.len() != self.member.capture_semantic_inputs.len()
            || captures.len() != physical_capture_count
            || args.len() != self.member.surface_semantic_inputs.len()
            || args.len() != self.wrapper.call_arity
        {
            return Err(format!(
                "backend callable construction {} member target {} does not match its published semantic layout",
                self.wrapper.identity, self.target_index
            ));
        }
        let mut semantic_values = vec![None; semantic_arity];
        let mut physical_captures = captures.iter().copied();
        for (capture, semantic_index) in self
            .wrapper
            .captures
            .iter()
            .zip(self.member.capture_semantic_inputs.iter().copied())
        {
            let slot = semantic_values.get_mut(semantic_index).ok_or_else(|| {
                format!(
                    "backend callable construction {} maps capture outside target {}",
                    self.wrapper.identity, self.target_index
                )
            })?;
            if !capture.layout.reprs.is_empty()
                && slot
                    .replace(physical_captures.next().ok_or_else(|| {
                        format!(
                            "backend callable construction {} is missing a physical capture",
                            self.wrapper.identity
                        )
                    })?)
                    .is_some()
            {
                return Err(format!(
                    "backend callable construction {} maps more than one capture to one target input",
                    self.wrapper.identity
                ));
            }
        }
        if physical_captures.next().is_some() {
            return Err(format!(
                "backend callable construction {} has excess physical captures",
                self.wrapper.identity
            ));
        }
        let mut explicit_values = vec![None; semantic_arity];
        for (arg_index, semantic_index) in self.member.surface_semantic_inputs.iter().copied().enumerate() {
            let slot = explicit_values.get_mut(semantic_index).ok_or_else(|| {
                format!(
                    "backend callable construction {} maps an argument outside target {}",
                    self.wrapper.identity, self.target_index
                )
            })?;
            if semantic_values[semantic_index].is_some() || slot.replace(arg_index).is_some() {
                return Err(format!(
                    "backend callable construction {} maps more than one value to target input {}",
                    self.wrapper.identity, semantic_index
                ));
            }
        }
        let mut lanes = Vec::new();
        for binding in &self.target.semantic_inputs {
            let input = self
                .member
                .target_inputs
                .iter()
                .find(|input| input.semantic_index == binding.semantic_index)
                .ok_or_else(|| {
                    format!(
                        "backend callable construction {} target {} omits semantic input {}",
                        self.wrapper.identity, self.target_index, binding.semantic_index
                    )
                })?;
            if input.layout.reprs.is_empty() {
                continue;
            }
            let value = match semantic_values[binding.semantic_index] {
                Some(value) => BackendBoundValue::Runtime(value),
                None => {
                    let arg_index = explicit_values[binding.semantic_index].ok_or_else(|| {
                        format!(
                            "backend callable construction {} cannot populate target {} semantic input {}",
                            self.wrapper.identity, self.target_index, binding.semantic_index
                        )
                    })?;
                    resolve_arg(&args[arg_index])?
                }
            };
            encode_runtime_input_binding(self.transport, self.runtime.cur_proc(), &value, binding, &mut lanes)?;
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
            let arity = callable.arity;
            if lanes.is_empty() {
                Ok(AnyValue::FnRef(FnId(function.as_u32()), arity))
            } else {
                make_closure_on_proc(proc, function.as_u32(), arity, lanes.to_vec())
            }
        }
    }
}

fn encode_call_args(
    transport: &TransportStore,
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
    let bindings = &executable.semantic_inputs;
    for binding in bindings
        .iter()
        .filter(|binding| binding.semantic_index >= semantic_start)
    {
        if binding.layout.reprs.is_empty() {
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
        encode_runtime_input_binding(transport, runtime.cur_proc(), &value, binding, &mut lanes).map_err(|error| {
            format!(
                "backend encode_call_args callee_fn={} semantic_index={} shape={:?} arg_value={:?}: {error}",
                executable.key.activation.function.as_u32(),
                binding.semantic_index,
                transport.interners().shape(binding.layout.structural),
                arg.value,
            )
        })?;
    }
    Ok(lanes)
}

fn bind_delivered_value(
    transport: &TransportStore,
    proc: *mut Process,
    entry_id: crate::compiler2::ControlEntryId,
    delivered: Option<&BackendBoundValue>,
    layout: &crate::compiler2::BackendReturnLayout,
) -> Result<Option<BackendBoundValue>, String> {
    match transport.interners().shape(layout.layout.structural) {
        ShapeDescr::Nothing if matches!(layout.layout.carrier, TransportCarrier::Absent) => Ok(None),
        _ => {
            let delivered = delivered.ok_or_else(|| {
                format!(
                    "backend entry {} expected a delivered value but none was provided",
                    entry_id.as_u32()
                )
            })?;
            Ok(Some(project_backend_value_for_contract(
                transport, proc, delivered, layout,
            )?))
        }
    }
}

fn project_backend_value_for_contract(
    transport: &TransportStore,
    proc: *mut Process,
    value: &BackendBoundValue,
    layout: &crate::compiler2::BackendReturnLayout,
) -> Result<BackendBoundValue, String> {
    if matches!(layout.layout.carrier, TransportCarrier::ValueRef) {
        return Ok(BackendBoundValue::Runtime(materialize_backend_value(
            transport, proc, value,
        )?));
    }
    let mut lanes = Vec::new();
    encode_runtime_value(transport, proc, value, layout.layout.structural, &mut lanes)?;
    let mut lane_index = 0;
    let decoded = decode_runtime_value_with_carrier(
        transport,
        proc,
        &lanes,
        layout.layout.structural,
        TransportCarrier::Absent,
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

fn encode_runtime_value_with_carrier(
    transport: &TransportStore,
    proc: *mut Process,
    value: &BackendBoundValue,
    shape: ShapeId,
    carrier: crate::compiler2::pull::TransportCarrier,
    lanes: &mut Vec<AnyValue>,
) -> Result<(), String> {
    match transport.interners().shape(shape) {
        ShapeDescr::Nothing if matches!(carrier, crate::compiler2::pull::TransportCarrier::ValueRef) => {
            lanes.push(materialize_backend_value(transport, proc, value)?);
            Ok(())
        }
        ShapeDescr::Callable(_) if matches!(carrier, crate::compiler2::pull::TransportCarrier::ValueRef) => {
            lanes.push(materialize_backend_value(transport, proc, value)?);
            Ok(())
        }
        ShapeDescr::Tuple(fields) => {
            let tuple_fields = tuple_field_values_for_shape(transport, proc, value, shape, fields)?;
            for (field_value, field_shape) in tuple_fields.iter().zip(fields.iter().copied()) {
                encode_runtime_value_with_carrier(transport, proc, field_value, field_shape, carrier, lanes)?;
            }
            Ok(())
        }
        ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Callable(_) => {
            encode_runtime_value(transport, proc, value, shape, lanes)
        }
    }
}

fn encode_runtime_input_binding(
    transport: &TransportStore,
    proc: *mut Process,
    value: &BackendBoundValue,
    input: &crate::compiler2::BackendSemanticInputLayout,
    lanes: &mut Vec<AnyValue>,
) -> Result<(), String> {
    if input.layout.reprs.is_empty() {
        return Ok(());
    }
    encode_runtime_value_with_carrier(
        transport,
        proc,
        value,
        input.layout.structural,
        input.layout.carrier,
        lanes,
    )
}

fn decode_runtime_value_with_carrier(
    transport: &TransportStore,
    proc: *mut Process,
    args: &[AnyValue],
    shape: ShapeId,
    carrier: crate::compiler2::pull::TransportCarrier,
    lane_index: &mut usize,
) -> Result<BackendBoundValue, String> {
    match transport.interners().shape(shape) {
        ShapeDescr::Nothing if matches!(carrier, crate::compiler2::pull::TransportCarrier::ValueRef) => {
            next_runtime_lane(args, lane_index).map(BackendBoundValue::Runtime)
        }
        ShapeDescr::Nothing => Ok(BackendBoundValue::Absent),
        ShapeDescr::Lane(_) => {
            let value = next_runtime_lane(args, lane_index)?;
            Ok(BackendBoundValue::Runtime(value))
        }
        ShapeDescr::Callable(_) if matches!(carrier, crate::compiler2::pull::TransportCarrier::ValueRef) => {
            next_runtime_lane(args, lane_index).map(BackendBoundValue::Runtime)
        }
        ShapeDescr::Callable(_) => {
            let width = backend_shape_width(transport, shape);
            let lanes = take_runtime_lanes(args, lane_index, width)?;
            decode_backend_value_from_lanes(transport, shape, lanes)
        }
        ShapeDescr::Tuple(fields) => {
            let mut field_values = Vec::with_capacity(fields.len());
            let mut raw_lanes = Vec::new();
            let mut all_raw = true;
            for field in fields.iter().copied() {
                let value = decode_runtime_value_with_carrier(transport, proc, args, field, carrier, lane_index)?;
                if all_raw {
                    if let Some(lanes) = raw_lanes_for_shape_value(transport, field, &value) {
                        raw_lanes.extend(lanes);
                    } else {
                        all_raw = false;
                    }
                }
                field_values.push(value);
            }
            if all_raw {
                return Ok(BackendBoundValue::Transport {
                    shape,
                    lanes: raw_lanes,
                });
            }
            let fields = field_values
                .iter()
                .map(|value| materialize_backend_value(transport, proc, value))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(BackendBoundValue::Runtime(make_tuple_on_proc(proc, fields)?))
        }
    }
}

fn backend_shape_width(transport: &TransportStore, shape: ShapeId) -> usize {
    match transport.interners().shape(shape) {
        ShapeDescr::Callable(callable) if transport.interners().callable(*callable).function.is_none() => 1,
        _ => transport.interners().shape_width(shape),
    }
}

fn raw_lanes_for_shape_value(
    transport: &TransportStore,
    shape: ShapeId,
    value: &BackendBoundValue,
) -> Option<Vec<AnyValue>> {
    match (transport.interners().shape(shape), value) {
        (ShapeDescr::Nothing, BackendBoundValue::Absent) => Some(Vec::new()),
        (ShapeDescr::Lane(_), BackendBoundValue::Runtime(value)) => Some(vec![*value]),
        (
            ShapeDescr::Tuple(_) | ShapeDescr::Callable(_),
            BackendBoundValue::Transport {
                shape: value_shape,
                lanes,
            },
        ) if *value_shape == shape && lanes.len() == transport.interners().shape_width(shape) => Some(lanes.clone()),
        _ => None,
    }
}

fn take_runtime_lanes(args: &[AnyValue], lane_index: &mut usize, width: usize) -> Result<Vec<AnyValue>, String> {
    let end = lane_index
        .checked_add(width)
        .ok_or_else(|| "backend runtime lane offset overflow".to_string())?;
    let lanes = args
        .get(*lane_index..end)
        .ok_or_else(|| format!("backend expected runtime lane range {}..{}", *lane_index, end))?
        .to_vec();
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
                AnyValue::FnRef(fn_id, _) => (fn_id, Vec::new()),
                other => unpack_closure(other.value(proc)?)?,
            };
            if fn_id.0 & CONSTRUCTION_WRAPPER_IDENTITY_BASE == 0 && FunctionId::from_fn_id(fn_id) != function {
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
            BodyLiteral::Binary(value) => {
                let ref_word = fz_runtime::ir_runtime::fz_alloc_bitstring_const(
                    runtime.cur_proc(),
                    value.as_ptr() as u64,
                    value.len() as u64,
                    (value.len() * 8) as u64,
                );
                interp_value_from_ref_word(ref_word, "backend binary literal")?
            }
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
    proc: *mut Process,
    executable: &BackendExecutable,
    env: &HashMap<ValueId, BackendBoundValue>,
    value: ValueId,
    items: &[ValueId],
) -> Result<BackendBoundValue, String> {
    if let Some(layout) = executable.value_layouts.get(&value)
        && !matches!(layout.carrier, TransportCarrier::ValueRef)
        && let ShapeDescr::Tuple(fields) = transport.interners().shape(layout.structural)
    {
        let fields = fields.clone();
        if fields.len() != items.len() {
            return Err(format!(
                "backend tuple step for value {} has {} item(s) but its layout shape has {} field(s)",
                value.as_u32(),
                items.len(),
                fields.len()
            ));
        }
        let mut lanes = Vec::new();
        for (item, field_shape) in items.iter().copied().zip(fields.iter().copied()) {
            let bound = env_get_value(env, item)?;
            encode_runtime_value(transport, proc, &bound, field_shape, &mut lanes)?;
        }
        return Ok(BackendBoundValue::Transport {
            shape: layout.structural,
            lanes,
        });
    }
    let items = env_values(transport, proc, env, items)?;
    Ok(BackendBoundValue::Runtime(make_tuple_on_proc(proc, items)?))
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

fn make_closure_on_proc(
    proc: *mut Process,
    code: u32,
    arity: u16,
    captures: Vec<AnyValue>,
) -> Result<AnyValue, String> {
    let heap = &mut unsafe { &mut *proc }.heap;
    let bits = heap.alloc_closure_slots(arity, captures.len(), 0);
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

fn make_closure(
    runtime: &mut IrInterpRuntime,
    code: u32,
    arity: u16,
    captures: Vec<AnyValue>,
) -> Result<AnyValue, String> {
    make_closure_on_proc(runtime.cur_proc(), code, arity, captures)
}

fn drain_pending_dtors_backend<T: Telemetry + ?Sized>(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &T,
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
        let (fn_id, captures) = unpack_pending_dtor_closure(closure)?;
        let payload = interp_value_from_ref_word(payload_ref, "backend dtor drain payload")?;
        let (target, args) =
            construction_wrapper_invocation(runtime, types, transport, program, module, fn_id, &captures, &[payload])?;
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

fn unpack_pending_dtor_closure(closure: RuntimeAnyValue) -> Result<(FnId, Vec<AnyValue>), String> {
    unpack_closure(closure).map_err(|error| format!("backend dtor drain: invalid closure: {error}"))
}

fn is_tuple_arity(runtime: &mut IrInterpRuntime, value: AnyValue, arity: usize) -> Result<bool, String> {
    let slot = value.value(runtime.cur_proc())?;
    Ok(slot.kind() == ValueKind::STRUCT
        && slot
            .heap_addr()
            .is_some_and(|p| unsafe { struct_schema_id(p) } == interp_tuple_schema_id(runtime, arity)))
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
    if slot.kind() == ValueKind::RESOURCE && field == "value" {
        let atom_id = module
            .atom_names
            .iter()
            .position(|name| name == field)
            .ok_or_else(|| format!("field atom `{field}` not interned"))?;
        return with_value_ref(runtime.cur_proc(), value, "backend resource field", |resource_ref| {
            fz_struct_get_named_field_ref(runtime.cur_proc(), resource_ref, atom_id as u64)
        })
        .and_then(|ref_word| interp_value_from_ref_word(ref_word, "backend resource field"));
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn backend_destructor_closure_unpack_errors_propagate() {
        let error = unpack_pending_dtor_closure(RuntimeAnyValue::null()).expect_err("non-closure destructor must fail");
        assert!(error.contains("backend dtor drain: invalid closure"), "{error}");
    }
}
