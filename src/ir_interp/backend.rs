use std::collections::HashMap;
use std::rc::Rc;

use super::binop::{eval_binop, eval_unop, interp_value_eq, unpack_closure};
use super::dispatch_exec::{
    DispatchExecState, DispatchMatch, DispatchValues, execute_dispatch_inputs, resolve_dispatch_subject,
};
use super::extern_call::call_lowered_extern;
use super::prim::{interp_list_cons, interp_list_head, interp_list_tail, interp_map_get, interp_map_put};
use super::value::{
    AnyValue, interp_bool_value, interp_empty_list_value, interp_nil_value, interp_runtime_type_predicate_schema_ids,
    interp_struct_field_from_tagged_bits, interp_value_from_ref_word, with_value_ref,
};
use super::*;
use crate::compiler2::pull::TransportCarrier;
use crate::compiler2::transport::{ShapeDescr, ShapeId, TransportLayout, TransportPosition, TransportStore};
use crate::compiler2::{
    BackendBody, BackendConstructionMemberAdapter, BackendConstructionWrapper, BackendEntry, BackendExecutable,
    BackendProgram, BackendStep as ProgramStep, BackendTail, CallEdge, CallTarget, ControlDestination,
    ExecutableDispatch, ValueId, required_dispatch_input_ordinals,
};
use crate::compiler2::{ExecutableKey, FunctionId};
use crate::fz_ir::{BinOp as IrBinOp, FnId, Module, UnOp as IrUnOp};
use crate::runtime_type_predicate::{
    CallableShape, RuntimeValueReader, matches_runtime_type_predicate, surface_membership,
};
use crate::telemetry::{Telemetry, TelemetryExt as _};
use crate::types::ClosureTarget;
use fz_runtime::any_value::{
    AnyValue as RuntimeAnyValue, AnyValueRef, ValueKind, closure_addr_from_tagged, struct_schema_id,
};
use fz_runtime::exec_ctx::ExecCtx;
use fz_runtime::heap::Schema;
use fz_runtime::heap::{Heap, deep_copy_any_value_ref};
use fz_runtime::ir_runtime::{
    fz_bs_begin, fz_bs_finalize, fz_bs_write_field_ref, fz_list_head_ref, fz_list_reuse_or_cons_parts,
    fz_list_tail_ref, fz_map_empty, fz_map_get_atom_key_ref, fz_mark_published_ref_aliased, fz_matcher_map_get_ref,
    fz_struct_get_field_ref, fz_struct_get_named_field_ref,
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
        executable: Rc<BackendExecutable>,
        args: Vec<AnyValue>,
        continuations: Vec<BackendContinuation>,
    },
    Entry {
        executable: Rc<BackendExecutable>,
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

/// Runs one closed Compiler2 backend program through the shared interpreter
/// runtime without reopening planner or type-resolution work.
pub(crate) fn run_backend_main<T: Telemetry + ?Sized>(
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &T,
    output: &dyn OutputSink,
    program: &BackendProgram,
) -> Result<i64, String> {
    let atom_names = program
        .atom_names
        .iter()
        .map(|name| name.as_ref().clone())
        .collect::<Vec<_>>();
    let mut runtime = IrInterpRuntime::fresh_with_atoms(atom_names.clone());
    let module = Module {
        atom_names,
        struct_schemas: program
            .struct_schemas
            .entries()
            .map(|(name, fields)| (name.as_ref().clone(), fields.as_ref().clone()))
            .collect(),
        ..Module::default()
    };
    runtime.enqueue_backend_entry(1, backend_executable_ref(program, types, program.entry())?, Vec::new())?;
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
    let names = program
        .atom_names
        .iter()
        .map(|name| name.as_ref().clone())
        .collect::<Vec<_>>();
    let mut runtime = IrInterpRuntime::with_process(process, &names);
    let atom_names = runtime
        .process_ref(1)
        .expect("macro runtime should own pid 1")
        .node
        .atom_names();
    let module = Module {
        atom_names,
        struct_schemas: program
            .struct_schemas
            .entries()
            .map(|(name, fields)| (name.as_ref().clone(), fields.as_ref().clone()))
            .collect(),
        ..Module::default()
    };
    let result = (|| {
        runtime.enqueue_backend_entry(1, backend_executable_ref(program, types, program.entry())?, args)?;
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
    fn enqueue_backend_entry(
        &mut self,
        pid: u32,
        executable: Rc<BackendExecutable>,
        args: Vec<AnyValue>,
    ) -> Result<(), String> {
        self.enqueue_backend_executable(pid, executable, args, Vec::new())
    }

    fn enqueue_backend_executable(
        &mut self,
        pid: u32,
        executable: Rc<BackendExecutable>,
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
        executable: Rc<BackendExecutable>,
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

    pub(super) fn spawn_backend(
        &mut self,
        executable: Rc<BackendExecutable>,
        args: Vec<AnyValue>,
    ) -> Result<u32, String> {
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
            let entries = entries_for_executable(&park.executable)?;
            let entry = entries
                .get(park.entry.as_u32() as usize)
                .ok_or_else(|| format!("backend parked entry {} is out of bounds", park.entry.as_u32()))?;
            let BackendTail::Receive(receive) = &entry.tail else {
                return Err(format!("backend parked entry {} is not a receive", park.entry.as_u32()));
            };
            if let Some((target, params)) = try_match_backend_receive(
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
            )? {
                let mut forwarding = HashMap::new();
                let sender = self.cur_proc();
                let receiver = self
                    .process_ptr(*receiver_pid)
                    .ok_or_else(|| format!("unknown receiver {receiver_pid}"))?;
                let params = params
                    .into_iter()
                    .map(|(parameter, value)| {
                        let value = value.as_any_value_ref(sender)?;
                        let copied = deep_copy_any_value_ref(
                            value,
                            unsafe { &*sender_heap },
                            &mut unsafe { &mut *receiver }.heap,
                            &mut forwarding,
                        );
                        Ok((parameter, AnyValue::from_any_value_ref(copied)?))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                self.current_proc = receiver;
                let env = delivered_env(self, transport, program, entries, &park.env, target, None, &params);
                self.current_proc = sender;
                let env = env?;
                self.enqueue_backend_local_entry(
                    *receiver_pid,
                    park.executable.clone(),
                    target,
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
    let executable = frame.executable.as_ref();
    let BackendBody::Clauses { entries, .. } = &executable.body else {
        return Err(format!(
            "backend continuation executable {:?} is not clause-backed",
            frame.executable.key
        ));
    };
    Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
        executable: frame.executable.clone(),
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
        )
        .map_err(|error| {
            format!(
                "backend continuation delivery executable={:?} entry={}: {error}",
                frame.executable.key,
                frame.entry.as_u32()
            )
        })?,
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
    args: Vec<AnyValue>,
    continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
    match &executable.body {
        BackendBody::Intrinsic { signature } => {
            let value = super::intrinsic::call_intrinsic(
                runtime,
                types,
                transport,
                tel,
                program,
                module,
                signature.identity,
                &args,
            )?;
            continue_backend_value(
                runtime,
                transport,
                program,
                BackendBoundValue::Runtime(value),
                continuations,
            )
        }
        BackendBody::Extern { signature } => {
            let value = call_lowered_extern(runtime, signature, None, &args)?;
            continue_backend_value(
                runtime,
                transport,
                program,
                BackendBoundValue::Runtime(value),
                continuations,
            )
        }
        BackendBody::Clauses { clauses, entries, .. } => {
            let semantic_inputs = bind_executable_inputs(transport, types, runtime, &executable, &args)?;
            let clause_index = match &executable.abi.materialized.entry_dispatch {
                None => 0,
                Some(dispatch) => {
                    select_clause(runtime, types, transport, program, module, dispatch, &semantic_inputs)?.ok_or_else(
                        || {
                            format!(
                                "function_clause: no backend entry clause matched for executable {:?}",
                                executable.key
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
                    "backend executable {:?} expected {} semantic input(s), got {}",
                    executable.key,
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
            eval_steps(
                runtime,
                types,
                tel,
                transport,
                program,
                module,
                &executable,
                &clause.projections,
                &mut env,
            )
            .map_err(|error| {
                format!(
                    "backend executable {:?} function {} clause {} failed before entry {}: {error}",
                    executable.key,
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
                &executable,
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
    args: &[Option<BackendBoundValue>],
) -> Result<Option<usize>, String> {
    let mut inputs = vec![interp_nil_value(); args.len()];
    for ordinal in dispatch.required_input_ordinals() {
        let value = args
            .get(ordinal)
            .and_then(Option::as_ref)
            .ok_or_else(|| format!("backend clause dispatch required omitted semantic input {}", ordinal))?;
        inputs[ordinal] = materialize_backend_value(transport, runtime.cur_proc(), value)?;
    }
    let prepared = prepared_dispatch_keys(runtime, module, dispatch.plan(), &inputs)?;
    let selected = select_dispatch_body(
        runtime,
        types,
        transport,
        program,
        module,
        dispatch.plan(),
        &inputs,
        &prepared,
    )?;
    Ok(selected.and_then(|body_id| dispatch.clause_index(body_id)))
}

/// Materialise a plan's prepared keys so entry dispatch can read them.
///
/// A map pattern keyed by a binary — `%{"name" => n}` — is decided through a
/// PREPARED key: `dispatch_const_key_value` finds the key's index in
/// `plan.prepared_keys` and then reads the materialised value out of the
/// prepared values. The receive path supplies those from its bindings, and native
/// entry dispatch materializes them itself, but interpreted entry dispatch used
/// to pass no prepared values here. The lookup
/// then found nothing, the region reported "key absent", and the clause was
/// skipped: `lookup(%{"name" => "ada"})` answered `:anonymous` on `interp`
/// while `run` and Elixir both answered `{:named, "ada"}`.
///
/// Only binary keys need this. Ints, floats, atoms, booleans and nil are
/// decided from the constant directly and never consult prepared values.
fn prepared_dispatch_keys(
    runtime: &mut IrInterpRuntime,
    module: &Module,
    plan: &crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
    inputs: &[AnyValue],
) -> Result<DispatchValues, String> {
    use crate::ground_value::DispatchShape;
    let mut prepared = Vec::new();
    for key in &plan.prepared_keys {
        let value = if let Some(DispatchShape::Utf8Binary(bytes)) = key.as_dispatch_shape() {
            let ref_word = fz_runtime::ir_runtime::fz_alloc_bitstring_const(
                runtime.cur_proc(),
                bytes.as_ptr() as u64,
                bytes.len() as u64,
                (bytes.len() * 8) as u64,
            );
            interp_value_from_ref_word(ref_word, "prepared dispatch key")?
        } else {
            super::dispatch_exec::dispatch_const_to_value(runtime.cur_proc(), module, key)
                .ok_or_else(|| format!("cannot materialize prepared dispatch key {key:?}"))?
        };
        prepared.push(value);
    }
    Ok(DispatchValues {
        pinned: plan
            .pinned
            .iter()
            .map(|pin| {
                pin.input
                    .and_then(|input| inputs.get(input as usize).copied())
                    .ok_or_else(|| "entry dispatch pin has no argument operand".to_string())
            })
            .collect::<Result<Vec<_>, _>>()?,
        prepared,
    })
}

fn select_dispatch_body(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    program: &BackendProgram,
    module: &Module,
    plan: &crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
    args: &[AnyValue],
    pinned: &DispatchValues,
) -> Result<Option<u32>, String> {
    Ok(
        select_dispatch_match(runtime, types, transport, program, module, plan, args, pinned)?
            .map(|matched| plan.outcome(matched.outcome).expect("winning dispatch outcome").body_id),
    )
}

/// The CONSTRUCTION a runtime code word denotes, in the terms the type lattice
/// uses: the function it runs, and the projected capture types it closed over.
///
/// A callable value the backend built through a construction wrapper carries
/// that wrapper's synthetic identity, which is this backend's own numbering;
/// the wrapper owns the ordered source capture annotations. Every other callable
/// value carries its function's own id directly and closes over nothing a test
/// can name, so it answers as a construction over no captures.
fn backend_callable_identity(
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

fn select_dispatch_match(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    program: &BackendProgram,
    module: &Module,
    plan: &crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
    args: &[AnyValue],
    pinned: &DispatchValues,
) -> Result<Option<DispatchMatch>, String> {
    let mut state = DispatchExecState::default();
    let types = &*types;
    let callables = |code: u64| backend_callable_identity(types, transport, program, code);
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
            let list_tail = |value: RuntimeAnyValue| {
                let tail = fz_list_tail_ref(value.ref_word().raw_word());
                interp_value_from_ref_word(tail, "list tail")
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
                list_tail: &list_tail,
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
    executable: &Rc<BackendExecutable>,
    entries: &[BackendEntry],
    entry_id: crate::compiler2::ControlEntryId,
    mut env: HashMap<ValueId, BackendBoundValue>,
    continuations: Vec<BackendContinuation>,
) -> Result<BackendEvalTransition, String> {
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
                && let Some(value) = env.get(&arg.value)
            {
                publish_backend_capture(runtime.cur_proc(), value)?;
            }
        }
    }
    let transition = match &entry.tail {
        BackendTail::Value { value, dest } => {
            // Zero-lane return contracts need no environment read. This is ABI
            // width, not semantic absence; decoding retains tuple/callable shape.
            let returns_no_lanes =
                matches!(dest, ControlDestination::Return) && executable.abi.return_layout.layout.publishes_no_lanes();
            let result = if returns_no_lanes && !env.contains_key(value) {
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
                env_get_value(&env, *value)?
            };
            match dest {
                ControlDestination::Return => {
                    continue_backend_value(runtime, transport, program, result, continuations)
                }
                ControlDestination::Deliver(target) => Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                    executable: executable.clone(),
                    entry: *target,
                    env: delivered_env(runtime, transport, program, entries, &env, *target, Some(result), &[])?,
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
                        &DispatchValues::default(),
                    )?
                    .ok_or_else(|| {
                        format!(
                            "backend dispatch callsite in executable {:?} missed an exhaustive dispatch",
                            executable.key
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
                        "backend direct callsite in executable {:?} materialized as an indirect closure edge; Indirect is closure-call-only",
                        executable.key
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
                executable,
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
            let callee_value = env.get(callee).cloned();
            let missing_direct_callee = callee_value.is_none();
            let (fn_id, capture_shape, capture_lanes) = match callee_value {
                Some(BackendBoundValue::Transport { shape, lanes })
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
                Some(other) => {
                    let materialized = materialize_backend_value(transport, runtime.cur_proc(), &other)?;
                    let (fn_id, captures) = match materialized {
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
                    (fn_id, None, captures)
                }
                None => {
                    let Some(target) = target else {
                        return Err(format!(
                            "closure call executable={:?} function={} callsite={} callee_value={}: backend value {} is unbound",
                            executable.key,
                            executable.key.activation.function.as_u32(),
                            callsite.as_u32(),
                            callee.as_u32(),
                            callee.as_u32()
                        ));
                    };
                    (FnId(target.activation.function.as_u32()), None, Vec::new())
                }
            };
            let wrapper = construction_wrapper_for_fn(program, fn_id);
            let executable_target = if let Some(wrapper) = wrapper {
                let args = args
                    .iter()
                    .map(|arg| env_get(transport, runtime.cur_proc(), &env, arg.value))
                    .collect::<Result<Vec<_>, _>>()?;
                &select_construction_member(runtime, types, transport, program, module, wrapper, &args)?.target
            } else if let Some(target) = target {
                target
            } else {
                return Err(format!(
                    "backend closure call executable={:?} function={} callsite={} has no construction wrapper or direct target",
                    executable.key,
                    executable.key.activation.function.as_u32(),
                    callsite.as_u32()
                ));
            };
            let executable_target = backend_executable_ref(program, types, executable_target)?;
            let callee_executable = executable_target.as_ref();
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
                    .abi
                    .semantic_inputs
                    .iter()
                    .any(|input| input.semantic_index < capture_inputs_end && !input.layout.publishes_no_lanes())
            {
                return Err(format!(
                    "closure call executable={:?} function={} callsite={} omitted callee value {} but target {:?} needs semantic inputs",
                    executable.key,
                    executable.key.activation.function.as_u32(),
                    callsite.as_u32(),
                    callee.as_u32(),
                    executable_target.key
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
                    program,
                    target: callee_executable,
                    wrapper,
                    member,
                }
                .encode(&capture_lanes, args, |arg| env_get_value(&env, arg.value))?
            } else {
                let captures = match capture_shape {
                    Some(shape) => decode_callable_captures(transport, shape, &capture_lanes)?,
                    None => capture_lanes.into_iter().map(BackendBoundValue::Runtime).collect(),
                };
                let mut lanes = Vec::new();
                for binding in callee_executable
                    .abi
                    .semantic_inputs
                    .iter()
                    .filter(|binding| binding.semantic_index < capture_inputs_end)
                {
                    if binding.layout.publishes_no_lanes() {
                        continue;
                    }
                    let capture = captures
                        .get(binding.semantic_index)
                        .ok_or_else(|| format!("direct closure call is missing capture {}", binding.semantic_index))?;
                    encode_runtime_input_binding(transport, program, runtime.cur_proc(), capture, binding, &mut lanes)?;
                }
                lanes.extend(encode_call_args(
                    transport,
                    program,
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
                    continuations.push(BackendContinuation {
                        executable: executable.clone(),
                        entry: *target,
                        env: capture_backend_continuation_env(transport, entries, *target, &env)?,
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
                executable: executable.clone(),
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
            let (target, params) = match select_dispatch_match(
                runtime,
                types,
                transport,
                program,
                module,
                &dispatch.plan,
                &input_values,
                &pinned_values,
            )? {
                Some(mut matched) => {
                    let edge = dispatch.outcome(matched.outcome);
                    let params = edge
                        .arguments
                        .iter()
                        .map(|argument| {
                            let value = resolve_dispatch_subject(
                                runtime.cur_proc(),
                                module,
                                &dispatch.plan,
                                argument.subject,
                                &input_values,
                                &pinned_values,
                                &mut matched.state,
                            )
                            .ok_or_else(|| format!("winning outcome lacks subject {:?}", argument.subject))?;
                            Ok((argument.parameter, value))
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    (edge.target, params)
                }
                None => (dispatch.miss_entry, Vec::new()),
            };
            Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                executable: executable.clone(),
                entry: target,
                env: delivered_env(runtime, transport, program, entries, &env, target, None, &params)?,
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
                    AnyValue::from_any_value_ref(proc.mailbox[mb_idx])?
                };
                if let Some((target, params)) = try_match_backend_receive(
                    runtime, types, transport, program, module, outcomes, dispatch, msg, bindings, &env,
                )? {
                    hit = Some((mb_idx, target, params));
                    break;
                }
            }
            if let Some((mb_idx, target, params)) = hit {
                unsafe { &mut *runtime.cur_proc() }.mailbox.remove(mb_idx);
                return Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                    executable: executable.clone(),
                    entry: target,
                    env: delivered_env(runtime, transport, program, entries, &env, target, None, &params)?,
                    continuations,
                }));
            }
            if let Some(after) = after
                && env_get(transport, runtime.cur_proc(), &env, after.timeout)?.as_i64() == Some(0)
            {
                return Ok(BackendEvalTransition::Next(BackendEvalState::Entry {
                    executable: executable.clone(),
                    entry: after.entry,
                    env: delivered_env(runtime, transport, program, entries, &env, after.entry, None, &[])?,
                    continuations,
                }));
            }
            runtime.backend_parked.insert(
                unsafe { &*runtime.cur_proc() }.pid,
                BackendParkRecord {
                    executable: executable.clone(),
                    entry: entry_id,
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
            "backend executable {:?} function {} entry {} tail failed: {error}",
            executable.key,
            executable.key.activation.function.as_u32(),
            entry_id.as_u32()
        )
    })
}

type OutcomeValues = (crate::compiler2::ControlEntryId, Vec<(ValueId, AnyValue)>);

fn try_match_backend_receive(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    program: &BackendProgram,
    module: &Module,
    outcomes: &[crate::compiler2::OutcomeEdge],
    dispatch: &crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
    msg: AnyValue,
    bindings: &crate::compiler2::DispatchBindings,
    env: &HashMap<ValueId, BackendBoundValue>,
) -> Result<Option<OutcomeValues>, String> {
    let pinned = local_dispatch_pinned(transport, runtime.cur_proc(), env, bindings, dispatch)?;
    let Some(mut matched) =
        select_dispatch_match(runtime, types, transport, program, module, dispatch, &[msg], &pinned)?
    else {
        return Ok(None);
    };
    let edge = outcomes
        .iter()
        .find(|edge| edge.outcome == matched.outcome)
        .expect("receive winning edge");
    let mut params = Vec::with_capacity(edge.arguments.len());
    for argument in &edge.arguments {
        let value = resolve_dispatch_subject(
            runtime.cur_proc(),
            module,
            dispatch,
            argument.subject,
            &[msg],
            &pinned,
            &mut matched.state,
        )
        .ok_or_else(|| format!("receive outcome lacks subject {:?}", argument.subject))?;
        params.push((argument.parameter, value));
    }
    Ok(Some((edge.target, params)))
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
                quoted_span,
            } => {
                let mut map_bits = if entries.is_empty() || quoted_span.is_some() {
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
                if let Some(span) = quoted_span {
                    let mut span_bits = fz_map_empty(runtime.cur_proc());
                    for (key, value) in crate::compiler2::quoted_span_entries(*span) {
                        span_bits = interp_map_put(
                            runtime.cur_proc(),
                            span_bits,
                            AnyValue::Atom(runtime.node.intern_atom(key)),
                            AnyValue::Int(value),
                            "quoted span metadata",
                        )?;
                    }
                    map_bits = interp_map_put(
                        runtime.cur_proc(),
                        map_bits,
                        AnyValue::Atom(runtime.node.intern_atom(crate::compiler2::META_SPAN_KEY)),
                        interp_value_from_ref_word(span_bits, "quoted span metadata")?,
                        "quoted AST metadata",
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
                    if let Some(value) = env.get(capture) {
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
    permission: crate::fz_ir::ListRewritePermission,
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
            u64::from(permission == crate::fz_ir::ListRewritePermission::Rewrite),
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
    params: &[(ValueId, AnyValue)],
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
    for (param, value) in params.iter().copied() {
        assert!(
            entry.params.contains(&param),
            "a delivered parameter belongs to its target"
        );
        next.insert(param, BackendBoundValue::Runtime(value));
    }
    match &entry.origin {
        crate::compiler2::BackendEntryOrigin::Clause
        | crate::compiler2::BackendEntryOrigin::Branch
        | crate::compiler2::BackendEntryOrigin::ReceiveOutcome => {}
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
                next.insert(*value, bound);
            }
        }
    }
    for capture in &entry.captures {
        if transport
            .interners()
            .shape(capture.layout.structural)
            .is_semantically_absent()
            && matches!(capture.layout.carrier, TransportCarrier::Absent)
        {
            continue;
        }
        next.insert(capture.value, env_get_value(env, capture.value)?);
    }
    for capture in &entry.physical_captures {
        next.insert(*capture, env_get_value(env, *capture)?);
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
    callee: &CallTarget<ExecutableKey>,
    args: &[crate::compiler2::BackendCallArg],
    extern_marshals: Option<&[crate::fz_ir::ExternTy]>,
    env: HashMap<ValueId, BackendBoundValue>,
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
                tel,
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
    }
}

fn eval_direct_call<T: Telemetry + ?Sized>(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    transport: &TransportStore,
    tel: &T,
    program: &BackendProgram,
    module: &Module,
    callee: Rc<BackendExecutable>,
    args: &[crate::compiler2::BackendCallArg],
    extern_marshals: Option<&[crate::fz_ir::ExternTy]>,
    env: HashMap<ValueId, BackendBoundValue>,
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
                env: capture_backend_continuation_env(transport, entries_for_executable(caller)?, target, &env)?,
            });
            continuations
        }
    };
    match &executable.body {
        BackendBody::Intrinsic { signature } => super::intrinsic::call_intrinsic(
            runtime,
            types,
            transport,
            tel,
            program,
            module,
            signature.identity,
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
        BackendBody::Extern { signature } => call_lowered_extern(runtime, signature, extern_marshals, &call_args)
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
    transport: &TransportStore,
    entries: &[BackendEntry],
    target: crate::compiler2::ControlEntryId,
    env: &HashMap<ValueId, BackendBoundValue>,
) -> Result<HashMap<ValueId, BackendBoundValue>, String> {
    let entry = entries
        .get(target.as_u32() as usize)
        .ok_or_else(|| format!("backend entry {} is out of bounds", target.as_u32()))?;
    let mut captured = HashMap::with_capacity(entry.captures.len() + entry.physical_captures.len());
    for capture in &entry.captures {
        if transport
            .interners()
            .shape(capture.layout.structural)
            .is_semantically_absent()
            && matches!(capture.layout.carrier, TransportCarrier::Absent)
        {
            continue;
        }
        let value = env_get_value(env, capture.value).map_err(|error| {
            format!(
                "backend continuation capture value {} is unavailable: {error}",
                capture.value.as_u32(),
            )
        })?;
        captured.insert(capture.value, value);
    }
    for capture in &entry.physical_captures {
        captured.insert(*capture, env_get_value(env, *capture)?);
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

fn entries_for_executable(executable: &Rc<BackendExecutable>) -> Result<&[BackendEntry], String> {
    let BackendBody::Clauses { entries, .. } = &executable.body else {
        return Err(format!("backend executable {:?} is not clause-backed", executable.key));
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
) -> Result<DispatchValues, String> {
    assert_eq!(bindings.pinned.len(), plan.pinned.len());
    assert_eq!(bindings.prepared.len(), plan.prepared_keys.len());
    Ok(DispatchValues {
        pinned: env_values(transport, proc, env, &bindings.pinned)?,
        prepared: env_values(transport, proc, env, &bindings.prepared)?,
    })
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
    if callable.capture_layouts.len() != captures.len() {
        return Err(format!(
            "backend direct callable producer {} expected {} capture shape(s), got {} capture value(s)",
            value.as_u32(),
            callable.capture_layouts.len(),
            captures.len()
        ));
    }
    let mut lanes = Vec::new();
    for (capture, layout) in captures.iter().copied().zip(callable.capture_layouts.iter().copied()) {
        if transport.interners().layout_width(layout) != 0 {
            let bound = env_get_value(env, capture)?;
            encode_transport_layout(transport, program, proc, &bound, layout, &mut lanes)?;
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
    Ok(BackendBoundValue::Transport { shape, lanes })
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
        Some(selection) => select_dispatch_body(
            runtime,
            types,
            transport,
            program,
            module,
            selection,
            args,
            &DispatchValues::default(),
        )?
        .ok_or_else(|| format!("backend callable construction {:?} matched no member", wrapper.identity))?
            as usize,
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
) -> Result<(Rc<BackendExecutable>, Vec<AnyValue>), String> {
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
    .encode(captures, args, |arg| Ok(BackendBoundValue::Runtime(*arg)))?;
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
        let mut lanes = Vec::new();
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
                Some(value) => BackendBoundValue::Runtime(value),
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
        encode_runtime_input_binding(transport, program, runtime.cur_proc(), &value, binding, &mut lanes).map_err(
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
    layout: &crate::compiler2::BackendValueLayout,
) -> Result<Option<BackendBoundValue>, String> {
    if transport.interners().shape(layout.structural).is_semantically_absent()
        && matches!(layout.carrier, TransportCarrier::Absent)
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
    layout: &crate::compiler2::BackendValueLayout,
) -> Result<BackendBoundValue, String> {
    if matches!(layout.carrier, TransportCarrier::ValueRef(_)) {
        return Ok(BackendBoundValue::Runtime(materialize_backend_value(
            transport, proc, value,
        )?));
    }
    let mut lanes = Vec::new();
    encode_runtime_value(transport, program, proc, value, layout.structural, &mut lanes)?;
    let mut lane_index = 0;
    let decoded = decode_transport_layout(
        transport,
        &lanes,
        TransportLayout::structural(layout.structural),
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
                Some(_) => {
                    let extracted = direct_callable_capture_lanes(transport, program, proc, value, callable)?;
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

fn encode_transport_layout(
    transport: &TransportStore,
    program: &BackendProgram,
    proc: *mut Process,
    value: &BackendBoundValue,
    layout: TransportLayout,
    lanes: &mut Vec<AnyValue>,
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
        ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Callable(_) => {
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
    lanes: &mut Vec<AnyValue>,
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
        ShapeDescr::Callable(_) | ShapeDescr::Tuple(_) => {
            let width = transport.interners().shape_width(shape);
            let lanes = take_runtime_lanes(args, lane_index, width)?;
            decode_backend_value_from_lanes(transport, shape, lanes)
        }
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
        .map(|(field_layout, span)| {
            let field_lanes = lanes
                .get(span)
                .ok_or_else(|| format!("backend tuple transport shape {shape:?} has an invalid lane span"))?
                .to_vec();
            if field_layout.carrier.is_value_ref() {
                field_lanes
                    .first()
                    .copied()
                    .map(BackendBoundValue::Runtime)
                    .ok_or_else(|| format!("backend ValueRef tuple field in {shape:?} has no runtime lane"))
            } else {
                decode_backend_value_from_lanes(transport, field_layout.structural, field_lanes)
            }
        })
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
        && matches!(transport.interners().shape(*value_shape), ShapeDescr::Tuple(source) if source.len() == fields.len())
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

fn decode_callable_captures(
    transport: &TransportStore,
    shape: ShapeId,
    lanes: &[AnyValue],
) -> Result<Vec<BackendBoundValue>, String> {
    let ShapeDescr::Callable(callable) = transport.interners().shape(shape) else {
        return Err("capture projection requires a callable source layout".into());
    };
    let mut cursor = 0;
    let values = transport
        .interners()
        .callable(*callable)
        .capture_layouts
        .iter()
        .map(|layout| decode_transport_layout(transport, lanes, *layout, &mut cursor))
        .collect::<Result<Vec<_>, _>>()?;
    if cursor != lanes.len() {
        return Err("direct callable source layout does not consume its lanes".into());
    }
    Ok(values)
}

fn direct_callable_capture_lanes(
    transport: &TransportStore,
    program: &BackendProgram,
    proc: *mut Process,
    value: &BackendBoundValue,
    callable: &crate::compiler2::transport::CallableDescr,
) -> Result<Vec<AnyValue>, String> {
    let function = callable.function.expect("direct callable names its source function");
    let captures = match value {
        BackendBoundValue::Transport { shape, lanes }
            if matches!(transport.interners().shape(*shape), ShapeDescr::Callable(_)) =>
        {
            let ShapeDescr::Callable(callable) = transport.interners().shape(*shape) else {
                unreachable!();
            };
            let source = transport.interners().callable(*callable);
            if source.function != Some(function) {
                return Err(format!(
                    "backend direct-callable transport expected function {}, got {:?}",
                    function.as_u32(),
                    source.function
                ));
            }
            decode_callable_captures(transport, *shape, lanes)?
        }
        other => {
            let materialized = materialize_backend_value(transport, proc, other)?;
            let (fn_id, words) = match materialized {
                AnyValue::FnRef(fn_id, _, _) => (fn_id, Vec::new()),
                other => unpack_closure(other.value(proc)?)?,
            };
            // The word is a CONSTRUCTION, not a function: a wrapper's word
            // is this backend's own numbering, so the program translates it
            // back before the check (fz-kdt.127).
            if backend_callable_function(transport, program, fn_id) != Some(function) {
                return Err(format!(
                    "backend direct-callable transport expected function {}, got construction word {}",
                    function.as_u32(),
                    fn_id.0
                ));
            }
            words.into_iter().map(BackendBoundValue::Runtime).collect()
        }
    };
    if captures.len() != callable.capture_layouts.len() {
        return Err(format!(
            "backend direct-callable transport expected {} lexical capture(s) for function {}, got {}",
            callable.capture_layouts.len(),
            function.as_u32(),
            captures.len()
        ));
    }
    let mut lanes = Vec::new();
    for (capture, layout) in captures.iter().zip(callable.capture_layouts.iter().copied()) {
        encode_transport_layout(transport, program, proc, capture, layout, &mut lanes)?;
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
    program: &BackendProgram,
    proc: *mut Process,
    executable: &BackendExecutable,
    env: &HashMap<ValueId, BackendBoundValue>,
    value: ValueId,
    items: &[crate::fz_ir::OwnershipUse<ValueId>],
) -> Result<BackendBoundValue, String> {
    for item in items {
        if item.mode == crate::fz_ir::OwnershipMode::Share
            && let Some(value) = env.get(&item.value)
        {
            publish_backend_capture(proc, value)?;
        }
    }
    if let Some(layout) = executable.abi.value_layouts.get(&value)
        && !matches!(layout.carrier, TransportCarrier::ValueRef(_))
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
        for (item, field_layout) in items.iter().copied().zip(fields.iter().copied()) {
            if transport.interners().layout_width(field_layout) != 0 {
                let bound = env_get_value(env, item.value)?;
                encode_transport_layout(transport, program, proc, &bound, field_layout, &mut lanes)?;
            }
        }
        return Ok(BackendBoundValue::Transport {
            shape: layout.structural,
            lanes,
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
    Ok(AnyValue::Ref(
        AnyValueRef::from_heap_object(ValueKind::STRUCT, p).expect("backend tuple ref"),
    ))
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
    Ok(AnyValue::Ref(
        AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure_addr).expect("backend closure ref"),
    ))
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
    name: &fz_runtime::module_name::ModuleName,
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
        .register_schema(Schema::named_struct(name.clone(), fields));
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
    fn parked_receive_copies_only_winning_subjects_into_receiver_heap() {
        use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
        let mut compiler = Compiler2::new(crate::telemetry::ConfiguredTelemetry::new());
        compiler.submit_code(CodeSubmission {
            name: Some("parked_projection.fz".into()),
            text: "fn main() do\n receive do\n [_, h | t] -> [h | t]\n end\nend\n".into(),
        });
        let root = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".into(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        compiler.run_root_interp(root).expect("compile and park receive");
        let program = compiler.retained_backend_program(root);
        let executable = backend_executable_ref(&program, compiler.world().types(), program.entry()).unwrap();
        let entries = entries_for_executable(&executable).unwrap();
        let owner = entries
            .iter()
            .position(|entry| matches!(entry.tail, BackendTail::Receive(_)))
            .unwrap();
        let source = entries
            .iter()
            .flat_map(|entry| &entry.steps)
            .find_map(|step| match step {
                ProgramStep::List {
                    retention: Some(retention),
                    ..
                } => Some(retention.source),
                _ => None,
            })
            .expect("physical exact source operand");
        let names = program
            .atom_names
            .iter()
            .map(|name| name.as_ref().clone())
            .collect::<Vec<_>>();
        let module = Module {
            atom_names: names.clone(),
            ..Module::default()
        };
        let mut runtime = IrInterpRuntime::fresh_with_atoms(names);
        let sender = runtime.process_ptr(1).unwrap();
        runtime.current_proc = sender;
        let receiver_pid = runtime.spawn_backend(Rc::clone(&executable), Vec::new()).unwrap();
        runtime.backend_parked.insert(
            receiver_pid,
            BackendParkRecord {
                executable,
                entry: crate::compiler2::ControlEntryId::from_u32(owner as u32),
                env: HashMap::new(),
                continuations: Vec::new(),
            },
        );
        let mut ignored = AnyValue::EmptyList;
        for value in 0..20 {
            ignored = interp_list_cons(sender, AnyValue::Int(value), ignored, "ignored").unwrap();
        }
        let tail = interp_list_cons(sender, AnyValue::Int(2), AnyValue::EmptyList, "tail").unwrap();
        let retained = interp_list_cons(sender, AnyValue::Int(1), tail, "source").unwrap();
        let message = interp_list_cons(sender, ignored, retained, "message").unwrap();
        runtime
            .send_opaque(
                compiler.world_mut().types_mut(),
                &TransportStore::new(),
                &crate::telemetry::ConfiguredTelemetry::new(),
                &program,
                &module,
                &receiver_pid,
                message,
            )
            .unwrap();
        let BackendResumeEntry::Entry { env, .. } = runtime.take_backend_resume(receiver_pid).expect("winning wake")
        else {
            panic!("direct outcome entry")
        };
        let receiver = runtime.process_ptr(receiver_pid).unwrap();
        let copied = env_get(&TransportStore::new(), receiver, &env, source)
            .unwrap()
            .as_any_value_ref(receiver)
            .unwrap();
        let address = copied.heap_addr(ValueKind::LIST).expect("retained cell");
        assert!(unsafe { &*receiver }.heap.contains_heap_addr(address));
        assert!(!unsafe { &*sender }.heap.contains_heap_addr(address));
        assert_eq!(
            unsafe { &*receiver }.heap.alloc_stats_snapshot().list_cons.allocs,
            2,
            "only the two-cell winning source crosses heaps; ignored list and outer cell do not"
        );
        let mut roots = [copied];
        unsafe { &mut *receiver }
            .heap
            .gc_with_any_value_ref_roots(&mut std::ptr::null_mut(), &mut roots);
        let source = roots[0].raw_word();
        let retained = fz_runtime::ir_runtime::fz_list_reuse_or_cons_ref(
            receiver,
            source,
            fz_list_head_ref(source),
            fz_list_tail_ref(source),
            0,
        );
        assert_eq!(retained, source, "receiver GC preserves the exact retention operand");
    }

    #[test]
    fn generic_callable_input_retains_structure_without_demanding_a_box() {
        let mut transport = TransportStore::new();
        let callable = transport
            .interners_mut()
            .intern_callable(crate::compiler2::transport::CallableDescr {
                function: None,
                arity: 0,
                capture_layouts: Box::default(),
            });
        let shape = transport.interners_mut().intern_shape(ShapeDescr::Callable(callable));
        let value = decode_transport_layout(&transport, &[], TransportLayout::structural(shape), &mut 0)
            .expect("an unused structural callable input requires no runtime allocation");
        assert!(
            matches!(value, BackendBoundValue::Transport { shape: actual, lanes } if actual == shape && lanes.is_empty())
        );
    }

    #[test]
    fn zero_lane_inputs_preserve_tuple_structure_without_inventing_absence() {
        let mut world = crate::compiler2::World::new();
        let mut transport = TransportStore::new();
        let nothing = transport.interners_mut().intern_shape(ShapeDescr::Nothing);
        let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "zero_lane", 4);
        let zero_capture = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "zero_capture", 0);
        let callable = transport
            .interners_mut()
            .intern_callable(crate::compiler2::transport::CallableDescr {
                function: Some(zero_capture),
                arity: 0,
                capture_layouts: Box::default(),
            });
        let callable = transport.interners_mut().intern_shape(ShapeDescr::Callable(callable));
        let empty_tuple = tuple_shape(&mut transport, &[]);
        let tuple = tuple_shape(&mut transport, &[empty_tuple, callable]);
        let ty = world.types_mut().any();
        let key = ExecutableKey {
            activation: crate::compiler2::ActivationKey::from_inputs(
                crate::compiler2::RootId::for_test(0),
                function,
                &[ty; 4],
                world.types_mut(),
            ),
            need: crate::compiler2::ExecutableNeed::Value,
        };
        let mut executable = BackendExecutable::for_test(key, ty, nothing);
        let empty_layout = executable.abi.return_layout.layout.clone();
        Rc::make_mut(&mut executable.abi).semantic_inputs = [nothing, callable, tuple]
            .into_iter()
            .enumerate()
            .map(|(semantic_index, structural)| {
                let mut layout = empty_layout.clone();
                layout.structural = structural;
                crate::compiler2::BackendSemanticInputLayout { semantic_index, layout }
            })
            .collect();
        let mut runtime = IrInterpRuntime::fresh_with_atoms(Vec::new());
        let bound = bind_executable_inputs(&transport, world.types(), &mut runtime, &executable, &[])
            .expect("zero physical lanes");
        assert!(
            matches!(&bound[0], Some(BackendBoundValue::Absent)),
            "a published Nothing layout carries explicit absence"
        );
        assert!(
            matches!(&bound[1], Some(BackendBoundValue::Transport { shape, lanes }) if *shape == callable && lanes.is_empty()),
            "a published lane-free callable retains its structural identity"
        );
        assert!(
            matches!(&bound[2], Some(BackendBoundValue::Transport { shape, lanes }) if *shape == tuple && lanes.is_empty()),
            "a recursive zero-lane tuple is a concrete structural value"
        );
        assert!(
            bound[3].is_none(),
            "only an unpublished semantic ordinal remains missing"
        );
        for (index, input) in executable.abi.semantic_inputs.iter().enumerate() {
            assert!(input.layout.publishes_no_lanes());
            assert_eq!(
                transport
                    .interners()
                    .shape(input.layout.structural)
                    .is_semantically_absent(),
                index == 0
            );
            let result = bind_delivered_value(
                &transport,
                &empty_backend_program(),
                std::ptr::null_mut(),
                crate::compiler2::ControlEntryId::from_u32(0),
                None,
                &input.layout,
            );
            assert_eq!(
                result.is_ok(),
                index == 0,
                "only Nothing/Absent permits a missing delivery"
            );
            let mut lane_index = 0;
            let decoded = decode_transport_layout(
                &transport,
                &[],
                TransportLayout::structural(input.layout.structural),
                &mut lane_index,
            )
            .unwrap();
            assert_eq!(
                matches!(decoded, BackendBoundValue::Absent),
                index == 0,
                "zero lanes do not imply semantic absence"
            );
            assert_eq!(
                encode_for_layout(
                    &transport,
                    std::ptr::null_mut(),
                    &BackendBoundValue::Absent,
                    input.layout.structural
                )
                .is_ok(),
                index == 0,
                "an absent value cannot satisfy a zero-lane tuple or callable contract"
            );
        }
        runtime.current_proc = runtime.process_ptr(1).unwrap();
        for structural in [callable, tuple] {
            Rc::make_mut(&mut executable.abi).return_layout.layout.structural = structural;
            let entries = [BackendEntry {
                span: crate::source::Span::DUMMY,
                origin: crate::compiler2::BackendEntryOrigin::Branch,
                params: Vec::new(),
                captures: Vec::new(),
                physical_captures: Vec::new(),
                physical_params: Vec::new(),
                steps: Vec::new(),
                tail: BackendTail::Value {
                    value: ValueId::from_u32(99),
                    dest: ControlDestination::Return,
                },
            }];
            let result = step_eval_entry(
                &mut runtime,
                world.types_mut(),
                &transport,
                &crate::telemetry::ConfiguredTelemetry::new(),
                &empty_backend_program(),
                &Module::default(),
                &Rc::new(executable.clone()),
                &entries,
                crate::compiler2::ControlEntryId::from_u32(0),
                HashMap::new(),
                Vec::new(),
            );
            assert!(
                matches!(result, Ok(BackendEvalTransition::Done(_))),
                "a zero-lane return decodes its concrete contract without reading the missing value"
            );
        }
    }

    #[test]
    fn only_a_missing_callee_selects_the_exact_direct_target() {
        let mut world = crate::compiler2::World::new();
        let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "exact_target", 0);
        let key = ExecutableKey {
            activation: crate::compiler2::ActivationKey::from_inputs(
                crate::compiler2::RootId::for_test(0),
                function,
                &[],
                world.types_mut(),
            ),
            need: crate::compiler2::ExecutableNeed::Value,
        };
        let nothing = world.intern_shape(ShapeDescr::Nothing);
        let ty = world.types_mut().int();
        let executable = Rc::new(BackendExecutable::for_test(key.clone(), ty, nothing));
        let mut program = BackendProgram::empty(key.clone());
        program.add_executable(executable.clone(), world.types());
        let callee = ValueId::from_u32(0);
        let entries = [BackendEntry {
            span: crate::source::Span::DUMMY,
            origin: crate::compiler2::BackendEntryOrigin::Branch,
            params: Vec::new(),
            captures: Vec::new(),
            physical_captures: Vec::new(),
            physical_params: Vec::new(),
            steps: Vec::new(),
            tail: BackendTail::ClosureCall {
                value: ValueId::from_u32(1),
                callsite: crate::compiler2::CallSiteId::from_u32(0),
                callee,
                target: Some(key.clone()),
                args: Vec::new(),
                dest: ControlDestination::Return,
                return_flow: None,
            },
        }];
        let mut runtime = IrInterpRuntime::fresh_with_atoms(Vec::new());
        runtime.current_proc = runtime.process_ptr(1).unwrap();
        let transport = TransportStore::new();
        let tel = crate::telemetry::ConfiguredTelemetry::new();
        let mut invoke = |env| {
            step_eval_entry(
                &mut runtime,
                world.types_mut(),
                &transport,
                &tel,
                &program,
                &Module::default(),
                &executable,
                &entries,
                crate::compiler2::ControlEntryId::from_u32(0),
                env,
                Vec::new(),
            )
        };
        assert!(
            matches!(invoke(HashMap::new()), Ok(BackendEvalTransition::Next(BackendEvalState::Executable { executable: target, .. })) if target.key == key)
        );
        let explicit_absence = invoke(HashMap::from([(callee, BackendBoundValue::Absent)]));
        assert!(
            matches!(explicit_absence, Err(error) if error.contains("absent and cannot be materialized")),
            "an explicit absent binding cannot select the missing-callee fallback"
        );
    }

    #[test]
    fn entry_dispatch_does_not_materialize_unneeded_structural_inputs() {
        use crate::dispatch_matrix::pattern::{PatternRow, SourcePatternRows, pattern_dispatch_from_source};
        let mut world = crate::compiler2::World::new();
        let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "ignore_tuple", 1);
        let ty = world.types_mut().any();
        let key = ExecutableKey {
            activation: crate::compiler2::ActivationKey::from_inputs(
                crate::compiler2::RootId::for_test(0),
                function,
                &[ty],
                world.types_mut(),
            ),
            need: crate::compiler2::ExecutableNeed::Value,
        };
        let mut transport = TransportStore::new();
        let nothing = transport.interners_mut().intern_shape(ShapeDescr::Nothing);
        let tuple = tuple_shape(&mut transport, &[nothing]);
        let mut executable = BackendExecutable::for_test(key, ty, nothing);
        let abi = Rc::make_mut(&mut executable.abi);
        let mut layout = abi.return_layout.layout.clone();
        layout.structural = tuple;
        abi.semantic_inputs = Box::new([crate::compiler2::BackendSemanticInputLayout {
            semantic_index: 0,
            layout,
        }]);
        let dispatch = ExecutableDispatch::new(
            pattern_dispatch_from_source(SourcePatternRows {
                input_count: 1,
                rows: vec![PatternRow {
                    patterns: vec![crate::ast::Spanned::dummy(crate::ast::Pattern::Wildcard)],
                    preconditions: Vec::new(),
                    guard: None,
                    body_id: 0,
                }],
            })
            .unwrap(),
            vec![0],
        );
        assert!(dispatch.required_input_ordinals().is_empty());
        Rc::make_mut(&mut abi.materialized).entry_dispatch = Some(dispatch);
        let value = ValueId::from_u32(0);
        let result_value = ValueId::from_u32(1);
        executable.body = BackendBody::Clauses {
            clauses: vec![crate::compiler2::BackendClause {
                span: crate::source::Span::DUMMY,
                params: vec![value],
                projections: Vec::new(),
                entry: crate::compiler2::ControlEntryId::from_u32(0),
            }],
            entries: vec![BackendEntry {
                span: crate::source::Span::DUMMY,
                origin: crate::compiler2::BackendEntryOrigin::Clause,
                params: Vec::new(),
                captures: Vec::new(),
                physical_captures: Vec::new(),
                physical_params: Vec::new(),
                steps: vec![
                    ProgramStep::AssertTuple {
                        source: value,
                        arity: 1,
                    },
                    ProgramStep::Const {
                        value: result_value,
                        literal: crate::ground_value::GroundValue::Int(42),
                    },
                ],
                tail: BackendTail::Value {
                    value: result_value,
                    dest: ControlDestination::Return,
                },
            }],
            generated: Vec::new(),
        };
        let mut runtime = IrInterpRuntime::fresh_with_atoms(Vec::new());
        runtime.current_proc = runtime.process_ptr(1).unwrap();
        let result = step_backend_executable(
            &mut runtime,
            world.types_mut(),
            &transport,
            &crate::telemetry::ConfiguredTelemetry::new(),
            &empty_backend_program(),
            &Module::default(),
            Rc::new(executable),
            Vec::new(),
            Vec::new(),
        );
        let result = result.unwrap_or_else(|error| panic!("entry dispatch must reach its body: {error}"));
        assert!(
            matches!(result, BackendEvalTransition::Done(value) if value.as_i64() == Some(42)),
            "dispatch must preserve the partial tuple for its body without trying to box its absent field"
        );
    }

    #[test]
    fn continuations_and_local_resumes_execute_the_retained_body_without_inventory_lookup() {
        let mut world = crate::compiler2::World::new();
        let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "retained_resume", 0);
        let key = ExecutableKey {
            activation: crate::compiler2::ActivationKey::from_inputs(
                crate::compiler2::RootId::for_test(0),
                function,
                &[],
                world.types_mut(),
            ),
            need: crate::compiler2::ExecutableNeed::Value,
        };
        let nothing = world.intern_shape(ShapeDescr::Nothing);
        let return_ty = world.types_mut().int();
        let mut executable = BackendExecutable::for_test(key.clone(), return_ty, nothing);
        let value = ValueId::from_u32(0);
        let first = crate::compiler2::ControlEntryId::from_u32(0);
        let last = crate::compiler2::ControlEntryId::from_u32(1);
        executable.body = BackendBody::Clauses {
            clauses: Vec::new(),
            entries: [ControlDestination::Deliver(last), ControlDestination::Return]
                .into_iter()
                .map(|dest| BackendEntry {
                    span: crate::source::Span::DUMMY,
                    origin: crate::compiler2::BackendEntryOrigin::Branch,
                    params: Vec::new(),
                    captures: Vec::new(),
                    physical_captures: Vec::new(),
                    physical_params: Vec::new(),
                    steps: vec![ProgramStep::Const {
                        value,
                        literal: crate::ground_value::GroundValue::Int(42),
                    }],
                    tail: BackendTail::Value { value, dest },
                })
                .collect(),
            generated: Vec::new(),
        };
        let executable = Rc::new(executable);
        let mut program = BackendProgram::empty(key.clone());
        program.add_executable(Rc::clone(&executable), world.types());
        let retained = backend_executable_ref(&program, world.types(), &key).expect("root boundary lookup");
        assert!(Rc::ptr_eq(&retained, &executable));
        let continuation = BackendContinuation {
            executable: retained,
            entry: first,
            env: HashMap::new(),
        };
        program.remove_executable(&key, world.types());
        assert!(
            program.executables().is_empty(),
            "no ordinal or key lookup can find the retained frame"
        );

        let transport = TransportStore::new();
        let mut runtime = IrInterpRuntime::fresh_with_atoms(Vec::new());
        runtime.current_proc = runtime.process_ptr(1).expect("test process");
        let next = continue_backend_value(
            &mut runtime,
            &transport,
            &program,
            BackendBoundValue::Runtime(AnyValue::Int(0)),
            vec![continuation],
        )
        .expect("retained continuation");
        let BackendEvalTransition::Next(BackendEvalState::Entry {
            executable: resumed,
            entry,
            env,
            continuations,
        }) = next
        else {
            panic!("continuation must resume its local body")
        };
        assert!(Rc::ptr_eq(&resumed, &executable));
        runtime
            .enqueue_backend_local_entry(1, resumed, entry, env, continuations)
            .expect("queue retained resume");
        let resume = runtime.take_backend_resume(1).expect("queued resume");
        let outcome = run_backend_resume(
            &mut runtime,
            world.types_mut(),
            &transport,
            &crate::telemetry::ConfiguredTelemetry::new(),
            &program,
            &Module::default(),
            resume,
        )
        .expect("local transitions must execute the retained allocation even without root membership");
        assert!(matches!(outcome, BackendRunStep::Done(value) if value.as_i64() == Some(42)));
    }

    fn empty_backend_program() -> BackendProgram {
        BackendProgram::empty_for_test()
    }

    fn encode_for_layout(
        transport: &TransportStore,
        process: *mut Process,
        value: &BackendBoundValue,
        shape: ShapeId,
    ) -> Result<Vec<AnyValue>, String> {
        encode_with_layout(transport, process, value, TransportLayout::structural(shape))
    }

    fn encode_with_layout(
        transport: &TransportStore,
        process: *mut Process,
        value: &BackendBoundValue,
        layout: TransportLayout,
    ) -> Result<Vec<AnyValue>, String> {
        let mut encoded = Vec::new();
        encode_transport_layout(
            transport,
            &empty_backend_program(),
            process,
            value,
            layout,
            &mut encoded,
        )?;
        Ok(encoded)
    }

    fn tuple_shape(transport: &mut TransportStore, fields: &[ShapeId]) -> ShapeId {
        transport.interners_mut().intern_shape(ShapeDescr::Tuple(
            fields
                .iter()
                .copied()
                .map(TransportLayout::structural)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        ))
    }

    #[test]
    fn tuple_decode_keeps_an_absent_parent_decomposed_and_a_carried_parent_boxed() {
        let mut transport = TransportStore::new();
        let mut types = crate::compiler2::Types::new();
        let int = types.int();
        let tuple_ty = types.tuple(&[int]);
        let lane = transport
            .interners_mut()
            .intern_lane(crate::compiler2::transport::LaneDescr {
                ty: int,
                class: crate::compiler2::transport::TransportClass::Value,
            });
        let tuple_lane = transport
            .interners_mut()
            .intern_lane(crate::compiler2::transport::LaneDescr {
                ty: tuple_ty,
                class: crate::compiler2::transport::TransportClass::Value,
            });
        let scalar = transport.interners_mut().intern_shape(ShapeDescr::Lane(lane));
        let tuple = transport
            .interners_mut()
            .intern_shape(ShapeDescr::Tuple(Box::new([TransportLayout {
                structural: scalar,
                carrier: TransportCarrier::ValueRef(lane),
            }])));
        let args = [AnyValue::Int(7)];
        let mut decomposed_index = 0;
        let decomposed = decode_transport_layout(
            &transport,
            &args,
            TransportLayout::structural(tuple),
            &mut decomposed_index,
        )
        .expect("an absent parent carrier preserves its recursive physical lanes");
        assert!(matches!(
            decomposed,
            BackendBoundValue::Transport { shape, lanes }
                if shape == tuple && matches!(lanes.as_slice(), [AnyValue::Int(7)])
        ));
        assert_eq!(decomposed_index, 1);

        let mut boxed_index = 0;
        let boxed = decode_transport_layout(
            &transport,
            &args,
            TransportLayout {
                structural: tuple,
                carrier: TransportCarrier::ValueRef(tuple_lane),
            },
            &mut boxed_index,
        )
        .expect("the parent carrier dominates its structural tuple");
        assert!(matches!(boxed, BackendBoundValue::Runtime(AnyValue::Int(7))));
        assert_eq!(boxed_index, 1);
    }

    #[test]
    fn tuple_encoding_reprojects_same_arity_partial_transport_by_position() {
        let mut transport = TransportStore::new();
        let nothing = transport.interners_mut().intern_shape(ShapeDescr::Nothing);
        let mut types = crate::compiler2::Types::new();
        let int = types.int();
        let inner_tuple_ty = types.tuple(&[int, int, int]);
        let outer_tuple_ty = types.tuple(&[int, inner_tuple_ty]);
        let lane = transport
            .interners_mut()
            .intern_lane(crate::compiler2::transport::LaneDescr {
                ty: int,
                class: crate::compiler2::transport::TransportClass::Value,
            });
        let scalar = transport.interners_mut().intern_shape(ShapeDescr::Lane(lane));
        let inner_tuple_lane = transport
            .interners_mut()
            .intern_lane(crate::compiler2::transport::LaneDescr {
                ty: inner_tuple_ty,
                class: crate::compiler2::transport::TransportClass::Value,
            });
        let inner_tuple_value = transport
            .interners_mut()
            .intern_shape(ShapeDescr::Lane(inner_tuple_lane));
        let outer_tuple_lane = transport
            .interners_mut()
            .intern_lane(crate::compiler2::transport::LaneDescr {
                ty: outer_tuple_ty,
                class: crate::compiler2::transport::TransportClass::Value,
            });
        let source_inner = tuple_shape(&mut transport, &[scalar, scalar, scalar]);
        let source = tuple_shape(&mut transport, &[nothing, source_inner]);
        let destination = tuple_shape(&mut transport, &[nothing, inner_tuple_value]);
        let selective_inner = tuple_shape(&mut transport, &[nothing, scalar, nothing]);
        let selective_destination = tuple_shape(&mut transport, &[nothing, selective_inner]);
        let required_absent_destination = tuple_shape(&mut transport, &[scalar, nothing]);
        let arity_mismatch_destination = tuple_shape(&mut transport, &[scalar]);
        let value = BackendBoundValue::Transport {
            shape: source,
            lanes: vec![AnyValue::Int(1), AnyValue::Int(2), AnyValue::Int(3)],
        };
        let mut runtime = IrInterpRuntime::fresh_with_atoms(Vec::new());
        let mut process = runtime.take_process(1).expect("test process");
        let process = &mut process as *mut Process;
        let encoded = encode_for_layout(&transport, process, &value, destination)
            .expect("the destination erases the absent field before encoding the required inner tuple");

        assert_eq!(encoded.len(), 1);
        assert!(
            matches!(encoded[0], AnyValue::Ref(_)),
            "the inner tuple crosses as one value ref"
        );
        assert_eq!(transport.interners().lane(inner_tuple_lane).ty, inner_tuple_ty);
        let inner_fields = (0..3)
            .map(|index| {
                with_value_ref(process, encoded[0], "reprojected inner tuple", |tuple| {
                    fz_struct_get_field_ref(process, tuple, index * 8)
                })
                .and_then(|word| interp_value_from_ref_word(word, "reprojected inner tuple field"))
                .and_then(|value| {
                    value
                        .as_i64()
                        .ok_or_else(|| "inner tuple field was not an int".to_string())
                })
            })
            .collect::<Result<Vec<_>, _>>()
            .expect("the destination lane should hold the materialized inner tuple");
        assert_eq!(inner_fields, [1, 2, 3]);

        let selectively_encoded = encode_for_layout(&transport, process, &value, selective_destination)
            .expect("a second consumer should independently select one nested source field");
        assert_eq!(selectively_encoded.len(), 1);
        assert_eq!(selectively_encoded[0].as_i64(), Some(2));

        let source_with_present_discard = tuple_shape(&mut transport, &[scalar, source_inner]);
        let value_with_present_discard = BackendBoundValue::Transport {
            shape: source_with_present_discard,
            lanes: vec![AnyValue::Int(99), AnyValue::Int(1), AnyValue::Int(2), AnyValue::Int(3)],
        };
        let present_discarded = encode_for_layout(&transport, process, &value_with_present_discard, destination)
            .expect("destination Nothing should discard a present source field");
        assert_eq!(present_discarded.len(), 1);
        assert!(matches!(present_discarded[0], AnyValue::Ref(_)));

        let whole_carrier = encode_with_layout(
            &transport,
            process,
            &value_with_present_discard,
            TransportLayout {
                structural: source_with_present_discard,
                carrier: TransportCarrier::ValueRef(outer_tuple_lane),
            },
        )
        .expect("a whole tuple should satisfy an outer ValueRef carrier");
        assert_eq!(whole_carrier.len(), 1);
        assert!(matches!(whole_carrier[0], AnyValue::Ref(_)));
        assert!(
            encode_with_layout(
                &transport,
                process,
                &value,
                TransportLayout {
                    structural: destination,
                    carrier: TransportCarrier::ValueRef(outer_tuple_lane),
                },
            )
            .is_err(),
            "same-arity reprojection must not bypass an outer ValueRef obligation",
        );

        let required_absent = encode_for_layout(&transport, process, &value, required_absent_destination)
            .expect_err("a required destination field cannot be invented from an absent source field");
        assert_eq!(required_absent, "backend value was absent and cannot be materialized");

        let arity_mismatch = encode_for_layout(&transport, process, &value, arity_mismatch_destination)
            .expect_err("arity-mismatched tuples retain outer materialization behavior");
        assert_eq!(arity_mismatch, "backend value was absent and cannot be materialized");

        let non_tuple = encode_runtime_value(
            &transport,
            &empty_backend_program(),
            process,
            &value,
            scalar,
            &mut Vec::new(),
        )
        .expect_err("non-tuple destinations retain outer materialization behavior");
        assert_eq!(non_tuple, "backend value was absent and cannot be materialized");

        let mut identical = Vec::new();
        encode_runtime_value(
            &transport,
            &empty_backend_program(),
            process,
            &value,
            source,
            &mut identical,
        )
        .expect("an identical layout keeps the direct lane-copy path");
        assert_eq!(
            identical.iter().map(|value| value.as_i64()).collect::<Vec<_>>(),
            [Some(1), Some(2), Some(3)]
        );
    }

    #[test]
    fn direct_callable_lanes_cannot_be_published_as_a_runtime_environment() {
        let mut transport = TransportStore::new();
        let nothing = transport.interners_mut().intern_shape(ShapeDescr::Nothing);
        let callable = transport
            .interners_mut()
            .intern_callable(crate::compiler2::transport::CallableDescr {
                function: Some(FunctionId::from_fn_id(FnId(123))),
                arity: 0,
                capture_layouts: Box::new([TransportLayout::structural(nothing)]),
            });
        let shape = transport.interners_mut().intern_shape(ShapeDescr::Callable(callable));
        let mut process = IrInterpRuntime::fresh_with_atoms(Vec::new()).take_process(1).unwrap();
        assert!(
            materialize_transport_value(&transport, &mut process, shape, &[]).is_err(),
            "an elided capture has no value to publish; the source construction must retain it",
        );
    }

    #[test]
    fn backend_destructor_closure_unpack_errors_propagate() {
        let error = unpack_pending_dtor_closure(RuntimeAnyValue::null()).expect_err("non-closure destructor must fail");
        assert!(error.contains("backend dtor drain: invalid closure"), "{error}");
    }
}
