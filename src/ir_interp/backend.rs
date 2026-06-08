use std::collections::HashMap;
use std::rc::Rc;

use super::binop::{eval_binop, eval_unop, interp_value_eq, unpack_closure};
use super::dispatch_exec::{DispatchExecState, execute_dispatch_inputs};
use super::extern_call::call_lowered_extern;
use super::prim::{interp_list_cons, interp_list_head, interp_list_tail, interp_map_get, interp_map_put};
use super::value::{
    AnyValue, interp_bool_value, interp_empty_list_value, interp_nil_value, interp_struct_field_from_tagged_bits,
    interp_value_from_ref_word, with_value_ref,
};
use super::*;
use crate::compiler2::{
    BackendBody, BackendEntry, BackendExecutable, BackendProgram, BackendStep, BackendTail, ControlDestination,
    ExecutableDispatch, ValueId,
};
use crate::compiler2::{ExecutableNeed, FunctionId};
use crate::fz_ir::{BinOp as IrBinOp, FnId, Module, UnOp as IrUnOp};
use crate::telemetry::Telemetry;
use fz_runtime::any_value::{
    AnyValue as RuntimeAnyValue, AnyValueRef, ValueKind, closure_addr_from_tagged, struct_schema_id,
};
use fz_runtime::exec_ctx::ExecCtx;
use fz_runtime::heap::Schema;
use fz_runtime::heap::{FieldKind, Heap, deep_copy_any_value_ref};
use fz_runtime::ir_runtime::{
    fz_bs_begin, fz_bs_finalize, fz_bs_write_field_ref, fz_map_empty, fz_map_get_atom_key_ref, fz_matcher_map_get_ref,
    fz_struct_get_field_ref,
};
use fz_runtime::procbin::mso_drop_all_deferred;
use fz_runtime::process::{CompiledModuleConsts, DEFAULT_REDUCTIONS_PER_QUANTUM, Process, ProcessState};

/// Runs one closed Compiler2 backend program through the shared interpreter
/// runtime without reopening planner or type-resolution work.
pub(crate) fn run_backend_main(
    types: &mut crate::compiler2::Types,
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
    let completions = drive_backend_until_idle(&mut runtime, types, tel, program, &module)?;
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

impl IrInterpRuntime {
    fn enqueue_backend_entry(&mut self, pid: u32, executable: usize, args: Vec<AnyValue>) -> Result<(), String> {
        if !self.tasks.contains_key(&pid) {
            return Err(format!("enqueue_backend_entry: unknown pid {}", pid));
        }
        self.backend_resume.insert(pid, (executable, args));
        self.run_queue.push_back(pid);
        self.set_process_state(pid, ProcessState::Ready);
        Ok(())
    }

    fn take_backend_resume(&mut self, pid: u32) -> Option<(usize, Vec<AnyValue>)> {
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

    pub(super) fn send_opaque(&mut self, tel: &dyn Telemetry, receiver_pid: u32, msg: AnyValue) -> Result<(), String> {
        let sender_heap = &unsafe { &*self.cur_proc() }.heap as *const Heap;
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
        if task.state == ProcessState::Blocked {
            let copied_msg = AnyValue::from_any_value_ref(copied).expect("copied backend interpreter message ref");
            if let Some(entry) = self.resume.get_mut(&receiver_pid) {
                entry.1.insert(0, copied_msg);
            }
            task.state = ProcessState::Ready;
            self.run_queue.push_back(receiver_pid);
        } else {
            task.mailbox.push_back(copied);
        }
        Ok(())
    }
}

fn drive_backend_until_idle(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    tel: &dyn Telemetry,
    program: &BackendProgram,
    module: &Module,
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
        let (executable, args) = runtime
            .take_backend_resume(pid)
            .expect("backend pid in run queue with no backend resume");
        let proc_ptr = runtime
            .process_ptr(pid)
            .expect("backend pid in run queue with no process entry");
        unsafe {
            (*proc_ptr).state = ProcessState::Running;
            (*proc_ptr).reset_reduction_budget();
            (*proc_ptr).ctx = &mut exec_ctx;
            (*proc_ptr).heap.set_owner(proc_ptr);
        }
        runtime.current_proc = proc_ptr;
        let value = run_backend_executable(runtime, types, tel, program, module, executable, args)?;
        completions.push((pid, value));
        unsafe {
            mso_drop_all_deferred(&mut (*proc_ptr).heap);
        }
        if let Err(e) = drain_pending_dtors_backend(runtime, types, tel, program, module) {
            tel.event(&["fz", "runtime", "dtor_drain_failed"], crate::metadata! { error: e });
        }
        unsafe {
            (*proc_ptr).halt_value = value_to_halt(proc_ptr, value);
            ExitRecord::emit(tel, pid, &*proc_ptr);
        }
        runtime.set_process_state(pid, ProcessState::Exited);
    }

    Ok(completions)
}

fn run_backend_executable(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    tel: &dyn Telemetry,
    program: &BackendProgram,
    module: &Module,
    executable_index: usize,
    args: Vec<AnyValue>,
) -> Result<AnyValue, String> {
    let executable = program
        .executables
        .get(executable_index)
        .ok_or_else(|| format!("backend executable {} is out of bounds", executable_index))?;
    match &executable.body {
        BackendBody::Extern { signature } => {
            call_lowered_extern(runtime, types, tel, program, module, signature, None, &args)
        }
        BackendBody::Clauses { clauses, entries, .. } => {
            let dispatch = executable
                .entry_dispatch
                .as_ref()
                .ok_or_else(|| format!("backend executable {} is missing clause dispatch", executable_index))?;
            let clause_index = select_clause(runtime, types, module, dispatch, &args)?.ok_or_else(|| {
                format!(
                    "function_clause: no backend entry clause matched for executable {}",
                    executable_index
                )
            })?;
            let clause = clauses
                .get(clause_index)
                .ok_or_else(|| format!("backend clause {} is out of bounds", clause_index))?;
            if clause.params.len() != args.len() {
                return Err(format!(
                    "backend executable {} expected {} arg(s), got {}",
                    executable_index,
                    clause.params.len(),
                    args.len()
                ));
            }
            let mut env = HashMap::new();
            for (param, value) in clause.params.iter().copied().zip(args) {
                env.insert(param, value);
            }
            eval_steps(
                runtime,
                types,
                tel,
                program,
                module,
                executable,
                &clause.projections,
                &mut env,
            )?;
            eval_entry(
                runtime,
                types,
                tel,
                program,
                module,
                executable,
                entries,
                clause.entry,
                env,
            )
        }
    }
}

fn select_clause(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    module: &Module,
    dispatch: &ExecutableDispatch,
    args: &[AnyValue],
) -> Result<Option<usize>, String> {
    let selected = select_dispatch_body(runtime, types, module, dispatch.plan(), args, &HashMap::new())?;
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
    let mut state = DispatchExecState::default();
    let mut type_match =
        |runtime: &mut IrInterpRuntime, module: &Module, want: &crate::compiler2::Ty, value: AnyValue| {
            let have = dynamic_value_ty(runtime, types, module, value).ok()?;
            let overlap = types.intersect(have, *want);
            Some(!types.is_empty(&overlap))
        };
    let selected = execute_dispatch_inputs(runtime, module, plan, args, pinned, &mut state, &mut type_match)
        .map(|(body_id, _)| body_id);
    Ok(selected)
}

fn eval_entry(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    tel: &dyn Telemetry,
    program: &BackendProgram,
    module: &Module,
    executable: &BackendExecutable,
    entries: &[BackendEntry],
    entry_id: crate::compiler2::ControlEntryId,
    mut env: HashMap<ValueId, AnyValue>,
) -> Result<AnyValue, String> {
    let entry = entries
        .get(entry_id.as_u32() as usize)
        .ok_or_else(|| format!("backend entry {} is out of bounds", entry_id.as_u32()))?;
    eval_steps(runtime, types, tel, program, module, executable, &entry.steps, &mut env)?;
    match &entry.tail {
        BackendTail::Value { value, dest } => {
            let result = env_get(&env, *value)?;
            match dest {
                ControlDestination::Return => Ok(result),
                ControlDestination::Deliver(target) => eval_entry(
                    runtime,
                    types,
                    tel,
                    program,
                    module,
                    executable,
                    entries,
                    *target,
                    delivered_env(entries, &env, *target, Some(result))?,
                ),
            }
        }
        BackendTail::DirectCall {
            callee,
            args,
            extern_marshals,
            dest,
            ..
        } => {
            let result = eval_direct_call(
                runtime,
                types,
                tel,
                program,
                module,
                *callee,
                args,
                extern_marshals.as_deref(),
                &env,
            )?;
            match dest {
                ControlDestination::Return => Ok(result),
                ControlDestination::Deliver(target) => eval_entry(
                    runtime,
                    types,
                    tel,
                    program,
                    module,
                    executable,
                    entries,
                    *target,
                    delivered_env(entries, &env, *target, Some(result))?,
                ),
            }
        }
        BackendTail::ClosureCall {
            target,
            callee,
            args,
            dest,
            ..
        } => {
            let mut call_args = closure_captures(runtime.cur_proc(), env_get(&env, *callee)?)?;
            call_args.extend(eval_call_args(&env, args)?);
            let result = run_backend_executable(runtime, types, tel, program, module, *target, call_args)?;
            match dest {
                ControlDestination::Return => Ok(result),
                ControlDestination::Deliver(target) => eval_entry(
                    runtime,
                    types,
                    tel,
                    program,
                    module,
                    executable,
                    entries,
                    *target,
                    delivered_env(entries, &env, *target, Some(result))?,
                ),
            }
        }
        BackendTail::If {
            cond,
            then_entry,
            else_entry,
        } => {
            let target = if env_get(&env, *cond)?.is_truthy() {
                *then_entry
            } else {
                *else_entry
            };
            eval_entry(
                runtime,
                types,
                tel,
                program,
                module,
                executable,
                entries,
                target,
                delivered_env(entries, &env, target, None)?,
            )
        }
        BackendTail::Dispatch {
            inputs,
            pinned,
            dispatch,
        } => {
            let input_values = env_values(&env, inputs)?;
            let pinned_values = local_dispatch_pinned(&env, pinned, &dispatch.plan)?;
            let target =
                match select_dispatch_body(runtime, types, module, &dispatch.plan, &input_values, &pinned_values)? {
                    Some(body_id) => *dispatch
                        .arm_entries
                        .get(body_id as usize)
                        .ok_or_else(|| format!("backend local dispatch arm {} is out of bounds", body_id))?,
                    None => dispatch.miss_entry,
                };
            eval_entry(
                runtime,
                types,
                tel,
                program,
                module,
                executable,
                entries,
                target,
                delivered_env(entries, &env, target, None)?,
            )
        }
        BackendTail::Halt { atom } => Err(atom.clone()),
    }
}

fn eval_steps(
    runtime: &mut IrInterpRuntime,
    _types: &mut crate::compiler2::Types,
    _tel: &dyn Telemetry,
    _program: &BackendProgram,
    module: &Module,
    _executable: &BackendExecutable,
    steps: &[BackendStep],
    env: &mut HashMap<ValueId, AnyValue>,
) -> Result<(), String> {
    for step in steps {
        match step {
            BackendStep::Const { value, literal } => {
                env.insert(*value, literal_value(runtime, literal)?);
            }
            BackendStep::Tuple { value, items } => {
                let tuple = make_tuple(runtime, env_values(env, items)?)?;
                env.insert(*value, tuple);
            }
            BackendStep::List { value, items, tail } => {
                let tail = tail.map_or(Ok(interp_empty_list_value()), |tail| env_get(env, tail))?;
                let mut acc = tail;
                for item in items.iter().rev() {
                    acc = interp_list_cons(runtime.cur_proc(), env_get(env, *item)?, acc, "backend list")?;
                }
                env.insert(*value, acc);
            }
            BackendStep::Map { value, entries } => {
                let mut map_bits = if entries.is_empty() {
                    fz_map_empty(runtime.cur_proc())
                } else {
                    0
                };
                for (key, item) in entries {
                    map_bits = interp_map_put(
                        runtime.cur_proc(),
                        map_bits,
                        env_get(env, *key)?,
                        env_get(env, *item)?,
                        "backend map",
                    )?;
                }
                env.insert(*value, interp_value_from_ref_word(map_bits, "backend map")?);
            }
            BackendStep::MapUpdate { value, base, entries } => {
                let base = env_get(env, *base)?;
                let mut map_bits = base.value(runtime.cur_proc())?.ref_word().raw_word();
                for (key, item) in entries {
                    map_bits = interp_map_put(
                        runtime.cur_proc(),
                        map_bits,
                        env_get(env, *key)?,
                        env_get(env, *item)?,
                        "backend map update",
                    )?;
                }
                env.insert(*value, interp_value_from_ref_word(map_bits, "backend map update")?);
            }
            BackendStep::Struct {
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
                    let item = env_get(env, *item)?;
                    unsafe { &mut *runtime.cur_proc() }.heap.write_field_slot(
                        ptr,
                        (index as u32) * 8,
                        item.value(runtime.cur_proc())?,
                    );
                }
                let struct_ref = AnyValueRef::from_heap_object(ValueKind::STRUCT, ptr).expect("backend struct ref");
                env.insert(*value, AnyValue::Ref(struct_ref));
            }
            BackendStep::Bitstring { value, fields } => {
                fz_bs_begin(runtime.cur_proc());
                for field in fields {
                    let item = env_get(env, field.value)?;
                    let (size_present, size_value) = backend_bit_size_value(env, &field.spec.size)?;
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
                    interp_value_from_ref_word(fz_bs_finalize(runtime.cur_proc()), "backend bitstring")?,
                );
            }
            BackendStep::FunctionRef { value, function } => {
                env.insert(*value, AnyValue::FnRef(FnId(function.as_u32())));
            }
            BackendStep::NamedFunctionRef { name, arity, .. } => {
                return Err(format!(
                    "backend interpreter reached unresolved fn ref `{name}/{arity}`"
                ));
            }
            BackendStep::Lambda {
                value,
                function,
                captures,
            } => {
                let closure = make_closure(runtime, function.as_u32(), env_values(env, captures)?)?;
                env.insert(*value, closure);
            }
            BackendStep::BinaryOp { value, op, left, right } => {
                let result = eval_binop(
                    runtime.cur_proc(),
                    backend_binop(*op)?,
                    env_get(env, *left)?,
                    env_get(env, *right)?,
                )?;
                env.insert(*value, result);
            }
            BackendStep::UnaryOp { value, op, input } => {
                let result = eval_unop(backend_unop(*op)?, env_get(env, *input)?)?;
                env.insert(*value, result);
            }
            BackendStep::MapIndex { value, base, key } => {
                let result = interp_map_get(runtime.cur_proc(), env_get(env, *base)?, env_get(env, *key)?)?;
                env.insert(*value, result);
            }
            BackendStep::FieldAccess { value, base, field } => {
                let base = env_get(env, *base)?;
                let result = interp_struct_field(runtime, module, base, field)?;
                env.insert(*value, result);
            }
            BackendStep::AssertLiteral { source, literal } => {
                let actual = env_get(env, *source)?;
                let expected = literal_value(runtime, literal)?;
                if !interp_value_eq(runtime.cur_proc(), actual, expected)? {
                    return Err(format!(
                        "match_error: literal assertion failed at value {}",
                        source.as_u32()
                    ));
                }
            }
            BackendStep::AssertStruct { source, module_name } => {
                if !is_named_struct(runtime, module, env_get(env, *source)?, module_name)? {
                    return Err(format!("match_error: expected struct {module_name}"));
                }
            }
            BackendStep::RequireMapValue { value, source, key } => {
                let key = literal_value(runtime, key)?;
                let result = matcher_map_get(runtime, env_get(env, *source)?, key)?;
                if matches!(result, AnyValue::Null) {
                    return Err("match_error: expected map key to exist".to_string());
                }
                env.insert(*value, result);
            }
            BackendStep::AssertTuple { source, arity } => {
                if !is_tuple_arity(runtime, env_get(env, *source)?, *arity)? {
                    return Err(format!("match_error: expected tuple arity {}", arity));
                }
            }
            BackendStep::TupleField { value, source, index } => {
                let source = env_get(env, *source)?;
                let field = with_value_ref(runtime.cur_proc(), source, "backend tuple field", |struct_ref| {
                    fz_struct_get_field_ref(runtime.cur_proc(), struct_ref, (*index as u32) * 8)
                })
                .and_then(|ref_word| interp_value_from_ref_word(ref_word, "backend tuple field"))?;
                env.insert(*value, field);
            }
            BackendStep::AssertEmptyList { source } => {
                if !env_get(env, *source)?.is_empty_list() {
                    return Err("match_error: expected empty list".to_string());
                }
            }
            BackendStep::AssertSame { source, value } => {
                if !interp_value_eq(runtime.cur_proc(), env_get(env, *source)?, env_get(env, *value)?)? {
                    return Err("match_error: pinned value mismatch".to_string());
                }
            }
            BackendStep::SplitList { source, head, tail } => {
                let source = env_get(env, *source)?;
                let head_value = interp_list_head(runtime.cur_proc(), source)?;
                let tail_value = interp_list_tail(runtime.cur_proc(), source)?;
                env.insert(*head, head_value);
                env.insert(*tail, tail_value);
            }
            BackendStep::BitstringInit { reader, source } => {
                let source = env_get(env, *source)?;
                let source_ref = source.as_ref_word(runtime.cur_proc())?;
                let reader_ref = fz_runtime::ir_runtime::fz_bs_reader_init_ref(runtime.cur_proc(), source_ref);
                env.insert(
                    *reader,
                    interp_value_from_ref_word(reader_ref, "backend bitstring reader")?,
                );
            }
            BackendStep::BitstringRead {
                ok,
                value,
                next_reader,
                reader,
                spec,
                is_last,
            } => {
                let reader_ref = env_get(env, *reader)?.as_ref_word(runtime.cur_proc())?;
                let (size_present, size_value) = backend_bit_size_value(env, &spec.size)?;
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
                env.insert(*ok, ok_value);
                if ok_value.is_false() || ok_value.is_nil() {
                    env.insert(*value, AnyValue::Null);
                    env.insert(*next_reader, AnyValue::Null);
                } else {
                    env.insert(
                        *value,
                        interp_struct_field_from_tagged_bits(
                            runtime.cur_proc(),
                            result,
                            8,
                            "backend bitstring extracted",
                        )?,
                    );
                    env.insert(
                        *next_reader,
                        interp_struct_field_from_tagged_bits(
                            runtime.cur_proc(),
                            result,
                            16,
                            "backend bitstring next reader",
                        )?,
                    );
                }
            }
            BackendStep::AssertBitstringDone { reader } => {
                let reader = env_get(env, *reader)?;
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

fn delivered_env(
    entries: &[BackendEntry],
    env: &HashMap<ValueId, AnyValue>,
    entry_id: crate::compiler2::ControlEntryId,
    delivered: Option<AnyValue>,
) -> Result<HashMap<ValueId, AnyValue>, String> {
    let entry = entries
        .get(entry_id.as_u32() as usize)
        .ok_or_else(|| format!("backend entry {} is out of bounds", entry_id.as_u32()))?;
    let mut next = HashMap::new();
    if let Some(value) = entry.origin.input_value() {
        let delivered = delivered.ok_or_else(|| {
            format!(
                "backend entry {} expected a delivered value but none was provided",
                entry_id.as_u32()
            )
        })?;
        next.insert(value, delivered);
    }
    for capture in &entry.captures {
        next.insert(*capture, env_get(env, *capture)?);
    }
    Ok(next)
}

fn eval_direct_call(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    tel: &dyn Telemetry,
    program: &BackendProgram,
    module: &Module,
    callee: usize,
    args: &[crate::compiler2::BackendCallArg],
    extern_marshals: Option<&[crate::fz_ir::ExternTy]>,
    env: &HashMap<ValueId, AnyValue>,
) -> Result<AnyValue, String> {
    let executable = program
        .executables
        .get(callee)
        .ok_or_else(|| format!("backend direct callee {} is out of bounds", callee))?;
    let call_args = eval_call_args(env, args)?;
    match &executable.body {
        BackendBody::Extern { signature } => call_lowered_extern(
            runtime,
            types,
            tel,
            program,
            module,
            signature,
            extern_marshals,
            &call_args,
        ),
        BackendBody::Clauses { .. } => run_backend_executable(runtime, types, tel, program, module, callee, call_args),
    }
}

fn eval_call_args(
    env: &HashMap<ValueId, AnyValue>,
    args: &[crate::compiler2::BackendCallArg],
) -> Result<Vec<AnyValue>, String> {
    args.iter().map(|arg| env_get(env, arg.value)).collect()
}

fn env_values(env: &HashMap<ValueId, AnyValue>, values: &[ValueId]) -> Result<Vec<AnyValue>, String> {
    values.iter().map(|value| env_get(env, *value)).collect()
}

fn local_dispatch_pinned(
    env: &HashMap<ValueId, AnyValue>,
    pinned_values: &[ValueId],
    plan: &crate::dispatch_matrix::pattern::PatternDispatchPlan<crate::compiler2::Ty>,
) -> Result<HashMap<String, AnyValue>, String> {
    let mut pinned = HashMap::new();
    for (index, value_id) in pinned_values.iter().copied().enumerate() {
        let Some(pin) = plan.pinned.get(index) else {
            return Err(format!("backend local dispatch pinned {} is out of bounds", index));
        };
        if pin.input.is_none() {
            pinned.insert(pin.name.clone(), env_get(env, value_id)?);
        }
    }
    Ok(pinned)
}

fn env_get(env: &HashMap<ValueId, AnyValue>, value: ValueId) -> Result<AnyValue, String> {
    env.get(&value)
        .copied()
        .ok_or_else(|| format!("backend value {} is unbound", value.as_u32()))
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
    let schema_id = interp_tuple_schema_id(runtime, items.len());
    let p = unsafe { &mut *runtime.cur_proc() }.heap.alloc_struct(schema_id);
    for (index, item) in items.iter().enumerate() {
        unsafe { &mut *runtime.cur_proc() }.heap.write_field_slot(
            p,
            (index as u32) * 8,
            item.value(runtime.cur_proc())?,
        );
    }
    Ok(AnyValue::Ref(
        AnyValueRef::from_heap_object(ValueKind::STRUCT, p).expect("backend tuple ref"),
    ))
}

fn make_closure(runtime: &mut IrInterpRuntime, code: u32, captures: Vec<AnyValue>) -> Result<AnyValue, String> {
    let heap = &mut unsafe { &mut *runtime.cur_proc() }.heap;
    let bits = heap.alloc_closure_slots(code, captures.len(), 0);
    let p = closure_addr_from_tagged(bits).expect("new backend closure ptr");
    unsafe { std::ptr::write(p.add(8) as *mut u64, code as u64) };
    for (index, value) in captures.iter().enumerate() {
        unsafe { heap.write_closure_capture_value(p, index, value.value(runtime.cur_proc())?) };
    }
    let closure_addr = closure_addr_from_tagged(bits).expect("backend closure bits");
    Ok(AnyValue::Ref(
        AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure_addr).expect("backend closure ref"),
    ))
}

fn closure_captures(proc: *mut Process, value: AnyValue) -> Result<Vec<AnyValue>, String> {
    match value {
        AnyValue::FnRef(_) => Ok(Vec::new()),
        other => {
            let (_, captures) = unpack_closure(other.value(proc)?)?;
            Ok(captures)
        }
    }
}

fn drain_pending_dtors_backend(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
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
        let _ = run_backend_executable(runtime, types, tel, program, module, target, args)?;
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
                && executable.key.activation.function == FunctionId::from_u32(fn_id.0)
                && entry.capture_count == captures.len()
                && executable.key.activation.input.len() == captures.len() + args.len())
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
            actual_types
                .iter()
                .zip(executable.key.activation.input.iter())
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
    env: &HashMap<ValueId, AnyValue>,
    size: &Option<crate::compiler2::LoweredBitSize>,
) -> Result<(u32, u32), String> {
    Ok(match size {
        None => (0, 0),
        Some(crate::compiler2::LoweredBitSize::Literal(value)) => (1, *value),
        Some(crate::compiler2::LoweredBitSize::Value(value)) => {
            let size = env_get(env, *value)?
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
