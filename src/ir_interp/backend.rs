use std::collections::HashMap;

use super::binop::{eval_binop, eval_unop, interp_value_eq, unpack_closure};
use super::dispatch_exec::{DispatchExecState, execute_dispatch_inputs};
use super::extern_call::call_lowered_extern;
use super::prim::{interp_list_cons, interp_list_head, interp_list_tail, interp_map_get};
use super::value::{
    AnyValue, interp_bool_value, interp_empty_list_value, interp_nil_value, interp_value_from_ref_word, with_value_ref,
};
use super::*;
use crate::compiler2::{
    BackendBlock, BackendBody, BackendExecutable, BackendProgram, BackendStep, ExecutableDispatch, ValueId,
};
use crate::fz_ir::{BinOp as IrBinOp, FnId, Module, UnOp as IrUnOp};
use crate::telemetry::Telemetry;
use fz_runtime::any_value::{
    AnyValue as RuntimeAnyValue, AnyValueRef, ValueKind, closure_addr_from_tagged, struct_schema_id,
};
use fz_runtime::exec_ctx::ExecCtx;
use fz_runtime::heap::FieldKind;
use fz_runtime::ir_runtime::fz_struct_get_field_ref;
use fz_runtime::process::{Process, ProcessState};

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
        ..Module::default()
    };
    let proc_ptr = runtime.process_ptr(1).expect("backend interp installed pid 1");
    let mut exec_ctx = ExecCtx {
        scheduler: &mut runtime as *mut IrInterpRuntime as *mut (),
        tel: (&tel) as *const &dyn Telemetry as *const (),
        output: Some(output_hook_thunk),
        module: &module as *const Module as *const (),
        ..ExecCtx::empty()
    };
    unsafe {
        (*proc_ptr).state = ProcessState::Running;
        (*proc_ptr).ctx = &mut exec_ctx;
        (*proc_ptr).heap.set_owner(proc_ptr);
    }
    runtime.current_proc = proc_ptr;
    let value = run_backend_executable(&mut runtime, types, tel, program, &module, program.entry, Vec::new())?;
    Ok(value_to_halt(proc_ptr, value))
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
        BackendBody::Extern { signature } => call_lowered_extern(runtime, tel, signature, None, &args),
        BackendBody::Clauses { clauses, .. } => {
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
            eval_block(runtime, types, tel, program, module, executable, &clause.body, &mut env)
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
    let mut state = DispatchExecState::default();
    let pinned = HashMap::new();
    let mut type_match =
        |runtime: &mut IrInterpRuntime, module: &Module, want: &crate::compiler2::Ty, value: AnyValue| {
            let have = dynamic_value_ty(runtime, types, module, value).ok()?;
            let overlap = types.intersect(have, *want);
            Some(!types.is_empty(&overlap))
        };
    let selected = execute_dispatch_inputs(
        runtime,
        module,
        dispatch.plan(),
        args,
        &pinned,
        &mut state,
        &mut type_match,
    )
    .map(|(body_id, _)| body_id);
    Ok(selected.and_then(|body_id| dispatch.clause_index(body_id)))
}

fn eval_block(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    tel: &dyn Telemetry,
    program: &BackendProgram,
    module: &Module,
    executable: &BackendExecutable,
    block: &BackendBlock,
    env: &mut HashMap<ValueId, AnyValue>,
) -> Result<AnyValue, String> {
    eval_steps(runtime, types, tel, program, module, executable, &block.steps, env)?;
    env_get(env, block.result)
}

fn eval_steps(
    runtime: &mut IrInterpRuntime,
    types: &mut crate::compiler2::Types,
    tel: &dyn Telemetry,
    program: &BackendProgram,
    module: &Module,
    executable: &BackendExecutable,
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
            BackendStep::FunctionRef { value, function } => {
                env.insert(*value, AnyValue::FnRef(FnId(function.as_u32())));
            }
            BackendStep::NamedFunctionRef { name, arity, .. } => {
                return Err(format!(
                    "backend interpreter reached unresolved fn ref `{name}/{arity}`"
                ));
            }
            BackendStep::DirectCall {
                value,
                callee,
                args,
                extern_marshals,
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
                    env,
                )?;
                env.insert(*value, result);
            }
            BackendStep::ClosureCall {
                value,
                target,
                callee,
                args,
                ..
            } => {
                let mut call_args = closure_captures(runtime.cur_proc(), env_get(env, *callee)?)?;
                call_args.extend(eval_call_args(env, args)?);
                let result = run_backend_executable(runtime, types, tel, program, module, *target, call_args)?;
                env.insert(*value, result);
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
            BackendStep::If {
                value,
                cond,
                then_block,
                else_block,
            } => {
                let branch = if env_get(env, *cond)?.is_truthy() {
                    then_block
                } else {
                    else_block
                };
                let result = eval_block(
                    runtime,
                    types,
                    tel,
                    program,
                    module,
                    executable,
                    branch,
                    &mut env.clone(),
                )?;
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
        }
    }
    Ok(())
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
        BackendBody::Extern { signature } => call_lowered_extern(runtime, tel, signature, extern_marshals, &call_args),
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
