//! Terminator emission for fz IR blocks.

use super::*;
use crate::compiler2::NativeEntryAbi;
use crate::fz_ir::{
    self as fz_ir, BlockId, Cont, DirectCallTarget, EmitSlot, FnId, ReceiveAfter, ReceiveClause, Term, Var,
};
use crate::types::{ClosureTypes, Types};
use cranelift_codegen::ir::TrapCode;
use cranelift_codegen::ir::{self, AbiParam, BlockArg, InstBuilder, MemFlags, Signature, condcodes::IntCC, types};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::FunctionBuilder;
use cranelift_module::FuncId;
use fz_runtime::failure::{fz_raise, fz_raise_showing};
use fz_runtime::ir_runtime::{fz_receive_park_matched, fz_yield_mid_flight_report, fz_yield_slow_path_begin};
use fz_runtime::process::YIELD_REASON_REDUCTIONS;
use fz_runtime::process_abi::PROCESS_REDUCTIONS_REMAINING_OFFSET;
use fz_runtime::scheduler_hooks::YIELD_PTR;
use std::collections::HashMap;

fn resolve_cont_sid(env: &CodegenEnv<'_>, blk: &fz_ir::Block) -> u32 {
    let cont_fn_id = match &blk.terminator {
        Term::Call { continuation, .. } | Term::CallClosure { continuation, .. } => continuation.fn_id,
        _ => panic!(
            "resolve_cont_sid called on non-call-shape terminator {:?}",
            blk.terminator
        ),
    };
    env.body_id_for_fn(cont_fn_id).unwrap_or_else(|| {
        panic!(
            "native continuation fn {} has no registered codegen body id",
            cont_fn_id.0
        )
    })
}

fn resolve_callee_sid(env: &CodegenEnv<'_>, blk: &fz_ir::Block, slot: EmitSlot) -> u32 {
    let callee_fn_id = match (&blk.terminator, slot) {
        (Term::Call { callee, .. } | Term::TailCall { callee, .. }, EmitSlot::Direct) => match callee {
            DirectCallTarget::Local(callee) => *callee,
            DirectCallTarget::ProviderBoundary(target) => {
                panic!(
                    "native callee `{}` reached codegen before provider-boundary link resolution",
                    target
                )
            }
        },
        _ => panic!(
            "resolve_callee_sid called with {:?} on native terminator {:?}",
            slot, blk.terminator
        ),
    };
    env.body_id_for_fn(callee_fn_id)
        .unwrap_or_else(|| panic!("native callee fn {} has no registered codegen body id", callee_fn_id.0))
}

fn emit_native_continuation_tail_delivery<M: cranelift_module::Module, T: Types<Ty = Ty> + ClosureTypes>(
    body: &mut CodegenFn<'_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    is_cont_fn: bool,
    cont_param: ir::Value,
    args: &[Var],
    is_back_edge: bool,
    callee_sid: u32,
    extra_params: usize,
) {
    let callee_param_reprs = &env.param_reprs[callee_sid as usize];
    assert!(
        args.len() >= extra_params,
        "continuation callee {} expected at least {} logical arg(s), got {}",
        callee_sid,
        extra_params,
        args.len()
    );
    assert_eq!(
        args.len(),
        callee_param_reprs.len(),
        "continuation callee {} logical arg count must match published param reprs",
        callee_sid
    );

    let mut delivered_args = Vec::with_capacity(
        callee_param_reprs
            .iter()
            .take(extra_params)
            .map(ArgRepr::abi_arity)
            .sum::<usize>()
            + 1,
    );
    let mut mid_flight_arg_shapes = Vec::with_capacity(extra_params + 1);
    for (i, arg) in args.iter().take(extra_params).enumerate() {
        let binding = *var_env
            .get(&arg.0)
            .unwrap_or_else(|| panic!("unbound continuation delivery arg {} for callee_sid={}", i, callee_sid));
        let repr = callee_param_reprs[i];
        body.push_binding_as_abi_arg(&mut delivered_args, binding, repr);
        mid_flight_arg_shapes.push(MidFlightArgShape::Value(repr));
    }

    let semantic_cap_vars = args.iter().skip(extra_params).copied().collect::<Vec<_>>();
    let semantic_cap_bindings = semantic_cap_vars
        .iter()
        .enumerate()
        .map(|(i, arg)| closure_capture_for_var_as(body, var_env, arg.0, callee_param_reprs[extra_params + i]))
        .collect::<Vec<_>>();
    let use_lazy = continuation_uses_lazy_descriptor(t, env, &semantic_cap_vars);
    let payload = ContinuationPayload::from_parts(env, callee_sid, semantic_cap_bindings, vec![], vec![]);
    let self_arg = plan_closure_shaped_continuation(payload, use_lazy).emit_value(body, is_cont_fn, cont_param);
    delivered_args.push(self_arg);
    mid_flight_arg_shapes.push(MidFlightArgShape::HeapRef);

    let code = body.closure_code_ref(self_arg);
    let mut sig = Signature::new(CallConv::Tail);
    for repr in callee_param_reprs.iter().take(extra_params).copied() {
        push_repr_param(&mut sig, repr);
    }
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    let sig_ref = body.b.import_signature(sig);
    if is_back_edge {
        emit_back_edge_yield_check(body, env, callee_sid, &mid_flight_arg_shapes, &delivered_args);
    }
    let call_inst = body.b.ins().call_indirect(sig_ref, code, &delivered_args);
    let result = body.b.inst_results(call_inst)[0];
    body.b.ins().return_(&[result]);
}

enum ContinuationPlan {
    LazyNativeDescriptor(ContinuationPayload),
    HeapClosure(ContinuationPayload),
}

struct ContinuationPayload {
    cont_fid: FuncId,
    semantic_cap_bindings: Vec<ClosureCapture>,
    physical_ref_captures: Vec<ir::Value>,
    materialization_ref_captures: Vec<ir::Value>,
}

impl ContinuationPayload {
    fn from_parts(
        env: &CodegenEnv<'_>,
        cont_sid: u32,
        semantic_cap_bindings: Vec<ClosureCapture>,
        physical_ref_captures: Vec<ir::Value>,
        materialization_ref_captures: Vec<ir::Value>,
    ) -> Self {
        let cont_fid = *env.fn_ids.get(&cont_sid).expect("cont fn_id missing");
        Self {
            cont_fid,
            semantic_cap_bindings,
            physical_ref_captures,
            materialization_ref_captures,
        }
    }

    fn from_capture_vars<M: cranelift_module::Module>(
        body: &mut CodegenFn<'_, '_, M>,
        env: &CodegenEnv<'_>,
        var_env: &HashMap<u32, CodegenValue>,
        cont_sid: u32,
        captures: &[Var],
    ) -> Self {
        let extras_count = continuation_entry_extra_count(env.body_native(cont_sid));
        let cap_bindings = captures
            .iter()
            .enumerate()
            .map(|(i, cv)| {
                let repr = env.param_reprs[cont_sid as usize]
                    .get(extras_count + i)
                    .copied()
                    .unwrap_or(ArgRepr::ValueRef);
                closure_capture_for_var_as(body, var_env, cv.0, repr)
            })
            .collect();
        Self::from_parts(env, cont_sid, cap_bindings, vec![], vec![])
    }

    fn ref_captures(&self) -> Vec<ir::Value> {
        self.physical_ref_captures
            .iter()
            .chain(&self.materialization_ref_captures)
            .copied()
            .collect()
    }
}

impl ContinuationPlan {
    fn lazy_native_descriptor(payload: ContinuationPayload) -> Self {
        Self::LazyNativeDescriptor(payload)
    }

    fn heap_closure(payload: ContinuationPayload) -> Self {
        Self::HeapClosure(payload)
    }

    fn uses_lazy_descriptor(&self) -> bool {
        matches!(self, Self::LazyNativeDescriptor(_))
    }

    fn emit_value<M: cranelift_module::Module>(
        &self,
        body: &mut CodegenFn<'_, '_, M>,
        is_cont_fn: bool,
        cont_param: ir::Value,
    ) -> ir::Value {
        match self {
            ContinuationPlan::LazyNativeDescriptor(payload) => {
                let ref_captures = payload.ref_captures();
                build_lazy_cont_descriptor(
                    body,
                    is_cont_fn,
                    cont_param,
                    payload.cont_fid,
                    &payload.semantic_cap_bindings,
                    &ref_captures,
                )
            }
            ContinuationPlan::HeapClosure(payload) => {
                let ref_captures = payload.ref_captures();
                build_cont_closure(
                    body,
                    is_cont_fn,
                    cont_param,
                    payload.cont_fid,
                    &payload.semantic_cap_bindings,
                    &ref_captures,
                )
            }
        }
    }
}

fn plan_closure_shaped_continuation(payload: ContinuationPayload, use_lazy: bool) -> ContinuationPlan {
    if use_lazy {
        ContinuationPlan::lazy_native_descriptor(payload)
    } else {
        ContinuationPlan::heap_closure(payload)
    }
}

// FP² borrowing/uniqueness: a continuation is stack-resident (borrows its
// captures) by default, so a destructively-matched cell it captures stays
// unique and owned-cons reuse can fire. The one exception is a capture that is
// itself a first-class closure value (a callable with a heap environment): a
// stack descriptor is not a GC root, so a cont that *owns* such a value must be
// a heap closure that the collector can trace. `match!`/known thin function
// refs (zero-capture callable boundaries) do not force the heap.
fn capture_forces_heap_continuation<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    env: &CodegenEnv<'_>,
    cv: &Var,
) -> bool {
    let Some(ty) = env.active_value_types().get(cv) else {
        return false;
    };
    if t.callable_clauses(ty).is_none() {
        return false;
    }
    !env.module.fn_by_id(env.active_body_fn_id).blocks.iter().any(|block| {
        block
            .stmts
            .iter()
            .any(|stmt| matches!(stmt, fz_ir::Stmt::Let(var, fz_ir::Prim::MakeFnRef(..)) if var == cv))
    })
}

// A newly-built continuation may live on the stack unless one of its captures
// forces it onto the GC heap (see `capture_forces_heap_continuation`). The call
// sites that build it all emit frame-persisting `call; return`, so the stack
// descriptor is invoked within the creating frame's extent and the cooperative
// yield spills it via `materialize_cont`.
fn continuation_uses_lazy_descriptor<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    env: &CodegenEnv<'_>,
    capture_vars: &[Var],
) -> bool {
    !capture_vars
        .iter()
        .any(|cv| capture_forces_heap_continuation(t, env, cv))
}

fn return_diverges(env: &CodegenEnv<'_>, body_sid: u32) -> bool {
    env.return_diverges[body_sid as usize]
}

pub(crate) fn emit_terminator<M: cranelift_module::Module, T: Types<Ty = Ty> + ClosureTypes>(
    body: &mut CodegenFn<'_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    blk: &fz_ir::Block,
    block_map: &HashMap<u32, ir::Block>,
    is_cont_fn: bool,
    this_spec_id: u32,
    caller_fn_id: FnId,
    cont_param: ir::Value,
) -> Result<(), CodegenError> {
    match &blk.terminator {
        Term::Goto(target, args) => emit_goto(body.b, var_env, block_map, target, args),
        Term::If {
            cond, then_b, else_b, ..
        } => emit_if(body, var_env, block_map, caller_fn_id, blk.id, cond, then_b, else_b),
        Term::Raise {
            exception,
            message,
            subject,
        } => emit_raise(body, var_env, *exception, *message, *subject),
        Term::Unreachable => {
            body.b.ins().trap(TrapCode::user(1).unwrap());
            Ok(())
        }
        Term::ReturnLanes(lanes) => emit_return_lanes(body, env, var_env, is_cont_fn, this_spec_id, cont_param, lanes),
        Term::Return(v) => emit_return_term(body, env, var_env, is_cont_fn, this_spec_id, cont_param, v),
        Term::Call {
            ident: _,
            callee: _,
            args,
            continuation,
        } => emit_call_term(body, t, env, var_env, blk, is_cont_fn, cont_param, args, continuation),
        Term::TailCall {
            ident: _,
            callee: _,
            args,
            is_back_edge,
        } => emit_tail_call_term(
            body,
            t,
            env,
            var_env,
            blk,
            is_cont_fn,
            this_spec_id,
            cont_param,
            args,
            *is_back_edge,
        ),
        Term::CallClosure {
            ident: _,
            closure,
            args,
            continuation,
        } => emit_call_closure(
            body,
            t,
            env,
            var_env,
            blk,
            is_cont_fn,
            cont_param,
            closure,
            args,
            continuation,
        ),
        Term::TailCallClosure {
            closure,
            args,
            ident: _,
        } => emit_tail_call_closure(body, var_env, is_cont_fn, cont_param, closure, args),
        Term::ReceiveMatched {
            clauses,
            after,
            pinned,
            captures,
            dispatch: _,
            ident: _,
        } => emit_receive_matched(
            body,
            env,
            var_env,
            blk,
            is_cont_fn,
            caller_fn_id,
            cont_param,
            clauses,
            after.as_ref(),
            pinned,
            captures,
        ),
    }
}

fn emit_goto(
    b: &mut FunctionBuilder<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    block_map: &HashMap<u32, ir::Block>,
    target: &BlockId,
    args: &[Var],
) -> Result<(), CodegenError> {
    let tgt = *block_map.get(&target.0).unwrap();
    let arg_vals: Vec<BlockArg> = args
        .iter()
        .map(|v| BlockArg::Value(var_env.get(&v.0).expect("unbound goto arg").value()))
        .collect();
    b.ins().jump(tgt, &arg_vals);
    Ok(())
}

fn emit_if<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    block_map: &HashMap<u32, ir::Block>,
    caller_fn_id: FnId,
    block_id: BlockId,
    cond: &Var,
    then_b: &BlockId,
    else_b: &BlockId,
) -> Result<(), CodegenError> {
    let no_args: Vec<BlockArg> = Vec::new();
    let t_b = block_map.get(&then_b.0).copied();
    let e_b = block_map.get(&else_b.0).copied();
    match (t_b, e_b) {
        (Some(t_b), Some(e_b)) => {
            let vb = *var_env.get(&cond.0).expect("unbound if cond");
            let truthy = if matches!(vb.repr(), ArgRepr::Condition) {
                vb.value()
            } else {
                body.value_truthy(vb)
            };
            body.b.ins().brif(truthy, t_b, &no_args, e_b, &no_args);
        }
        (Some(t_b), None) => {
            body.b.ins().jump(t_b, &no_args);
        }
        (None, Some(e_b)) => {
            body.b.ins().jump(e_b, &no_args);
        }
        (None, None) => {
            return Err(CodegenError::new(format!(
                "if terminator in caller {:?} block {:?} has no spec-reachable successor: then={:?}, else={:?}",
                caller_fn_id, block_id, then_b, else_b
            )));
        }
    }
    Ok(())
}

/// `Term::Raise` is a decision's last resort: the process raises its
/// exception through the one panic route and returns to the scheduler.
fn emit_raise<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    exception: Var,
    message: Var,
    subject: Option<Var>,
) -> Result<(), CodegenError> {
    let exception = body.any_ref_for_var(var_env, exception.0);
    let message = body.any_ref_for_var(var_env, message.0);
    let process = body.process_arg();
    match subject {
        Some(subject) => {
            let subject = body.any_ref_for_var(var_env, subject.0);
            runtime_call!(body, fz_raise_showing, [process, exception, message, subject]);
        }
        None => {
            runtime_call!(body, fz_raise, [process, exception, message]);
        }
    }
    let done = body.b.ins().iconst(types::I64, 0);
    body.b.ins().return_(&[done]);
    Ok(())
}

fn emit_return_lanes<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    is_cont_fn: bool,
    this_spec_id: u32,
    cont_param: ir::Value,
    lanes: &[Var],
) -> Result<(), CodegenError> {
    if return_diverges(env, this_spec_id) {
        body.b.ins().trap(TrapCode::user(1).unwrap());
        return Ok(());
    }
    let return_reprs = env.body_return_reprs(this_spec_id);
    if lanes.len() != return_reprs.len() {
        return Err(CodegenError::new(format!(
            "ReturnLanes arity mismatch in {}: lanes={}, return_reprs={}",
            env.active_body_name,
            lanes.len(),
            return_reprs.len()
        )));
    }
    let cont_val = resolve_outer_cont(body, is_cont_fn, cont_param);
    let code = body.closure_code_ref(cont_val);
    let mut sig = Signature::new(CallConv::Tail);
    let mut cont_args = Vec::with_capacity(lanes.len() + 1);
    for (lane, repr) in lanes.iter().copied().zip(return_reprs.iter().copied()) {
        let binding = *var_env.get(&lane.0).expect("unbound return lane");
        push_repr_param(&mut sig, repr);
        body.push_binding_as_abi_arg(&mut cont_args, binding, repr);
    }
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    let sigref = body.b.import_signature(sig);
    cont_args.push(cont_val);
    body.b.ins().return_call_indirect(sigref, code, &cont_args);
    Ok(())
}

fn emit_return_term<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    is_cont_fn: bool,
    this_spec_id: u32,
    cont_param: ir::Value,
    v: &Var,
) -> Result<(), CodegenError> {
    let cont_val = resolve_outer_cont(body, is_cont_fn, cont_param);
    let return_reprs = env.body_return_reprs(this_spec_id);
    if return_diverges(env, this_spec_id) {
        body.b.ins().trap(TrapCode::user(1).unwrap());
    } else if return_reprs.is_empty() {
        let code = body.closure_code_ref(cont_val);
        let mut sig = Signature::new(CallConv::Tail);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let sigref = body.b.import_signature(sig);
        body.b.ins().return_call_indirect(sigref, code, &[cont_val]);
    } else if let [my_return_repr] = return_reprs.as_slice() {
        let binding = *var_env.get(&v.0).expect("unbound return val");
        let code = body.closure_code_ref(cont_val);
        let mut sig = Signature::new(CallConv::Tail);
        push_repr_param(&mut sig, *my_return_repr);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let sigref = body.b.import_signature(sig);
        let mut cont_args = Vec::with_capacity(2);
        body.push_binding_as_abi_arg(&mut cont_args, binding, *my_return_repr);
        cont_args.push(cont_val);
        body.b.ins().return_call_indirect(sigref, code, &cont_args);
    } else {
        panic!(
            "native multi-lane return must lower as Term::ReturnLanes, got {} lane(s) through scalar v{}",
            return_reprs.len(),
            v.0
        );
    }
    Ok(())
}

// Term::Call: builds the cont closure before the callee call so the callee's
// Term::Return can indirect-call through it (docs/cps-in-clif.md §2.1).
fn emit_call_term<M: cranelift_module::Module, T: Types<Ty = Ty> + ClosureTypes>(
    body: &mut CodegenFn<'_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    blk: &fz_ir::Block,
    is_cont_fn: bool,
    cont_param: ir::Value,
    args: &[Var],
    continuation: &Cont,
) -> Result<(), CodegenError> {
    let callee_sid = resolve_callee_sid(env, blk, EmitSlot::Direct);
    let cont_sid = resolve_cont_sid(env, blk);
    let fn_ids = env.fn_ids;
    let param_reprs = env.param_reprs;
    // Coerce each arg from its current var repr to the callee's param_repr.
    // The result rides back to the cont in the callee's return_repr.
    let callee_param_reprs = &param_reprs[callee_sid as usize];
    let callee_fid = *fn_ids.get(&callee_sid).expect("callee fn_id missing");
    let callee_fref = body.jmod.declare_func_in_func(callee_fid, body.b.func);
    let mut native_args = body.coerce_call_args(args, callee_param_reprs, var_env);
    let use_lazy = continuation_uses_lazy_descriptor(t, env, &continuation.captured);
    let payload = ContinuationPayload::from_capture_vars(body, env, var_env, cont_sid, &continuation.captured);
    let continuation_plan = plan_closure_shaped_continuation(payload, use_lazy);
    native_args.push(continuation_plan.emit_value(body, is_cont_fn, cont_param));
    if continuation_plan.uses_lazy_descriptor() {
        let inst = body.b.ins().call(callee_fref, &native_args);
        let result = body.b.inst_results(inst)[0];
        body.b.ins().return_(&[result]);
    } else {
        body.b.ins().return_call(callee_fref, &native_args);
    }
    Ok(())
}

// Term::TailCall ABI emission. The planned ABI facts guarantee callee's
// return_repr matches mine, so return_call is ABI-compatible.
fn emit_tail_call_term<M: cranelift_module::Module, T: Types<Ty = Ty> + ClosureTypes>(
    body: &mut CodegenFn<'_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    blk: &fz_ir::Block,
    is_cont_fn: bool,
    this_spec_id: u32,
    cont_param: ir::Value,
    args: &[Var],
    is_back_edge: bool,
) -> Result<(), CodegenError> {
    let callee_sid = resolve_callee_sid(env, blk, EmitSlot::Direct);
    let fn_ids = env.fn_ids;
    let param_reprs = env.param_reprs;
    if let NativeEntryAbi::Continuation { extra_params } = env.body_native(callee_sid).entry_abi {
        emit_native_continuation_tail_delivery(
            body,
            t,
            env,
            var_env,
            is_cont_fn,
            cont_param,
            args,
            is_back_edge,
            callee_sid,
            extra_params,
        );
        return Ok(());
    }
    let callee_param_reprs = &param_reprs[callee_sid as usize];
    let callee_fid = *fn_ids.get(&callee_sid).expect("callee fn_id missing");
    let callee_fref = body.jmod.declare_func_in_func(callee_fid, body.b.func);
    let callee_return_reprs = env.body_return_reprs(callee_sid);
    let caller_return_reprs = env.body_return_reprs(this_spec_id);
    let mut native_args = Vec::with_capacity(callee_param_reprs.iter().map(ArgRepr::abi_arity).sum());
    let mut mid_flight_arg_shapes: Vec<MidFlightArgShape> = Vec::with_capacity(callee_param_reprs.len() + 2);
    for (i, av) in args.iter().enumerate() {
        let binding = *var_env.get(&av.0).unwrap_or_else(|| {
            panic!(
                "unbound call arg {:?}; callee_sid={}; args={:?}; bound={:?}",
                av,
                callee_sid,
                args,
                var_env.keys().copied().collect::<Vec<_>>()
            )
        });
        let to = callee_param_reprs[i];
        body.push_binding_as_abi_arg(&mut native_args, binding, to);
        mid_flight_arg_shapes.push(MidFlightArgShape::Value(to));
    }
    // Trailing cont arg (docs/cps-in-clif.md §2.1): cont fns forward the
    // outer_cont from their closure env; every other fn forwards its own cont.
    let caller_outer_cont = resolve_outer_cont(body, is_cont_fn, cont_param);
    let tail_cont_arg = if return_diverges(env, callee_sid) || callee_return_reprs == caller_return_reprs {
        caller_outer_cont
    } else {
        panic!(
            "native tail delivery requires exact transport return-lane agreement: callee={:?}, caller={:?}",
            callee_return_reprs, caller_return_reprs
        );
    };
    native_args.push(tail_cont_arg);
    mid_flight_arg_shapes.push(MidFlightArgShape::HeapRef);
    let expected_arg_count = expected_native_tail_arg_count(callee_param_reprs);
    assert_eq!(
        native_args.len(),
        expected_arg_count,
        "native tail-call arg lanes must match the published callee ABI contract; caller_sid={this_spec_id}; callee_sid={callee_sid}; term_args={args:?}; callee_param_reprs={callee_param_reprs:?}",
    );
    // return_call so recursive tail calls reuse the same stack frame (TCO).
    // Without this, count_100k blows the stack.
    //
    // Back-edge cooperative yield check: every native loop spends
    // reductions, including pure scalar loops that do not allocate.
    if is_back_edge {
        emit_back_edge_yield_check(body, env, callee_sid, &mid_flight_arg_shapes, &native_args);
    }
    body.b.ins().return_call(callee_fref, &native_args);
    Ok(())
}

fn expected_native_tail_arg_count(callee_param_reprs: &[ArgRepr]) -> usize {
    callee_param_reprs.iter().map(ArgRepr::abi_arity).sum::<usize>() + 1
}

// Cooperative back-edge yield check: spend one reduction from the
// scheduler-installed budget; if exhausted, capture next-iteration args into a
// scheduler-runnable closure and yield it as the primary mid-flight root.
// Otherwise fall through to the caller's normal TCO path.
fn emit_back_edge_yield_check<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    callee_sid: u32,
    mid_flight_arg_shapes: &[MidFlightArgShape],
    native_args: &[ir::Value],
) {
    let process = body.b.ins().get_pinned_reg(types::I64);
    let reductions_ptr = body
        .b
        .ins()
        .iadd_imm(process, PROCESS_REDUCTIONS_REMAINING_OFFSET as i64);
    let remaining = body.b.ins().load(types::I32, MemFlags::trusted(), reductions_ptr, 0);
    let one = body.b.ins().iconst(types::I32, 1);
    let new_remaining = body.b.ins().isub(remaining, one);
    body.b
        .ins()
        .store(MemFlags::trusted(), new_remaining, reductions_ptr, 0);
    let exhausted = body.b.ins().icmp_imm(IntCC::SignedLessThanOrEqual, new_remaining, 0);
    let yield_blk = body.b.create_block();
    let proceed_blk = body.b.create_block();
    let no_args: Vec<BlockArg> = Vec::new();
    body.b.ins().brif(exhausted, yield_blk, &no_args, proceed_blk, &no_args);

    body.b.switch_to_block(yield_blk);
    body.b.seal_block(yield_blk);
    let cont_key = (callee_sid, mid_flight_arg_shapes.to_vec());
    let cont_id = *env.mid_flight_cont_tail_fn_ids.get(&cont_key).unwrap_or_else(|| {
        panic!(
            "missing mid-flight continuation tail for {:?}; available {:?}",
            cont_key,
            env.mid_flight_cont_tail_fn_ids.keys().collect::<Vec<_>>()
        )
    });
    let mut abi_cursor = 0;
    let native_root_values: Vec<CodegenValue> = mid_flight_arg_shapes
        .iter()
        .map(|shape| {
            let root = shape.capture_from_args(body.b, native_args, abi_cursor);
            abi_cursor += shape.abi_arity();
            root
        })
        .collect();
    debug_assert_eq!(abi_cursor, native_args.len());
    let process = body.process_arg();
    runtime_call!(body, fz_yield_slow_path_begin, [process]);
    let cont_arity = body.b.ins().iconst(types::I32, CONT_ARITY);
    let n_caps_v = body.b.ins().iconst(types::I32, native_root_values.len() as i64);
    let stub_fref = body.jmod.declare_func_in_func(cont_id, body.b.func);
    let stub_addr = body.b.ins().func_addr(types::I64, stub_fref);
    let zero_hk = body.b.ins().iconst(types::I32, 0);
    let cont_closure = body.alloc_closure(
        fz_runtime::any_value::ClosureDenotationId::INTERNAL,
        cont_arity,
        n_caps_v,
        zero_hk,
        stub_addr,
    );
    let last_root = native_root_values.len().saturating_sub(1);
    for (i, root) in native_root_values.iter().copied().enumerate() {
        let mut root_ref = body.value_as_any_ref(root);
        if i == last_root {
            root_ref = body.materialize_cont(root_ref);
        }
        body.store_closure_capture_ref_word(cont_closure, i, root_ref);
    }
    let reason = body.b.ins().iconst(types::I32, YIELD_REASON_REDUCTIONS as i64);
    let yield_ret = runtime_call1!(
        body,
        fz_yield_mid_flight_report,
        [process, cont_closure, new_remaining, reason]
    );
    body.b.ins().return_(&[yield_ret]);

    body.b.switch_to_block(proceed_blk);
    body.b.seal_block(proceed_blk);
}

fn emit_call_closure<M: cranelift_module::Module, T: Types<Ty = Ty> + ClosureTypes>(
    body: &mut CodegenFn<'_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    blk: &fz_ir::Block,
    is_cont_fn: bool,
    cont_param: ir::Value,
    closure: &Var,
    args: &[Var],
    continuation: &Cont,
) -> Result<(), CodegenError> {
    // Closure invocation is opaque to the caller: read code_ptr
    // through the runtime ABI and call it with args, self, and cont.
    let closure_binding = *var_env.get(&closure.0).expect("unbound callclosure closure");
    let cl_val = body.value_as_any_ref(closure_binding);
    let arg_vals: Vec<ir::Value> = args
        .iter()
        .map(|v| var_env.get(&v.0).expect("unbound callclosure arg").value())
        .collect();
    let cont_sid = resolve_cont_sid(env, blk);
    let cont_payload = ContinuationPayload::from_capture_vars(body, env, var_env, cont_sid, &continuation.captured);
    let can_use_lazy_cont = continuation_uses_lazy_descriptor(t, env, &continuation.captured);
    let continuation_plan = plan_closure_shaped_continuation(cont_payload, can_use_lazy_cont);
    let cf = continuation_plan.emit_value(body, is_cont_fn, cont_param);
    // Load body address from the closure and
    // Tail-CC indirect-call with closure-target sig
    // `(args..., self, cont) -> i64 tail` (all-ValueRef params).
    // A lazy cont lives in this frame, so the call returns here;
    // a heap cont tail-calls (TCO via return_call_indirect).
    let body_fp = body.closure_code_ref(cl_val);
    let mut sig = Signature::new(CallConv::Tail);
    for _ in &arg_vals {
        push_repr_param(&mut sig, ArgRepr::ValueRef);
    }
    sig.params.push(AbiParam::new(types::I64)); // self
    sig.params.push(AbiParam::new(types::I64)); // cont
    sig.returns.push(AbiParam::new(types::I64));
    let sig_ref = body.b.func.import_signature(sig);
    let mut indirect_args: Vec<ir::Value> = Vec::with_capacity(arg_vals.len() + 2);
    for (i, _v) in arg_vals.iter().enumerate() {
        let binding = *var_env.get(&args[i].0).expect("unbound callclosure arg");
        body.push_binding_as_abi_arg(&mut indirect_args, binding, ArgRepr::ValueRef);
    }
    indirect_args.push(cl_val);
    indirect_args.push(cf);
    if can_use_lazy_cont {
        let call_inst = body.b.ins().call_indirect(sig_ref, body_fp, &indirect_args);
        let result = body.b.inst_results(call_inst)[0];
        body.b.ins().return_(&[result]);
    } else {
        body.b.ins().return_call_indirect(sig_ref, body_fp, &indirect_args);
    }
    Ok(())
}

fn emit_tail_call_closure<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    is_cont_fn: bool,
    cont_param: ir::Value,
    closure: &Var,
    args: &[Var],
) -> Result<(), CodegenError> {
    // Tail-CC indirect-call through the closure code ptr with the
    // caller's own cont (TCO via return_call_indirect). Closure-
    // target sig `(args..., self, cont) -> i64 tail`. For cont fns
    // the forwarded cont is the env's outer_cont; every other fn
    // forwards cont_param.
    let closure_binding = *var_env.get(&closure.0).expect("unbound tailcallclosure closure");
    let cl_val = body.value_as_any_ref(closure_binding);
    let arg_vals: Vec<ir::Value> = args
        .iter()
        .map(|v| var_env.get(&v.0).expect("unbound tailcallclosure arg").value())
        .collect();
    let my_cont = resolve_outer_cont(body, is_cont_fn, cont_param);

    let body_fp = body.closure_code_ref(cl_val);
    let mut sig = Signature::new(CallConv::Tail);
    for _ in &arg_vals {
        push_repr_param(&mut sig, ArgRepr::ValueRef);
    }
    sig.params.push(AbiParam::new(types::I64)); // self
    sig.params.push(AbiParam::new(types::I64)); // cont
    sig.returns.push(AbiParam::new(types::I64));
    let sig_ref = body.b.func.import_signature(sig);
    let mut indirect_args: Vec<ir::Value> = Vec::with_capacity(arg_vals.len() + 2);
    for (i, _v) in arg_vals.iter().enumerate() {
        let binding = *var_env.get(&args[i].0).expect("unbound tailcallclosure arg");
        body.push_binding_as_abi_arg(&mut indirect_args, binding, ArgRepr::ValueRef);
    }
    indirect_args.push(cl_val);
    indirect_args.push(my_cont);
    body.b.ins().return_call_indirect(sig_ref, body_fp, &indirect_args);
    Ok(())
}

// Selective-receive park-site CLIF.
//
// Layout, mirroring fz_runtime::park::ParkRecord:
//   - matcher fn addr (declared/emitted from the receive dispatch plan).
//   - pinned[]: plan-indexed pinned inputs followed by prepared keys.
//   - clause_bodies[]: i64 array of cont-closure refs,
//     one per source clause; each closure carries the clause-body
//     fn entry, while captures are populated through closure
//     accessors in source order (ContinuationPlan handles all
//     bookkeeping).
//   - clause_bound_counts[]: i64 array, one per source clause.
//     The matcher scratch uses max bound_arity; the resumed
//     outcome env uses only the winning edge's semantic/physical arguments.
//   - bound_arity: max outcome-argument count across clauses; sizes
//     the `out` buffer the matcher fills on a hit.
//   - after_deadline_or_neg1: -1 when no after clause,
//     else the unboxed timeout in ms.
//   - after_cont: closure ptr when after is Some, else null.
//
// After laying these out the helper calls fz_receive_park_matched, which
// decides the receive. Anything but the YIELD sentinel is the closure to run
// next (the matched clause, or the `after 0` body): the receive tail-calls
// it. The sentinel is returned so the trampoline parks.
fn emit_receive_matched<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    blk: &fz_ir::Block,
    is_cont_fn: bool,
    caller_fn_id: FnId,
    cont_param: ir::Value,
    clauses: &[ReceiveClause],
    after: Option<&ReceiveAfter>,
    pinned: &[Var],
    captures: &[Var],
) -> Result<(), CodegenError> {
    let dispatch_fid = *env
        .receive_dispatch_fn_ids
        .get(&(caller_fn_id.0, blk.id.0))
        .expect("receive dispatch fn pre-declared by planned codegen pass");
    let dispatch_addr = fn_addr(body.jmod, dispatch_fid, body.b);
    let park_result = build_park_record(
        body,
        env,
        var_env,
        is_cont_fn,
        cont_param,
        clauses,
        after,
        pinned,
        captures,
        dispatch_addr,
    );
    let yield_sentinel = body.b.ins().iconst(types::I64, YIELD_PTR as i64);
    let parked = body.b.ins().icmp(IntCC::Equal, park_result, yield_sentinel);
    let yield_blk = body.b.create_block();
    let run_blk = body.b.create_block();
    let no_args: Vec<BlockArg> = Vec::new();
    body.b.ins().brif(parked, yield_blk, &no_args, run_blk, &no_args);

    body.b.switch_to_block(yield_blk);
    body.b.seal_block(yield_blk);
    body.b.ins().return_(&[park_result]);

    body.b.switch_to_block(run_blk);
    body.b.seal_block(run_blk);
    emit_resume_closure(body, park_result);
    Ok(())
}

// Run a zero-arg outcome closure the way `fz_resume` does: Tail-CC call
// through its code pointer with the closure as `self`.
fn emit_resume_closure<M: cranelift_module::Module>(body: &mut CodegenFn<'_, '_, M>, closure: ir::Value) {
    let code = body.closure_code_ref(closure);
    let mut sig = Signature::new(CallConv::Tail);
    sig.params.push(AbiParam::new(types::I64)); // self
    sig.returns.push(AbiParam::new(types::I64));
    let sig_ref = body.b.func.import_signature(sig);
    body.b.ins().return_call_indirect(sig_ref, code, &[closure]);
}

// Lay out the ParkRecord fields described in
// `fz_runtime::park::ParkRecord` (pinned inputs, clause cont
// closures, optional after closure, bound-arity), then call
// fz_receive_park_matched and return its result.
fn build_park_record<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    is_cont_fn: bool,
    cont_param: ir::Value,
    clauses: &[ReceiveClause],
    after: Option<&ReceiveAfter>,
    pinned: &[Var],
    captures: &[Var],
    matcher_addr: ir::Value,
) -> ir::Value {
    use cranelift_codegen::ir::{StackSlotData, StackSlotKind};

    // Pinned inputs: alloca [AnyValueRef; n_pinned], take base addr.
    let n_pinned = pinned.len();
    let pinned_ptr = if n_pinned == 0 {
        body.b.ins().iconst(types::I64, 0)
    } else {
        let slot = body.b.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            (n_pinned * SLOT_BYTES as usize) as u32,
            3,
        ));
        for (i, v) in pinned.iter().enumerate() {
            let value_ref = body.tagged_var(var_env, v.0);
            body.b
                .ins()
                .stack_store(value_ref, slot, (i * SLOT_BYTES as usize) as i32);
        }
        body.b.ins().stack_addr(types::I64, slot, 0)
    };

    // Capture operands, shared across every clause body /
    // guard / after closure. `Term::ReceiveMatched::captures`
    // is already deduplicated by ir_lower; the cont fns'
    // capture-param slots line up with this order.
    let cap_bindings: Vec<ClosureCapture> = captures
        .iter()
        .map(|cv| closure_capture_for_var(body, var_env, cv.0))
        .collect();
    // bound_arity: max outcome-argument count across clauses (matcher
    // ABI sizes the out buffer to this).
    let bound_arity = clauses.iter().map(|c| c.arguments.len()).max().unwrap_or(0);

    // clause_bodies[]: build one cont-closure per clause body
    // and stack-store its ptr.
    let n_clauses = clauses.len();
    assert!(
        n_clauses > 0,
        "ReceiveMatched with zero clauses should not reach codegen"
    );
    let bodies_slot = body.b.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        (n_clauses * SLOT_BYTES as usize) as u32,
        3,
    ));
    let needs_bound_counts = clauses.iter().any(|c| c.arguments.len() != bound_arity);
    let bound_counts_slot = needs_bound_counts.then(|| {
        body.b.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            (n_clauses * SLOT_BYTES as usize) as u32,
            3,
        ))
    });
    let resolve_body_sid = |body: FnId| -> u32 {
        env.body_id_for_fn(body)
            .unwrap_or_else(|| panic!("native receive outcome fn {} has no registered codegen body id", body.0))
    };
    for (i, c) in clauses.iter().enumerate() {
        let cont_sid = resolve_body_sid(c.body);
        let payload = ContinuationPayload::from_parts(env, cont_sid, cap_bindings.clone(), vec![], vec![]);
        let cl_ptr = ContinuationPlan::heap_closure(payload).emit_value(body, is_cont_fn, cont_param);
        body.b.ins().stack_store(cl_ptr, bodies_slot, (i * 8) as i32);
        if let Some(slot) = bound_counts_slot {
            let bound_count_v = body.b.ins().iconst(types::I64, c.arguments.len() as i64);
            body.b.ins().stack_store(bound_count_v, slot, (i * 8) as i32);
        }
    }
    let bodies_ptr = body.b.ins().stack_addr(types::I64, bodies_slot, 0);
    let bound_counts_ptr = if let Some(slot) = bound_counts_slot {
        body.b.ins().stack_addr(types::I64, slot, 0)
    } else {
        body.b.ins().iconst(types::I64, 0)
    };

    // After: build the after closure if present and unbox the
    // timeout from its tagged Int. `-1` sentinel when no after.
    let (after_deadline_v, after_cont_v) = match after {
        Some(a) => {
            let cont_sid = resolve_body_sid(a.body);
            let payload = ContinuationPayload::from_parts(env, cont_sid, cap_bindings, vec![], vec![]);
            let cl_ptr = ContinuationPlan::heap_closure(payload).emit_value(body, is_cont_fn, cont_param);
            let unboxed = body.as_raw_i64(var_env, a.timeout.0);
            (unboxed, cl_ptr)
        }
        None => {
            let neg1 = body.b.ins().iconst(types::I64, -1);
            let nullp = body.b.ins().iconst(types::I64, 0);
            (neg1, nullp)
        }
    };

    let n_pinned_v = body.b.ins().iconst(types::I64, n_pinned as i64);
    let n_clauses_v = body.b.ins().iconst(types::I64, n_clauses as i64);
    let bound_arity_v = body.b.ins().iconst(types::I32, bound_arity as i64);

    let process = body.process_arg();
    let park_inst = runtime_call!(
        body,
        fz_receive_park_matched,
        [
            process,
            matcher_addr,
            pinned_ptr,
            n_pinned_v,
            bodies_ptr,
            n_clauses_v,
            bound_counts_ptr,
            bound_arity_v,
            after_deadline_v,
            after_cont_v,
        ]
    );
    body.b.inst_results(park_inst)[0]
}
