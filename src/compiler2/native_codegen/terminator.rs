//! Terminator emission for fz IR blocks.

use super::*;
use crate::fz_ir::{
    self as fz_ir, BlockId, Cont, DirectCallTarget, EmitSlot, FnId, ReceiveAfter, ReceiveClause, Term, Var,
};
use crate::types::{ClosureTypes, Types};
use crate::{measurements, metadata};
use cranelift_codegen::ir::{self, AbiParam, BlockArg, InstBuilder, MemFlags, Signature, condcodes::IntCC, types};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::FunctionBuilder;
use cranelift_module::FuncId;
use fz_runtime::heap::Schema;
use fz_runtime::process::YIELD_REASON_REDUCTIONS;
use fz_runtime::process_abi::PROCESS_REDUCTIONS_REMAINING_OFFSET;
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

fn resolve_native_closure_sid(env: &CodegenEnv<'_>, block_id: BlockId) -> Option<u32> {
    let target_fn = env.active_native_body().closure_call_targets.get(&block_id).copied()?;
    env.body_id_for_fn(target_fn)
}

fn callee_is_native(env: &CodegenEnv<'_>, id: u32) -> bool {
    env.native_abi_fns.contains(&FnId(id))
}

fn spec_fn_id(env: &CodegenEnv<'_>, sid: u32) -> FnId {
    env.body_fn_id(sid)
}

fn spec_is_native(env: &CodegenEnv<'_>, sid: u32) -> bool {
    callee_is_native(env, spec_fn_id(env, sid).0)
}

enum ContinuationPlan {
    LazyNativeDescriptor(ContinuationPayload),
    HeapClosure(ContinuationPayload),
}

struct ContinuationPayload {
    cont_sid: u32,
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
            cont_sid,
            cont_fid,
            semantic_cap_bindings,
            physical_ref_captures,
            materialization_ref_captures,
        }
    }

    fn from_capture_vars<M: cranelift_module::Module>(
        body: &mut CodegenFn<'_, '_, '_, M>,
        env: &CodegenEnv<'_>,
        var_env: &HashMap<u32, CodegenValue>,
        cont_sid: u32,
        captures: &[Var],
    ) -> Self {
        let demand_abi = NativeDemandAbi::new(env.body_native(cont_sid));
        let extras_count = demand_abi.continuation_extras();
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

    fn uses_heap_closure(&self) -> bool {
        matches!(self, Self::HeapClosure(_))
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_value<M: cranelift_module::Module>(
        &self,
        body: &mut CodegenFn<'_, '_, '_, M>,
        runtime: &RuntimeRefs,
        return_reprs: &[ArgRepr],
        is_cont_fn: bool,
        cont_param: Option<ir::Value>,
        frame_ptr: Option<ir::Value>,
    ) -> ir::Value {
        match self {
            ContinuationPlan::LazyNativeDescriptor(payload) => {
                let ref_captures = payload.ref_captures();
                build_lazy_cont_descriptor(
                    body,
                    runtime,
                    return_reprs,
                    is_cont_fn,
                    cont_param,
                    frame_ptr,
                    payload.cont_sid,
                    payload.cont_fid,
                    &payload.semantic_cap_bindings,
                    &ref_captures,
                )
            }
            ContinuationPlan::HeapClosure(payload) => {
                let ref_captures = payload.ref_captures();
                build_cont_closure(
                    body,
                    runtime,
                    return_reprs,
                    is_cont_fn,
                    cont_param,
                    frame_ptr,
                    payload.cont_sid,
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

fn native_call_result_value<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    result: ir::Value,
    repr: ArgRepr,
) -> CodegenValue {
    match repr {
        ArgRepr::RawF64 => CodegenValue::RawF64(body.b.ins().bitcast(types::F64, MemFlags::new(), result)),
        _ => CodegenValue::from_abi_value(result, repr),
    }
}

fn build_boundary_return_adapter_cont<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    outer_cont: ir::Value,
    source: ArgRepr,
    dest: ArgRepr,
) -> ir::Value {
    let adapter_id = env.boundary_return_adapters.id_for(source, dest).unwrap_or_else(|| {
        panic!(
            "missing boundary return adapter for {} -> {}",
            source.as_str(),
            dest.as_str()
        )
    });
    let adapter_addr = fn_addr(body.jmod, adapter_id, body.b);
    let adapter_schema = body.b.ins().iconst(types::I32, 0);
    let captured_count = body.b.ins().iconst(types::I32, 1);
    let halt_kind = body.b.ins().iconst(types::I32, 0);
    let adapter_cont = body.alloc_closure(adapter_schema, captured_count, halt_kind, adapter_addr);
    let outer_cont = body.materialize_cont(outer_cont);
    body.store_closure_capture_ref_word(adapter_cont, 0, outer_cont);
    adapter_cont
}

fn returned_shape(env: &CodegenEnv<'_>, body_sid: u32, is_cont_fn: bool) -> DeliveredShape {
    NativeDemandAbi::new(env.body_native(body_sid)).returned_shape(is_cont_fn)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn emit_terminator<M: cranelift_module::Module, T: Types<Ty = Ty> + ClosureTypes>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    schemas: &[Schema],
    var_env: &HashMap<u32, CodegenValue>,
    blk: &fz_ir::Block,
    block_map: &HashMap<u32, ir::Block>,
    is_native: bool,
    is_cont_fn: bool,
    this_spec_id: u32,
    caller_fn_id: FnId,
    cont_ptr_known_null: bool,
    frame_ptr: Option<ir::Value>,
    host_ctx: Option<ir::Value>,
    cont_param: Option<ir::Value>,
    var_types: &HashMap<Var, Ty>,
    block_env: Option<&HashMap<Var, Ty>>,
) -> Result<(), CodegenError> {
    match &blk.terminator {
        Term::Goto(target, args) => emit_goto(body.b, var_env, block_map, target, args),
        Term::If {
            cond, then_b, else_b, ..
        } => emit_if(body, var_env, block_map, caller_fn_id, blk.id, cond, then_b, else_b),
        Term::Halt(v) => emit_halt(body, var_env, is_native, host_ctx, v),
        Term::Return(v) => emit_return_term(
            body,
            t,
            env,
            var_env,
            var_types,
            block_env,
            is_native,
            is_cont_fn,
            this_spec_id,
            caller_fn_id,
            cont_ptr_known_null,
            frame_ptr,
            cont_param,
            v,
        ),
        Term::Call {
            ident: _,
            callee,
            args,
            continuation,
        } => emit_call_term(
            body,
            env,
            schemas,
            var_env,
            blk,
            is_native,
            is_cont_fn,
            this_spec_id,
            frame_ptr,
            cont_param,
            callee,
            args,
            continuation,
        ),
        Term::TailCall {
            ident: _,
            callee,
            args,
            is_back_edge,
        } => emit_tail_call_term(
            body,
            env,
            schemas,
            var_env,
            blk,
            is_native,
            is_cont_fn,
            this_spec_id,
            frame_ptr,
            host_ctx,
            cont_param,
            callee,
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
            env,
            var_env,
            blk,
            is_native,
            is_cont_fn,
            frame_ptr,
            host_ctx,
            cont_param,
            closure,
            args,
            continuation,
        ),
        Term::TailCallClosure {
            closure,
            args,
            ident: _,
        } => emit_tail_call_closure(
            body, env, var_env, blk, is_native, is_cont_fn, frame_ptr, host_ctx, cont_param, closure, args,
        ),
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
            frame_ptr,
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

#[allow(clippy::too_many_arguments)]
fn emit_if<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
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

#[allow(clippy::too_many_arguments)]
fn emit_halt<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    is_native: bool,
    host_ctx: Option<ir::Value>,
    v: &Var,
) -> Result<(), CodegenError> {
    let _ = host_ctx;
    let binding = *var_env.get(&v.0).expect("unbound halt val");
    emit_halt_for_binding(body, var_env, v.0, binding);
    if is_native {
        // fz_halt already recorded process.halt_value; the
        // returned bits are unobservable but the sig requires
        // a typed return. iconst(0) also covers dead-code halt
        // blocks (match_error etc.) without depending on val's repr.
        let zero = body.b.ins().iconst(types::I64, 0);
        body.b.ins().return_(&[zero]);
    } else {
        // Uniform fn: trampoline sentinel is null.
        let null = body.b.ins().iconst(types::I64, 0);
        body.b.ins().return_(&[null]);
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn emit_return_term<M: cranelift_module::Module, T: Types<Ty = Ty> + ClosureTypes>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    var_types: &HashMap<Var, Ty>,
    _block_env: Option<&HashMap<Var, Ty>>,
    is_native: bool,
    is_cont_fn: bool,
    this_spec_id: u32,
    caller_fn_id: FnId,
    cont_ptr_known_null: bool,
    frame_ptr: Option<ir::Value>,
    cont_param: Option<ir::Value>,
    v: &Var,
) -> Result<(), CodegenError> {
    let closure_capture_counts = env.closure_capture_counts;
    {
        if is_native {
            let return_abi = NativeDemandAbi::new(env.body_native(this_spec_id));
            if let Some(arity) = return_abi.returned_tuple_field_arity(is_cont_fn)
                && let Some(fields) = body.cache.tuple_return_fields.get(&v.0)
            {
                let fields = fields.clone();
                debug_assert_eq!(fields.len(), arity);
                let cont_val = if is_cont_fn {
                    let self_val = cont_param.expect("cont fn binds self via cont_param");
                    body.outer_cont_ref(self_val)
                } else {
                    cont_param.expect("non-cont native fn has cont_param")
                };
                let code = body.closure_code_ref(cont_val);
                let mut sig = Signature::new(CallConv::Tail);
                let mut cont_args = Vec::with_capacity(fields.len() + 1);
                for field in fields {
                    let binding = *var_env.get(&field.0).expect("unbound tuple return field");
                    let repr = var_types
                        .get(&field)
                        .map(|ty| ArgRepr::from_ty(t, ty))
                        .unwrap_or_else(|| binding.repr());
                    push_repr_param(&mut sig, repr);
                    body.push_binding_as_abi_arg(&mut cont_args, binding, repr);
                }
                sig.params.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
                let sigref = body.b.import_signature(sig);
                cont_args.push(cont_val);
                body.b.ins().return_call_indirect(sigref, code, &cont_args);
                return Ok(());
            }
            // Native Term::Return (see docs/cps-in-clif.md §2.1): read
            // cont code_ptr; return_call_indirect sig(val, cont). Cont
            // fns fetch outer_cont from `self`; non-cont fns use their
            // cont_param SSA. Sig and val coerce match this fn's
            // narrow return_repr — chosen at construction to match.
            //
            // ReturnDemand selects the return shape; return_reprs selects
            // the wire representation for the single delivered lane.
            let _ = (&closure_capture_counts, caller_fn_id);
            assert!(
                return_abi.returned_delivers_value_lane(is_cont_fn),
                "native return must deliver one value lane outside tuple-field fast path"
            );
            let my_return_repr = env.return_reprs[this_spec_id as usize];
            let binding = *var_env.get(&v.0).expect("unbound return val");
            let cont_val = if is_cont_fn {
                let self_val = cont_param.expect("cont fn binds self via cont_param");
                body.outer_cont_ref(self_val)
            } else {
                cont_param.expect("non-cont native fn has cont_param")
            };
            let code = body.closure_code_ref(cont_val);
            let mut sig = Signature::new(CallConv::Tail);
            push_repr_param(&mut sig, my_return_repr);
            sig.params.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));
            let sigref = body.b.import_signature(sig);
            let mut cont_args = Vec::with_capacity(2);
            body.push_binding_as_abi_arg(&mut cont_args, binding, my_return_repr);
            cont_args.push(cont_val);
            body.b.ins().return_call_indirect(sigref, code, &cont_args);
        } else if cont_ptr_known_null {
            let value = *var_env.get(&v.0).expect("unbound return val");
            // This fn is never a cont target; cont_ptr is statically
            // null. Skip the load/icmp/brif dispatch.
            emit_halt_and_return_null(body, value);
        } else {
            let value = *var_env.get(&v.0).expect("unbound return val");
            emit_return(body, frame_ptr, value);
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn emit_call_term<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    schemas: &[Schema],
    var_env: &HashMap<u32, CodegenValue>,
    blk: &fz_ir::Block,
    is_native: bool,
    is_cont_fn: bool,
    _this_spec_id: u32,
    frame_ptr: Option<ir::Value>,
    cont_param: Option<ir::Value>,
    _callee: &DirectCallTarget,
    args: &[Var],
    continuation: &Cont,
) -> Result<(), CodegenError> {
    {
        let cap_vals: Vec<ir::Value> = continuation
            .captured
            .iter()
            .map(|v| var_env.get(&v.0).expect("unbound captured val").value())
            .collect();
        mark_retained_call_args_as_published(body, var_env, args, &continuation.captured);
        let callee_sid = resolve_callee_sid(env, blk, EmitSlot::Direct);
        let cont_sid = resolve_cont_sid(env, blk);
        if spec_is_native(env, callee_sid) {
            emit_native_call_with_cont(
                body,
                env,
                schemas,
                var_env,
                is_native,
                is_cont_fn,
                frame_ptr,
                cont_param,
                args,
                continuation,
                callee_sid,
                cont_sid,
                &cap_vals,
            );
        } else {
            let arg_bindings: Vec<CodegenValue> = args
                .iter()
                .map(|v| *var_env.get(&v.0).expect("unbound call arg"))
                .collect();
            let cap_bindings: Vec<CodegenValue> = continuation
                .captured
                .iter()
                .map(|v| *var_env.get(&v.0).expect("unbound captured val"))
                .collect();
            emit_call(
                body,
                schemas,
                frame_ptr,
                callee_sid,
                &arg_bindings,
                Some((cont_sid, &cap_bindings)),
            );
        }
    }
    Ok(())
}

// Native-callee Term::Call CPS plumbing. Builds the cont closure
// before the callee call so the callee's Term::Return can
// indirect-call through it (docs/cps-in-clif.md §2.1).
#[allow(clippy::too_many_arguments)]
fn emit_native_call_with_cont<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    schemas: &[Schema],
    var_env: &HashMap<u32, CodegenValue>,
    is_native: bool,
    is_cont_fn: bool,
    frame_ptr: Option<ir::Value>,
    cont_param: Option<ir::Value>,
    args: &[Var],
    continuation: &Cont,
    callee_sid: u32,
    cont_sid: u32,
    cap_vals: &[ir::Value],
) {
    let runtime = env.runtime;
    let fn_ids = env.fn_ids;
    let param_reprs = env.param_reprs;
    let closure_capture_counts = env.closure_capture_counts;
    let callee_fn_id = spec_fn_id(env, callee_sid);
    // Coerce each arg from its current var repr to the
    // callee's param_repr. Result rides back in the callee's
    // return_repr; the cont is the any-key spec by invariant
    // (all-ValueRef param_reprs, AnyValue cont frame slot 1).
    let callee_param_reprs = &param_reprs[callee_sid as usize];
    let callee_fid = *fn_ids.get(&callee_sid).expect("callee fn_id missing");
    let callee_fref = body.jmod.declare_func_in_func(callee_fid, body.b.func);
    let mut native_args = body.coerce_call_args(args, callee_param_reprs, var_env);
    // Closure-target sig is `(args..., self, cont) tail`. Direct
    // callers pass the per-Process static singleton as `self`.
    // The zero-cap invariant (asserted at closure_target_fns
    // build) means the body ignores self at runtime, so a
    // singleton with no captures is valid for any direct-call site.
    if closure_capture_counts.contains_key(&callee_fn_id) {
        native_args.push(fetch_static_closure(body.jmod, body.b, runtime, callee_sid));
    }
    let cont_is_native = spec_is_native(env, cont_sid);
    let cont_can_use_lazy_descriptor = false;
    let continuation_plan = if cont_is_native {
        let payload = ContinuationPayload::from_capture_vars(body, env, var_env, cont_sid, &continuation.captured);
        Some(plan_closure_shaped_continuation(
            payload,
            is_native && cont_can_use_lazy_descriptor,
        ))
    } else {
        None
    };
    let cont_value_opt = continuation_plan
        .as_ref()
        .map(|plan| plan.emit_value(body, runtime, env.return_reprs, is_cont_fn, cont_param, frame_ptr));
    // cont arg passed to the callee: cl_ptr for native cont,
    // else cont_param fallback. When the cont-fn is uniform
    // (rare; only main's halt-style cont after the
    // parking-reachable lift) and there is no cont_param,
    // build a halt-cont closure inline so the callee's
    // Term::Return doesn't load through null+16.
    // synth_halt_cont marks that path: the callee chains all
    // the way into halt-cont body, so the caller must NOT
    // execute its uniform-cont write-back after the call
    // (would double-halt with the wrong value).
    let mut synth_halt_cont = false;
    let cont_arg = if let Some(cont_value) = cont_value_opt {
        cont_value
    } else {
        match cont_param {
            Some(c) => c,
            None => {
                synth_halt_cont = true;
                let callee_ret_repr = NativeDemandAbi::new(env.body_native(callee_sid))
                    .returned_delivers_value_lane(env.cont_fns.contains(&callee_fn_id))
                    .then_some(env.return_reprs[callee_sid as usize])
                    .expect("synthesized halt continuation requires one delivered value lane");
                synthesize_halt_cont(body, runtime, callee_ret_repr)
            }
        }
    };
    native_args.push(cont_arg);

    let uses_lazy_cont = continuation_plan
        .as_ref()
        .is_some_and(ContinuationPlan::uses_lazy_descriptor);
    let uses_heap_cont = continuation_plan
        .as_ref()
        .is_some_and(ContinuationPlan::uses_heap_closure);
    if uses_lazy_cont && is_native {
        let inst = body.b.ins().call(callee_fref, &native_args);
        let result = body.b.inst_results(inst)[0];
        body.b.ins().return_(&[result]);
    } else if (uses_heap_cont || synth_halt_cont) && is_native {
        body.b.ins().return_call(callee_fref, &native_args);
    } else if uses_heap_cont || synth_halt_cont {
        // Uniform caller → native callee (chained). Can't
        // return_call across CC; synchronous call then
        // return the chain-final value (halt_value already
        // set by the time we get here). Call result is
        // intentionally discarded — chain unwinds via halt-cont.
        body.b.ins().call(callee_fref, &native_args);
        let zero = body.b.ins().iconst(types::I64, 0);
        body.b.ins().return_(&[zero]);
    } else {
        let call_inst = body.b.ins().call(callee_fref, &native_args);
        let result = body.b.inst_results(call_inst)[0];
        let cont_schema = &schemas[cont_sid as usize];
        let alloc_fref = body.jmod.declare_func_in_func(runtime.alloc_id, body.b.func);
        let sid = body.b.ins().iconst(types::I32, cont_sid as i64);
        let sz = body
            .b
            .ins()
            .iconst(types::I32, cont_schema.allocation_payload_size() as i64);
        let alloc_call = body.b.ins().call(alloc_fref, &[sid, sz]);
        let cf = body.b.inst_results(alloc_call)[0];
        let my_cont = body.b.ins().load(
            types::I64,
            MemFlags::trusted(),
            frame_ptr.expect(
                "Term::Call uniform-cont write-back reached from \
                 native-fn body — planned ABI invariant violated",
            ),
            HEADER_SIZE,
        );
        body.b.ins().store(MemFlags::trusted(), my_cont, cf, HEADER_SIZE);
        // Result + captures are written into the cont's
        // typed entry slots. Native result already has an
        // ABI repr; captured vars come from var_env.
        let callee_ret_repr = NativeDemandAbi::new(env.body_native(callee_sid))
            .returned_delivers_value_lane(env.cont_fns.contains(&callee_fn_id))
            .then_some(env.return_reprs[callee_sid as usize])
            .expect("uniform continuation write-back requires one delivered value lane");
        let mut payload: Vec<(ir::Value, ArgRepr)> = Vec::with_capacity(continuation.captured.len() + 1);
        payload.push((result, callee_ret_repr));
        for (cv, val) in continuation.captured.iter().zip(cap_vals.iter()) {
            let from = var_env.get(&cv.0).map_or(ArgRepr::ValueRef, |vb| vb.repr());
            payload.push((*val, from));
        }
        body.store_typed_args_into_callee_frame(cont_schema, cf, &payload, 1);
        body.b.ins().return_(&[cf]);
    }
}

#[allow(clippy::too_many_arguments)]
fn emit_tail_call_term<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    schemas: &[Schema],
    var_env: &HashMap<u32, CodegenValue>,
    blk: &fz_ir::Block,
    is_native: bool,
    is_cont_fn: bool,
    this_spec_id: u32,
    frame_ptr: Option<ir::Value>,
    host_ctx: Option<ir::Value>,
    cont_param: Option<ir::Value>,
    _callee: &DirectCallTarget,
    args: &[Var],
    is_back_edge: bool,
) -> Result<(), CodegenError> {
    let _ = schemas;
    {
        let callee_sid = resolve_callee_sid(env, blk, EmitSlot::Direct);
        if spec_is_native(env, callee_sid) {
            emit_native_tail_call(
                body,
                env,
                var_env,
                is_native,
                is_cont_fn,
                this_spec_id,
                frame_ptr,
                host_ctx,
                cont_param,
                args,
                is_back_edge,
                callee_sid,
            );
        } else {
            let arg_bindings: Vec<CodegenValue> = args
                .iter()
                .map(|v| *var_env.get(&v.0).expect("unbound tailcall arg"))
                .collect();
            emit_tail_call(body, schemas, this_spec_id, frame_ptr, callee_sid, &arg_bindings);
        }
    }
    Ok(())
}

// Native-callee Term::TailCall ABI emission. The planned ABI facts
// guarantee callee's return_repr matches mine, so
// return_call is ABI-compatible.
#[allow(clippy::too_many_arguments)]
fn emit_native_tail_call<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    is_native: bool,
    is_cont_fn: bool,
    this_spec_id: u32,
    frame_ptr: Option<ir::Value>,
    host_ctx: Option<ir::Value>,
    cont_param: Option<ir::Value>,
    args: &[Var],
    is_back_edge: bool,
    callee_sid: u32,
) {
    let runtime = env.runtime;
    let fn_ids = env.fn_ids;
    let param_reprs = env.param_reprs;
    let closure_capture_counts = env.closure_capture_counts;
    let callee_fn_id = spec_fn_id(env, callee_sid);
    let callee_param_reprs = &param_reprs[callee_sid as usize];
    let callee_fid = *fn_ids.get(&callee_sid).expect("callee fn_id missing");
    let callee_fref = body.jmod.declare_func_in_func(callee_fid, body.b.func);
    let callee_shape = returned_shape(env, callee_sid, env.cont_fns.contains(&callee_fn_id));
    let caller_shape = returned_shape(env, this_spec_id, is_cont_fn);
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
    // TailCall to a closure-target fn: insert static
    // singleton as `self` before cont (mirror of Term::Call;
    // zero-cap invariant lets any singleton serve as self).
    if closure_capture_counts.contains_key(&callee_fn_id) {
        let static_closure = fetch_static_closure(body.jmod, body.b, runtime, callee_sid);
        native_args.push(static_closure);
        mid_flight_arg_shapes.push(MidFlightArgShape::HeapRef);
    }
    // Trailing cont arg (docs/cps-in-clif.md §2.1). Build a
    // halt-cont closure inline when a uniform-tier caller
    // (cont_param=None) tail-calls a native callee, so the
    // callee's Term::Return doesn't deref null. Cont fns
    // forward outer_cont from their closure env; cont_param
    // for cont fns is self.
    let mut synth_halt_cont = false;
    let caller_outer_cont = if is_cont_fn {
        let self_val = cont_param.expect("cont fn binds self via cont_param");
        body.outer_cont_ref(self_val)
    } else {
        match cont_param {
            Some(c) => c,
            None => {
                synth_halt_cont = true;
                let DeliveredShape::Value(caller_ret_repr) = caller_shape else {
                    panic!(
                        "top-level native tail delivery must end in one value lane, got {:?}",
                        caller_shape
                    );
                };
                synthesize_halt_cont(body, runtime, caller_ret_repr)
            }
        }
    };
    let tail_cont_arg = match (&callee_shape, &caller_shape) {
        (left, right) if left == right => caller_outer_cont,
        (DeliveredShape::Value(callee_ret_repr), DeliveredShape::Value(caller_ret_repr)) => {
            build_boundary_return_adapter_cont(body, env, caller_outer_cont, *callee_ret_repr, *caller_ret_repr)
        }
        _ => {
            panic!(
                "native tail delivery mismatch requires structural agreement or a value-lane adapter: callee={:?}, caller={:?}",
                callee_shape, caller_shape
            );
        }
    };
    native_args.push(tail_cont_arg);
    mid_flight_arg_shapes.push(MidFlightArgShape::HeapRef);
    assert_eq!(
        native_args.len(),
        expected_native_tail_arg_count(callee_param_reprs, closure_capture_counts.contains_key(&callee_fn_id),),
        "native tail-call arg lanes must match the published callee ABI contract"
    );
    if is_native {
        // Native-to-native TailCall: use return_call so
        // recursive tail calls reuse the same stack frame
        // (TCO). Without this, count_100k blows the stack.
        //
        // Back-edge cooperative yield check: every native loop spends
        // reductions, including pure scalar loops that do not allocate.
        if is_back_edge {
            emit_back_edge_yield_check(body, env, callee_sid, &mid_flight_arg_shapes, &native_args);
        }
        body.b.ins().return_call(callee_fref, &native_args);
    } else if synth_halt_cont {
        // Uniform caller + native callee with synthesized
        // halt-cont: callee's chain runs all the way through
        // halt_cont_body. Caller must NOT do post-call uniform
        // write-back (would double-halt with the wrong value).
        let _ = body.b.ins().call(callee_fref, &native_args);
        let zero = body.b.ins().iconst(types::I64, 0);
        body.b.ins().return_(&[zero]);
    } else {
        // Uniform caller: synchronous call, then write result
        // into MY cont according to the continuation schema.
        let call_inst = body.b.ins().call(callee_fref, &native_args);
        let result = body.b.inst_results(call_inst)[0];
        let DeliveredShape::Value(callee_ret_repr) = callee_shape else {
            panic!(
                "uniform native tail call requires one delivered value lane, got {:?}",
                callee_shape
            );
        };
        let result_value = native_call_result_value(body, result, callee_ret_repr);
        let my_cont = body.b.ins().load(
            types::I64,
            MemFlags::trusted(),
            frame_ptr.expect(
                "Term::TailCall uniform-caller writeback reached from \
                 native-fn body — planned ABI invariant violated",
            ),
            HEADER_SIZE,
        );
        // Halt path: my_cont may be null on the top frame.
        let zero = body.b.ins().iconst(types::I64, 0);
        let is_null = body.b.ins().icmp(IntCC::Equal, my_cont, zero);
        let halt_blk = body.b.create_block();
        let invoke_blk = body.b.create_block();
        let no_args: Vec<BlockArg> = Vec::new();
        body.b.ins().brif(is_null, halt_blk, &no_args, invoke_blk, &no_args);
        body.b.switch_to_block(halt_blk);
        body.b.seal_block(halt_blk);
        let _ = host_ctx;
        emit_halt_from_codegen_value(body, result_value);
        let null = body.b.ins().iconst(types::I64, 0);
        body.b.ins().return_(&[null]);
        body.b.switch_to_block(invoke_blk);
        body.b.seal_block(invoke_blk);
        body.store_frame_value_dynamic(my_cont, SLOT_BYTES as u32, result_value);
        body.b.ins().return_(&[my_cont]);
    }
}

fn expected_native_tail_arg_count(callee_param_reprs: &[ArgRepr], has_static_self: bool) -> usize {
    callee_param_reprs.iter().map(ArgRepr::abi_arity).sum::<usize>() + usize::from(has_static_self) + 1
}

// Cooperative back-edge yield check: spend one reduction from the
// scheduler-installed budget; if exhausted, capture next-iteration args into a
// scheduler-runnable closure and yield it as the primary mid-flight root.
// Otherwise fall through to the caller's normal TCO path.
fn emit_back_edge_yield_check<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    callee_sid: u32,
    mid_flight_arg_shapes: &[MidFlightArgShape],
    native_args: &[ir::Value],
) {
    let runtime = env.runtime;
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
    let slow_path_begin_fref = body
        .jmod
        .declare_func_in_func(runtime.yield_slow_path_begin_id, body.b.func);
    let process = body.process_arg();
    body.b.ins().call(slow_path_begin_fref, &[process]);
    let fid_v = body.b.ins().iconst(types::I32, callee_sid as i64);
    let n_caps_v = body.b.ins().iconst(types::I32, native_root_values.len() as i64);
    let stub_fref = body.jmod.declare_func_in_func(cont_id, body.b.func);
    let stub_addr = body.b.ins().func_addr(types::I64, stub_fref);
    let zero_hk = body.b.ins().iconst(types::I32, 0);
    let cont_closure = body.alloc_closure(fid_v, n_caps_v, zero_hk, stub_addr);
    let last_root = native_root_values.len().saturating_sub(1);
    for (i, root) in native_root_values.iter().copied().enumerate() {
        let mut root_ref = body.value_as_any_ref(root);
        if i == last_root {
            root_ref = body.materialize_cont(root_ref);
        }
        body.store_closure_capture_ref_word(cont_closure, i, root_ref);
    }
    let yield_fref = body
        .jmod
        .declare_func_in_func(runtime.yield_mid_flight_report_id, body.b.func);
    let reason = body.b.ins().iconst(types::I32, YIELD_REASON_REDUCTIONS as i64);
    let yield_inst = body
        .b
        .ins()
        .call(yield_fref, &[process, cont_closure, new_remaining, reason]);
    let yield_ret = body.b.inst_results(yield_inst)[0];
    body.b.ins().return_(&[yield_ret]);

    body.b.switch_to_block(proceed_blk);
    body.b.seal_block(proceed_blk);
}

#[allow(clippy::too_many_arguments)]
fn emit_call_closure<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    blk: &fz_ir::Block,
    is_native: bool,
    is_cont_fn: bool,
    frame_ptr: Option<ir::Value>,
    host_ctx: Option<ir::Value>,
    cont_param: Option<ir::Value>,
    closure: &Var,
    args: &[Var],
    continuation: &Cont,
) -> Result<(), CodegenError> {
    let runtime = env.runtime;
    let fn_ids = env.fn_ids;
    let param_reprs = env.param_reprs;
    let closure_capture_counts = env.closure_capture_counts;
    {
        // Closure invocation is opaque to the caller: read code_ptr
        // through the runtime ABI and call it with args, self, and cont.
        let closure_binding = *var_env.get(&closure.0).expect("unbound callclosure closure");
        let cl_val = closure_binding.value();
        let arg_vals: Vec<ir::Value> = args
            .iter()
            .map(|v| var_env.get(&v.0).expect("unbound callclosure arg").value())
            .collect();
        mark_retained_call_args_as_published(body, var_env, args, &continuation.captured);
        let cont_sid = resolve_cont_sid(env, blk);
        // Singleton closure-lit fast path: if this spec types `closure`
        // as a single closure_lit(F, K), resolve F's narrow body spec
        // at [K..., arg_descrs...] and call it directly with the body's
        // narrow ABI. Opaque / polymorphic closures fall through to the
        // all-ValueRef indirect seam below.
        let lit_resolved: Option<(u32, FuncId, Option<usize>)> =
            resolve_native_closure_sid(env, blk.id).map(|body_sid| {
                let body_fn_id = spec_fn_id(env, body_sid);
                let body_fid = *fn_ids.get(&body_sid).expect("native closure target fn_id missing");
                let n_caps = closure_capture_counts.get(&body_fn_id).copied();
                (body_sid, body_fid, n_caps)
            });
        let cont_payload = ContinuationPayload::from_capture_vars(body, env, var_env, cont_sid, &continuation.captured);
        let can_use_lazy_cont = false;
        let continuation_plan = plan_closure_shaped_continuation(cont_payload, can_use_lazy_cont);
        let cf = continuation_plan.emit_value(body, runtime, env.return_reprs, is_cont_fn, cont_param, frame_ptr);
        let continuation_storage = if continuation_plan.uses_lazy_descriptor() {
            "lazy_descriptor"
        } else {
            "heap_closure"
        };
        env.telemetry.execute(
            &["fz", "codegen", "closure_call_lowered"],
            &measurements! {
                spec_id: env.active_spec_id as u64,
                closure_var: closure.0 as u64,
                continuation_spec_id: cont_sid as u64,
            },
            &metadata! {
                body_name: env.active_body_name,
                call_kind: "call_closure",
                closure_binding_repr: closure_binding.repr().as_str(),
                dispatch_kind: if lit_resolved.is_some() { "direct" } else { "indirect" },
                continuation_storage: continuation_storage,
            },
        );
        if let Some((body_sid, body_fid, closure_target_n_caps)) = lit_resolved {
            let body_param_reprs = &param_reprs[body_sid as usize];
            let body_fref = body.jmod.declare_func_in_func(body_fid, body.b.func);
            let n_caps = closure_target_n_caps.unwrap_or(0);
            let mut direct_args: Vec<ir::Value> =
                Vec::with_capacity(arg_vals.len() + 1 + usize::from(closure_target_n_caps.is_some()));
            for (i, _v) in arg_vals.iter().enumerate() {
                let binding = *var_env.get(&args[i].0).expect("unbound callclosure arg");
                let to = body_param_reprs.get(n_caps + i).copied().unwrap_or(ArgRepr::ValueRef);
                body.push_binding_as_abi_arg(&mut direct_args, binding, to);
            }
            if closure_target_n_caps.is_some() {
                direct_args.push(cl_val);
            }
            direct_args.push(cf);
            let _ = host_ctx;
            if can_use_lazy_cont {
                let call_inst = body.b.ins().call(body_fref, &direct_args);
                let result = body.b.inst_results(call_inst)[0];
                body.b.ins().return_(&[result]);
            } else if is_native {
                body.b.ins().return_call(body_fref, &direct_args);
            } else {
                let call_inst = body.b.ins().call(body_fref, &direct_args);
                let result = body.b.inst_results(call_inst)[0];
                body.b.ins().return_(&[result]);
            }
            return Ok(());
        }
        // Indirect path: load body address from the closure and
        // Tail-CC indirect-call with closure-target sig
        // `(args..., self, cont) -> i64 tail` (all-ValueRef params).
        // Native callers use return_call_indirect (TCO); uniform
        // callers use call_indirect Tail (cross-CC) and return result.
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
        let _ = host_ctx; // no host_ctx in closure-target sig
        if can_use_lazy_cont {
            let call_inst = body.b.ins().call_indirect(sig_ref, body_fp, &indirect_args);
            let result = body.b.inst_results(call_inst)[0];
            body.b.ins().return_(&[result]);
        } else if is_native {
            body.b.ins().return_call_indirect(sig_ref, body_fp, &indirect_args);
        } else {
            let call_inst = body.b.ins().call_indirect(sig_ref, body_fp, &indirect_args);
            let result = body.b.inst_results(call_inst)[0];
            body.b.ins().return_(&[result]);
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn emit_tail_call_closure<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    blk: &fz_ir::Block,
    is_native: bool,
    is_cont_fn: bool,
    frame_ptr: Option<ir::Value>,
    host_ctx: Option<ir::Value>,
    cont_param: Option<ir::Value>,
    closure: &Var,
    args: &[Var],
) -> Result<(), CodegenError> {
    let fn_ids = env.fn_ids;
    let param_reprs = env.param_reprs;
    let closure_capture_counts = env.closure_capture_counts;
    {
        // Tail-CC indirect-call through the closure code ptr with the
        // caller's own cont (TCO via return_call_indirect). Closure-
        // target sig `(args..., self, cont) -> i64 tail`. For cont fns
        // the forwarded cont is the env's outer_cont; non-cont native
        // forwards cont_param; uniform loads from frame_ptr+16.
        //
        // Closure-lit fast path: when the closure Var's per-spec type
        // is a single closure_lit(F, K), resolve F's narrow body spec
        // at [K..., arg_descrs...] and emit a direct return_call,
        // bypassing the runtime code-pointer read. Falls back to the
        // indirect path on union-of-lits, plain arrows, unresolved keys.
        let closure_binding = *var_env.get(&closure.0).expect("unbound tailcallclosure closure");
        let cl_val = closure_binding.value();
        let arg_vals: Vec<ir::Value> = args
            .iter()
            .map(|v| var_env.get(&v.0).expect("unbound tailcallclosure arg").value())
            .collect();
        let my_cont = if is_cont_fn {
            let self_val = cont_param.expect("cont fn binds self via cont_param");
            body.outer_cont_ref(self_val)
        } else {
            match cont_param {
                Some(c) => c,
                None => body.b.ins().load(
                    types::I64,
                    MemFlags::trusted(),
                    frame_ptr.expect("uniform TailCallClosure must have frame_ptr"),
                    HEADER_SIZE,
                ),
            }
        };

        let lit_resolved: Option<(u32, FuncId, Option<usize>)> =
            resolve_native_closure_sid(env, blk.id).map(|body_sid| {
                let body_fn_id = spec_fn_id(env, body_sid);
                let body_fid = *fn_ids.get(&body_sid).expect("native closure target fn_id missing");
                let n_caps = closure_capture_counts.get(&body_fn_id).copied();
                (body_sid, body_fid, n_caps)
            });
        env.telemetry.execute(
            &["fz", "codegen", "closure_call_lowered"],
            &measurements! {
                spec_id: env.active_spec_id as u64,
                closure_var: closure.0 as u64,
            },
            &metadata! {
                body_name: env.active_body_name,
                call_kind: "tail_call_closure",
                closure_binding_repr: closure_binding.repr().as_str(),
                dispatch_kind: if lit_resolved.is_some() { "direct" } else { "indirect" },
            },
        );

        if let Some((body_sid, body_fid, closure_target_n_caps)) = lit_resolved {
            let body_param_reprs = &param_reprs[body_sid as usize];
            let body_fref = body.jmod.declare_func_in_func(body_fid, body.b.func);
            let n_caps = closure_target_n_caps.unwrap_or(0);
            let mut direct_args: Vec<ir::Value> =
                Vec::with_capacity(arg_vals.len() + 1 + usize::from(closure_target_n_caps.is_some()));
            for (i, _v) in arg_vals.iter().enumerate() {
                let binding = *var_env.get(&args[i].0).expect("unbound tailcallclosure arg");
                let to = body_param_reprs.get(n_caps + i).copied().unwrap_or(ArgRepr::ValueRef);
                body.push_binding_as_abi_arg(&mut direct_args, binding, to);
            }
            if closure_target_n_caps.is_some() {
                direct_args.push(cl_val);
            }
            direct_args.push(my_cont);
            let _ = host_ctx;
            if is_native {
                body.b.ins().return_call(body_fref, &direct_args);
            } else {
                let call_inst = body.b.ins().call(body_fref, &direct_args);
                let result = body.b.inst_results(call_inst)[0];
                body.b.ins().return_(&[result]);
            }
        } else {
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
            let _ = host_ctx;
            if is_native {
                body.b.ins().return_call_indirect(sig_ref, body_fp, &indirect_args);
            } else {
                let call_inst = body.b.ins().call_indirect(sig_ref, body_fp, &indirect_args);
                let result = body.b.inst_results(call_inst)[0];
                body.b.ins().return_(&[result]);
            }
        }
    }
    Ok(())
}

// Selective-receive park-site CLIF.
//
// Layout, mirroring fz_runtime::park::ParkRecord:
//   - matcher fn addr (declared/emitted by the planned codegen matcher pass).
//   - pinned[]: one-word value entries, one per `^name`
//     referenced across all clauses, in source order.
//   - clause_bodies[]: i64 array of cont-closure refs,
//     one per source clause; each closure carries the clause-body
//     fn entry, while captures are populated through closure
//     accessors in source order (ContinuationPlan handles all
//     bookkeeping).
//   - clause_bound_counts[]: i64 array, one per source clause.
//     The matcher scratch uses max bound_arity; the resumed
//     outcome env uses only the winning clause's actual binds.
//   - bound_arity: max bound-var count across clauses; sizes
//     the `out` buffer the matcher fills on a hit.
//   - after_deadline_or_neg1: -1 when no after clause,
//     else the unboxed timeout in ms.
//   - after_cont: closure ptr when after is Some, else null.
//
// After laying these out the helper calls fz_receive_park_matched
// and returns the YIELD sentinel so the trampoline parks.
#[allow(clippy::too_many_arguments)]
fn emit_receive_matched<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    blk: &fz_ir::Block,
    is_cont_fn: bool,
    caller_fn_id: FnId,
    frame_ptr: Option<ir::Value>,
    cont_param: Option<ir::Value>,
    clauses: &[ReceiveClause],
    after: Option<&ReceiveAfter>,
    pinned: &[(String, Var)],
    captures: &[Var],
) -> Result<(), CodegenError> {
    let dispatch_fid = *env
        .receive_dispatch_fn_ids
        .get(&(caller_fn_id.0, blk.id.0))
        .expect("receive dispatch fn pre-declared by planned codegen pass");
    let dispatch_addr = fn_addr(body.jmod, dispatch_fid, body.b);
    let yield_sentinel = build_park_record(
        body,
        env,
        var_env,
        is_cont_fn,
        frame_ptr,
        cont_param,
        clauses,
        after,
        pinned,
        captures,
        dispatch_addr,
    );
    // Both native and uniform bodies return the YIELD sentinel so the
    // trampoline parks.
    body.b.ins().return_(&[yield_sentinel]);
    Ok(())
}

// Lay out the ParkRecord fields described in
// `fz_runtime::park::ParkRecord` (pinned snapshot, clause cont
// closures, optional after closure, bound-arity), then call
// fz_receive_park_matched and return the YIELD sentinel.
#[allow(clippy::too_many_arguments)]
fn build_park_record<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    is_cont_fn: bool,
    frame_ptr: Option<ir::Value>,
    cont_param: Option<ir::Value>,
    clauses: &[ReceiveClause],
    after: Option<&ReceiveAfter>,
    pinned: &[(String, Var)],
    captures: &[Var],
    matcher_addr: ir::Value,
) -> ir::Value {
    use cranelift_codegen::ir::{StackSlotData, StackSlotKind};
    let runtime = env.runtime;

    // Pinned snapshot: alloca [AnyValueRef; n_pinned], take base addr.
    let n_pinned = pinned.len();
    let pinned_ptr = if n_pinned == 0 {
        body.b.ins().iconst(types::I64, 0)
    } else {
        let slot = body.b.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            (n_pinned * SLOT_BYTES as usize) as u32,
            3,
        ));
        for (i, (_name, v)) in pinned.iter().enumerate() {
            let value_ref = body.tagged_var(var_env, v.0);
            body.b
                .ins()
                .stack_store(value_ref, slot, (i * SLOT_BYTES as usize) as i32);
        }
        body.b.ins().stack_addr(types::I64, slot, 0)
    };

    // Captures snapshot, shared across every clause body /
    // guard / after closure. `Term::ReceiveMatched::captures`
    // is already deduplicated by ir_lower; the cont fns'
    // capture-param slots line up with this order.
    let cap_bindings: Vec<ClosureCapture> = captures
        .iter()
        .map(|cv| closure_capture_for_var(body, var_env, cv.0))
        .collect();

    // bound_arity: max bound-var count across clauses (matcher
    // ABI sizes the out buffer to this).
    let bound_arity = clauses.iter().map(|c| c.bound_names.len()).max().unwrap_or(0);

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
    let needs_bound_counts = clauses.iter().any(|c| c.bound_names.len() != bound_arity);
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
        let cl_ptr = ContinuationPlan::heap_closure(payload).emit_value(
            body,
            runtime,
            env.return_reprs,
            is_cont_fn,
            cont_param,
            frame_ptr,
        );
        body.b.ins().stack_store(cl_ptr, bodies_slot, (i * 8) as i32);
        if let Some(slot) = bound_counts_slot {
            let bound_count_v = body.b.ins().iconst(types::I64, c.bound_names.len() as i64);
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
            let cl_ptr = ContinuationPlan::heap_closure(payload).emit_value(
                body,
                runtime,
                env.return_reprs,
                is_cont_fn,
                cont_param,
                frame_ptr,
            );
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

    let park_fref = body
        .jmod
        .declare_func_in_func(runtime.receive_park_matched_id, body.b.func);
    let process = body.process_arg();
    let park_inst = body.b.ins().call(
        park_fref,
        &[
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
        ],
    );
    body.b.inst_results(park_inst)[0]
}
