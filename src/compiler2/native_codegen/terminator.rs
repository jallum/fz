//! Terminator emission for fz IR blocks.

use super::receive::{ReceiveFns, clause_roots};
use super::static_object::ReceiveClauseLayout;
use super::*;
use crate::compiler2::artifact::{BodyFrame, FrameRole};
use crate::compiler2::{NativeBody, NativeEntryAbi};
use crate::dispatch_matrix::pattern::PatternDispatchPlan;
use crate::fast_hash::{HashMap, HashSet};
use crate::fz_ir::{
    self as fz_ir, Block, BlockId, Cont, DirectCallTarget, EmitSlot, FnId, FnIr, Prim, ReceiveAfter, ReceiveClause,
    Stmt, Term, Var,
};
use crate::runtime_type_predicate::RuntimeTypePredicate;
use cranelift_codegen::ir::TrapCode;
use cranelift_codegen::ir::{self, AbiParam, BlockArg, InstBuilder, MemFlagsData, Signature, condcodes::IntCC, types};
use cranelift_codegen::isa::CallConv;
use cranelift_module::FuncId;
use fz_runtime::failure::{fz_panic, fz_panic_reason, fz_raise_undefined_function, fz_reraise};
use fz_runtime::ir_runtime::{fz_receive_park_matched, fz_yield_mid_flight_report, fz_yield_slow_path_begin};
use fz_runtime::process::YIELD_REASON_REDUCTIONS;
use fz_runtime::process_abi::PROCESS_REDUCTIONS_REMAINING_OFFSET;
use fz_runtime::scheduler_hooks::YIELD_PTR;

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

fn emit_native_continuation_tail_delivery<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
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
    assert!(
        is_frame_member(env, callee_sid) || args.len() == callee_param_reprs.len(),
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

    let self_arg = hand_continuation_on(body, env, var_env, cont_param, callee_sid, &args[extra_params..]);
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
    body.b.ins().return_call_indirect(sig_ref, code, &delivered_args);
}

/// The continuation a call site hands its callee: the body frame it resumes
/// in when it is a member of the running frame (the frame is pointed at it),
/// else a closure built here.
fn is_frame_member(env: &CodegenEnv<'_>, sid: u32) -> bool {
    matches!(
        env.body_native(sid).frame,
        Some(BodyFrame {
            role: FrameRole::Member,
            ..
        })
    )
}

/// A member of the running frame is handed exactly the frame: it is pointed at
/// the member's code and travels as the continuation.
fn hand_frame_on<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    cont_sid: u32,
    captured: &[Var],
) -> ir::Value {
    let [frame] = captured else {
        panic!(
            "a frame member is handed exactly its frame, got {} value(s)",
            captured.len()
        );
    };
    let frame = var_env.get(&frame.0).expect("unbound body frame").value();
    let cont_fid = *env.fn_ids.get(&cont_sid).expect("cont fn_id missing");
    let code = fn_addr(body.jmod, cont_fid, body.b);
    body.frame_resume_at(frame, code);
    frame
}

fn hand_continuation_on<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    cont_param: ir::Value,
    cont_sid: u32,
    captured: &[Var],
) -> ir::Value {
    if is_frame_member(env, cont_sid) {
        return hand_frame_on(body, env, var_env, cont_sid, captured);
    }
    ContinuationPayload::from_capture_vars(body, env, var_env, cont_sid, captured).emit_value(body, cont_param)
}

/// The slots a continuation's body keeps empty behind the outer continuation
/// and its `capture_count` captures.
fn continuation_empty_slots(env: &CodegenEnv<'_>, cont_sid: u32, capture_count: usize) -> usize {
    match env.body_native(cont_sid).frame {
        Some(BodyFrame {
            role: FrameRole::Root,
            slots,
        }) => slots as usize - 1 - capture_count,
        _ => 0,
    }
}

struct ContinuationPayload {
    cont_fid: FuncId,
    semantic_cap_bindings: Vec<ClosureCapture>,
    empty_slots: usize,
}

impl ContinuationPayload {
    fn from_parts(env: &CodegenEnv<'_>, cont_sid: u32, semantic_cap_bindings: Vec<ClosureCapture>) -> Self {
        let cont_fid = *env.fn_ids.get(&cont_sid).expect("cont fn_id missing");
        let empty_slots = continuation_empty_slots(env, cont_sid, semantic_cap_bindings.len());
        Self {
            cont_fid,
            semantic_cap_bindings,
            empty_slots,
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
        Self::from_parts(env, cont_sid, cap_bindings)
    }

    fn push_handler_record<M: cranelift_module::Module>(&self, body: &mut CodegenFn<'_, '_, M>, cont_param: ir::Value) {
        closure::push_handler_record(
            body,
            cont_param,
            self.cont_fid,
            &self.semantic_cap_bindings,
            self.empty_slots,
        );
    }

    fn emit_value<M: cranelift_module::Module>(
        &self,
        body: &mut CodegenFn<'_, '_, M>,
        cont_param: ir::Value,
    ) -> ir::Value {
        build_cont_closure(
            body,
            cont_param,
            self.cont_fid,
            &self.semantic_cap_bindings,
            self.empty_slots,
        )
    }
}

fn return_diverges(env: &CodegenEnv<'_>, body_sid: u32) -> bool {
    env.return_diverges[body_sid as usize]
}

pub(crate) fn emit_terminator<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    blk: &fz_ir::Block,
    block_map: &HashMap<u32, ir::Block>,
    this_spec_id: u32,
    f: &FnIr,
    cont_param: ir::Value,
) -> Result<(), CodegenError> {
    let caller_fn_id = f.id;
    let edges = GotoEdges {
        f,
        native_body: env.body_native(this_spec_id),
        block_map,
    };
    match &blk.terminator {
        Term::Goto(target, args) => edges.emit(body, var_env, target, args),
        Term::Try {
            handler,
            captures,
            body: body_block,
        } => emit_try(body, env, var_env, &edges, cont_param, *handler, captures, body_block),
        Term::If {
            cond, then_b, else_b, ..
        } => emit_if(body, var_env, block_map, caller_fn_id, blk.id, cond, then_b, else_b),
        Term::Raise { value, reason } => emit_raise(body, var_env, *value, *reason),
        Term::Reraise { kind, value, reason } => emit_reraise(body, var_env, *kind, *value, *reason),
        Term::RaiseUndefined {
            receiver,
            function,
            arity,
            modules_without,
        } => emit_raise_undefined(body, var_env, *receiver, *function, *arity, *modules_without),
        Term::Unreachable => {
            body.b.ins().trap(TrapCode::user(1).unwrap());
            Ok(())
        }
        Term::ReturnLanes(lanes) => emit_return_lanes(body, env, var_env, this_spec_id, cont_param, lanes),
        Term::Return(v) => emit_return_term(body, env, var_env, this_spec_id, cont_param, v),
        Term::Call {
            ident: _,
            callee: _,
            args,
            continuation,
        } => emit_call_term(body, env, var_env, blk, cont_param, args, continuation),
        Term::TailCall {
            ident: _,
            callee: _,
            args,
            is_back_edge,
        } => emit_tail_call_term(body, env, var_env, blk, this_spec_id, cont_param, args, *is_back_edge),
        Term::CallClosure {
            ident: _,
            closure,
            args,
            continuation,
        } => emit_call_closure(body, env, var_env, blk, cont_param, closure, args, continuation),
        Term::TailCallClosure {
            closure,
            args,
            ident: _,
        } => emit_tail_call_closure(body, var_env, cont_param, closure, args),
        Term::ReceiveMatched {
            clauses,
            after,
            pinned,
            captures,
            dispatch,
            ident: _,
        } => emit_receive_matched(
            body,
            env,
            var_env,
            blk,
            caller_fn_id,
            cont_param,
            clauses,
            dispatch,
            after.as_ref(),
            pinned,
            captures,
        ),
    }
}

/// Enter a `try`: push the handler's record over the live captures as the
/// process's innermost handler, and fall into the body block. The record holds
/// the image of the handler's continuation, so `fz_panic` materialises it the
/// way it does a receive outcome template, with the raise's three values; a
/// body that completes pops it without having built anything on the heap.
fn emit_try<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    edges: &GotoEdges<'_>,
    cont_param: ir::Value,
    handler: FnId,
    captures: &[Var],
    body_block: &BlockId,
) -> Result<(), CodegenError> {
    let cont_sid = env
        .body_id_for_fn(handler)
        .unwrap_or_else(|| panic!("native try handler fn {} has no registered codegen body id", handler.0));
    let cap_bindings: Vec<ClosureCapture> = captures
        .iter()
        .map(|cv| closure_capture_for_var(body, var_env, cv.0))
        .collect();
    ContinuationPayload::from_parts(env, cont_sid, cap_bindings).push_handler_record(body, cont_param);
    edges.emit(body, var_env, body_block, &[])
}

/// The jumps between one function's blocks. Each jump hands every argument
/// over in the form its target parameter takes, converting on that edge
/// alone: a value that jumps to two blocks wanting different forms is
/// converted once per edge, and its own binding is left as it was.
struct GotoEdges<'a> {
    f: &'a FnIr,
    native_body: &'a NativeBody,
    block_map: &'a HashMap<u32, ir::Block>,
}

impl GotoEdges<'_> {
    fn emit<M: cranelift_module::Module>(
        &self,
        body: &mut CodegenFn<'_, '_, M>,
        var_env: &HashMap<u32, CodegenValue>,
        target: &BlockId,
        args: &[Var],
    ) -> Result<(), CodegenError> {
        let Some(&successor) = self.block_map.get(&target.0) else {
            return Err(CodegenError::new(format!(
                "{}#{} jumps to an unknown successor {target:?}",
                self.f.name, self.f.id.0
            )));
        };
        let params = &self.f.block(*target).params;
        if params.len() != args.len() {
            return Err(CodegenError::new(format!(
                "{}#{} jumps to {target:?} with {} arguments for {} parameters",
                self.f.name,
                self.f.id.0,
                args.len(),
                params.len()
            )));
        }
        let mut arg_vals = Vec::with_capacity(args.len());
        for (arg, param) in args.iter().zip(params) {
            let binding = *var_env.get(&arg.0).expect("unbound goto arg");
            body.push_binding_as_abi_arg(&mut arg_vals, binding, block_param_repr(self.native_body, param));
        }
        let arg_vals: Vec<BlockArg> = arg_vals.into_iter().map(BlockArg::Value).collect();
        body.b.ins().jump(successor, &arg_vals);
        Ok(())
    }
}

/// A runtime type test that ends its block by branching.
pub(super) struct BranchingTypeTest<'a> {
    pub(super) subject: Var,
    pub(super) predicate: &'a RuntimeTypePredicate,
    pub(super) admit: ir::Block,
    pub(super) reject: ir::Block,
}

/// The type test a block's `if` is the only reader of, when it is the block's
/// last statement and both successors are reachable. Such a test branches
/// straight to the successors; its answer is never held as a value.
pub(super) fn type_test_that_only_branches<'a>(
    blk: &'a Block,
    if_only_conds: &HashSet<u32>,
    block_map: &HashMap<u32, ir::Block>,
) -> Option<BranchingTypeTest<'a>> {
    let Term::If {
        cond, then_b, else_b, ..
    } = &blk.terminator
    else {
        return None;
    };
    let Some(Stmt::Let(tested, Prim::RuntimeTypeTest(subject, predicate))) = blk.stmts.last() else {
        return None;
    };
    (tested == cond && if_only_conds.contains(&cond.0)).then_some(())?;
    Some(BranchingTypeTest {
        subject: *subject,
        predicate,
        admit: *block_map.get(&then_b.0)?,
        reject: *block_map.get(&else_b.0)?,
    })
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

/// `Term::Raise` is a decision's last resort: the process raises the
/// exception the block built, through the one raise route, with the reason
/// the failure declares when it declares one, and what follows is what follows
/// any raise.
fn emit_raise<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    value: Var,
    reason: Option<Var>,
) -> Result<(), CodegenError> {
    let [value_word, value_kind] = stored_parts(body, binding_for_var(var_env, value.0));
    let process = body.process_arg();
    match reason {
        Some(reason) => {
            let [reason_word, reason_kind] = stored_parts(body, binding_for_var(var_env, reason.0));
            runtime_call!(
                body,
                fz_panic_reason,
                [process, value_word, value_kind, reason_word, reason_kind]
            );
        }
        None => {
            runtime_call!(body, fz_panic, [process, value_word, value_kind]);
        }
    }
    continue_after_raise(body);
    Ok(())
}

/// `Term::Reraise` is a handler's last resort: the process continues the raise
/// the handler was delivered, with its reason, and what follows is what follows
/// any raise.
fn emit_reraise<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    kind: Var,
    value: Var,
    reason: Var,
) -> Result<(), CodegenError> {
    let kind = body.any_ref_for_var(var_env, kind.0);
    let [value_word, value_kind] = stored_parts(body, binding_for_var(var_env, value.0));
    let [reason_word, reason_kind] = stored_parts(body, binding_for_var(var_env, reason.0));
    let process = body.process_arg();
    runtime_call!(
        body,
        fz_reraise,
        [process, kind, value_word, value_kind, reason_word, reason_kind]
    );
    continue_after_raise(body);
    Ok(())
}

/// `Term::RaiseUndefined` is a call on a module value that found nothing to
/// call: the runtime raises Elixir's exception for the receiver it is shown,
/// and what follows is what follows any raise.
fn emit_raise_undefined<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    receiver: Var,
    function: Var,
    arity: usize,
    modules_without: Var,
) -> Result<(), CodegenError> {
    let receiver = body.any_ref_for_var(var_env, receiver.0);
    let function = body.any_ref_for_var(var_env, function.0);
    let modules_without = body.any_ref_for_var(var_env, modules_without.0);
    let arity = body.b.ins().iconst(types::I64, arity as i64);
    let process = body.process_arg();
    runtime_call!(
        body,
        fz_raise_undefined_function,
        [process, receiver, function, arity, modules_without]
    );
    continue_after_raise(body);
    Ok(())
}

fn emit_return_lanes<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
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
    let code = body.closure_code_ref(cont_param);
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
    cont_args.push(cont_param);
    body.b.ins().return_call_indirect(sigref, code, &cont_args);
    Ok(())
}

fn emit_return_term<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    this_spec_id: u32,
    cont_param: ir::Value,
    v: &Var,
) -> Result<(), CodegenError> {
    let return_reprs = env.body_return_reprs(this_spec_id);
    if return_diverges(env, this_spec_id) {
        body.b.ins().trap(TrapCode::user(1).unwrap());
    } else if return_reprs.is_empty() {
        let code = body.closure_code_ref(cont_param);
        let mut sig = Signature::new(CallConv::Tail);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let sigref = body.b.import_signature(sig);
        body.b.ins().return_call_indirect(sigref, code, &[cont_param]);
    } else if let [my_return_repr] = return_reprs.as_slice() {
        let binding = *var_env.get(&v.0).expect("unbound return val");
        let code = body.closure_code_ref(cont_param);
        let mut sig = Signature::new(CallConv::Tail);
        push_repr_param(&mut sig, *my_return_repr);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let sigref = body.b.import_signature(sig);
        let mut cont_args = Vec::with_capacity(2);
        body.push_binding_as_abi_arg(&mut cont_args, binding, *my_return_repr);
        cont_args.push(cont_param);
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
fn emit_call_term<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    blk: &fz_ir::Block,
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
    native_args.push(hand_continuation_on(
        body,
        env,
        var_env,
        cont_param,
        cont_sid,
        &continuation.captured,
    ));
    body.b.ins().return_call(callee_fref, &native_args);
    Ok(())
}

// Term::TailCall ABI emission. The planned ABI facts guarantee callee's
// return_repr matches mine, so return_call is ABI-compatible.
fn emit_tail_call_term<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    blk: &fz_ir::Block,
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
            env,
            var_env,
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
    let tail_cont_arg = if return_diverges(env, callee_sid) || callee_return_reprs == caller_return_reprs {
        cont_param
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
    if callee_sid == this_spec_id
        && let Some(head) = body.cache.loop_head
    {
        let head_args: Vec<BlockArg> = native_args.iter().map(|v| BlockArg::Value(*v)).collect();
        body.b.ins().jump(head, &head_args);
        return Ok(());
    }
    body.b.ins().return_call(callee_fref, &native_args);
    Ok(())
}

fn expected_native_tail_arg_count(callee_param_reprs: &[ArgRepr]) -> usize {
    callee_param_reprs.iter().map(ArgRepr::abi_arity).sum::<usize>() + 1
}

// Cooperative back-edge yield check: spend one reduction from the
// scheduler-installed budget; if exhausted, tail-call the key's yield stub with
// the next-iteration args and the spent count. Otherwise fall through to the
// caller's normal TCO path. The yield path lives in its own function so nothing
// on the hot path is live across a runtime call.
fn emit_back_edge_yield_check<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    callee_sid: u32,
    mid_flight_arg_shapes: &[MidFlightArgShape],
    native_args: &[ir::Value],
) {
    let process = body.process_arg();
    let reductions_ptr = body
        .b
        .ins()
        .iadd_imm_s(process, PROCESS_REDUCTIONS_REMAINING_OFFSET as i64);
    let remaining = body
        .b
        .ins()
        .load(types::I32, MemFlagsData::trusted(), reductions_ptr, 0);
    let one = body.b.ins().iconst(types::I32, 1);
    let new_remaining = body.b.ins().isub(remaining, one);
    body.b
        .ins()
        .store(MemFlagsData::trusted(), new_remaining, reductions_ptr, 0);
    let exhausted = body.b.ins().icmp_imm_s(IntCC::SignedLessThanOrEqual, new_remaining, 0);
    let yield_blk = body.b.create_block();
    let proceed_blk = body.b.create_block();
    let no_args: Vec<BlockArg> = Vec::new();
    body.b.ins().brif(exhausted, yield_blk, &no_args, proceed_blk, &no_args);

    body.b.switch_to_block(yield_blk);
    body.b.seal_block(yield_blk);
    body.b.set_cold_block(yield_blk);
    let cont_key = (callee_sid, mid_flight_arg_shapes.to_vec());
    let fns = env.mid_flight_cont_tail_fn_ids.get(&cont_key).unwrap_or_else(|| {
        panic!(
            "missing mid-flight continuation tail for {:?}; available {:?}",
            cont_key,
            env.mid_flight_cont_tail_fn_ids.keys().collect::<Vec<_>>()
        )
    });
    let stub_ref = body.func_ref(fns.yield_stub);
    let mut stub_args = native_args.to_vec();
    stub_args.push(new_remaining);
    body.b.ins().return_call(stub_ref, &stub_args);

    body.b.switch_to_block(proceed_blk);
    body.b.seal_block(proceed_blk);
}

/// The yield stub's signature: the native args of the back edge's callee, then
/// the remaining reduction count the back edge just wrote.
pub(super) fn back_edge_yield_stub_signature(arg_shapes: &[MidFlightArgShape]) -> Signature {
    let mut sig = Signature::new(CallConv::Tail);
    for shape in arg_shapes {
        shape.push_param(&mut sig);
    }
    sig.params.push(AbiParam::new(types::I32));
    sig.returns.push(AbiParam::new(types::I64));
    sig
}

/// Define the yield stub for one back-edge key: capture the next-iteration args
/// into a scheduler-runnable closure over the key's resume continuation and
/// report it as the primary mid-flight root.
pub(super) fn define_back_edge_yield_stub<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut cranelift_frontend::FunctionBuilderContext,
    sites: &std::cell::RefCell<SiteTable>,
    callee_sid: u32,
    arg_shapes: &[MidFlightArgShape],
    stub_id: FuncId,
    resume_id: FuncId,
) -> Result<(), Box<cranelift_module::ModuleError>> {
    let name = format!("fz_back_edge_yield_{callee_sid}");
    emit_fn_body(m, fbctx, back_edge_yield_stub_signature(arg_shapes), stub_id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let params = b.block_params(entry).to_vec();
        let (native_args, new_remaining) = params.split_at(params.len() - 1);
        let mut cache = CodegenCache::default();
        let mut body = CodegenFn::new(b, m, &mut cache, SiteScope { sites, function: &name });
        let mut abi_cursor = 0;
        let roots: Vec<CodegenValue> = arg_shapes
            .iter()
            .map(|shape| {
                let root = shape.capture_from_args(native_args, abi_cursor);
                abi_cursor += shape.abi_arity();
                root
            })
            .collect();
        debug_assert_eq!(abi_cursor, native_args.len());
        let process = body.process_arg();
        runtime_call!(body, fz_yield_slow_path_begin, [process]);
        let resume_addr = body.func_addr(resume_id);
        let cont_closure = place_cont_closure(&mut body, roots.len(), resume_addr).reference;
        for (i, root) in roots.iter().copied().enumerate() {
            match root {
                CodegenValue::RawInt(word) => body.store_closure_capture_i64(cont_closure, i, word),
                CodegenValue::RawF64(word) => body.store_closure_capture_f64(cont_closure, i, word),
                CodegenValue::RawAtom(word) => body.store_closure_capture_atom(cont_closure, i, word),
                root => body.store_closure_capture_value(cont_closure, i, root),
            }
        }
        let reason = body.b.ins().iconst(types::I32, YIELD_REASON_REDUCTIONS as i64);
        let yield_ret = runtime_call1!(
            body,
            fz_yield_mid_flight_report,
            [process, cont_closure, new_remaining[0], reason]
        );
        body.b.ins().return_(&[yield_ret]);
    })
}

fn emit_call_closure<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    blk: &fz_ir::Block,
    cont_param: ir::Value,
    closure: &Var,
    args: &[Var],
    continuation: &Cont,
) -> Result<(), CodegenError> {
    // Closure invocation is opaque to the caller: read code_ptr
    // through the runtime ABI and call it with args, self, and cont.
    let closure_binding = *var_env.get(&closure.0).expect("unbound callclosure closure");
    let cl_val = body.value_as_any_ref(closure_binding);
    let cont_sid = resolve_cont_sid(env, blk);
    let cf = hand_continuation_on(body, env, var_env, cont_param, cont_sid, &continuation.captured);
    // Load body address from the closure and
    // Tail-CC indirect-call with closure-target sig
    // `(args..., self, cont) -> i64 tail` (all-ValueRef params).
    // The cont is a heap object, so the call tail-calls (TCO via
    // return_call_indirect).
    let body_fp = body.closure_code_ref(cl_val);
    let mut sig = Signature::new(CallConv::Tail);
    for _ in args {
        push_repr_param(&mut sig, ArgRepr::Stored);
    }
    sig.params.push(AbiParam::new(types::I64)); // self
    sig.params.push(AbiParam::new(types::I64)); // cont
    sig.returns.push(AbiParam::new(types::I64));
    let sig_ref = body.b.func.import_signature(sig);
    let mut indirect_args: Vec<ir::Value> = Vec::with_capacity(args.len() * 2 + 2);
    for arg in args {
        let binding = *var_env.get(&arg.0).expect("unbound callclosure arg");
        body.push_binding_as_abi_arg(&mut indirect_args, binding, ArgRepr::Stored);
    }
    indirect_args.push(cl_val);
    indirect_args.push(cf);
    body.b.ins().return_call_indirect(sig_ref, body_fp, &indirect_args);
    Ok(())
}

fn emit_tail_call_closure<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    cont_param: ir::Value,
    closure: &Var,
    args: &[Var],
) -> Result<(), CodegenError> {
    // Tail-CC indirect-call through the closure code ptr with the
    // caller's own cont (TCO via return_call_indirect). Closure-
    // target sig `(args..., self, cont) -> i64 tail`.
    let closure_binding = *var_env.get(&closure.0).expect("unbound tailcallclosure closure");
    let cl_val = body.value_as_any_ref(closure_binding);

    let body_fp = body.closure_code_ref(cl_val);
    let mut sig = Signature::new(CallConv::Tail);
    for _ in args {
        push_repr_param(&mut sig, ArgRepr::Stored);
    }
    sig.params.push(AbiParam::new(types::I64)); // self
    sig.params.push(AbiParam::new(types::I64)); // cont
    sig.returns.push(AbiParam::new(types::I64));
    let sig_ref = body.b.func.import_signature(sig);
    let mut indirect_args: Vec<ir::Value> = Vec::with_capacity(args.len() * 2 + 2);
    for arg in args {
        let binding = *var_env.get(&arg.0).expect("unbound tailcallclosure arg");
        body.push_binding_as_abi_arg(&mut indirect_args, binding, ArgRepr::Stored);
    }
    indirect_args.push(cl_val);
    indirect_args.push(cont_param);
    body.b.ins().return_call_indirect(sig_ref, body_fp, &indirect_args);
    Ok(())
}

// Selective-receive park-site CLIF.
//
// A receive has a site and an arrival (see fz_runtime::park):
//   - the site is a read-only record emitted once: the matcher, the after
//     body's code, the pinned count, and each clause's code, bound count and
//     empty slot count.
//   - the arrival is one frame closure, [outer_cont, captures..., pinned...],
//     where pinned is the plan-indexed pinned inputs followed by prepared keys.
//
// The helper hands both to fz_receive_park_matched, which
// decides the receive. Anything but the YIELD sentinel is the closure to run
// next (the matched clause, or the `after 0` body): the receive tail-calls
// it. The sentinel is returned so the trampoline parks.
fn emit_receive_matched<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    blk: &fz_ir::Block,
    caller_fn_id: FnId,
    cont_param: ir::Value,
    clauses: &[ReceiveClause],
    dispatch: &PatternDispatchPlan<RuntimeTypePredicate>,
    after: Option<&ReceiveAfter>,
    pinned: &[Var],
    captures: &[Var],
) -> Result<(), CodegenError> {
    let fns = env
        .receive_dispatch_fn_ids
        .get(&(caller_fn_id.0, blk.id.0))
        .expect("receive dispatch fn pre-declared by planned codegen pass");
    let site_name = format!("__fz_receive_site_{}_{}", caller_fn_id.0, blk.id.0);
    let park_result = build_park_record(
        body, env, var_env, cont_param, &site_name, clauses, dispatch, after, pinned, captures, fns,
    )?;
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
pub(super) fn emit_resume_closure<M: cranelift_module::Module>(body: &mut CodegenFn<'_, '_, M>, closure: ir::Value) {
    let code = body.closure_code_ref(closure);
    let mut sig = Signature::new(CallConv::Tail);
    sig.params.push(AbiParam::new(types::I64)); // self
    sig.returns.push(AbiParam::new(types::I64));
    let sig_ref = body.b.func.import_signature(sig);
    body.b.ins().return_call_indirect(sig_ref, code, &[closure]);
}

// Build this arrival's frame, `[outer_cont, captures..., pinned...]`, and
// hand it to fz_receive_park_matched with the receive's site record.
fn build_park_record<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    cont_param: ir::Value,
    site_name: &str,
    clauses: &[ReceiveClause],
    dispatch: &PatternDispatchPlan<RuntimeTypePredicate>,
    after: Option<&ReceiveAfter>,
    pinned: &[Var],
    captures: &[Var],
    fns: &ReceiveFns,
) -> Result<ir::Value, CodegenError> {
    // Each resume body's code and the slots it keeps empty behind the captures.
    let resume_body = |fn_id: FnId| -> (FuncId, u32) {
        let cont_sid = env.body_id_for_fn(fn_id).unwrap_or_else(|| {
            panic!(
                "native receive outcome fn {} has no registered codegen body id",
                fn_id.0
            )
        });
        let code = *env.fn_ids.get(&cont_sid).expect("cont fn_id missing");
        (code, continuation_empty_slots(env, cont_sid, captures.len()) as u32)
    };
    let site = ReceiveSiteLayout {
        matcher: fns.matcher,
        after: after.map(|a| resume_body(a.body)),
        pinned_count: pinned.len() as u32,
        clauses: clauses
            .iter()
            .zip(&fns.projectors)
            .map(|(c, projector)| {
                let (code, empty_slots) = resume_body(c.body);
                let roots = clause_roots(env.module, dispatch, c);
                ReceiveClauseLayout {
                    code,
                    projector: *projector,
                    root_count: roots.roots.len() as u32,
                    argument_count: c.arguments.len() as u32,
                    empty_slots,
                }
            })
            .collect(),
    };
    // The frame is never called. Its code word names the receive's first
    // outcome: the first clause, or the `after` body when the receive has no
    // clause.
    let frame_code = site
        .clauses
        .first()
        .map(|clause| clause.code)
        .or(site.after.map(|(code, _)| code))
        .expect("a receive has a clause or an after body");
    let site_data = define_receive_site(body.jmod, site_name, &site)?;
    let site_addr = data_addr(body.jmod, site_data, body.b);

    let mut frame_captures: Vec<ClosureCapture> = Vec::with_capacity(captures.len() + pinned.len());
    for capture in captures {
        frame_captures.push(closure_capture_for_var(body, var_env, capture.0));
    }
    for pinned_var in pinned {
        frame_captures.push(closure_capture_for_var(body, var_env, pinned_var.0));
    }
    let frame = build_cont_closure(body, cont_param, frame_code, &frame_captures, 0);

    let after_ms = match after {
        Some(a) => body.as_raw_i64(var_env, a.timeout.0),
        None => body.b.ins().iconst(types::I64, -1),
    };
    let process = body.process_arg();
    let park_inst = runtime_call!(body, fz_receive_park_matched, [process, site_addr, frame, after_ms]);
    Ok(body.b.inst_results(park_inst)[0])
}
