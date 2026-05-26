//! Terminator emission for fz IR blocks.

use super::*;
use crate::fz_ir::Term;
use cranelift_codegen::ir::{
    self, AbiParam, BlockArg, InstBuilder, MemFlags, Signature, condcodes::IntCC, types,
};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{FuncId, Linkage};
use fz_runtime::heap::Schema;
use std::collections::HashMap;

#[allow(clippy::too_many_arguments)]
pub(crate) fn emit_terminator<
    M: cranelift_module::Module,
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    t: &mut T,
    env: &CodegenEnv<'_>,
    schemas: &[Schema],
    var_env: &HashMap<u32, CodegenValue>,
    blk: &crate::fz_ir::Block,
    block_map: &HashMap<u32, ir::Block>,
    is_native: bool,
    is_cont_fn: bool,
    this_spec_id: u32,
    caller_fn_id: crate::fz_ir::FnId,
    cont_ptr_known_null: bool,
    frame_ptr: Option<ir::Value>,
    host_ctx: Option<ir::Value>,
    cont_param: Option<ir::Value>,
    cache: &mut CodegenCache,
    block_env: Option<&HashMap<crate::fz_ir::Var, crate::types::Ty>>,
) -> Result<(), CodegenError> {
    let runtime = env.runtime;
    let fn_types = env.fn_types;
    let spec_registry = env.spec_registry;
    let fn_ids = env.fn_ids;
    let param_reprs = env.param_reprs;
    let return_reprs = env.return_reprs;
    let natively_callable = env.natively_callable;
    let closure_n_captures = env.closure_n_captures;
    let module = env.module;

    let callee_is_native = |id: u32| natively_callable.contains(&crate::fz_ir::FnId(id));
    // fz-uwq.5 — Cont dispatch reads from `fn_types.dispatches[cid]`.
    // The typer has already normalized recursive direct-call keys and
    // used those same keys for dispatch and return propagation, so the
    // SpecId resolved here is the one the worklist proved reachable.
    // fz-kgk + fz-uwq.12 — `fn_types.dispatches` keyed by the term's
    // intrinsic `CallsiteIdent` is the authoritative dispatch source.
    // The ident is positional-rewrite invariant (fuse moves the Term,
    // ident comes along); the older block_env recompute fallback is
    // gone.
    let resolve_cont_sid = |blk: &crate::fz_ir::Block, _continuation: &crate::fz_ir::Cont| -> u32 {
        let term_ident = blk
            .terminator
            .ident()
            .expect("resolve_cont_sid called on non-call-shape terminator");
        let cid = crate::fz_ir::CallsiteId {
            caller: caller_fn_id,
            ident: term_ident.clone(),
            slot: crate::fz_ir::EmitSlot::Cont,
        };
        let target = fn_types.dispatches.get(&cid).unwrap_or_else(|| {
            let mut available: Vec<String> = fn_types
                .dispatches
                .keys()
                .map(|k| format!("{:?}", k))
                .collect();
            available.sort();
            panic!(
                "fz-kgk: no dispatches entry for Cont at {:?} — typer-authoritative \
                 invariant violated; available dispatches: [{}]",
                cid,
                available.join(", ")
            )
        });
        spec_registry
            .resolve_spec_key(t, target)
            .map(|s| s.0)
            .unwrap_or_else(|| {
                panic!(
                    "fz-kgk: dispatches[{:?}] = {:?} but no SpecId registered",
                    cid, target
                )
            })
    };
    // fz-qbg.2 — Resolve callee spec by querying with FLOW-NARROWED arg
    // types from the current block's typer env (`fn_types.block_envs`),
    // not the def-site types (`fn_types.vars`). The dispatcher in
    // multi-clause (and any `if`/`case` pattern-bind narrowing) refines
    // an entry-block Var's type via per-block narrowing; the typer
    // registers callee specs keyed against that narrowing, so the
    // codegen lookup must use the same. Falls back to def-site when a
    // block env entry is absent (e.g. for Vars defined later in the
    // block — though calls in fz CPS-form only see args bound at or
    // before the terminator, so this is rare).
    let resolve_callee_sid_in = |_callee: crate::fz_ir::FnId,
                                 _args: &[crate::fz_ir::Var],
                                 _block_id: crate::fz_ir::BlockId,
                                 term_ident: &crate::fz_ir::CallsiteIdent|
     -> u32 {
        // fz-kgk + fz-uwq.12 — see resolve_cont_sid.
        let cid = crate::fz_ir::CallsiteId {
            caller: caller_fn_id,
            ident: term_ident.clone(),
            slot: crate::fz_ir::EmitSlot::Direct,
        };
        let target = fn_types.dispatches.get(&cid).unwrap_or_else(|| {
            panic!(
                "fz-kgk: no dispatches entry for Direct at {:?} — typer-authoritative \
                 invariant violated",
                cid
            )
        });
        spec_registry
            .resolve_spec_key(t, target)
            .map(|s| s.0)
            .unwrap_or_else(|| {
                panic!(
                    "fz-kgk: dispatches[{:?}] = {:?} but no SpecId registered",
                    cid, target
                )
            })
    };
    let resolve_callee_sid = |callee: crate::fz_ir::FnId, args: &[crate::fz_ir::Var]| -> u32 {
        let term_ident = blk
            .terminator
            .ident()
            .expect("resolve_callee_sid called on non-call-shape terminator");
        resolve_callee_sid_in(callee, args, blk.id, term_ident)
    };

    match &blk.terminator {
        Term::Goto(target, args) => {
            let tgt = *block_map.get(&target.0).unwrap();
            let arg_vals: Vec<BlockArg> = args
                .iter()
                .map(|v| BlockArg::Value(var_env.get(&v.0).expect("unbound goto arg").value()))
                .collect();
            b.ins().jump(tgt, &arg_vals);
        }
        Term::If {
            cond: c,
            then_b: t,
            else_b: e,
            ..
        } => {
            let vb = var_env.get(&c.0).expect("unbound if cond");
            let t_b = *block_map.get(&t.0).unwrap();
            let e_b = *block_map.get(&e.0).unwrap();
            let no_args: Vec<BlockArg> = Vec::new();
            let truthy = if matches!(vb.repr(), ArgRepr::Condition) {
                vb.value()
            } else {
                codegen_value_truthy(b, jmod, runtime, *vb)
            };
            b.ins().brif(truthy, t_b, &no_args, e_b, &no_args);
        }
        Term::Halt(v) => {
            let binding = *var_env.get(&v.0).expect("unbound halt val");
            let _ = host_ctx;
            emit_halt_for_binding(b, jmod, runtime, var_env, cache, v.0, binding);
            if is_native {
                // fz-ul4.27.6.4 — native fn: propagate halt via the
                // native return register. fz_halt already recorded
                // process.halt_value; the actual bits are unobservable
                // but the Cranelift sig requires a typed return.
                // fz-ul4.27.13: dead-code halt blocks (match_error etc.)
                // still need a well-typed return — iconst(0) satisfies
                // the i64 sig without depending on val's repr.
                let zero = b.ins().iconst(types::I64, 0);
                b.ins().return_(&[zero]);
            } else {
                // Uniform fn: trampoline sentinel is null.
                let null = b.ins().iconst(types::I64, 0);
                b.ins().return_(&[null]);
            }
        }
        Term::Return(v) => {
            if is_native {
                let this_demand = DemandAbi::new(&env.spec_keys[this_spec_id as usize]);
                if this_demand.delivers_list_tail_return()
                    && let Some(elems) = cache.list_tail_return_elems.get(&v.0).cloned()
                {
                    let delivered = emit_list_tail_return_value(
                        b, jmod, t, env, var_env, cache, block_env, &elems,
                    );
                    let cont_val = if is_cont_fn {
                        let self_val = cont_param.expect("cont fn binds self via cont_param");
                        load_outer_cont_ref(b, jmod, runtime, self_val)
                    } else {
                        cont_param.expect("non-cont native fn has cont_param")
                    };
                    let code = load_closure_code_ref(b, jmod, runtime, cont_val);
                    let mut sig = Signature::new(CallConv::Tail);
                    sig.params.push(AbiParam::new(types::I64));
                    sig.params.push(AbiParam::new(types::I64));
                    sig.returns.push(AbiParam::new(types::I64));
                    let sigref = b.import_signature(sig);
                    b.ins()
                        .return_call_indirect(sigref, code, &[delivered, cont_val]);
                    return Ok(());
                }
                if let Some(arity) = this_demand.tuple_field_arity()
                    && let Some(fields) = cache.tuple_return_fields.get(&v.0)
                {
                    let fields = fields.clone();
                    debug_assert_eq!(fields.len(), arity);
                    let cont_val = if is_cont_fn {
                        let self_val = cont_param.expect("cont fn binds self via cont_param");
                        load_outer_cont_ref(b, jmod, runtime, self_val)
                    } else {
                        cont_param.expect("non-cont native fn has cont_param")
                    };
                    let code = load_closure_code_ref(b, jmod, runtime, cont_val);
                    let mut sig = Signature::new(CallConv::Tail);
                    let mut cont_args = Vec::with_capacity(fields.len() + 1);
                    for field in fields {
                        let binding = *var_env.get(&field.0).expect("unbound tuple return field");
                        let repr = binding.repr();
                        push_repr_param(&mut sig, repr);
                        push_binding_as_abi_args(
                            &mut cont_args,
                            b,
                            jmod,
                            runtime,
                            cache,
                            binding,
                            repr,
                        );
                    }
                    sig.params.push(AbiParam::new(types::I64));
                    sig.returns.push(AbiParam::new(types::I64));
                    let sigref = b.import_signature(sig);
                    cont_args.push(cont_val);
                    b.ins().return_call_indirect(sigref, code, &cont_args);
                    return Ok(());
                }
                // fz-ul4.27.22.3 — native Term::Return per docs/cps-in-clif.md
                // §2.1: read cont code_ptr; return_call_indirect sig(val, cont).
                // Cont fns fetch outer_cont from `self`; non-cont fns
                // use their cont_param SSA. Sig and val coerce match this
                // fn's narrow return_repr — the cont body was chosen at
                // construction time to match (per fz-ul4.27.22.3
                // halt-cont typing + cont-seam narrowing in
                // build_fn_signature).
                //
                // fz-try.15 — closure-target bodies coerce to ValueRef
                // unconditionally to match the seam ABI (matches
                // build_fn_signature's closure-target return = i64).
                // Cont fns retain narrow return_repr — they're not at
                // the indirect seam.
                let is_closure_target_body =
                    closure_n_captures.contains_key(&caller_fn_id) && !is_cont_fn;
                let my_return_repr = if is_closure_target_body {
                    ArgRepr::ValueRef
                } else {
                    return_reprs[this_spec_id as usize]
                };
                let from = var_env.get(&v.0).map_or(ArgRepr::ValueRef, |vb| vb.repr());
                let cont_val = if is_cont_fn {
                    let self_val = cont_param.expect("cont fn binds self via cont_param");
                    load_outer_cont_ref(b, jmod, runtime, self_val)
                } else {
                    cont_param.expect("non-cont native fn has cont_param")
                };
                let code = load_closure_code_ref(b, jmod, runtime, cont_val);
                let mut sig = Signature::new(CallConv::Tail);
                push_repr_param(&mut sig, my_return_repr);
                sig.params.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
                let sigref = b.import_signature(sig);
                let mut cont_args = Vec::with_capacity(2);
                if my_return_repr == ArgRepr::ValueRef {
                    let binding = *var_env.get(&v.0).expect("unbound return val");
                    push_binding_as_abi_args(
                        &mut cont_args,
                        b,
                        jmod,
                        runtime,
                        cache,
                        binding,
                        ArgRepr::ValueRef,
                    );
                } else {
                    let val = var_env.get(&v.0).expect("unbound return val").value();
                    push_repr_arg(&mut cont_args, b, jmod, runtime, val, from, my_return_repr);
                }
                cont_args.push(cont_val);
                b.ins().return_call_indirect(sigref, code, &cont_args);
            } else if cont_ptr_known_null {
                let value = *var_env.get(&v.0).expect("unbound return val");
                // fz-ul4.27.18: this fn is never a cont target; cont_ptr
                // is statically null. Skip the load/icmp/brif dispatch.
                emit_halt_and_return_null(b, jmod, runtime, cache, value);
            } else {
                let value = *var_env.get(&v.0).expect("unbound return val");
                emit_return(b, jmod, runtime, cache, frame_ptr, value);
            }
        }
        Term::Call {
            ident: _,
            callee,
            args,
            continuation,
        } => {
            let cap_vals: Vec<ir::Value> = continuation
                .captured
                .iter()
                .map(|v| var_env.get(&v.0).expect("unbound captured val").value())
                .collect();
            // fz-ul4.29.7: resolve callee → narrow SpecId.0 (falls
            // back to any-key == callee.0 via subsumption).
            // fz-ul4.29.12.1: resolve the Cont to its narrow
            // SpecId.0 too (typer registers one per Cont site;
            // any-key is the subsumption backstop).
            let callee_sid = resolve_callee_sid(*callee, args);
            let mut cont_sid = resolve_cont_sid(blk, continuation);
            let this_demand = DemandAbi::new(&env.spec_keys[this_spec_id as usize]);
            let cont_cid = crate::fz_ir::CallsiteId {
                caller: caller_fn_id,
                ident: blk
                    .terminator
                    .ident()
                    .expect("Term::Call must carry callsite ident")
                    .clone(),
                slot: crate::fz_ir::EmitSlot::Cont,
            };
            if env.spec_keys[this_spec_id as usize].demand.is_value()
                && let Some(crate::ir_typer::fn_types::ListTailPlan::ContinuationEmptyTail {
                    target,
                    ..
                }) = fn_types.list_tail_plans.get(&cont_cid)
                && let Some(sid) = spec_registry.resolve_spec_key(t, target)
            {
                cont_sid = sid.0;
            }
            let cont_demand = DemandAbi::new(&env.spec_keys[cont_sid as usize]);
            if this_demand.carries_list_tail_capture()
                && args.len() == 1
                && continuation.captured.len() >= 2
                && callee_is_native(callee.0)
                && callee_is_native(continuation.fn_id.0)
                && DemandAbi::new(&env.spec_keys[callee_sid as usize]).has_list_tail_context()
                && cont_demand.has_list_tail_context()
            {
                let Some((pivot_capture, tail_capture)) = list_tail_cont_captures(continuation)
                else {
                    return Err(CodegenError::new(
                        "ListTail continuation plan missing pivot/tail captures",
                    ));
                };
                let hi_arg = [tail_capture];
                let callee_param_reprs = &param_reprs[callee_sid as usize];
                let callee_fid = *fn_ids.get(&callee_sid).expect("callee fn_id missing");
                let callee_fref = jmod.declare_func_in_func(callee_fid, b.func);
                let mut native_args = coerce_call_args(
                    &hi_arg,
                    callee_param_reprs,
                    var_env,
                    b,
                    jmod,
                    runtime,
                    cache,
                );
                native_args.push(list_tail_destination_arg(b, cache));
                let cont_fid = *fn_ids.get(&cont_sid).expect("cont fn_id missing");
                let cap_bindings = [
                    closure_capture_for_var(var_env, b, jmod, runtime, pivot_capture.0, cache),
                    closure_capture_for_var(var_env, b, jmod, runtime, args[0].0, cache),
                ];
                let cont_arg = build_cont_closure(
                    jmod,
                    b,
                    runtime,
                    return_reprs,
                    is_cont_fn,
                    cont_param,
                    frame_ptr,
                    cont_sid,
                    cont_fid,
                    &cap_bindings,
                    &[],
                );
                native_args.push(cont_arg);
                b.ins().return_call(callee_fref, &native_args);
                return Ok(());
            }
            if this_demand.delivers_list_tail_return()
                && args.len() == 1
                && continuation.captured.len() >= 2
                && callee_is_native(callee.0)
            {
                let caller_fn = module.fn_by_id(caller_fn_id);
                let entry = caller_fn.block(caller_fn.entry);
                let Some((pivot_capture, tail_capture)) = list_tail_cont_captures(continuation)
                else {
                    return Err(CodegenError::new(
                        "ListTail continuation plan missing pivot/tail captures",
                    ));
                };
                if entry.params.first().copied() == Some(tail_capture) {
                    let tail_var = tail_capture;
                    let tail_bits = any_ref_for_var(var_env, b, jmod, runtime, tail_var.0, cache);
                    let pivot_tail = emit_list_cons_bif(
                        b,
                        jmod,
                        runtime,
                        var_env,
                        pivot_capture,
                        expected_runtime_value_kind(t, fn_types, block_env, pivot_capture),
                        ListTailBits::ValueRef(tail_bits),
                        cache,
                    );
                    let callee_param_reprs = &param_reprs[callee_sid as usize];
                    let callee_fid = *fn_ids.get(&callee_sid).expect("callee fn_id missing");
                    let callee_fref = jmod.declare_func_in_func(callee_fid, b.func);
                    let mut native_args = coerce_call_args(
                        args,
                        callee_param_reprs,
                        var_env,
                        b,
                        jmod,
                        runtime,
                        cache,
                    );
                    native_args.push(pivot_tail);
                    let tail_cont_arg = if is_cont_fn {
                        let self_val = cont_param.expect("cont fn binds self via cont_param");
                        load_outer_cont_ref(b, jmod, runtime, self_val)
                    } else {
                        cont_param.expect("non-cont native fn has cont_param")
                    };
                    native_args.push(tail_cont_arg);
                    b.ins().return_call(callee_fref, &native_args);
                    return Ok(());
                }
            }
            if callee_is_native(callee.0) {
                // fz-ul4.27.13 — coerce each arg from its current var
                // repr to the callee's param_repr. Result rides back
                // in the callee's return_repr; we then coerce it to
                // ValueRef for the cont (cont is the any-key spec by
                // invariant — all-ValueRef param_reprs, AnyValue cont
                // frame slot 1).
                let callee_param_reprs = &param_reprs[callee_sid as usize];
                let callee_ret_repr = return_reprs[callee_sid as usize];
                let callee_fid = *fn_ids.get(&callee_sid).expect("callee fn_id missing");
                let callee_fref = jmod.declare_func_in_func(callee_fid, b.func);
                let mut native_args =
                    coerce_call_args(args, callee_param_reprs, var_env, b, jmod, runtime, cache);
                // fz-cps.1.8 — if the callee is a closure-target fn,
                // its sig is `(args..., self, cont) tail`. Direct
                // callers load the per-Process static singleton and
                // pass it as `self`. The zero-cap invariant (asserted
                // at closure_target_fns build) means the body ignores
                // self at runtime, so a singleton with no captures is
                // valid for any direct-call site.
                if closure_n_captures.contains_key(callee) {
                    native_args.push(fetch_static_closure(jmod, b, runtime, callee.0));
                }
                if DemandAbi::new(&env.spec_keys[callee_sid as usize]).has_list_tail_context() {
                    native_args.push(list_tail_destination_arg(b, cache));
                }
                // fz-cps.1.a: trailing cont arg per §2.1. Native
                // caller forwards its cont SSA; uniform caller passes
                // fz-cps.1.2 — chained-native cutover. Build the cont
                // closure BEFORE the callee call so the callee's
                // Term::Return can indirect-call through it (§2.1).
                // The closure's user captures must be stored before
                // the call too, since the cont body loads them on
                // entry. After the callee call, the chain unwinds
                // via halt-cont's regular return; the caller body
                // just returns whatever propagated.
                let cont_is_native = callee_is_native(continuation.fn_id.0);
                let cl_ptr_opt: Option<ir::Value> = if cont_is_native {
                    let cont_fid = *fn_ids.get(&cont_sid).expect("cont fn_id missing");
                    let cap_bindings: Vec<ClosureCapture> = continuation
                        .captured
                        .iter()
                        .map(|cv| closure_capture_for_var(var_env, b, jmod, runtime, cv.0, cache))
                        .collect();
                    let extra_ref_captures =
                        cont_extra_ref_captures(b, cache, &env.spec_keys[cont_sid as usize]);
                    Some(build_cont_closure(
                        jmod,
                        b,
                        runtime,
                        return_reprs,
                        is_cont_fn,
                        cont_param,
                        frame_ptr,
                        cont_sid,
                        cont_fid,
                        &cap_bindings,
                        &extra_ref_captures,
                    ))
                } else {
                    None
                };
                // cont arg passed to the callee: cl_ptr for native cont,
                // else cont_param fallback (uniform-cont path). fz-cps.1.11:
                // when the cont-fn is uniform (rare; really only main's
                // halt-style cont after the parking-reachable lift) and
                // we have no cont_param, build a halt-cont closure inline
                // so the callee's Term::Return doesn't load through null+16.
                // synth_halt_cont tracks the latter: the callee chains
                // all the way into the halt-cont body, so the caller
                // must NOT execute its uniform-cont write-back after
                // the call (that would double-halt with the wrong value).
                let mut synth_halt_cont = false;
                let cont_arg = if let Some(cl_ptr) = cl_ptr_opt {
                    cl_ptr
                } else {
                    match cont_param {
                        Some(c) => c,
                        None => {
                            synth_halt_cont = true;
                            synthesize_halt_cont(jmod, b, runtime, callee_ret_repr)
                        }
                    }
                };
                native_args.push(cont_arg);

                if (cl_ptr_opt.is_some() || synth_halt_cont) && is_native {
                    // fz-cps.1.8 — native→native chained call uses
                    // return_call (TCO via Tail-CC). The callee's
                    // Term::Return tail-chains into the cont closure
                    // we built above. Matches §8.2 target clif.
                    // Repr invariant: natively_callable fixed-point guarantees
                    // return_reprs[this_spec_id] == callee_ret_repr here.
                    b.ins().return_call(callee_fref, &native_args);
                } else if cl_ptr_opt.is_some() || synth_halt_cont {
                    // Uniform caller → native callee (chained). Can't
                    // return_call across CC; synchronous call then
                    // return the chain-final value (halt_value already
                    // set by the time we get here). Call result is
                    // intentionally discarded — chain unwinds via halt-cont.
                    b.ins().call(callee_fref, &native_args);
                    let zero = b.ins().iconst(types::I64, 0);
                    b.ins().return_(&[zero]);
                } else {
                    let call_inst = b.ins().call(callee_fref, &native_args);
                    let result = b.inst_results(call_inst)[0];
                    let cont_schema = &schemas[cont_sid as usize];
                    let alloc_fref = jmod.declare_func_in_func(runtime.alloc_id, b.func);
                    let sid = b.ins().iconst(types::I32, cont_sid as i64);
                    let sz = b
                        .ins()
                        .iconst(types::I32, cont_schema.allocation_payload_size() as i64);
                    let alloc_call = b.ins().call(alloc_fref, &[sid, sz]);
                    let cf = b.inst_results(alloc_call)[0];
                    let my_cont = b.ins().load(
                        types::I64,
                        MemFlags::trusted(),
                        frame_ptr.expect(
                            "Term::Call uniform-cont write-back reached from \
                             native-fn body — natively_callable invariant violated",
                        ),
                        HEADER_SIZE,
                    );
                    b.ins().store(MemFlags::trusted(), my_cont, cf, HEADER_SIZE);
                    // fz-ul4.29.12.1: result + captures are written
                    // into the cont's typed entry slots. The native
                    // result already has an ABI repr; captured vars
                    // still come from the local binding table.
                    let mut payload: Vec<(ir::Value, ArgRepr)> =
                        Vec::with_capacity(continuation.captured.len() + 1);
                    payload.push((result, callee_ret_repr));
                    for (cv, val) in continuation.captured.iter().zip(cap_vals.iter()) {
                        let from = var_env.get(&cv.0).map_or(ArgRepr::ValueRef, |vb| vb.repr());
                        payload.push((*val, from));
                    }
                    store_typed_args_into_callee_frame(
                        b,
                        jmod,
                        runtime,
                        cache,
                        cont_schema,
                        cf,
                        &payload,
                        1,
                    );
                    b.ins().return_(&[cf]);
                }
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
                    b,
                    jmod,
                    runtime,
                    schemas,
                    frame_ptr,
                    callee_sid,
                    &arg_bindings,
                    Some((cont_sid, &cap_bindings)),
                    cache,
                );
            }
        }
        Term::TailCall {
            ident: _,
            callee,
            args,
            is_back_edge,
        } => {
            let callee_sid = resolve_callee_sid(*callee, args);
            if callee_is_native(callee.0) {
                // fz-ul4.27.6.2.3 / .27.13 — TailCall to a native callee.
                // Coerce each arg from its current var repr to the
                // callee's param_repr. The natively_callable fixed point
                // guarantees callee's return_repr matches mine, so
                // return_call is ABI-compatible without further coerce.
                let callee_param_reprs = &param_reprs[callee_sid as usize];
                let callee_ret_repr = return_reprs[callee_sid as usize];
                let callee_fid = *fn_ids.get(&callee_sid).expect("callee fn_id missing");
                let callee_fref = jmod.declare_func_in_func(callee_fid, b.func);
                let mut native_args =
                    Vec::with_capacity(callee_param_reprs.iter().map(ArgRepr::abi_arity).sum());
                let mut mid_flight_arg_shapes: Vec<MidFlightArgShape> =
                    Vec::with_capacity(callee_param_reprs.len() + 2);
                for (i, av) in args.iter().enumerate() {
                    let binding = *var_env.get(&av.0).expect("unbound call arg");
                    let to = callee_param_reprs[i];
                    if to == ArgRepr::ValueRef {
                        push_binding_as_abi_args(
                            &mut native_args,
                            b,
                            jmod,
                            runtime,
                            cache,
                            binding,
                            to,
                        );
                    } else {
                        let value = coerce_binding_to(b, jmod, runtime, binding, to);
                        native_args.push(value);
                    }
                    mid_flight_arg_shapes.push(MidFlightArgShape::Value(to));
                }
                // fz-cps.1.8 — TailCall to a closure-target fn: insert
                // static singleton as `self` before cont. Mirror of
                // the Term::Call path; same zero-cap invariant lets
                // any singleton serve as self (body ignores it).
                if closure_n_captures.contains_key(callee) {
                    let static_closure = fetch_static_closure(jmod, b, runtime, callee.0);
                    native_args.push(static_closure);
                    mid_flight_arg_shapes.push(MidFlightArgShape::HeapRef);
                }
                if DemandAbi::new(&env.spec_keys[callee_sid as usize]).has_list_tail_context() {
                    native_args.push(list_tail_destination_arg(b, cache));
                    mid_flight_arg_shapes.push(MidFlightArgShape::HeapRef);
                }
                // fz-cps.1.a: trailing cont arg per §2.1. fz-cps.1.11:
                // build halt-cont closure inline when uniform-tier
                // caller (cont_param=None) tail-calls native callee,
                // so the callee's Term::Return doesn't deref null.
                // fz-cps.1.12: cont fns forward outer_cont from their
                // closure env; cont_param for cont fns is self.
                let mut synth_halt_cont = false;
                let tail_cont_arg = if is_cont_fn {
                    let self_val = cont_param.expect("cont fn binds self via cont_param");
                    load_outer_cont_ref(b, jmod, runtime, self_val)
                } else {
                    match cont_param {
                        Some(c) => c,
                        None => {
                            synth_halt_cont = true;
                            synthesize_halt_cont(jmod, b, runtime, callee_ret_repr)
                        }
                    }
                };
                native_args.push(tail_cont_arg);
                mid_flight_arg_shapes.push(MidFlightArgShape::HeapRef);
                if is_native {
                    // Native-to-native TailCall: use return_call so
                    // recursive tail calls reuse the same stack frame
                    // (TCO). Without this, count_100k blows the stack.
                    //
                    // fz-02r.5 — back-edge cooperative yield check. Only
                    // allocation-capable native loop bodies can set the
                    // heap-pressure flag that this path services. Pure
                    // scalar loops stay a plain return_call and keep their
                    // zero-allocation CLIF contract.
                    if *is_back_edge && env.spec_heap_allocates[this_spec_id as usize] {
                        let yield_gv =
                            jmod.declare_data_in_func(runtime.should_yield_data_id, b.func);
                        let flag_ptr = b.ins().global_value(types::I64, yield_gv);
                        let flag = b.ins().load(types::I8, MemFlags::trusted(), flag_ptr, 0);
                        let flag64 = b.ins().uextend(types::I64, flag);
                        let zero64 = b.ins().iconst(types::I64, 0);
                        let is_set = b.ins().icmp(IntCC::NotEqual, flag64, zero64);
                        let yield_blk = b.create_block();
                        let proceed_blk = b.create_block();
                        let no_args: Vec<BlockArg> = Vec::new();
                        b.ins()
                            .brif(is_set, yield_blk, &no_args, proceed_blk, &no_args);

                        // yield block: capture next-iteration args into a
                        // scheduler-runnable closure and yield that closure
                        // as the primary mid-flight GC root.
                        b.switch_to_block(yield_blk);
                        b.seal_block(yield_blk);
                        let cont_key = (callee_sid, mid_flight_arg_shapes.clone());
                        let cont_id = *env
                            .mid_flight_cont_tail_fn_ids
                            .get(&cont_key)
                            .unwrap_or_else(|| {
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
                                let root = shape.capture_from_args(b, &native_args, abi_cursor);
                                abi_cursor += shape.abi_arity();
                                root
                            })
                            .collect();
                        debug_assert_eq!(abi_cursor, native_args.len());
                        let alloc_fref =
                            jmod.declare_func_in_func(runtime.alloc_closure_id, b.func);
                        let fid_v = b.ins().iconst(types::I32, callee_sid as i64);
                        let n_caps_v = b.ins().iconst(types::I32, native_root_values.len() as i64);
                        let stub_fref = jmod.declare_func_in_func(cont_id, b.func);
                        let stub_addr = b.ins().func_addr(types::I64, stub_fref);
                        let zero_hk = b.ins().iconst(types::I32, 0);
                        let alloc_inst = b
                            .ins()
                            .call(alloc_fref, &[fid_v, n_caps_v, zero_hk, stub_addr]);
                        let cont_closure = b.inst_results(alloc_inst)[0];
                        let captured_count = native_root_values.len();
                        for (i, root) in native_root_values.iter().copied().enumerate() {
                            let root_ref = codegen_value_as_any_ref(b, jmod, runtime, cache, root);
                            store_closure_capture_ref_word(
                                b,
                                jmod,
                                runtime,
                                cont_closure,
                                captured_count,
                                i,
                                root_ref,
                            );
                        }
                        let yield_fref =
                            jmod.declare_func_in_func(runtime.yield_mid_flight_id, b.func);
                        let yield_inst = b.ins().call(yield_fref, &[cont_closure]);
                        let yield_ret = b.inst_results(yield_inst)[0];
                        b.ins().return_(&[yield_ret]);

                        // proceed block: normal TCO.
                        b.switch_to_block(proceed_blk);
                        b.seal_block(proceed_blk);
                    }
                    b.ins().return_call(callee_fref, &native_args);
                } else if synth_halt_cont {
                    // fz-cps.1.11 — uniform caller + native callee
                    // with synthesized halt-cont: callee's chain runs
                    // all the way through halt_cont_body. Caller must
                    // NOT do post-call uniform write-back (would
                    // double-halt with the wrong value).
                    let _ = b.ins().call(callee_fref, &native_args);
                    let zero = b.ins().iconst(types::I64, 0);
                    b.ins().return_(&[zero]);
                } else {
                    // Uniform caller: synchronous call, then write result
                    // into MY cont according to the continuation schema.
                    let call_inst = b.ins().call(callee_fref, &native_args);
                    let result = b.inst_results(call_inst)[0];
                    let result_value = CodegenValue::from_abi_value(result, callee_ret_repr);
                    let my_cont = b.ins().load(
                        types::I64,
                        MemFlags::trusted(),
                        frame_ptr.expect(
                            "Term::TailCall uniform-caller writeback reached from \
                             native-fn body — natively_callable invariant violated",
                        ),
                        HEADER_SIZE,
                    );
                    // Halt path: my_cont may be null on the top frame.
                    let zero = b.ins().iconst(types::I64, 0);
                    let is_null = b.ins().icmp(IntCC::Equal, my_cont, zero);
                    let halt_blk = b.create_block();
                    let invoke_blk = b.create_block();
                    let no_args: Vec<BlockArg> = Vec::new();
                    b.ins()
                        .brif(is_null, halt_blk, &no_args, invoke_blk, &no_args);
                    b.switch_to_block(halt_blk);
                    b.seal_block(halt_blk);
                    let _ = host_ctx;
                    emit_halt_from_codegen_value(b, jmod, runtime, cache, result_value);
                    let null = b.ins().iconst(types::I64, 0);
                    b.ins().return_(&[null]);
                    b.switch_to_block(invoke_blk);
                    b.seal_block(invoke_blk);
                    store_frame_value_dynamic(
                        b,
                        jmod,
                        runtime,
                        cache,
                        my_cont,
                        SLOT_BYTES as u32,
                        result_value,
                    );
                    b.ins().return_(&[my_cont]);
                }
            } else {
                let arg_bindings: Vec<CodegenValue> = args
                    .iter()
                    .map(|v| *var_env.get(&v.0).expect("unbound tailcall arg"))
                    .collect();
                emit_tail_call(
                    b,
                    jmod,
                    runtime,
                    schemas,
                    this_spec_id,
                    frame_ptr,
                    callee_sid,
                    &arg_bindings,
                    cache,
                );
            }
        }
        Term::CallClosure {
            ident: _,
            closure,
            args,
            continuation,
        } => {
            // Closure invocation is opaque to the caller: read code_ptr
            // through the runtime ABI and call it with args, self, and cont.
            let cl_val = var_env
                .get(&closure.0)
                .expect("unbound callclosure closure")
                .value();
            let arg_vals: Vec<ir::Value> = args
                .iter()
                .map(|v| var_env.get(&v.0).expect("unbound callclosure arg").value())
                .collect();
            // Build the continuation as a closure env. The body will
            // project any captures it needs from `self`.
            let cont_sid = resolve_cont_sid(blk, continuation);
            let cont_fid = *fn_ids.get(&cont_sid).expect("cont fn_id missing");
            let cap_bindings: Vec<ClosureCapture> = continuation
                .captured
                .iter()
                .map(|cv| closure_capture_for_var(var_env, b, jmod, runtime, cv.0, cache))
                .collect();
            let extra_ref_captures =
                cont_extra_ref_captures(b, cache, &env.spec_keys[cont_sid as usize]);
            let cf = build_cont_closure(
                jmod,
                b,
                runtime,
                return_reprs,
                is_cont_fn,
                cont_param,
                frame_ptr,
                cont_sid,
                cont_fid,
                &cap_bindings,
                &extra_ref_captures,
            );
            // fz-t45 — singleton closure-lit fast path for non-tail
            // closure calls. If this spec types `closure` as a single
            // closure_lit(F, K), resolve F's narrow body spec at
            // [K..., arg_descrs...] and call it directly with the
            // body's narrow ABI, threading the synthesized cont closure
            // as the callee's `cont` argument. Opaque / polymorphic
            // closures still fall back to the all-ValueRef indirect seam.
            let lit_resolved: Option<(u32, FuncId, usize)> = (|| {
                let (body_fn_id, body_sid) =
                    resolve_tcc_body(t, closure, args, fn_types, module, spec_registry)?;
                let body_fid = *fn_ids.get(&body_sid)?;
                let n_caps = closure_n_captures.get(&body_fn_id).copied().unwrap_or(0);
                Some((body_sid, body_fid, n_caps))
            })();
            if let Some((body_sid, body_fid, n_caps)) = lit_resolved {
                let body_param_reprs = &param_reprs[body_sid as usize];
                let body_fref = jmod.declare_func_in_func(body_fid, b.func);
                let mut direct_args: Vec<ir::Value> = Vec::with_capacity(arg_vals.len() + 2);
                for (i, _v) in arg_vals.iter().enumerate() {
                    let binding = *var_env.get(&args[i].0).expect("unbound callclosure arg");
                    let to = body_param_reprs
                        .get(n_caps + i)
                        .copied()
                        .unwrap_or(ArgRepr::ValueRef);
                    push_binding_as_abi_args(
                        &mut direct_args,
                        b,
                        jmod,
                        runtime,
                        cache,
                        binding,
                        to,
                    );
                }
                direct_args.push(cl_val);
                direct_args.push(cf);
                let _ = host_ctx;
                if is_native {
                    b.ins().return_call(body_fref, &direct_args);
                } else {
                    let call_inst = b.ins().call(body_fref, &direct_args);
                    let result = b.inst_results(call_inst)[0];
                    b.ins().return_(&[result]);
                }
                return Ok(());
            }
            // fz-cps.1.8 — ask runtime for the closure body address and
            // Tail-CC indirect-call with closure-target sig `(args..., self,
            // cont) -> i64 tail`. All-ValueRef params. Native callers
            // use return_call_indirect (TCO); uniform callers use
            // call_indirect Tail (cross-CC) and return result.
            let body_fp = load_closure_code_ref(b, jmod, runtime, cl_val);
            let mut sig = Signature::new(CallConv::Tail);
            for _ in &arg_vals {
                push_repr_param(&mut sig, ArgRepr::ValueRef);
            }
            sig.params.push(AbiParam::new(types::I64)); // self
            sig.params.push(AbiParam::new(types::I64)); // cont
            sig.returns.push(AbiParam::new(types::I64));
            let sig_ref = b.func.import_signature(sig);
            let mut indirect_args: Vec<ir::Value> = Vec::with_capacity(arg_vals.len() + 2);
            for (i, _v) in arg_vals.iter().enumerate() {
                let binding = *var_env.get(&args[i].0).expect("unbound callclosure arg");
                push_binding_as_abi_args(
                    &mut indirect_args,
                    b,
                    jmod,
                    runtime,
                    cache,
                    binding,
                    ArgRepr::ValueRef,
                );
            }
            indirect_args.push(cl_val);
            indirect_args.push(cf);
            let _ = host_ctx; // no host_ctx in closure-target sig
            if is_native {
                b.ins()
                    .return_call_indirect(sig_ref, body_fp, &indirect_args);
            } else {
                let call_inst = b.ins().call_indirect(sig_ref, body_fp, &indirect_args);
                let result = b.inst_results(call_inst)[0];
                b.ins().return_(&[result]);
            }
        }
        Term::TailCallClosure {
            closure,
            args,
            ident: _,
        } => {
            // fz-cps.1.8 — Tail-CC indirect-call through the closure code ptr with
            // the caller's own cont (TCO via return_call_indirect).
            // Closure-target sig `(args..., self, cont) -> i64 tail`.
            // For cont fns, the forwarded cont is the env's outer_cont.
            // For non-cont native fns, cont_param is the cont SSA.
            // Uniform callers load from frame_ptr+16.
            //
            // fz-ul4.27.22.11 — closure_lit fast path. When the closure
            // Var's per-spec type is a single closure_lit(F, K), resolve
            // F's narrow body spec at key [K..., arg_descrs...] and emit
            // a direct return_call. Bypasses the runtime code-pointer read and
            // uses the body's narrow ABI directly. Falls back to the
            // indirect path on union-of-lits, plain arrows, and
            // unresolved keys.
            let cl_val = var_env
                .get(&closure.0)
                .expect("unbound tailcallclosure closure")
                .value();
            let arg_vals: Vec<ir::Value> = args
                .iter()
                .map(|v| {
                    var_env
                        .get(&v.0)
                        .expect("unbound tailcallclosure arg")
                        .value()
                })
                .collect();
            let my_cont = if is_cont_fn {
                let self_val = cont_param.expect("cont fn binds self via cont_param");
                load_outer_cont_ref(b, jmod, runtime, self_val)
            } else {
                match cont_param {
                    Some(c) => c,
                    None => b.ins().load(
                        types::I64,
                        MemFlags::trusted(),
                        frame_ptr.expect("uniform TailCallClosure must have frame_ptr"),
                        HEADER_SIZE,
                    ),
                }
            };

            // fz-ul4.27.22.11 — try singleton resolution.
            let lit_resolved: Option<(u32, FuncId, usize)> = (|| {
                let (body_fn_id, body_sid) =
                    resolve_tcc_body(t, closure, args, fn_types, module, spec_registry)?;
                let body_fid = *fn_ids.get(&body_sid)?;
                let n_caps = closure_n_captures.get(&body_fn_id).copied().unwrap_or(0);
                Some((body_sid, body_fid, n_caps))
            })();

            if let Some((body_sid, body_fid, n_caps)) = lit_resolved {
                // Direct dispatch: build sig from body's narrow
                // param_reprs; emit return_call passing cl_val as self
                // and my_cont as cont.
                let body_param_reprs = &param_reprs[body_sid as usize];
                let mut sig = Signature::new(CallConv::Tail);
                // Closure-target sig: only arg slots [n_caps..] go on
                // the wire; capture slots live inside the closure heap
                // object and the body's entry harness loads them.
                for r in &body_param_reprs[n_caps..] {
                    push_repr_param(&mut sig, *r);
                }
                sig.params.push(AbiParam::new(types::I64)); // self
                sig.params.push(AbiParam::new(types::I64)); // cont
                sig.returns.push(AbiParam::new(types::I64));
                let body_fref = jmod.declare_func_in_func(body_fid, b.func);
                let mut direct_args: Vec<ir::Value> = Vec::with_capacity(arg_vals.len() + 2);
                for (i, _v) in arg_vals.iter().enumerate() {
                    let binding = *var_env
                        .get(&args[i].0)
                        .expect("unbound tailcallclosure arg");
                    let to = body_param_reprs
                        .get(n_caps + i)
                        .copied()
                        .unwrap_or(ArgRepr::ValueRef);
                    push_binding_as_abi_args(
                        &mut direct_args,
                        b,
                        jmod,
                        runtime,
                        cache,
                        binding,
                        to,
                    );
                }
                direct_args.push(cl_val);
                direct_args.push(my_cont);
                let _ = host_ctx;
                let _ = sig; // body_fref carries the signature implicitly.
                if is_native {
                    b.ins().return_call(body_fref, &direct_args);
                } else {
                    let call_inst = b.ins().call(body_fref, &direct_args);
                    let result = b.inst_results(call_inst)[0];
                    b.ins().return_(&[result]);
                }
            } else {
                // Indirect path for unresolved / union-of-lits /
                // plain-arrow closures.
                let body_fp = load_closure_code_ref(b, jmod, runtime, cl_val);
                let mut sig = Signature::new(CallConv::Tail);
                for _ in &arg_vals {
                    push_repr_param(&mut sig, ArgRepr::ValueRef);
                }
                sig.params.push(AbiParam::new(types::I64)); // self
                sig.params.push(AbiParam::new(types::I64)); // cont
                sig.returns.push(AbiParam::new(types::I64));
                let sig_ref = b.func.import_signature(sig);
                let mut indirect_args: Vec<ir::Value> = Vec::with_capacity(arg_vals.len() + 2);
                for (i, _v) in arg_vals.iter().enumerate() {
                    let binding = *var_env
                        .get(&args[i].0)
                        .expect("unbound tailcallclosure arg");
                    push_binding_as_abi_args(
                        &mut indirect_args,
                        b,
                        jmod,
                        runtime,
                        cache,
                        binding,
                        ArgRepr::ValueRef,
                    );
                }
                indirect_args.push(cl_val);
                indirect_args.push(my_cont);
                let _ = host_ctx;
                if is_native {
                    b.ins()
                        .return_call_indirect(sig_ref, body_fp, &indirect_args);
                } else {
                    let call_inst = b.ins().call_indirect(sig_ref, body_fp, &indirect_args);
                    let result = b.inst_results(call_inst)[0];
                    b.ins().return_(&[result]);
                }
            }
        }
        Term::Receive {
            continuation,
            ident: _,
        } => {
            // fz-cps.1.2 Receive cutover per docs/cps-in-clif.md §4.
            // Build the cont closure, with outer_cont as env field 0,
            // hand it to fz_receive_park which parks an accept-any
            // matcher record and returns YIELD sentinel.
            let cont_sid = resolve_cont_sid(blk, continuation);
            let cap_bindings: Vec<ClosureCapture> = continuation
                .captured
                .iter()
                .map(|cv| closure_capture_for_var(var_env, b, jmod, runtime, cv.0, cache))
                .collect();
            let cont_fid = *fn_ids.get(&cont_sid).expect("cont fn_id missing");
            let cl_ptr = build_cont_closure(
                jmod,
                b,
                runtime,
                return_reprs,
                is_cont_fn,
                cont_param,
                frame_ptr,
                cont_sid,
                cont_fid,
                &cap_bindings,
                &[],
            );

            // fz_receive_park(cl_ptr) — stash + yield.
            let park_fref = jmod.declare_func_in_func(runtime.receive_park_id, b.func);
            let park_inst = b.ins().call(park_fref, &[cl_ptr]);
            let yield_sentinel = b.inst_results(park_inst)[0];
            if is_native {
                // Native body returns i64 (canonical); the yield
                // sentinel propagates back to the scheduler.
                b.ins().return_(&[yield_sentinel]);
            } else {
                // Uniform body returns next_frame ptr (here, YIELD
                // sentinel — trampoline parks the task).
                b.ins().return_(&[yield_sentinel]);
            }
        }
        // fz-70q.3 — selective-receive park-site CLIF.
        //
        // Layout, mirroring fz_runtime::park::ParkRecord:
        //   - matcher fn addr (declared/emitted by the pre-pass in
        //     compile_with_backend).
        //   - pinned[]: one-word value entries, one per `^name`
        //     referenced across all clauses, in source order.
        //   - clause_bodies[]: i64 array of cont-closure refs,
        //     one per source clause; each closure carries the clause-body
        //     fn entry, while captures are populated through closure
        //     accessors in source order (build_cont_closure handles all
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
        // After laying these out the arm calls fz_receive_park_matched
        // and returns the YIELD sentinel so the trampoline parks.
        Term::ReceiveMatched {
            clauses,
            after,
            pinned,
            captures,
            matcher: _,
            ident: _,
        } => {
            use cranelift_codegen::ir::{StackSlotData, StackSlotKind};

            let matcher_fid = *env
                .matcher_fn_ids
                .get(&(caller_fn_id.0, blk.id.0))
                .expect("matcher fn pre-declared by compile_with_backend pre-pass");
            let matcher_addr = fn_addr(jmod, matcher_fid, b);

            // Pinned snapshot: alloca [AnyValueRef; n_pinned], take base addr.
            let n_pinned = pinned.len();
            let pinned_ptr = if n_pinned == 0 {
                b.ins().iconst(types::I64, 0)
            } else {
                let slot = b.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    (n_pinned * SLOT_BYTES as usize) as u32,
                    3,
                ));
                for (i, (_name, v)) in pinned.iter().enumerate() {
                    let value_ref = tagged_get(var_env, b, jmod, runtime, v.0, cache);
                    b.ins()
                        .stack_store(value_ref, slot, (i * SLOT_BYTES as usize) as i32);
                }
                b.ins().stack_addr(types::I64, slot, 0)
            };

            // Captures snapshot, shared across every clause body /
            // guard / after closure. `Term::ReceiveMatched::captures`
            // is already deduplicated by ir_lower; the cont fns'
            // capture-param slots line up with this order.
            let cap_bindings: Vec<ClosureCapture> = captures
                .iter()
                .map(|cv| closure_capture_for_var(var_env, b, jmod, runtime, cv.0, cache))
                .collect();

            // bound_arity: max bound-var count across clauses (matcher
            // ABI sizes the out buffer to this).
            let bound_arity = clauses
                .iter()
                .map(|c| c.bound_names.len())
                .max()
                .unwrap_or(0);

            // clause_bodies[]: build one cont-closure per clause body
            // and stack-store its ptr.
            let n_clauses = clauses.len();
            assert!(
                n_clauses > 0,
                "ReceiveMatched with zero clauses should not reach codegen"
            );
            let bodies_slot = b.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                (n_clauses * SLOT_BYTES as usize) as u32,
                3,
            ));
            let needs_bound_counts = clauses.iter().any(|c| c.bound_names.len() != bound_arity);
            let bound_counts_slot = needs_bound_counts.then(|| {
                b.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    (n_clauses * SLOT_BYTES as usize) as u32,
                    3,
                ))
            });
            let any = t.any();
            let resolve_body_sid = |body: crate::fz_ir::FnId, _bound_arity: usize| -> u32 {
                let body_fn = env.module.fn_by_id(body);
                let np = body_fn.block(body_fn.entry).params.len();
                let key = crate::fz_ir::receive_outcome_spec_key(&any, np);
                let key = crate::ir_typer::fn_types::SpecKey::value(
                    body,
                    crate::types::key_slots_from_tys(key),
                );
                env.spec_registry
                    .resolve_spec_key(t, &key)
                    .unwrap_or_else(|| {
                        panic!(
                            "matcher body fn_id {} key {:?} has no spec; \
                             typer emit at Term::ReceiveMatched may be missing",
                            body.0, key
                        )
                    })
                    .0
            };
            for (i, c) in clauses.iter().enumerate() {
                let cont_sid = resolve_body_sid(c.body, c.bound_names.len());
                let cont_fid = *fn_ids
                    .get(&cont_sid)
                    .expect("clause body sid has no FuncId");
                let cl_ptr = build_cont_closure(
                    jmod,
                    b,
                    runtime,
                    return_reprs,
                    is_cont_fn,
                    cont_param,
                    frame_ptr,
                    cont_sid,
                    cont_fid,
                    &cap_bindings,
                    &[],
                );
                b.ins().stack_store(cl_ptr, bodies_slot, (i * 8) as i32);
                if let Some(slot) = bound_counts_slot {
                    let bound_count_v = b.ins().iconst(types::I64, c.bound_names.len() as i64);
                    b.ins().stack_store(bound_count_v, slot, (i * 8) as i32);
                }
            }
            let bodies_ptr = b.ins().stack_addr(types::I64, bodies_slot, 0);
            let bound_counts_ptr = if let Some(slot) = bound_counts_slot {
                b.ins().stack_addr(types::I64, slot, 0)
            } else {
                b.ins().iconst(types::I64, 0)
            };

            // After: build the after closure if present and unbox the
            // timeout from its tagged Int. `-1` sentinel when no after.
            let (after_deadline_v, after_cont_v) = match after {
                Some(a) => {
                    let cont_sid = resolve_body_sid(a.body, 0);
                    let cont_fid = *fn_ids.get(&cont_sid).expect("after body sid has no FuncId");
                    let cl_ptr = build_cont_closure(
                        jmod,
                        b,
                        runtime,
                        return_reprs,
                        is_cont_fn,
                        cont_param,
                        frame_ptr,
                        cont_sid,
                        cont_fid,
                        &cap_bindings,
                        &[],
                    );
                    let unboxed = as_raw_i64(var_env, b, jmod, runtime, a.timeout.0);
                    (unboxed, cl_ptr)
                }
                None => {
                    let neg1 = b.ins().iconst(types::I64, -1);
                    let nullp = b.ins().iconst(types::I64, 0);
                    (neg1, nullp)
                }
            };

            let n_pinned_v = b.ins().iconst(types::I64, n_pinned as i64);
            let n_clauses_v = b.ins().iconst(types::I64, n_clauses as i64);
            let bound_arity_v = b.ins().iconst(types::I32, bound_arity as i64);

            let park_fref = jmod.declare_func_in_func(runtime.receive_park_matched_id, b.func);
            let park_inst = b.ins().call(
                park_fref,
                &[
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
            let yield_sentinel = b.inst_results(park_inst)[0];
            // Both native and uniform bodies return the YIELD
            // sentinel so the trampoline parks (same as Term::Receive).
            b.ins().return_(&[yield_sentinel]);
        }
    }
    Ok(())
}

fn list_tail_destination_arg(b: &mut FunctionBuilder<'_>, cache: &mut CodegenCache) -> ir::Value {
    cache
        .list_tail_param
        .unwrap_or_else(|| emit_empty_list_value_ref_word(b, cache))
}

fn cont_extra_ref_captures(
    b: &mut FunctionBuilder<'_>,
    cache: &mut CodegenCache,
    cont_key: &crate::ir_typer::fn_types::SpecKey,
) -> Vec<ir::Value> {
    if DemandAbi::new(cont_key).carries_list_tail_capture() {
        vec![list_tail_destination_arg(b, cache)]
    } else {
        Vec::new()
    }
}

fn list_tail_cont_captures(
    continuation: &crate::fz_ir::Cont,
) -> Option<(crate::fz_ir::Var, crate::fz_ir::Var)> {
    let mut captures = continuation.captured.iter().copied();
    let pivot = captures.next()?;
    let tail = captures.next()?;
    Some((pivot, tail))
}

fn emit_list_tail_return_value<
    M: cranelift_module::Module,
    T: crate::types::Types<Ty = crate::types::Ty>,
>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    cache: &mut CodegenCache,
    block_env: Option<&HashMap<crate::fz_ir::Var, crate::types::Ty>>,
    elems: &[crate::fz_ir::Var],
) -> ir::Value {
    let mut acc = ListTailBits::ValueRef(list_tail_destination_arg(b, cache));
    for elem in elems.iter().rev() {
        let cons = emit_list_cons_bif(
            b,
            jmod,
            env.runtime,
            var_env,
            *elem,
            expected_runtime_value_kind(t, env.fn_types, block_env, *elem),
            acc,
            cache,
        );
        acc = ListTailBits::NonEmptyValueRef(cons);
    }
    match acc {
        ListTailBits::ValueRef(bits) | ListTailBits::NonEmptyValueRef(bits) => bits,
        ListTailBits::Empty => emit_empty_list_value_ref_word(b, cache),
    }
}
