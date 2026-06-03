use std::collections::HashMap;

use super::*;
use crate::exec::matcher::Matcher;
use crate::fz_ir::{FnId, Module, Stmt, Term, Var};
use crate::ir_extern_marshal::resolve_fn_types;
use crate::ir_planner::ModulePlan;
use crate::ir_planner::type_fn::type_fn;
use crate::measurements;
use crate::metadata;
use crate::telemetry::{Metadata, Telemetry};
use crate::types::{ClosureTypes, RenderTypes, Ty, Types};
use fz_runtime::any_value::AnyValueRef;
use fz_runtime::any_value::{AnyValue as RuntimeAnyValue, ValueKind};
use fz_runtime::process::YIELD_REASON_REDUCTIONS;

/// fz-yxs/fz-2v3 — try matching the message against each clause's
/// pattern + guard in order; first match wins. Returns the matched
/// clause index plus the bindings list (in source order, aligned with
/// `MatchedClause::bound_names`) on success.
///
/// Receive probes execute the cached AST-free Matcher lowered at the
/// receive site; misses return None without compiling or walking AST.
pub(super) fn try_match_clauses<T: Types<Ty = Ty>>(
    runtime: &mut IrInterpRuntime,
    _t: &mut T,
    module: &Module,
    tel: &dyn Telemetry,
    clauses: &[MatchedClause],
    matcher: &Matcher,
    msg: AnyValue,
    pinned: &HashMap<String, AnyValue>,
    _captures: &[AnyValue],
) -> Result<Option<(usize, Vec<AnyValue>)>, String> {
    let matched = execute_matcher(runtime, module, matcher, msg, pinned);
    let Some((body_id, binds)) = matched else {
        tel.execute(
            &["fz", "interp", "receive", "probe_miss"],
            &measurements! {
                clause_count: clauses.len() as u64
            },
            &Metadata::new(),
        );
        return Ok(None);
    };
    let i = body_id as usize;
    let c = &clauses[i];
    // Align with declared bound_names order. The matrix's bindings list
    // is keyed by source name and reflects pattern-walk order; the
    // explicit reorder protects against any future drift.
    let mut bound_vals: Vec<AnyValue> = Vec::with_capacity(c.bound_names.len());
    for name in &c.bound_names {
        let Some((_, v)) = binds.iter().rev().find(|(n, _)| n == name) else {
            return Err(format!(
                "try_match_clauses: bound name `{}` missing from pattern walk",
                name
            ));
        };
        bound_vals.push(*v);
    }
    tel.execute(
        &["fz", "interp", "receive", "probe_hit"],
        &measurements! {
            clause_idx: i as u64,
            bound_count: bound_vals.len() as u64,
            clause_count: clauses.len() as u64
        },
        &Metadata::new(),
    );
    debug_assert!(c.guard.is_none(), "receive guards execute inside the cached Matcher");
    Ok(Some((i, bound_vals)))
}

/// Run an fz fn. Tail calls reuse this stack frame (O(1) Rust stack).
/// Returns Done(val) on Halt/Return or Blocked(fn_id, cap_vals) when a
/// Term::Receive fires on an empty mailbox.
pub(super) fn run_fn_typed<T: Types<Ty = Ty> + ClosureTypes + RenderTypes>(
    runtime: &mut IrInterpRuntime,
    t: &mut T,
    module: &Module,
    tel: &dyn Telemetry,
    module_types: &ModulePlan,
    mut fn_id: FnId,
    mut args: Vec<AnyValue>,
) -> Result<InterpStep, String> {
    'tail: loop {
        let fn_ir = module.fn_by_id(fn_id);
        let mut fallback_fn_types;
        let fn_types = if let Some(fn_types) = module_types.any_spec_for(fn_id) {
            fn_types
        } else {
            fallback_fn_types = type_fn(t, fn_ir, module, None);
            let diagnostics = resolve_fn_types(t, module, fn_id, &mut fallback_fn_types);
            if let Some(diagnostic) = diagnostics.into_iter().next() {
                return Err(diagnostic.message);
            }
            &fallback_fn_types
        };
        let mut env: HashMap<Var, AnyValue> = HashMap::new();
        let entry = fn_ir.block(fn_ir.entry);
        if entry.params.len() != args.len() {
            return Err(format!(
                "fn {} expected {} args, got {}",
                fn_ir.name,
                entry.params.len(),
                args.len()
            ));
        }
        for (p, v) in entry.params.iter().zip(args.iter()) {
            env.insert(*p, *v);
        }
        let mut cur = fn_ir.entry;
        loop {
            let blk = fn_ir.block(cur);
            for (stmt_idx, Stmt::Let(v, prim)) in blk.stmts.iter().enumerate() {
                let val = eval_prim(runtime, t, module, tel, fn_types, blk.id, stmt_idx, prim, &env)?;
                env.insert(*v, val);
            }
            match &blk.terminator {
                Term::Goto(b, gargs) => {
                    let vals: Vec<AnyValue> = gargs.iter().map(|v| env_get(&env, *v)).collect::<Result<_, _>>()?;
                    let next = fn_ir.block(*b);
                    for (p, val) in next.params.iter().zip(vals) {
                        env.insert(*p, val);
                    }
                    cur = *b;
                }
                Term::If {
                    cond, then_b, else_b, ..
                } => {
                    let cv = env_get(&env, *cond)?;
                    cur = if is_truthy(cv) { *then_b } else { *else_b };
                }
                Term::Call {
                    ident: _,
                    callee,
                    args: call_args,
                    continuation,
                } => {
                    let arg_vals = collect(&env, call_args)?;
                    let outer_cap_vals = collect(&env, &continuation.captured)?;
                    match run_fn_typed(runtime, t, module, tel, module_types, *callee, arg_vals)? {
                        InterpStep::Done(val) => {
                            let mut cont_args = vec![val];
                            cont_args.extend(outer_cap_vals);
                            fn_id = continuation.fn_id;
                            args = cont_args;
                            continue 'tail;
                        }
                        InterpStep::Blocked(rf, cv, mut inner_after) => {
                            // Append our continuation to the chain so the
                            // scheduler calls it after the blocked task resumes.
                            inner_after.push((continuation.fn_id, outer_cap_vals));
                            return Ok(InterpStep::Blocked(rf, cv, inner_after));
                        }
                        InterpStep::BlockedMatched(park, mut inner_after) => {
                            inner_after.push((continuation.fn_id, outer_cap_vals));
                            return Ok(InterpStep::BlockedMatched(park, inner_after));
                        }
                        InterpStep::Yielded {
                            resume_fn,
                            resume_args,
                            mut after,
                            remaining_reductions,
                            reason,
                        } => {
                            after.push((continuation.fn_id, outer_cap_vals));
                            return Ok(InterpStep::Yielded {
                                resume_fn,
                                resume_args,
                                after,
                                remaining_reductions,
                                reason,
                            });
                        }
                    }
                }
                Term::TailCall {
                    ident: _,
                    callee,
                    args: call_args,
                    is_back_edge,
                } => {
                    let arg_vals = collect(&env, call_args)?;
                    // fz-02r.6 — interpreter back-edge cooperative GC.
                    // The interpreter runs synchronously, so a pressured
                    // back-edge forwards its live RuntimeAnyValue args in place
                    // instead of yielding a scheduler continuation closure.
                    if *is_back_edge {
                        let (budget_exhausted, remaining_reductions) = {
                            let p = unsafe { &mut *runtime.cur_proc() };
                            p.reductions_remaining -= 1;
                            (p.reductions_remaining <= 0, p.reductions_remaining)
                        };
                        // Allocation pressure zeroes the budget on the Process
                        // (`expire_current_budget`), so a pressured loop trips
                        // `budget_exhausted` here too; its ALLOCATION_PRESSURE
                        // bit already stands on `yield_reasons` and is folded in
                        // by the scheduler-boundary `finish_yield_report`.
                        if budget_exhausted {
                            return Ok(InterpStep::Yielded {
                                resume_fn: *callee,
                                resume_args: arg_vals,
                                after: vec![],
                                remaining_reductions,
                                reason: YIELD_REASON_REDUCTIONS,
                            });
                        }
                    }
                    fn_id = *callee;
                    args = arg_vals;
                    continue 'tail;
                }
                Term::CallClosure {
                    ident: _,
                    closure,
                    args: call_args,
                    continuation,
                } => {
                    let cl = env_get(&env, *closure)?;
                    let (lam_fn, mut clos_args) = unpack_closure(cl.value()?)?;
                    clos_args.extend(collect(&env, call_args)?);
                    let outer_cap_vals = collect(&env, &continuation.captured)?;
                    match run_fn_typed(runtime, t, module, tel, module_types, lam_fn, clos_args)? {
                        InterpStep::Done(val) => {
                            let mut cont_args = vec![val];
                            cont_args.extend(outer_cap_vals);
                            fn_id = continuation.fn_id;
                            args = cont_args;
                            continue 'tail;
                        }
                        InterpStep::Blocked(rf, cv, mut inner_after) => {
                            inner_after.push((continuation.fn_id, outer_cap_vals));
                            return Ok(InterpStep::Blocked(rf, cv, inner_after));
                        }
                        InterpStep::BlockedMatched(park, mut inner_after) => {
                            inner_after.push((continuation.fn_id, outer_cap_vals));
                            return Ok(InterpStep::BlockedMatched(park, inner_after));
                        }
                        InterpStep::Yielded {
                            resume_fn,
                            resume_args,
                            mut after,
                            remaining_reductions,
                            reason,
                        } => {
                            after.push((continuation.fn_id, outer_cap_vals));
                            return Ok(InterpStep::Yielded {
                                resume_fn,
                                resume_args,
                                after,
                                remaining_reductions,
                                reason,
                            });
                        }
                    }
                }
                Term::TailCallClosure {
                    ident: _,
                    closure,
                    args: call_args,
                } => {
                    let cl = env_get(&env, *closure)?;
                    let (lam_fn, mut clos_args) = unpack_closure(cl.value()?)?;
                    clos_args.extend(collect(&env, call_args)?);
                    fn_id = lam_fn;
                    args = clos_args;
                    continue 'tail;
                }
                Term::Return(v) => return Ok(InterpStep::Done(env_get(&env, *v)?)),
                Term::Halt(v) => return Ok(InterpStep::Done(env_get(&env, *v)?)),
                Term::Receive { continuation, ident: _ } => {
                    let cap_vals = collect(&env, &continuation.captured)?;
                    match unsafe { &mut *runtime.cur_proc() }.mailbox.pop_front() {
                        Some(msg) => {
                            let msg = AnyValue::from_any_value_ref(msg)?;
                            let mut cont_args = vec![msg];
                            cont_args.extend(cap_vals);
                            fn_id = continuation.fn_id;
                            args = cont_args;
                            continue 'tail;
                        }
                        None => {
                            return Ok(InterpStep::Blocked(continuation.fn_id, cap_vals, vec![]));
                        }
                    }
                }
                // fz-yxs/fz-2v3 — selective receive. Walk the mailbox
                // head-to-tail trying each clause in order; first match
                // wins. On miss, return BlockedMatched so the scheduler
                // can stash a park record for `interp_send`'s sender-side
                // probe to consult on the next arrival.
                Term::ReceiveMatched {
                    clauses,
                    matcher,
                    after,
                    pinned,
                    captures,
                    ..
                } => {
                    let pinned_map: HashMap<String, AnyValue> = pinned
                        .iter()
                        .map(|(name, var)| env_get(&env, *var).map(|v| (name.clone(), v)))
                        .collect::<Result<_, _>>()?;
                    let capture_vals: Vec<AnyValue> = collect(&env, captures)?;

                    let matched_clauses: Vec<MatchedClause> = clauses
                        .iter()
                        .map(|c| MatchedClause {
                            bound_names: c.bound_names.clone(),
                            guard: c.guard,
                            body: c.body,
                        })
                        .collect();

                    // Initial mailbox scan.
                    let mailbox_len = unsafe { &mut *runtime.cur_proc() }.mailbox.len();
                    let mut hit: Option<(usize, usize, Vec<AnyValue>)> = None;
                    for mb_idx in 0..mailbox_len {
                        let msg = {
                            let p = unsafe { &mut *runtime.cur_proc() };
                            AnyValue::from_any_value_ref(p.mailbox[mb_idx])?
                        };
                        if let Some((clause_idx, binds)) = try_match_clauses(
                            runtime,
                            t,
                            module,
                            tel,
                            &matched_clauses,
                            matcher,
                            msg,
                            &pinned_map,
                            &capture_vals,
                        )? {
                            hit = Some((mb_idx, clause_idx, binds));
                            break;
                        }
                    }

                    if let Some((mb_idx, clause_idx, bound_vals)) = hit {
                        unsafe { &mut *runtime.cur_proc() }.mailbox.remove(mb_idx);
                        let body = matched_clauses[clause_idx].body;
                        let mut new_args = bound_vals;
                        new_args.extend(capture_vals);
                        fn_id = body;
                        args = new_args;
                        continue 'tail;
                    }

                    // Miss — `after 0` (timeout literal 0) fires the after
                    // body inline; any other after value (including
                    // `:infinity`) parks without a timer since the interp
                    // has no wall clock.
                    if let Some(a) = after {
                        let timeout_val = env_get(&env, a.timeout)?;
                        if timeout_val.as_i64() == Some(0) {
                            fn_id = a.body;
                            args = capture_vals;
                            continue 'tail;
                        }
                    }

                    let park = ParkRecord {
                        clauses: matched_clauses,
                        matcher: matcher.clone(),
                        pinned: pinned_map,
                        captures: capture_vals,
                    };
                    return Ok(InterpStep::BlockedMatched(park, vec![]));
                }
            }
        }
    }
}

pub(super) fn collect(env: &HashMap<Var, AnyValue>, vars: &[Var]) -> Result<Vec<AnyValue>, String> {
    vars.iter().map(|v| env_get(env, *v)).collect()
}

pub(super) fn env_get(env: &HashMap<Var, AnyValue>, v: Var) -> Result<AnyValue, String> {
    env.get(&v).copied().ok_or_else(|| format!("unbound Var({})", v.0))
}

pub(super) fn is_truthy(v: AnyValue) -> bool {
    v.is_truthy()
}

/// fz-4mk — interpreter-leg drain of `Heap::pending_dtors`. Pops each
/// `(closure_bits, payload)` enqueued by `mso_sweep`/`mso_drop_all`,
/// unpacks the closure to its body FnId + captures, and runs the body
/// as a fully fz-side call via `run_fn`. The dtor's return value is
/// discarded. Errors from the dtor body propagate to the caller; the
/// run-loop logs and continues.
///
/// Pre-conditions: `runtime.cur_proc()` owns the heap holding the
/// queue. Closures in the queue point into that heap.
pub(super) fn drain_pending_dtors_interp<T: Types<Ty = Ty> + ClosureTypes + RenderTypes>(
    runtime: &mut IrInterpRuntime,
    t: &mut T,
    module: &Module,
    tel: &dyn Telemetry,
    module_types: &ModulePlan,
) -> Result<(), String> {
    loop {
        let entry = {
            let p = unsafe { &mut *runtime.cur_proc() };
            p.heap.pending_dtors.pop_front()
        };
        let Some((closure_bits, payload_ref)) = entry else {
            break;
        };
        let closure_ref = AnyValueRef::from_raw_word(closure_bits)
            .map_err(|err| format!("fz-4mk drain: invalid dtor closure ref {closure_bits:#x}: {err:?}"))?;
        let closure = RuntimeAnyValue::heap_ptr(
            closure_ref
                .closure_addr()
                .map_err(|err| format!("fz-4mk drain: dtor ref is not a closure: {err:?}"))?,
            ValueKind::CLOSURE,
        );
        let (fn_id, captured) = match unpack_closure(closure) {
            Ok(x) => x,
            Err(e) => {
                tel.event(&["fz", "runtime", "bad_dtor_closure"], metadata! { error: e });
                continue;
            }
        };
        let mut args = captured;
        args.push(interp_value_from_ref_word(payload_ref, "fz-4mk drain payload")?);
        match run_fn_typed(runtime, t, module, tel, module_types, fn_id, args)? {
            InterpStep::Done(_) => {}
            InterpStep::Yielded { .. } | InterpStep::Blocked(_, _, _) | InterpStep::BlockedMatched(_, _) => {
                return Err("fz-4mk drain: dtor blocked on receive (unsupported in v1)".into());
            }
        }
    }
    Ok(())
}
