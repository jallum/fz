use std::collections::HashMap;

use super::*;
use crate::fz_ir::{FnId, Module, Stmt, Term, Var};
use crate::types::Types;
use fz_runtime::any_value::AnyValueRef;
use fz_runtime::any_value::{AnyValue as RuntimeAnyValue, ValueKind};

/// fz-yxs/fz-2v3 — try matching the message against each clause's
/// pattern + guard in order; first match wins. Returns the matched
/// clause index plus the bindings list (in source order, aligned with
/// `MatchedClause::bound_names`) on success.
///
/// Receive probes execute the cached AST-free Matcher lowered at the
/// receive site; misses return None without compiling or walking AST.
pub(super) fn try_match_clauses<T: Types<Ty = crate::types::Ty>>(
    runtime: &mut IrInterpRuntime,
    _t: &mut T,
    module: &Module,
    tel: &dyn crate::telemetry::Telemetry,
    clauses: &[MatchedClause],
    matcher: &crate::matcher::Matcher,
    msg: AnyValue,
    pinned: &HashMap<String, AnyValue>,
    _captures: &[AnyValue],
) -> Result<Option<(usize, Vec<AnyValue>)>, String> {
    let matched = execute_matcher(runtime, module, matcher, msg, pinned);
    let Some((body_id, binds)) = matched else {
        tel.execute(
            &["fz", "interp", "receive", "probe_miss"],
            &crate::measurements! {
                clause_count: clauses.len() as u64
            },
            &crate::telemetry::Metadata::new(),
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
        &crate::measurements! {
            clause_idx: i as u64,
            bound_count: bound_vals.len() as u64,
            clause_count: clauses.len() as u64
        },
        &crate::telemetry::Metadata::new(),
    );
    debug_assert!(
        c.guard.is_none(),
        "receive guards execute inside the cached Matcher"
    );
    Ok(Some((i, bound_vals)))
}

/// Run an fz fn. Tail calls reuse this stack frame (O(1) Rust stack).
/// Returns Done(val) on Halt/Return or Blocked(fn_id, cap_vals) when a
/// Term::Receive fires on an empty mailbox.
pub(super) fn run_fn<T: Types<Ty = crate::types::Ty>>(
    runtime: &mut IrInterpRuntime,
    t: &mut T,
    module: &Module,
    tel: &dyn crate::telemetry::Telemetry,
    mut fn_id: FnId,
    mut args: Vec<AnyValue>,
) -> Result<InterpStep, String> {
    'tail: loop {
        let fn_ir = module.fn_by_id(fn_id);
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
            for Stmt::Let(v, prim) in &blk.stmts {
                let val = eval_prim(runtime, t, module, tel, prim, &env)?;
                env.insert(*v, val);
            }
            match &blk.terminator {
                Term::Goto(b, gargs) => {
                    let vals: Vec<AnyValue> = gargs
                        .iter()
                        .map(|v| env_get(&env, *v))
                        .collect::<Result<_, _>>()?;
                    let next = fn_ir.block(*b);
                    for (p, val) in next.params.iter().zip(vals) {
                        env.insert(*p, val);
                    }
                    cur = *b;
                }
                Term::If {
                    cond,
                    then_b,
                    else_b,
                    ..
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
                    match run_fn(runtime, t, module, tel, *callee, arg_vals)? {
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
                    }
                }
                Term::ExportCall { .. } | Term::ExportTailCall { .. } => {
                    return Err("exported module calls require CodeServer lowering".to_string());
                }
                Term::TailCall {
                    ident: _,
                    callee,
                    args: call_args,
                    is_back_edge,
                } => {
                    let mut arg_vals = collect(&env, call_args)?;
                    // fz-02r.6 — interpreter back-edge cooperative GC.
                    // The interpreter runs synchronously, so a pressured
                    // back-edge forwards its live RuntimeAnyValue args in place
                    // instead of yielding a scheduler continuation closure.
                    if *is_back_edge {
                        if fz_runtime::yield_flag::load() != 0 {
                            let p = fz_runtime::process::current_process();
                            let mut root_slots: Vec<RuntimeAnyValue> = arg_vals
                                .iter()
                                .map(|v| v.value())
                                .collect::<Result<_, _>>()?;
                            p.heap.gc_any_value_roots_with_process_roots(
                                &mut root_slots,
                                &mut p.mailbox,
                            );
                            arg_vals = root_slots.into_iter().map(interp_value_from_slot).collect();
                            p.quiet_quanta = 0;
                            fz_runtime::yield_flag::clear();
                        } else {
                            let p = fz_runtime::process::current_process();
                            p.quiet_quanta = p.quiet_quanta.saturating_add(1);
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
                    match run_fn(runtime, t, module, tel, lam_fn, clos_args)? {
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
                Term::Receive {
                    continuation,
                    ident: _,
                } => {
                    let cap_vals = collect(&env, &continuation.captured)?;
                    match fz_runtime::process::current_process().mailbox.pop_front() {
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
                    let mailbox_len = fz_runtime::process::current_process().mailbox.len();
                    let mut hit: Option<(usize, usize, Vec<AnyValue>)> = None;
                    for mb_idx in 0..mailbox_len {
                        let msg = {
                            let p = fz_runtime::process::current_process();
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
                        fz_runtime::process::current_process()
                            .mailbox
                            .remove(mb_idx);
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
    env.get(&v)
        .copied()
        .ok_or_else(|| format!("unbound Var({})", v.0))
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
/// Pre-conditions: `CURRENT_PROCESS` is set to the heap owning the
/// queue. Closures in the queue point into that heap.
pub(super) fn drain_pending_dtors_interp<T: Types<Ty = crate::types::Ty>>(
    runtime: &mut IrInterpRuntime,
    t: &mut T,
    module: &Module,
    tel: &dyn crate::telemetry::Telemetry,
) -> Result<(), String> {
    loop {
        let entry = {
            let p = fz_runtime::process::current_process();
            p.heap.pending_dtors.pop_front()
        };
        let Some((closure_bits, payload_ref)) = entry else {
            break;
        };
        let closure_ref = AnyValueRef::from_raw_word(closure_bits).map_err(|err| {
            format!("fz-4mk drain: invalid dtor closure ref {closure_bits:#x}: {err:?}")
        })?;
        let closure = RuntimeAnyValue::heap_ptr(
            closure_ref
                .closure_addr()
                .map_err(|err| format!("fz-4mk drain: dtor ref is not a closure: {err:?}"))?,
            ValueKind::CLOSURE,
        );
        let (fn_id, captured) = match unpack_closure(closure) {
            Ok(x) => x,
            Err(e) => {
                tel.event(
                    &["fz", "runtime", "bad_dtor_closure"],
                    crate::metadata! { error: e },
                );
                continue;
            }
        };
        let mut args = captured;
        args.push(interp_value_from_ref_word(
            payload_ref,
            "fz-4mk drain payload",
        )?);
        match run_fn(runtime, t, module, tel, fn_id, args)? {
            InterpStep::Done(_) => {}
            InterpStep::Blocked(_, _, _) | InterpStep::BlockedMatched(_, _) => {
                return Err("fz-4mk drain: dtor blocked on receive (unsupported in v1)".into());
            }
        }
    }
    Ok(())
}
