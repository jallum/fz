use super::fn_types::{CapabilityPlan, SpecKey};
use crate::fz_ir::{FnId, Module, Prim, Stmt, Term, Var};
use std::collections::{BTreeSet, HashMap, HashSet};

/// Resolve a closure call's return type for this call site's argument types.
///
/// Translates value-demand `effective_returns` into the closure-target return
/// table expected by `Types::resolve_closure_return`, then delegates.
pub fn resolve_closure_return<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    closure_ty: &crate::types::Ty,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    arg_tys: &[crate::types::Ty],
) -> Option<T::Ty> {
    let translated: HashMap<
        (crate::types::ClosureTarget, Vec<crate::types::Ty>),
        crate::types::Ty,
    > = effective_returns
        .iter()
        .filter_map(|(key, ty)| {
            if !key.demand.is_value() || key.input.iter().any(Option::is_none) {
                return None;
            }
            Some((
                (
                    key.fn_id.into(),
                    crate::types::key_slots_observed(&key.input),
                ),
                ty.clone(),
            ))
        })
        .collect();
    t.resolve_closure_return(closure_ty, &translated, arg_tys)
}

/// Rewrite `Term::CallClosure(v, args, cont)` to `Term::Call(F, args, cont)`
/// (and `TailCallClosure` to `TailCall`) when every spec of the enclosing FnIr
/// that has an opinion on `v` agrees that `v` holds `F`. Disagreement leaves
/// the terminator untouched.
///
/// Module mutation only; callers re-run `plan_module` afterwards to
/// refresh `ModulePlan` against the rewritten IR.
pub fn rewrite_known_target_closures<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    _t: &mut T,
    module: &mut Module,
    types: &CapabilityPlan,
) {
    let mut unified: HashMap<FnId, HashMap<Var, Option<FnId>>> = HashMap::new();
    for (fn_id, caps) in &types.spec_capabilities {
        let entry = unified.entry(*fn_id).or_default();
        for (v, fnid) in caps
            .iter()
            .filter_map(|(v, cap)| cap.known_fn().map(|fnid| (*v, fnid)))
        {
            merge_known_fn(entry, v, fnid);
        }
    }
    for f in &mut module.fns {
        let Some(map) = unified.get(&f.id) else {
            continue;
        };
        for b in &mut f.blocks {
            let new_term = match &b.terminator {
                Term::CallClosure {
                    ident: _,
                    closure,
                    args,
                    continuation,
                } => {
                    if let Some(Some(target)) = map.get(closure).copied() {
                        Some(Term::Call {
                            ident: crate::fz_ir::CallsiteIdent::from_source(
                                crate::diag::Span::DUMMY,
                            ),
                            callee: target,
                            args: args.clone(),
                            continuation: continuation.clone(),
                        })
                    } else {
                        None
                    }
                }
                Term::TailCallClosure {
                    closure,
                    args,
                    ident: _,
                } => {
                    if let Some(Some(target)) = map.get(closure).copied() {
                        Some(Term::TailCall {
                            ident: crate::fz_ir::CallsiteIdent::from_source(
                                crate::diag::Span::DUMMY,
                            ),
                            callee: target,
                            args: args.clone(),
                            is_back_edge: false,
                        })
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if let Some(nt) = new_term {
                b.terminator = nt;
            }
        }
    }
    eliminate_constant_closure_values(module, &unified);
}

fn merge_known_fn(entry: &mut HashMap<Var, Option<FnId>>, var: Var, fnid: FnId) {
    match entry.get(&var).copied() {
        None => {
            entry.insert(var, Some(fnid));
        }
        Some(Some(prev)) if prev == fnid => {}
        Some(_) => {
            entry.insert(var, None);
        }
    }
}

/// Erase a module-constant, zero-capture closure that survives only as a
/// threaded value.
///
/// After `rewrite_known_target_closures` devirtualizes `CallClosure(v, …)` to
/// `Call(F, …)`, the closure value `v` is no longer *called* anywhere — but the
/// callable capability facts show it is still *passed*: threaded as a parameter
/// through a recursive component and captured into continuations (e.g.
/// `Enum.sort`'s comparator riding `merge`'s frame). A callable left in a
/// frame trips the lazy-continuation gate (`caller_has_callable_state`), forcing
/// every continuation onto the heap. The value is dead weight: a zero-capture
/// constant closure is just a function pointer, and the direct `Call(F, …)`
/// does not need it.
///
/// This removes that dead value entirely — its entry-parameter slot in every
/// fn that threads it, the matching argument at every call site, its
/// continuation captures, and the originating `MakeClosure` — so `F` stops
/// being a closure-target. The existing inliner then splices `F`, and the
/// untouched lazy-continuation gate sees a closure-free frame. No new pass, no
/// gate change: the devirtualization pass simply finishes its own job.
///
/// `unified[F][v] == Some(Some(fid))` is the typer's interprocedural proof that
/// `v` holds the constant closure `fid` under *every* value-spec of `F` — it is
/// the tainted-slot set, already computed. Elimination is correct by
/// construction: a candidate is taken only when every occurrence of the value
/// is a pure pass-through (entry param, zero-capture `MakeClosure` source, call
/// argument, or continuation capture). Any other use — inspected by a prim,
/// returned, threaded through a `Goto` block parameter, or reaching an
/// un-devirtualized `CallClosure` — bails the whole candidate, leaving the IR
/// untouched. Captures with state are excluded up front (only all-zero-capture
/// targets qualify), so no captured value is ever silently dropped.
fn eliminate_constant_closure_values(
    module: &mut Module,
    unified: &HashMap<FnId, HashMap<Var, Option<FnId>>>,
) {
    // A lambda is a candidate only if *every* MakeClosure that targets it is
    // zero-capture (a bare function pointer). A captured-state site for the
    // same lambda would lose state if we deleted it, so one such site
    // disqualifies the lambda entirely.
    let mut all_zero_capture: HashMap<FnId, bool> = HashMap::new();
    for f in &module.fns {
        for b in &f.blocks {
            for Stmt::Let(_, prim) in &b.stmts {
                if let Prim::MakeClosure(_, fid, caps) = prim {
                    let entry = all_zero_capture.entry(*fid).or_insert(true);
                    *entry &= caps.is_empty();
                }
            }
        }
    }
    let candidates: Vec<FnId> = unified
        .values()
        .flat_map(|m| m.values())
        .filter_map(|target| *target)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter(|fid| all_zero_capture.get(fid).copied().unwrap_or(false))
        .collect();

    // Continuation entry params are laid out `[return value(s)…, captures…]`, so
    // capture index `i` lands at param `offset + i` where `offset` is computed
    // from the *original* arity. Snapshot it before any mutation.
    let orig_param_count: HashMap<FnId, usize> = module
        .fns
        .iter()
        .map(|f| (f.id, f.block(f.entry).params.len()))
        .collect();

    // Removals accumulated across all validated candidates, keyed by original
    // positions so every list filters consistently in one final apply.
    let mut remove_param_pos: HashMap<FnId, BTreeSet<usize>> = HashMap::new();
    let mut remove_makeclosure: HashSet<(FnId, Var)> = HashSet::new();

    'candidate: for fid in candidates {
        let tainted = |fn_id: FnId, v: Var| -> bool {
            unified.get(&fn_id).and_then(|m| m.get(&v)).copied() == Some(Some(fid))
        };

        // Tainted entry-parameter positions per fn: the slots this candidate
        // would vacate. Drives the call-site/capture consistency checks below.
        let mut tainted_params: HashMap<FnId, BTreeSet<usize>> = HashMap::new();
        for f in &module.fns {
            for (pos, p) in f.block(f.entry).params.iter().enumerate() {
                if tainted(f.id, *p) {
                    tainted_params.entry(f.id).or_default().insert(pos);
                }
            }
        }
        let param_tainted = |fn_id: FnId, pos: usize| -> bool {
            tainted_params.get(&fn_id).is_some_and(|s| s.contains(&pos))
        };

        let mut cand_makeclosure: HashSet<(FnId, Var)> = HashSet::new();

        for f in &module.fns {
            for b in &f.blocks {
                for Stmt::Let(out, prim) in &b.stmts {
                    if let Prim::MakeClosure(_, g, caps) = prim
                        && *g == fid
                        && caps.is_empty()
                        && tainted(f.id, *out)
                    {
                        cand_makeclosure.insert((f.id, *out));
                        continue;
                    }
                    // The value flowing into any other prim, or a tainted var
                    // bound by a non-source prim, means the closure is observed
                    // as data — not a pure pass-through. Bail.
                    let mut observed = tainted(f.id, *out);
                    crate::fz_ir::visit_prim_vars(prim, |v| observed |= tainted(f.id, v));
                    if observed {
                        continue 'candidate;
                    }
                }

                match &b.terminator {
                    Term::Goto(_, args) => {
                        if args.iter().any(|v| tainted(f.id, *v)) {
                            continue 'candidate;
                        }
                    }
                    Term::If { cond, .. } => {
                        if tainted(f.id, *cond) {
                            continue 'candidate;
                        }
                    }
                    Term::Return(v) | Term::Halt(v) => {
                        if tainted(f.id, *v) {
                            continue 'candidate;
                        }
                    }
                    Term::Call {
                        callee,
                        args,
                        continuation,
                        ..
                    } => {
                        for (pos, a) in args.iter().enumerate() {
                            if tainted(f.id, *a) && !param_tainted(*callee, pos) {
                                continue 'candidate;
                            }
                        }
                        if !cont_captures_consistent(
                            continuation,
                            f.id,
                            &orig_param_count,
                            &tainted,
                            &param_tainted,
                        ) {
                            continue 'candidate;
                        }
                    }
                    Term::TailCall { callee, args, .. } => {
                        for (pos, a) in args.iter().enumerate() {
                            if tainted(f.id, *a) && !param_tainted(*callee, pos) {
                                continue 'candidate;
                            }
                        }
                    }
                    Term::CallClosure {
                        closure,
                        args,
                        continuation,
                        ..
                    } => {
                        if tainted(f.id, *closure)
                            || args.iter().any(|v| tainted(f.id, *v))
                            || continuation.captured.iter().any(|v| tainted(f.id, *v))
                        {
                            continue 'candidate;
                        }
                    }
                    Term::TailCallClosure { closure, args, .. } => {
                        if tainted(f.id, *closure) || args.iter().any(|v| tainted(f.id, *v)) {
                            continue 'candidate;
                        }
                    }
                    Term::Receive { continuation, .. } => {
                        if continuation.captured.iter().any(|v| tainted(f.id, *v)) {
                            continue 'candidate;
                        }
                    }
                    Term::ReceiveMatched {
                        pinned, captures, ..
                    } => {
                        if pinned.iter().any(|(_, v)| tainted(f.id, *v))
                            || captures.iter().any(|v| tainted(f.id, *v))
                        {
                            continue 'candidate;
                        }
                    }
                }
            }
        }

        // Clean: commit this candidate's removals.
        for (fn_id, positions) in tainted_params {
            remove_param_pos.entry(fn_id).or_default().extend(positions);
        }
        remove_makeclosure.extend(cand_makeclosure);
    }

    if remove_param_pos.is_empty() && remove_makeclosure.is_empty() {
        return;
    }

    // Apply, reading only the original-position maps. Pass 1: vacate entry
    // params (and their parallel side-tables) and delete the dead MakeClosures.
    for f in &mut module.fns {
        if let Some(positions) = remove_param_pos.get(&f.id) {
            let entry = f.entry;
            let removed_vars: Vec<Var> = f
                .block(entry)
                .params
                .iter()
                .enumerate()
                .filter_map(|(i, v)| positions.contains(&i).then_some(*v))
                .collect();
            if let Some(block) = f.blocks.iter_mut().find(|b| b.id == entry) {
                retain_by_position(&mut block.params, positions);
            }
            if !f.ignored_entry_params.is_empty() {
                retain_by_position(&mut f.ignored_entry_params, positions);
            }
            f.physical_entry_params
                .retain(|v| !removed_vars.contains(v));
        }
        for b in &mut f.blocks {
            b.stmts.retain(|Stmt::Let(out, prim)| {
                !(matches!(prim, Prim::MakeClosure(_, _, _))
                    && remove_makeclosure.contains(&(f.id, *out)))
            });
        }
    }

    // Pass 2: drop the matching argument at every call site and the matching
    // continuation captures.
    for f in &mut module.fns {
        for b in &mut f.blocks {
            match &mut b.terminator {
                Term::Call {
                    callee,
                    args,
                    continuation,
                    ..
                } => {
                    if let Some(positions) = remove_param_pos.get(callee) {
                        retain_by_position(args, positions);
                    }
                    drop_cont_captures(continuation, &remove_param_pos, &orig_param_count);
                }
                Term::TailCall { callee, args, .. } => {
                    if let Some(positions) = remove_param_pos.get(callee) {
                        retain_by_position(args, positions);
                    }
                }
                Term::CallClosure { continuation, .. } | Term::Receive { continuation, .. } => {
                    drop_cont_captures(continuation, &remove_param_pos, &orig_param_count);
                }
                _ => {}
            }
        }
    }
}

/// Validate that every tainted continuation capture lands on a param slot we
/// will vacate — so dropping the capture and the param stay in lockstep.
fn cont_captures_consistent(
    continuation: &crate::fz_ir::Cont,
    caller: FnId,
    orig_param_count: &HashMap<FnId, usize>,
    tainted: &impl Fn(FnId, Var) -> bool,
    param_tainted: &impl Fn(FnId, usize) -> bool,
) -> bool {
    let k = continuation.fn_id;
    let kcount = orig_param_count.get(&k).copied().unwrap_or(0);
    if continuation.captured.len() > kcount {
        return false;
    }
    let offset = kcount - continuation.captured.len();
    for (i, c) in continuation.captured.iter().enumerate() {
        if tainted(caller, *c) && !param_tainted(k, offset + i) {
            return false;
        }
    }
    true
}

/// Drop the continuation captures whose target param slot is being vacated.
fn drop_cont_captures(
    continuation: &mut crate::fz_ir::Cont,
    remove_param_pos: &HashMap<FnId, BTreeSet<usize>>,
    orig_param_count: &HashMap<FnId, usize>,
) {
    let Some(positions) = remove_param_pos.get(&continuation.fn_id) else {
        return;
    };
    let kcount = orig_param_count
        .get(&continuation.fn_id)
        .copied()
        .unwrap_or(0);
    let offset = kcount - continuation.captured.len();
    let mut i = 0;
    continuation.captured.retain(|_| {
        let keep = !positions.contains(&(offset + i));
        i += 1;
        keep
    });
}

/// Retain only the entries whose original index is not in `positions`.
fn retain_by_position<X>(items: &mut Vec<X>, positions: &BTreeSet<usize>) {
    let mut idx = 0;
    items.retain(|_| {
        let keep = !positions.contains(&idx);
        idx += 1;
        keep
    });
}
