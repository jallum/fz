use super::closures::resolve_closure_return;
use super::fn_types::{FnTypes, ModuleTypes, SpecKey};
use super::type_fn::type_stmts_into_env;
use crate::fz_ir::{Block, Cont, FnId, FnIr, Module, Prim, Stmt, Term, Var};
use std::collections::{HashMap, HashSet};

// ----------------------------------------------------------------------
// fz-ul4.29.12.1 — Cont input-type key helpers
// ----------------------------------------------------------------------

/// Reconstruct the per-Var env at the *terminator* of `block` under
/// `caller_ft`. Starts from `caller_ft.block_envs[block.id]` (which
/// already incorporates if-narrowing from predecessor blocks) and
/// folds in each Let by re-applying `type_prim`. This mirrors the
/// typer's own propagation pass at `type_module`'s `callsite_keys`
/// site (`ir_typer.rs:142-145`).
pub(crate) fn env_at_terminator<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    caller_ft: &FnTypes,
    block: &Block,
    module: &Module,
) -> HashMap<Var, crate::types::Ty> {
    let mut env: HashMap<Var, crate::types::Ty> = caller_ft
        .block_envs
        .get(&block.id)
        .cloned()
        .unwrap_or_default();
    type_stmts_into_env(t, &mut env, &block.stmts, module);
    env
}

/// fz-ul4.29.12.1 — slot-0 type for a Cont's input-type key at the
/// call-site whose terminator is `block.terminator`. Mirrors the
/// typer's logic at `ir_typer.rs:190-215`:
///
///   * `Term::Call`: callee's specialized return type under this
///     call-site's arg types (joined over the callee's `Return`
///     terminators using `module_types.specs[(callee, arg_tys)]`).
///   * `Term::CallClosure` / `Term::Receive`: callee/sender is
///     opaque, so slot 0 stays `any()`.
///   * Anything else: not a Cont-producing terminator, returns `any`.
pub fn cont_slot0_descr<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    block: &Block,
    caller_ft: &FnTypes,
    module: &Module,
    module_types: &ModuleTypes,
) -> T::Ty {
    match &block.terminator {
        Term::Call { callee, args, .. } => {
            let env = env_at_terminator(t, caller_ft, block, module);
            let arg_tys: Vec<crate::types::Ty> = args
                .iter()
                .map(|av| env.get(av).cloned().unwrap_or_else(|| t.any()))
                .collect();
            // fz-rh5.6 — subsumption-aware lookup. "What does `callee`
            // return for these args?" is a subsumption query: any
            // registered spec whose key covers arg_tys is a sound
            // answer. Exact-match HashMap lookup (the old code here)
            // fell back to `any` whenever the typer's registered key
            // didn't match exactly — even when a wider covering spec
            // existed — producing too-wide cont keys that no
            // registered spec could cover. See
            // `ModuleTypes::effective_return_for_call`.
            module_types
                .effective_return_for_call_ty(t, *callee, &arg_tys)
                .as_ref()
                .cloned()
                .unwrap_or_else(|| t.any())
        }
        // fz-ul4.27.22.6 — at a CallClosure seam, the closure's static
        // The type names the body's possible return shapes. For singleton
        // closure-lits, resolve against the registered body spec using
        // [captures..., arg_tys...]; otherwise fall back to the
        // structural arrow-return join. This is the value the body's
        // Term::Return passes to the cont's slot 0.
        Term::CallClosure { closure, args, .. } => {
            let env = env_at_terminator(t, caller_ft, block, module);
            let closure_d = env.get(closure).cloned().unwrap_or_else(|| t.any());
            if t.closure_lit_parts(&closure_d)
                .is_some_and(|lit| !lit.captures.is_empty())
            {
                let arg_tys: Vec<crate::types::Ty> = args
                    .iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(|| t.any()))
                    .collect();
                match resolve_closure_return(
                    t,
                    &closure_d,
                    &module_types.effective_returns,
                    &arg_tys,
                ) {
                    Some(ty) => ty,
                    None => t.arrow_join_return(&closure_d),
                }
            } else {
                t.arrow_join_return(&closure_d)
            }
        }
        _ => t.any(),
    }
}

/// fz-ul4.42 — compute the set of SpecIds reachable at runtime from
/// `main` (plus closure-dispatched any-key specs as a conservative catch).
///
/// Codegen consults this to skip body emission for unreached specs: a
/// trap stub goes out instead of the full body, dramatically shrinking
/// the emitted binary and the golden CLIF for fixtures that have any
/// per-callsite specialization fan-out the runtime never reaches
/// (ast_eval is the canonical example — pre-prune it ships eval(any),
/// eval(int), eval(2), eval(3), eval(4) bodies that no callsite ever
/// resolves to).
///
/// Algorithm:
///   - Seed with main's spec id, every test/exported entry, and every
///     any-key spec whose fn appears in a `MakeClosure` (conservatively
///     covers opaque closure dispatch without needing per-site
///     closure_lit resolution).
///   - BFS: for each reached spec, walk its reachable blocks, find
///     direct Call/TailCall + their conts and CallClosure/TailCallClosure
///     resolvable via fn_constants. Use the same `SpecRegistry::resolve`
///     subsumption search codegen uses, so a spec marked reachable here
///     is exactly a spec codegen will look up.
pub fn reachable_specs<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    spec_registry: &crate::spec_registry::SpecRegistry,
    module_types: &ModuleTypes,
    extra_seeds: impl IntoIterator<Item = u32>,
) -> HashSet<u32> {
    let mut reached: HashSet<u32> = HashSet::new();
    let mut worklist: Vec<u32> = Vec::new();

    // Build spec_fn_types lookup keyed by SpecId.
    let spec_keys: Vec<SpecKey> = spec_registry.iter().map(|(_, key)| key.clone()).collect();
    let ft_of = |sid: u32| -> Option<&FnTypes> {
        let key = spec_keys.get(sid as usize)?;
        module_types.specs.get(key)
    };
    let fn_of = |sid: u32| -> Option<&FnIr> {
        let key = spec_keys.get(sid as usize)?;
        let &j = module.fn_idx.get(&key.fn_id)?;
        Some(&module.fns[j])
    };

    // fz-uwq.13 — the blanket any-key seed is retired. Pre-uwq the
    // typer marked every registered any-key spec as reachable, a
    // conservative bias that protected codegen's
    // `spec_registry.resolve` fallback. With codegen reading
    // `FnTypes.dispatches` (fz-uwq.5-8) and the fallback dropped
    // (fz-uwq.12/fz-kgk), the blanket seed has no consumer. The seeds
    // that remain are the genuinely-opaque entry channels:
    //
    //   - main (the program entry, seeded just below).
    //   - `extra_seeds` (caller-supplied — closure_shapes, spawn
    //     thunks, scheduler hooks, anything codegen knows is an entry
    //     point the IR-body BFS can't see).
    //   - Closure-target fns (any spec of any fn whose id appears in
    //     a `Prim::MakeClosure`, seeded below).
    //
    // Narrow specs become reachable only when some reachable body
    // explicitly resolves into them via `spec_registry.resolve`. The
    // value-narrow dead-spec win (fz-ul4.42) deepens: previously-
    // reachable any-keys for narrow-only fns now drop too.
    if let Some(main_fn) = module.fns.iter().find(|f| f.name == "main") {
        let n_params = main_fn.block(main_fn.entry).params.len();
        let key = {
            let any = t.any();
            t.repeat(any, n_params)
        };
        let key = SpecKey::value(main_fn.id, crate::types::key_slots_from_tys(key));
        if let Some(sid) = spec_registry.resolve_spec_key(t, &key) {
            worklist.push(sid.0);
        }
    }
    // Caller-supplied seeds: closure-target specs (dispatched via code pointer
    // at runtime), spawn thunks, scheduler hooks, etc. — anything codegen
    // knows is an entry point that our IR-body BFS can't see.
    worklist.extend(extra_seeds);
    // Closure-lit dispatch: any fn whose id appears in a MakeClosure prim
    // could be invoked through a closure-typed Var whose type carries a
    // closure_lit. The per-callsite invocation might resolve to any of
    // that fn's narrow specs. Without modeling the full closure_lit
    // narrowing chain (deferred from v1), mark every spec of every
    // MakeClosure'd fn reachable. Over-marks but stays correct; the
    // value-narrow dead specs in non-closure'd fns (the actual fz-ul4.42
    // target — eval(2)/eval(3)/etc in ast_eval) are still pruned.
    let mut closure_target_fns: HashSet<FnId> = HashSet::new();
    for f in &module.fns {
        for blk in &f.blocks {
            for stmt in &blk.stmts {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeClosure(_, lam_id, _) = prim {
                    closure_target_fns.insert(*lam_id);
                }
            }
        }
    }
    for (sid, key) in spec_registry.iter() {
        if closure_target_fns.contains(&key.fn_id) {
            worklist.push(sid.0);
        }
    }

    while let Some(sid) = worklist.pop() {
        if !reached.insert(sid) {
            continue;
        }
        let Some(f) = fn_of(sid) else { continue };
        let Some(ft) = ft_of(sid) else { continue };
        for blk in &f.blocks {
            if !ft.reachable_blocks.contains(&blk.id) {
                continue;
            }
            let env = env_at_terminator(t, ft, blk, module);
            // Capture `any` once so the closures stay `Fn` (no &mut T capture).
            let any_ty = t.any();
            let arg_tys = |args: &[Var]| -> Vec<crate::types::Ty> {
                args.iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(|| any_ty.clone()))
                    .collect()
            };
            let pad_to_arity =
                |callee: FnId, mut tys: Vec<crate::types::Ty>| -> Vec<crate::types::Ty> {
                    if let Some(&j) = module.fn_idx.get(&callee) {
                        let np = module.fns[j].block(module.fns[j].entry).params.len();
                        while tys.len() < np {
                            tys.push(any_ty.clone());
                        }
                        tys.truncate(np);
                    }
                    tys
                };
            let value_key = |callee: FnId, tys: Vec<crate::types::Ty>| {
                SpecKey::value(callee, crate::types::key_slots_from_tys(tys))
            };
            match &blk.terminator {
                Term::Call {
                    ident: _,
                    callee,
                    args,
                    continuation,
                } => {
                    let key = pad_to_arity(*callee, arg_tys(args));
                    let key = value_key(*callee, key);
                    if let Some(sid) = spec_registry.resolve_spec_key(t, &key) {
                        worklist.push(sid.0);
                    }
                    let cont_key = cont_input_key(t, blk, continuation, ft, module, module_types);
                    let cont_key = value_key(continuation.fn_id, cont_key);
                    if let Some(sid) = spec_registry.resolve_spec_key(t, &cont_key) {
                        worklist.push(sid.0);
                    }
                }
                Term::TailCall { callee, args, .. } => {
                    let key = pad_to_arity(*callee, arg_tys(args));
                    let key = value_key(*callee, key);
                    if let Some(sid) = spec_registry.resolve_spec_key(t, &key) {
                        worklist.push(sid.0);
                    }
                }
                Term::CallClosure {
                    ident: _,
                    closure,
                    args,
                    continuation,
                } => {
                    if let Some(&target) = ft.fn_constants.get(closure) {
                        let key = pad_to_arity(target, arg_tys(args));
                        let key = value_key(target, key);
                        if let Some(sid) = spec_registry.resolve_spec_key(t, &key) {
                            worklist.push(sid.0);
                        }
                    }
                    let cont_key = cont_input_key(t, blk, continuation, ft, module, module_types);
                    let cont_key = value_key(continuation.fn_id, cont_key);
                    if let Some(sid) = spec_registry.resolve_spec_key(t, &cont_key) {
                        worklist.push(sid.0);
                    }
                }
                Term::TailCallClosure {
                    closure,
                    args,
                    ident: _,
                } => {
                    if let Some(&target) = ft.fn_constants.get(closure) {
                        let key = pad_to_arity(target, arg_tys(args));
                        let key = value_key(target, key);
                        if let Some(sid) = spec_registry.resolve_spec_key(t, &key) {
                            worklist.push(sid.0);
                        }
                    }
                }
                Term::Receive {
                    continuation,
                    ident: _,
                } => {
                    let cont_key = cont_input_key(t, blk, continuation, ft, module, module_types);
                    let cont_key = value_key(continuation.fn_id, cont_key);
                    if let Some(sid) = spec_registry.resolve_spec_key(t, &cont_key) {
                        worklist.push(sid.0);
                    }
                }
                Term::ReceiveMatched {
                    clauses,
                    after,
                    captures: _,
                    ..
                } => {
                    // fz-70q.3 — clause body / guard / after fns are
                    // reached only through the selective-receive
                    // dispatch. The outcome closure env is opaque at
                    // this seam, so resolve the all-`any` body key.
                    let enq = |fid: FnId, _bound_arity: usize, wl: &mut Vec<u32>| {
                        let Some(&j) = module.fn_idx.get(&fid) else {
                            return;
                        };
                        let body = &module.fns[j];
                        let np = body.block(body.entry).params.len();
                        let key = crate::fz_ir::receive_outcome_spec_key(&any_ty, np);
                        let key = SpecKey::value(fid, crate::types::key_slots_from_tys(key));
                        if let Some(sid) = spec_registry.resolve_spec_key(t, &key) {
                            wl.push(sid.0);
                        }
                    };
                    for c in clauses {
                        enq(c.body, c.bound_names.len(), &mut worklist);
                        if let Some(g) = c.guard {
                            enq(g, c.bound_names.len(), &mut worklist);
                        }
                    }
                    if let Some(a) = after {
                        // After body takes no bound vars — just captures.
                        enq(a.body, 0, &mut worklist);
                    }
                }
                _ => {}
            }
        }
    }
    reached
}

/// fz-ul4.29.12.1 — build the full Cont input-type key at a call-site:
/// `[slot0, ...captured_tys]`, padded with `any` to the cont fn's
/// entry-block arity. Mirrors the typer's key construction at
/// `ir_typer.rs:233-240` exactly.
pub fn cont_input_key<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    block: &Block,
    continuation: &Cont,
    caller_ft: &FnTypes,
    module: &Module,
    module_types: &ModuleTypes,
) -> Vec<crate::types::Ty> {
    use crate::types::Ty;
    let cont_fn = module.fn_by_id(continuation.fn_id);
    let n_params = cont_fn.block(cont_fn.entry).params.len();
    let any_t = t.any();
    let mut key: Vec<Ty> = vec![any_t.clone(); n_params];
    if !key.is_empty() {
        let slot0_ty = cont_slot0_descr(t, block, caller_ft, module, module_types);
        key[0] = slot0_ty;
    }
    let env = env_at_terminator(t, caller_ft, block, module);
    for (k, cv) in continuation.captured.iter().enumerate() {
        if let Some(p) = key.get_mut(k + 1) {
            *p = env.get(cv).cloned().unwrap_or_else(|| any_t.clone());
        }
    }
    key
}
