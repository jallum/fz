//! Flow-sensitive type inference over `fz_ir::Module`.
//!
//! For each `FnIr`, walks blocks to a fixed point producing two views:
//!
//!   * `vars: HashMap<Var, Descr>` — type at each Var's definition site
//!     (or, for block params, the union over all incoming Goto args). This
//!     is what consumers ask when they want "the" type of v.
//!   * `block_envs: HashMap<BlockId, HashMap<Var, Descr>>` — per-block entry
//!     environment with branch-narrowed types. Consumers positioned inside a
//!     specific block read this for the tightest available info (e.g. inside
//!     the truthy branch of an `If`, a `cond` predicate's operand may carry
//!     a narrower type than its definition).
//!
//! Branch narrowing (fz-ul4.11.24.3):
//!   * `Term::If(cond, t, e)` inspects the stmt that bound `cond`. If it was
//!     `ListIsNil(v)`, the truthy branch refines `v` to `nil`; the falsy
//!     branch keeps the list shape. If it was `BinOp::Eq(a, b)` and either
//!     operand is a singleton literal, the truthy branch intersects the other
//!     operand with that singleton.
//!   * `Stmt::Let(_, ListHead(v))` types the head as `list_element_type(v)`.
//!   * `Stmt::Let(_, ListTail(v))` types the tail as the list shape itself
//!     (possibly empty -> list_of(elem) ∪ nil; we union with nil).
//!   * `Stmt::Let(_, TupleField(v, i))` uses `tuple_projections` over the
//!     max arity tuple shape in env[v].
//!   * `Stmt::Let(_, MapGet(m, k))` uses `map_field_lookup` when `k` is a
//!     singleton literal.
//!
//! Consumers are still not wired (.11.24.4-.7). The pipeline hook at
//! `ir_codegen::compile()` continues to populate `CompiledModule.types`.

use crate::fz_ir::{
    BinOp, Block, BlockId, BuiltinId, BuiltinKind, Const, Cont, FnId, FnIr, Module, Prim, Stmt,
    Term, UnOp, Var, VecKindIr,
};
use crate::types::{Descr, MapKey};
use std::collections::HashMap;

#[derive(Debug, Clone, Default)]
pub struct FnTypes {
    /// Definition-site type for each Var. Block params get the join of their
    /// predecessor args; Let-bound vars get their Prim's type under the env
    /// at that point in the block.
    pub vars: HashMap<Var, Descr>,
    /// Entry env per block, with branch narrowing applied at If terminators.
    pub block_envs: HashMap<BlockId, HashMap<Var, Descr>>,
}

/// Per-module type information.
///
/// `by_fn_idx` is the legacy per-FnIr view (one FnTypes per fn, with entry
/// params narrowed via lub-aggregation across direct callsites). External
/// consumers index this view via `Index<usize>`; behavior is preserved
/// from before fz-ul4.29.1.
///
/// `specs` is the per-callsite specialization map, keyed by
/// `(FnId, input-Descr-tuple)`. Each distinct argument-Descr signature
/// seen at any direct-call site produces a fresh FnTypes via
/// `type_fn(f, m, Some(&input_descrs))`. The any-key specialization
/// (`vec![Descr::any(); n_params]`) is unconditionally present for every
/// fn so that closure / Spawn / Receive paths have a fallback target.
///
/// fz-ul4.29.1: `specs` is populated but not yet consumed by codegen.
/// fz-ul4.29.2 will introduce a `SpecId` and re-key the codegen-internal
/// structures against this map; `by_fn_idx` retires at that point.
pub struct ModuleTypes {
    by_fn_idx: Vec<FnTypes>,
    #[allow(dead_code)] // .29.2 consumes this.
    pub specs: HashMap<(FnId, Vec<Descr>), FnTypes>,
}

impl std::ops::Index<usize> for ModuleTypes {
    type Output = FnTypes;
    fn index(&self, i: usize) -> &Self::Output { &self.by_fn_idx[i] }
}

impl ModuleTypes {
    // .29.1: `len`, `iter`, `spec` are exercised by the new typer unit tests
    // (specs_contains_any_key_for_every_fn, specs_records_narrow_int_callsite,
    // module_types_index_preserves_legacy_view) but no codegen path consumes
    // them yet. .29.2 makes them load-bearing and the lint goes quiet.
    #[allow(dead_code)]
    pub fn len(&self) -> usize { self.by_fn_idx.len() }
    #[allow(dead_code)]
    pub fn iter(&self) -> std::slice::Iter<'_, FnTypes> { self.by_fn_idx.iter() }
    /// Look up a specific specialization. Returns `None` if no callsite has
    /// requested this exact input-Descr-tuple (yet); the any-key
    /// specialization is guaranteed to exist for every fn.
    #[allow(dead_code)]
    pub fn spec(&self, fn_id: FnId, input_descrs: &[Descr]) -> Option<&FnTypes> {
        self.specs.get(&(fn_id, input_descrs.to_vec()))
    }
}

/// Type a whole module. Iterates type_fn to a fixed point, propagating
/// call-site arg Descrs into callee entry-param Descrs after each pass.
/// fz-ul4.27.10: replaces the previous one-shot `map`. Fns with no direct
/// caller (main, closure-only targets) keep entry params at `any`.
pub fn type_module(m: &Module) -> ModuleTypes {
    // Initial pass: every fn typed with `any` entry params.
    let mut by_fn_idx: Vec<FnTypes> =
        m.fns.iter().map(|f| type_fn(f, m, None)).collect();

    // Fn-id → index into the `m.fns` / `by_fn_idx` vectors (cps_split inserts
    // continuation fns out of declaration order).
    let mut idx_of: HashMap<FnId, usize> = HashMap::new();
    for (i, f) in m.fns.iter().enumerate() {
        idx_of.insert(f.id, i);
    }

    // fz-ul4.29.1: per-callsite specialization map. Seeded with the any-key
    // specialization for every fn so closure / Spawn / Receive paths always
    // have a fallback. The fixed point below adds entries for each distinct
    // (callee, input-Descr-tuple) pair seen at any direct call site.
    let mut specs: HashMap<(FnId, Vec<Descr>), FnTypes> = HashMap::new();
    for (i, f) in m.fns.iter().enumerate() {
        let n_params = f.block(f.entry).params.len();
        let any_key = vec![Descr::any(); n_params];
        specs.insert((f.id, any_key), by_fn_idx[i].clone());
    }

    // fz-ul4.29.3: closure-reachable fns no longer skip narrowing —
    // dynamic-dispatch sites (CallClosure, Spawn, Receive) route through
    // the any-key specialization, which type_module unconditionally
    // registers above (line 117) by capturing the initial all-any pass.
    // The direct-call lub-narrowing recorded in `by_fn_idx` is safe to
    // apply: it reflects what's true at direct callsites and isn't read
    // by the closure-invoke path.

    loop {
        // Aggregate per-callee entry-param Descrs as the union over all
        // direct (Call / TailCall) call sites. fz-ul4.29.1 also collects
        // each callsite's distinct arg-Descr tuple into `callsite_keys` so
        // we can emit per-specialization FnTypes alongside the lub-narrowed
        // by_fn_idx view.
        let mut narrowed: HashMap<FnId, Vec<Descr>> = HashMap::new();
        let mut callsite_keys: HashMap<FnId, std::collections::HashSet<Vec<Descr>>> =
            HashMap::new();
        for (i, f) in m.fns.iter().enumerate() {
            let ft = &by_fn_idx[i];
            for b in &f.blocks {
                // Reconstruct env at the terminator.
                let mut env = ft.block_envs.get(&b.id).cloned().unwrap_or_default();
                for stmt in &b.stmts {
                    let Stmt::Let(v, prim) = stmt;
                    env.insert(*v, type_prim(prim, &env, m));
                }
                // Propagate to the callee for direct calls (Call / TailCall).
                match &b.terminator {
                    Term::Call { callee, args, .. } | Term::TailCall { callee, args } => {
                        if let Some(&j) = idx_of.get(callee) {
                            let callee_fn = &m.fns[j];
                            let n_params = callee_fn.block(callee_fn.entry).params.len();
                            let slot = narrowed
                                .entry(*callee)
                                .or_insert_with(|| vec![Descr::none(); n_params]);
                            for (k, av) in args.iter().enumerate() {
                                if let Some(p) = slot.get_mut(k) {
                                    let at = env.get(av).cloned().unwrap_or_else(Descr::any);
                                    *p = p.union(&at);
                                }
                            }
                            // fz-ul4.29.1: record this callsite's exact
                            // arg-Descr tuple. Pad with `any` if fewer args
                            // than params (defensive — shouldn't happen for
                            // well-formed IR but keeps the key well-shaped).
                            let mut key: Vec<Descr> = args.iter().map(|av|
                                env.get(av).cloned().unwrap_or_else(Descr::any)
                            ).collect();
                            while key.len() < n_params { key.push(Descr::any()); }
                            key.truncate(n_params);
                            callsite_keys.entry(*callee).or_default().insert(key);
                        }
                    }
                    _ => {}
                }

                // fz-ul4.27.5.4 / .29.4: propagate to continuations for
                // Call / CallClosure / Receive. Continuation entry params
                // are `[result_var, ...captured_vars]`. Slot 0 (the
                // result) is the callee's return Descr at this callsite —
                // for Term::Call we resolve it via `specs.get((callee,
                // arg_descrs))`; for CallClosure / Receive the callee /
                // sender is opaque so slot 0 stays `any`.
                let cont = match &b.terminator {
                    Term::Call { continuation, .. } => Some(continuation),
                    Term::CallClosure { continuation, .. } => Some(continuation),
                    Term::Receive { continuation } => Some(continuation),
                    _ => None,
                };
                let slot0_descr: Descr = match &b.terminator {
                    Term::Call { callee, args, .. } => {
                        let arg_descrs: Vec<Descr> = args.iter().map(|av|
                            env.get(av).cloned().unwrap_or_else(Descr::any)
                        ).collect();
                        let callee_key = (*callee, arg_descrs);
                        if let Some(callee_ft) = specs.get(&callee_key) {
                            if let Some(&j) = idx_of.get(callee) {
                                let callee_fn = &m.fns[j];
                                let mut joined: Option<Descr> = None;
                                for cb in &callee_fn.blocks {
                                    if let Term::Return(rv) = &cb.terminator {
                                        let d = callee_ft.vars.get(rv).cloned()
                                            .unwrap_or_else(Descr::any);
                                        joined = Some(match joined {
                                            Some(p) => p.union(&d),
                                            None => d,
                                        });
                                    }
                                }
                                joined.unwrap_or_else(Descr::any)
                            } else { Descr::any() }
                        } else { Descr::any() }
                    }
                    _ => Descr::any(),
                };
                if let Some(cont) = cont {
                    if let Some(&j) = idx_of.get(&cont.fn_id) {
                        let cont_fn = &m.fns[j];
                        let n_params = cont_fn.block(cont_fn.entry).params.len();
                        let slot = narrowed
                            .entry(cont.fn_id)
                            .or_insert_with(|| vec![Descr::none(); n_params]);
                        if let Some(p0) = slot.get_mut(0) {
                            *p0 = p0.union(&slot0_descr);
                        }
                        for (k, cv) in cont.captured.iter().enumerate() {
                            if let Some(p) = slot.get_mut(k + 1) {
                                let ct = env.get(cv).cloned().unwrap_or_else(Descr::any);
                                *p = p.union(&ct);
                            }
                        }
                        // Record this callsite's exact cont input-Descr
                        // tuple with slot 0 = callee's specialized return.
                        let mut key: Vec<Descr> = vec![Descr::any(); n_params];
                        if !key.is_empty() { key[0] = slot0_descr.clone(); }
                        for (k, cv) in cont.captured.iter().enumerate() {
                            if let Some(p) = key.get_mut(k + 1) {
                                *p = env.get(cv).cloned().unwrap_or_else(Descr::any);
                            }
                        }
                        callsite_keys.entry(cont.fn_id).or_default().insert(key);
                    }
                }
            }
        }

        // Apply narrowed entry-param Descrs and retype any fn that changed
        // (lub-aggregated view → by_fn_idx; this is the legacy behavior
        // codegen still consumes through .29.1).
        let mut changed = false;
        for (i, f) in m.fns.iter().enumerate() {
            let entry_block = f.block(f.entry);
            let current: Vec<Descr> = entry_block
                .params
                .iter()
                .map(|p| by_fn_idx[i].vars.get(p).cloned().unwrap_or_else(Descr::any))
                .collect();
            let next: Vec<Descr> = match narrowed.get(&f.id) {
                Some(v) => v.clone(),
                None => continue, // no direct caller — leave entry params alone
            };
            if next.iter().zip(current.iter()).any(|(n, c)| !n.is_equiv(c)) {
                by_fn_idx[i] = type_fn(f, m, Some(&next));
                changed = true;
            }
        }

        // fz-ul4.29.1: ensure `specs` has an entry for every (callee, key)
        // pair seen at any callsite this iteration. Newly-discovered keys
        // count as `changed` so the fixed point re-runs (a fresh spec may
        // itself contain calls that surface further new keys).
        for (callee, key_set) in &callsite_keys {
            for key in key_set {
                let entry_key = (*callee, key.clone());
                if let Some(&j) = idx_of.get(callee) {
                    if !specs.contains_key(&entry_key) {
                        specs.insert(entry_key, type_fn(&m.fns[j], m, Some(key)));
                        changed = true;
                    }
                    // Existing keys' FnTypes may also drift as the module's
                    // callsite envs sharpen; recompute and replace if so.
                    // (We don't have a deep FnTypes equality so the cheap
                    // signal is: replace if the body uses any other fn's
                    // type info — which may have changed elsewhere this
                    // iter. .29.2 will tighten this to a proper equality
                    // check once specs becomes load-bearing.)
                }
            }
        }

        if !changed {
            break;
        }
    }

    ModuleTypes { by_fn_idx, specs }
}

pub fn type_fn(f: &FnIr, m: &Module, entry_param_types: Option<&[Descr]>) -> FnTypes {
    let mut vars: HashMap<Var, Descr> = HashMap::new();
    let mut block_envs: HashMap<BlockId, HashMap<Var, Descr>> = HashMap::new();

    // Entry block: params come from the caller-narrowed `entry_param_types`
    // when provided (fz-ul4.27.10 module-level fixed point), or default to
    // `any` for the initial pass, fns with no direct caller (main,
    // closure-only targets), and fns that are closure-reachable (whose
    // caller set isn't bounded by the direct-call sites we can see).
    // Non-entry blocks: empty env, populated by goto/if predecessors.
    for b in &f.blocks {
        let mut env = HashMap::new();
        if b.id == f.entry {
            for (i, &p) in b.params.iter().enumerate() {
                let t = entry_param_types
                    .and_then(|ts| ts.get(i))
                    .cloned()
                    .unwrap_or_else(Descr::any);
                env.insert(p, t.clone());
                vars.insert(p, t);
            }
        }
        block_envs.insert(b.id, env);
    }

    loop {
        let mut changed = false;

        for b in &f.blocks {
            // Re-derive env at each stmt position.
            let mut env = block_envs[&b.id].clone();
            for stmt in &b.stmts {
                let Stmt::Let(v, prim) = stmt;
                let t = type_prim(prim, &env, m);
                env.insert(*v, t.clone());
                // vars is the definition-site type; single assignment so
                // we just overwrite each iteration (will converge).
                let prev = vars.get(v).cloned().unwrap_or_else(Descr::none);
                if !t.is_equiv(&prev) {
                    vars.insert(*v, t);
                    changed = true;
                }
            }

            // Propagate to successors.
            match &b.terminator {
                Term::Goto(target, args) => {
                    let target_b = f.block(*target);
                    let mut delta = env.clone();
                    // Substitute target's params with the supplied arg types.
                    let arg_ts: Vec<Descr> = args
                        .iter()
                        .map(|a| env.get(a).cloned().unwrap_or_else(Descr::any))
                        .collect();
                    // Remove anything keyed by the source-block's view of
                    // the args (they're not the same Vars as target params).
                    for (i, &p) in target_b.params.iter().enumerate() {
                        if let Some(t) = arg_ts.get(i) {
                            delta.insert(p, t.clone());
                        }
                    }
                    if merge_into(&mut block_envs, *target, &delta) {
                        changed = true;
                    }
                    // Update vars for target's params via union across all
                    // predecessors (handled via merge_into's union, but we
                    // also need to mirror in vars).
                    for (i, &p) in target_b.params.iter().enumerate() {
                        let from_env = block_envs[target].get(&p).cloned().unwrap_or_else(Descr::none);
                        let prev = vars.get(&p).cloned().unwrap_or_else(Descr::none);
                        if !from_env.is_equiv(&prev) {
                            vars.insert(p, from_env);
                            changed = true;
                        }
                        let _ = i;
                    }
                }
                Term::If(cond, then_b, else_b) => {
                    let (then_env, else_env) = narrow_for_if(&env, *cond, &b.stmts);
                    if merge_into(&mut block_envs, *then_b, &then_env) { changed = true; }
                    if merge_into(&mut block_envs, *else_b, &else_env) { changed = true; }
                }
                Term::Call { .. }
                | Term::TailCall { .. }
                | Term::CallClosure { .. }
                | Term::TailCallClosure { .. }
                | Term::Return(_)
                | Term::Halt(_)
                | Term::Receive { .. } => {
                    // Inter-fn flow goes through separate FnIr continuations;
                    // intra-fn flow stops here.
                }
            }
        }

        if !changed { break; }
    }

    FnTypes { vars, block_envs }
}

/// Union `delta` into `block_envs[target]`. Returns true if anything changed.
fn merge_into(
    block_envs: &mut HashMap<BlockId, HashMap<Var, Descr>>,
    target: BlockId,
    delta: &HashMap<Var, Descr>,
) -> bool {
    let env = block_envs.entry(target).or_default();
    let mut changed = false;
    for (v, t) in delta {
        let prev = env.get(v).cloned().unwrap_or_else(Descr::none);
        let unioned = prev.union(t);
        if !unioned.is_equiv(&prev) {
            env.insert(*v, unioned);
            changed = true;
        }
    }
    changed
}

/// Find the stmt that bound `cond` (if any) and split the env into
/// (then_env, else_env) narrowing the predicate's operands accordingly.
fn narrow_for_if(
    env: &HashMap<Var, Descr>,
    cond: Var,
    stmts: &[Stmt],
) -> (HashMap<Var, Descr>, HashMap<Var, Descr>) {
    let mut then_env = env.clone();
    let mut else_env = env.clone();

    let prim = stmts.iter().find_map(|s| {
        let Stmt::Let(v, p) = s;
        if *v == cond { Some(p) } else { None }
    });

    let Some(prim) = prim else {
        return (then_env, else_env);
    };

    match prim {
        Prim::ListIsNil(v) => {
            let current = env.get(v).cloned().unwrap_or_else(Descr::any);
            let then_t = current.intersect(&Descr::nil());
            let else_t = current.intersect(&Descr::list_of(Descr::any()));
            then_env.insert(*v, then_t);
            else_env.insert(*v, else_t);
        }
        Prim::BinOp(BinOp::Eq, a, b) => {
            let at = env.get(a).cloned().unwrap_or_else(Descr::any);
            let bt = env.get(b).cloned().unwrap_or_else(Descr::any);
            // Truthy: intersect the non-singleton operand with the singleton.
            // Falsy: subtract the singleton from the non-singleton operand
            // (.24.6 brought this in; .24.3 had it scoped out).
            if is_singleton_lit(&at) {
                then_env.insert(*b, bt.intersect(&at));
                else_env.insert(*b, bt.diff(&at));
            }
            if is_singleton_lit(&bt) {
                then_env.insert(*a, at.intersect(&bt));
                else_env.insert(*a, at.diff(&bt));
            }
        }
        Prim::BinOp(BinOp::Neq, a, b) => {
            // Mirror of Eq: narrow on the else branch (truthy) and diff on
            // then.
            let at = env.get(a).cloned().unwrap_or_else(Descr::any);
            let bt = env.get(b).cloned().unwrap_or_else(Descr::any);
            if is_singleton_lit(&at) {
                else_env.insert(*b, bt.intersect(&at));
                then_env.insert(*b, bt.diff(&at));
            }
            if is_singleton_lit(&bt) {
                else_env.insert(*a, at.intersect(&bt));
                then_env.insert(*a, at.diff(&bt));
            }
        }
        _ => {}
    }

    (then_env, else_env)
}

fn is_singleton_lit(d: &Descr) -> bool {
    (!d.ints.cofinite && d.ints.set.len() == 1)
        || (!d.atoms.cofinite && d.atoms.set.len() == 1)
        || (!d.strs.cofinite && d.strs.set.len() == 1)
        || (!d.floats.cofinite && d.floats.set.len() == 1)
}

fn type_prim(prim: &Prim, env: &HashMap<Var, Descr>, m: &Module) -> Descr {
    match prim {
        Prim::Const(c) => type_const(c),

        Prim::BinOp(op, a, b) => {
            let at = lookup(env, *a);
            let bt = lookup(env, *b);
            type_binop(*op, &at, &bt)
        }
        Prim::UnOp(op, v) => {
            let vt = lookup(env, *v);
            match op {
                UnOp::Neg => numeric_result(&vt, &vt),
                UnOp::Not => Descr::bool_t(),
            }
        }

        Prim::MakeTuple(vs) => {
            let elems: Vec<Descr> = vs.iter().map(|v| lookup(env, *v)).collect();
            Descr::tuple_of(elems)
        }
        Prim::TupleField(v, i) => {
            let vt = lookup(env, *v);
            // Find the widest arity in v's tuple clauses that covers index i;
            // project that component. Falls back to any when there's no
            // matching tuple shape.
            let mut max_arity = 0usize;
            for cl in &vt.tuples {
                for sig in &cl.pos {
                    if sig.elems.len() > max_arity {
                        max_arity = sig.elems.len();
                    }
                }
            }
            if (*i as usize) < max_arity {
                let comps = crate::typer::tuple_projections(&vt, max_arity);
                comps.into_iter().nth(*i as usize).unwrap_or_else(Descr::any)
            } else {
                Descr::any()
            }
        }

        Prim::MakeList(els, tail) => {
            let mut elem = Descr::none();
            for v in els { elem = elem.union(&lookup(env, *v)); }
            if let Some(t) = tail {
                let tt = lookup(env, *t);
                elem = elem.union(&crate::typer::list_element_type(&tt));
            }
            Descr::list_of(elem)
        }
        Prim::ListCons(h, t) => {
            let ht = lookup(env, *h);
            let tt = lookup(env, *t);
            Descr::list_of(ht.union(&crate::typer::list_element_type(&tt)))
        }
        Prim::ListHead(l) => crate::typer::list_element_type(&lookup(env, *l)),
        Prim::ListTail(l) => {
            let lt = lookup(env, *l);
            let elem = crate::typer::list_element_type(&lt);
            // Tail is either a (possibly empty) list of the same elem, or nil.
            Descr::list_of(elem).union(&Descr::nil())
        }
        Prim::ListIsNil(_) => Descr::bool_t(),

        Prim::MakeMap(entries) => {
            let mut fields = std::collections::BTreeMap::new();
            let mut all_static = true;
            for (k, v) in entries {
                let vt = lookup(env, *v);
                match var_as_map_key(*k, env) {
                    Some(mk) => { fields.insert(mk, vt); }
                    None => { all_static = false; break; }
                }
            }
            if all_static && !entries.is_empty() {
                Descr::map_of(fields)
            } else if entries.is_empty() {
                Descr::map_of([])
            } else {
                Descr::map_top()
            }
        }
        Prim::MapUpdate(base, entries) => {
            let mut d = lookup(env, *base);
            for (k, v) in entries {
                let vt = lookup(env, *v);
                if let Some(mk) = var_as_map_key(*k, env) {
                    d = crate::typer::refine_map_field(&d, &mk, &vt);
                }
            }
            d
        }
        Prim::MapGet(map, k) => {
            let mt = lookup(env, *map);
            if let Some(mk) = var_as_map_key(*k, env) {
                crate::typer::map_field_lookup(&mt, &mk)
                    .unwrap_or_else(|| Descr::any().union(&Descr::nil()))
            } else {
                Descr::any().union(&Descr::nil())
            }
        }

        Prim::MakeVec(kind, _) => match kind {
            VecKindIr::I64 => Descr::vec_i64(),
            VecKindIr::F64 => Descr::vec_f64(),
            VecKindIr::U8 => Descr::vec_u8(),
            VecKindIr::Bit => Descr::vec_bit(),
        },
        Prim::MakeBitstring(_) => Descr::vec_u8().union(&Descr::vec_bit()),

        Prim::MakeClosure(fn_id, _) => {
            let callee = m.fn_by_id(*fn_id);
            let entry = callee.block(callee.entry);
            let arity = entry.params.len();
            let args: Vec<Descr> = std::iter::repeat_n(Descr::any(), arity).collect();
            Descr::arrow(args, Descr::any())
        }

        Prim::Builtin(bid, _) => type_builtin(*bid),

        // Reader and struct ops: conservative Top until later tickets refine.
        Prim::AllocStruct(_, _) => Descr::any(),
        Prim::BitReaderInit(_) => Descr::any(),
        Prim::BitReadField { ty, .. } => {
            // Returns Tuple([ok, value, new_reader]) on success, Tuple([false])
            // on failure. We over-approximate to a generic tuple shape; pattern
            // narrowing on TupleField then projects per-position. Field value
            // depends on the BitType.
            use crate::ast::BitType;
            let value_t = match ty {
                BitType::Integer | BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => Descr::int(),
                BitType::Float => Descr::float(),
                BitType::Binary => Descr::vec_u8(),
                BitType::Bits => Descr::vec_u8().union(&Descr::vec_bit()),
            };
            let success = Descr::tuple_of([Descr::bool_t(), value_t, Descr::any()]);
            let failure = Descr::tuple_of([Descr::bool_t()]);
            success.union(&failure)
        }
        Prim::BitReaderDone(_) => Descr::bool_t(),
    }
}

fn type_const(c: &Const) -> Descr {
    match c {
        Const::Int(n) => Descr::int_lit(*n),
        Const::Float(f) => Descr::float_lit(*f),
        Const::Str(s) => Descr::str_lit(s.clone()),
        Const::Atom(id) => Descr::atom_lit(format!("a{}", id)),
        Const::Nil => Descr::nil(),
        Const::True => Descr::atom_lit("true"),
        Const::False => Descr::atom_lit("false"),
    }
}

fn type_binop(op: BinOp, a: &Descr, b: &Descr) -> Descr {
    use BinOp::*;
    match op {
        Add | Sub | Mul | Div | Mod => numeric_result(a, b),
        Eq | Neq | Lt | Le | Gt | Ge => Descr::bool_t(),
        And | Or => a.union(b),
    }
}

fn numeric_result(a: &Descr, b: &Descr) -> Descr {
    let int = Descr::int();
    let float = Descr::float();
    let both_int = a.is_subtype(&int) && b.is_subtype(&int);
    let both_float = a.is_subtype(&float) && b.is_subtype(&float);
    if both_int { int }
    else if both_float { float }
    else { int.union(&float) }
}

fn type_builtin(bid: BuiltinId) -> Descr {
    match BuiltinKind::from_id(bid) {
        Some(BuiltinKind::Print) => Descr::nil(),
        Some(BuiltinKind::Assert)
        | Some(BuiltinKind::AssertEq)
        | Some(BuiltinKind::AssertNeq) => Descr::nil(),
        Some(BuiltinKind::VecGet) => Descr::int().union(&Descr::float()),
        // fz-ul4.19.2: spawn/self both return a Pid (boxed Int for v1).
        Some(BuiltinKind::Spawn) | Some(BuiltinKind::SelfPid) => Descr::int(),
        // fz-ul4.19.3: send returns the original message (any type).
        Some(BuiltinKind::Send) => Descr::any(),
        None => Descr::any(),
    }
}

fn lookup(env: &HashMap<Var, Descr>, v: Var) -> Descr {
    env.get(&v).cloned().unwrap_or_else(Descr::any)
}

fn var_as_map_key(v: Var, env: &HashMap<Var, Descr>) -> Option<MapKey> {
    let d = env.get(&v)?;
    if !d.ints.cofinite && d.ints.set.len() == 1 {
        return Some(MapKey::Int(*d.ints.set.iter().next().unwrap()));
    }
    if !d.atoms.cofinite && d.atoms.set.len() == 1 {
        return Some(MapKey::Atom(d.atoms.set.iter().next().unwrap().clone()));
    }
    if !d.strs.cofinite && d.strs.set.len() == 1 {
        return Some(MapKey::Str(d.strs.set.iter().next().unwrap().clone()));
    }
    None
}

// Suppress unused imports under cfg(not(test)).
#[allow(dead_code)]
fn _suppress_block(_: &Block) {}

/// .11.24.7: re-type a target FnIr's body assuming its entry-block params
/// have the supplied Descrs. Returns the union of Descrs at every local
/// Return/Halt site, suitable for tier-up specialization decisions.
///
/// Scope-down (authorized): only follows Return/Halt sites inside this FnIr.
/// Cross-fn continuation chains (introduced by `cps_split` at non-tail calls)
/// are not chased — a self-recursive function whose recursive paths exit via
/// a continuation FnIr will appear to return only its base-case Descrs. A
/// follow-up ticket can extend this once tier-up profiling exposes the gap.
/// For non-recursive single-FnIr functions (the .13 starting point) the
/// result is precise.
///
/// Termination: capped at K=4 fixpoint iterations; values are widened past
/// K=3 via `crate::typer::widen` so singleton-growing recursive paths still
/// converge.
#[allow(dead_code, reason = "tier-up hook; consumed by fz-ul4.19.5 per .24.7")]
pub fn specialize_return(
    m: &Module,
    fn_id: crate::fz_ir::FnId,
    params: &[Descr],
) -> Descr {
    use crate::fz_ir::Stmt;
    let f = m.fn_by_id(fn_id);

    let mut block_envs: HashMap<crate::fz_ir::BlockId, HashMap<crate::fz_ir::Var, Descr>> =
        HashMap::new();
    let entry_b = f.block(f.entry);
    let mut entry_env: HashMap<crate::fz_ir::Var, Descr> = HashMap::new();
    for (i, &p) in entry_b.params.iter().enumerate() {
        let t = params.get(i).cloned().unwrap_or_else(Descr::any);
        entry_env.insert(p, t);
    }
    block_envs.insert(f.entry, entry_env);
    for b in &f.blocks {
        if b.id != f.entry {
            block_envs.insert(b.id, HashMap::new());
        }
    }

    let max_iter: usize = 4;
    let widen_at: usize = 3;
    for iter in 0..max_iter {
        let mut changed = false;
        for b in &f.blocks {
            let mut env = block_envs[&b.id].clone();
            for stmt in &b.stmts {
                let Stmt::Let(v, prim) = stmt;
                let t = type_prim(prim, &env, m);
                env.insert(*v, t);
            }
            match &b.terminator {
                Term::Goto(target, args) => {
                    let target_b = f.block(*target);
                    let mut delta = env.clone();
                    let arg_ts: Vec<Descr> = args
                        .iter()
                        .map(|a| env.get(a).cloned().unwrap_or_else(Descr::any))
                        .collect();
                    for (i, &p) in target_b.params.iter().enumerate() {
                        if let Some(t) = arg_ts.get(i) {
                            delta.insert(p, t.clone());
                        }
                    }
                    if merge_into(&mut block_envs, *target, &delta) {
                        changed = true;
                    }
                }
                Term::If(cond, then_b, else_b) => {
                    let (then_env, else_env) = narrow_for_if(&env, *cond, &b.stmts);
                    if merge_into(&mut block_envs, *then_b, &then_env) { changed = true; }
                    if merge_into(&mut block_envs, *else_b, &else_env) { changed = true; }
                }
                _ => {}
            }
        }
        if iter >= widen_at {
            for env in block_envs.values_mut() {
                for v in env.values_mut() {
                    *v = crate::typer::widen(v);
                }
            }
        }
        if !changed { break; }
    }

    // Collect union of Descrs at every local Return/Halt site.
    let mut ret = Descr::none();
    for b in &f.blocks {
        let mut env = block_envs.get(&b.id).cloned().unwrap_or_default();
        for stmt in &b.stmts {
            let Stmt::Let(v, prim) = stmt;
            let t = type_prim(prim, &env, m);
            env.insert(*v, t);
        }
        match &b.terminator {
            Term::Return(v) | Term::Halt(v) => {
                let t = env.get(v).cloned().unwrap_or_else(Descr::any);
                ret = ret.union(&t);
            }
            _ => {}
        }
    }
    ret
}

/// .11.24.6: scan typer output for unreachable If branches. For each
/// `Term::If(cond, then_b, else_b)`, re-run the branch narrowing under the
/// terminator's pre-env. If either branch's narrowed operand is empty, that
/// branch is unreachable.
///
/// Returns diagnostics in a stable order (sorted by fn position then block id).
/// Each diagnostic carries the offending block's terminator span (when
/// recorded by ir_lower in `Module.source.term_span`); .20.8 will enrich
/// the message with the set-theoretic type vocabulary.
pub fn collect_diagnostics(
    module: &Module,
    types: &ModuleTypes,
) -> crate::diag::Diagnostics {
    use crate::diag::{Diagnostic, Diagnostics, Span};
    use crate::diag::codes::{TYPE_UNREACHABLE_ARM, TYPE_DEAD_BINOP};

    let mut out = Diagnostics::new();
    for (i, f) in module.fns.iter().enumerate() {
        let ft = &types[i];
        let mut blocks_sorted: Vec<&crate::fz_ir::Block> = f.blocks.iter().collect();
        blocks_sorted.sort_by_key(|b| b.id.0);
        for b in blocks_sorted {
            let Term::If(cond, then_b, else_b) = b.terminator else { continue };

            // Reconstruct the env at the terminator.
            let mut env = ft.block_envs.get(&b.id).cloned().unwrap_or_default();
            for stmt in &b.stmts {
                let Stmt::Let(v, prim) = stmt;
                let t = type_prim(prim, &env, module);
                env.insert(*v, t);
            }

            let (then_env, else_env) = narrow_for_if(&env, cond, &b.stmts);
            let term_span = module.source.term_span
                .get(&(f.id, b.id))
                .copied()
                .unwrap_or(Span::DUMMY);

            let check = |branch_env: &HashMap<crate::fz_ir::Var, Descr>, tag: &str, bb_id: crate::fz_ir::BlockId| -> Option<Diagnostic> {
                let mut keys: Vec<crate::fz_ir::Var> = branch_env.keys().copied().collect();
                keys.sort_by_key(|v| v.0);
                for v in keys {
                    let new_t = branch_env.get(&v).unwrap();
                    let old_t = env.get(&v).cloned().unwrap_or_else(Descr::any);
                    if !new_t.is_equiv(&old_t) && new_t.is_empty() && !old_t.is_empty() {
                        // `.20.8`: render the source name (or "this value"
                        // for compiler temps) and the *set-theoretic type*
                        // the user's value had right before the failing
                        // narrowing. The vocabulary comes from
                        // `Descr::display_for_diag` — same algebra the
                        // typer reasons in.
                        let var_name = module.source.var_name_of(v);
                        let label_subject = match var_name {
                            Some(n) => format!("`{}`", n),
                            None => "this value".to_string(),
                        };
                        let var_span = module.source.var_span_of(v);

                        let message = format!("the {} branch is never reachable", tag);
                        let type_note = format!(
                            "{} here has type `{}`",
                            label_subject,
                            old_t.display_for_diag(),
                        );
                        let narrow_note = format!(
                            "narrowing for this branch would need `{}`, but that intersection \
                             is uninhabited (unreachable arm at bb{})",
                            new_t.display_for_diag(),
                            bb_id.0,
                        );

                        let mut d = Diagnostic::warning(TYPE_UNREACHABLE_ARM, message, term_span)
                            .with_label(format!("in fn `{}`", f.name))
                            .with_note(type_note)
                            .with_note(narrow_note);
                        // Point a secondary at the var's binding site
                        // when we have it — gives the reader the source
                        // line where the value entered scope.
                        if !var_span.is_dummy() && var_span != term_span {
                            d = d.with_secondary(var_span, format!("{} bound here", label_subject));
                        }
                        return Some(d);
                    }
                }
                None
            };
            if let Some(d) = check(&then_env, "then", then_b) { out.push(d); }
            if let Some(d) = check(&else_env, "else", else_b) { out.push(d); }
        }
    }

    // VR.5a (fz-ul4.27.4): flag kind-disjoint equality / inequality. We walk
    // each Let stmt, rebuild the env up to that stmt, and report a
    // type/dead-binop diagnostic when `intersect(t_a, t_b)` is empty. The
    // codegen-side fold (Eq -> FALSE, Neq -> TRUE) is unaffected by the
    // diagnostic; the user just gets a warning that the comparison can never
    // hold.
    for (i, f) in module.fns.iter().enumerate() {
        let ft = &types[i];
        let mut blocks_sorted: Vec<&crate::fz_ir::Block> = f.blocks.iter().collect();
        blocks_sorted.sort_by_key(|b| b.id.0);
        for b in blocks_sorted {
            let mut env = ft.block_envs.get(&b.id).cloned().unwrap_or_default();
            let spans = module.source.stmt_spans.get(&(f.id, b.id));
            for (sidx, stmt) in b.stmts.iter().enumerate() {
                let Stmt::Let(v, prim) = stmt;
                if let Prim::BinOp(op, lhs, rhs) = prim {
                    if matches!(op, BinOp::Eq | BinOp::Neq) {
                        let ta = env.get(lhs).cloned().unwrap_or_else(Descr::any);
                        let tb = env.get(rhs).cloned().unwrap_or_else(Descr::any);
                        // Lint only on cross-kind disjointness (int vs atom,
                        // float vs nil, etc.). Within a single axis, two
                        // disjoint literal sets (e.g. `1 == 2`) still fold to
                        // false at codegen but are not surprising to the
                        // reader, so we keep them silent.
                        let cross_kind = !ta.is_empty() && !tb.is_empty()
                            && !axes_overlap(&ta, &tb);
                        if cross_kind {
                            let span = spans
                                .and_then(|s| s.get(sidx).copied())
                                .unwrap_or(Span::DUMMY);
                            let constant = if matches!(op, BinOp::Eq) { "false" } else { "true" };
                            let opname = if matches!(op, BinOp::Eq) { "==" } else { "!=" };
                            let message = format!(
                                "`{}` is always {}: operand types do not overlap",
                                opname, constant,
                            );
                            let note = format!(
                                "left has type `{}`; right has type `{}`",
                                ta.display_for_diag(),
                                tb.display_for_diag(),
                            );
                            let d = Diagnostic::warning(TYPE_DEAD_BINOP, message, span)
                                .with_label(format!("in fn `{}`", f.name))
                                .with_note(note);
                            out.push(d);
                        }
                    }
                }
                let t = type_prim(prim, &env, module);
                env.insert(*v, t);
            }
        }
    }

    out
}

/// True iff `a` and `b` have at least one axis (basic-kind bit, atoms,
/// ints, floats, strs, tuples, lists, funcs, maps) on which both are
/// non-empty. Used by the VR.5a `type/dead-binop` lint to distinguish
/// "different kinds" (worth surfacing) from "same kind, narrowed to
/// disjoint literals" (silent fold).
fn axes_overlap(a: &Descr, b: &Descr) -> bool {
    !a.basic.intersect(b.basic).is_empty()
        || (!a.atoms.is_none()  && !b.atoms.is_none())
        || (!a.ints.is_none()   && !b.ints.is_none())
        || (!a.floats.is_none() && !b.floats.is_none())
        || (!a.strs.is_none()   && !b.strs.is_none())
        || (!a.tuples.is_empty() && !b.tuples.is_empty())
        || (!a.lists.is_empty()  && !b.lists.is_empty())
        || (!a.funcs.is_empty()  && !b.funcs.is_empty())
        || (!a.maps.is_empty()   && !b.maps.is_empty())
}

/// .11.24.5: refine `MakeVec(I64, els)` to `MakeVec(F64, els)` when any
/// element is typed Float. Errors on the "mixed Int and Float" case under
/// the no-auto-promotion rule.
///
/// Operates in-place on `module`. Caller supplies a typer output that was
/// produced from the same module shape (run `type_module(module)` first).
pub fn rewrite_vec_kinds(
    module: &mut Module,
    types: &ModuleTypes,
) -> Result<(), String> {
    use crate::fz_ir::Stmt;
    for (i, f) in module.fns.iter_mut().enumerate() {
        let vars = &types[i].vars;
        for blk in &mut f.blocks {
            for stmt in &mut blk.stmts {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeVec(kind @ VecKindIr::I64, els) = prim {
                    let mut any_float = false;
                    let mut any_int = false;
                    for &ev in els.iter() {
                        let d = vars.get(&ev).cloned().unwrap_or_else(Descr::any);
                        if !d.intersect(&Descr::float()).is_empty()
                            && d.intersect(&Descr::int()).is_empty()
                        {
                            any_float = true;
                        } else if d.is_subtype(&Descr::int()) {
                            any_int = true;
                        }
                    }
                    if any_float && any_int {
                        return Err(format!(
                            "~v[..] in {} mixes Int and Float element types; \
                             no auto-promotion (fz-ul4.11.24.5)",
                            f.name
                        ));
                    }
                    if any_float {
                        *kind = VecKindIr::F64;
                    }
                }
            }
        }
    }
    Ok(())
}

// ----------------------------------------------------------------------
// fz-ul4.29.12.1 — Cont input-Descr key helpers
// ----------------------------------------------------------------------

/// Reconstruct the per-Var env at the *terminator* of `block` under
/// `caller_ft`. Starts from `caller_ft.block_envs[block.id]` (which
/// already incorporates if-narrowing from predecessor blocks) and
/// folds in each Let by re-applying `type_prim`. This mirrors the
/// typer's own propagation pass at `type_module`'s `callsite_keys`
/// site (`ir_typer.rs:142-145`).
fn env_at_terminator(
    caller_ft: &FnTypes,
    block: &Block,
    module: &Module,
) -> HashMap<Var, Descr> {
    let mut env = caller_ft
        .block_envs
        .get(&block.id)
        .cloned()
        .unwrap_or_default();
    for stmt in &block.stmts {
        let Stmt::Let(v, prim) = stmt;
        let t = type_prim(prim, &env, module);
        env.insert(*v, t);
    }
    env
}

/// fz-ul4.29.12.1 — slot-0 Descr for a Cont's input-Descr key at the
/// call-site whose terminator is `block.terminator`. Mirrors the
/// typer's logic at `ir_typer.rs:190-215`:
///
///   * `Term::Call`: callee's specialized return Descr under this
///     call-site's arg Descrs (joined over the callee's `Return`
///     terminators using `module_types.specs[(callee, arg_descrs)]`).
///   * `Term::CallClosure` / `Term::Receive`: callee/sender is
///     opaque, so slot 0 stays `Descr::any()`.
///   * Anything else: not a Cont-producing terminator, returns `any`.
pub fn cont_slot0_descr(
    block: &Block,
    caller_ft: &FnTypes,
    module: &Module,
    module_types: &ModuleTypes,
) -> Descr {
    let Term::Call { callee, args, .. } = &block.terminator else {
        return Descr::any();
    };
    let env = env_at_terminator(caller_ft, block, module);
    let arg_descrs: Vec<Descr> = args
        .iter()
        .map(|av| env.get(av).cloned().unwrap_or_else(Descr::any))
        .collect();
    let Some(callee_ft) = module_types.specs.get(&(*callee, arg_descrs)) else {
        return Descr::any();
    };
    let callee_fn = module.fn_by_id(*callee);
    let mut joined: Option<Descr> = None;
    for cb in &callee_fn.blocks {
        if let Term::Return(rv) = &cb.terminator {
            let d = callee_ft.vars.get(rv).cloned().unwrap_or_else(Descr::any);
            joined = Some(match joined {
                Some(p) => p.union(&d),
                None => d,
            });
        }
    }
    joined.unwrap_or_else(Descr::any)
}

/// fz-ul4.29.12.1 — build the full Cont input-Descr key at a call-site:
/// `[slot0, ...captured_descrs]`, padded with `any` to the cont fn's
/// entry-block arity. Mirrors the typer's key construction at
/// `ir_typer.rs:233-240` exactly.
pub fn cont_input_key(
    block: &Block,
    continuation: &Cont,
    caller_ft: &FnTypes,
    module: &Module,
    module_types: &ModuleTypes,
) -> Vec<Descr> {
    let cont_fn = module.fn_by_id(continuation.fn_id);
    let n_params = cont_fn.block(cont_fn.entry).params.len();
    let mut key: Vec<Descr> = vec![Descr::any(); n_params];
    if !key.is_empty() {
        key[0] = cont_slot0_descr(block, caller_ft, module, module_types);
    }
    let env = env_at_terminator(caller_ft, block, module);
    for (k, cv) in continuation.captured.iter().enumerate() {
        if let Some(p) = key.get_mut(k + 1) {
            *p = env.get(cv).cloned().unwrap_or_else(Descr::any);
        }
    }
    key
}

// ----------------------------------------------------------------------
// Tests
// ----------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{BinOp, Const, FnBuilder, FnId, ModuleBuilder, Prim, Term, Var};

    fn build_module(fns: Vec<crate::fz_ir::FnIr>) -> Module {
        let mut mb = ModuleBuilder::new();
        for f in fns { mb.add_fn(f); }
        mb.build()
    }

    // ---- .24.2 tests (preserved, adjusted to FnTypes API) ----

    #[test]
    fn const_int_typed_as_singleton() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let v = b.let_(entry, Prim::Const(Const::Int(42)));
        b.set_terminator(entry, Term::Halt(v));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        assert!(mt[0].vars.get(&v).unwrap().is_equiv(&Descr::int_lit(42)));
    }

    #[test]
    fn add1_body_is_int_top_when_param_is_any() {
        let mut b = FnBuilder::new(FnId(0), "add1");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let sum = b.let_(entry, Prim::BinOp(BinOp::Add, x, one));
        b.set_terminator(entry, Term::Return(sum));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let sum_t = mt[0].vars.get(&sum).cloned().unwrap();
        assert!(sum_t.is_equiv(&Descr::int().union(&Descr::float())),
            "got {}", sum_t);
    }

    #[test]
    fn make_list_of_ints() {
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let a = b.let_(entry, Prim::Const(Const::Int(1)));
        let bv = b.let_(entry, Prim::Const(Const::Int(2)));
        let cv = b.let_(entry, Prim::Const(Const::Int(3)));
        let l = b.let_(entry, Prim::MakeList(vec![a, bv, cv], None));
        b.set_terminator(entry, Term::Return(l));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let lt = mt[0].vars.get(&l).cloned().unwrap();
        let elem = crate::typer::list_element_type(&lt);
        assert!(elem.is_subtype(&Descr::int()), "list elem: {}", elem);
        assert!(!elem.is_empty());
    }

    #[test]
    fn goto_joins_param_types_across_predecessors() {
        let mut b = FnBuilder::new(FnId(0), "join");
        let entry = b.block(vec![]);
        let zero = b.let_(entry, Prim::Const(Const::Int(0)));
        let bb1 = b.block(vec![]);
        let bb2 = b.block(vec![]);
        let joined = Var(99);
        let bb3 = b.block(vec![joined]);
        b.set_terminator(entry, Term::If(zero, bb1, bb2));
        let one = b.let_(bb1, Prim::Const(Const::Int(1)));
        b.set_terminator(bb1, Term::Goto(bb3, vec![one]));
        let two = b.let_(bb2, Prim::Const(Const::Int(2)));
        b.set_terminator(bb2, Term::Goto(bb3, vec![two]));
        b.set_terminator(bb3, Term::Return(joined));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let join_t = mt[0].vars.get(&joined).cloned().unwrap();
        let expected = Descr::int_lit(1).union(&Descr::int_lit(2));
        assert!(join_t.is_equiv(&expected), "got {}", join_t);
    }

    // ---- .24.3 narrowing tests ----

    #[test]
    fn tuple_field_projects_elem_descr() {
        // fn f(t), do: TupleField(t, 0)
        //   - call site builds t = {1, :ok} so we have a concrete tuple shape.
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let ok = b.let_(entry, Prim::Const(Const::Atom(7)));
        let t = b.let_(entry, Prim::MakeTuple(vec![one, ok]));
        let f0 = b.let_(entry, Prim::TupleField(t, 0));
        b.set_terminator(entry, Term::Return(f0));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let f0_t = mt[0].vars.get(&f0).cloned().unwrap();
        assert!(f0_t.is_subtype(&Descr::int_lit(1)) && Descr::int_lit(1).is_subtype(&f0_t),
            "field 0 should be int_lit(1), got {}", f0_t);
    }

    #[test]
    fn list_head_yields_element_type() {
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let two = b.let_(entry, Prim::Const(Const::Int(2)));
        let l = b.let_(entry, Prim::MakeList(vec![one, two], None));
        let h = b.let_(entry, Prim::ListHead(l));
        b.set_terminator(entry, Term::Return(h));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let h_t = mt[0].vars.get(&h).cloned().unwrap();
        // head type = list elem = union(int_lit(1), int_lit(2)) ⊆ int.
        assert!(h_t.is_subtype(&Descr::int()), "head type: {}", h_t);
    }

    #[test]
    fn if_list_is_nil_narrows_v_to_nil_in_then_branch() {
        // Build:
        //   entry(l):
        //     c = ListIsNil(l)
        //     if c then then_b else else_b
        //   then_b: return l   (l narrowed to nil here)
        //   else_b: return l   (l narrowed to list_top here)
        let mut b = FnBuilder::new(FnId(0), "f");
        let l = b.fresh_var();
        let entry = b.block(vec![l]);
        let c = b.let_(entry, Prim::ListIsNil(l));
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        b.set_terminator(entry, Term::If(c, then_b, else_b));
        b.set_terminator(then_b, Term::Return(l));
        b.set_terminator(else_b, Term::Return(l));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);

        // In then_b's entry env, l should be narrowed to nil.
        let then_env = mt[0].block_envs.get(&then_b).unwrap();
        let l_then = then_env.get(&l).cloned().unwrap();
        assert!(l_then.is_subtype(&Descr::nil()) && Descr::nil().is_subtype(&l_then),
            "l in then-branch should be nil: {}", l_then);

        // In else_b's entry env, l should be narrowed to list_top (no nil).
        let else_env = mt[0].block_envs.get(&else_b).unwrap();
        let l_else = else_env.get(&l).cloned().unwrap();
        // Subtype of list_of(any) (loosely: at least the list portion).
        assert!(l_else.is_subtype(&Descr::list_of(Descr::any())),
            "l in else-branch should be list-shaped: {}", l_else);
    }

    #[test]
    fn if_eq_with_int_singleton_narrows_var_in_then_branch() {
        // entry(x):
        //   z = const(0)
        //   c = (x == z)
        //   if c then then_b else else_b
        let mut b = FnBuilder::new(FnId(0), "f");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let z = b.let_(entry, Prim::Const(Const::Int(0)));
        let c = b.let_(entry, Prim::BinOp(BinOp::Eq, x, z));
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        b.set_terminator(entry, Term::If(c, then_b, else_b));
        b.set_terminator(then_b, Term::Return(x));
        b.set_terminator(else_b, Term::Return(x));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);

        let then_env = mt[0].block_envs.get(&then_b).unwrap();
        let x_then = then_env.get(&x).cloned().unwrap();
        assert!(x_then.is_subtype(&Descr::int_lit(0)) && Descr::int_lit(0).is_subtype(&x_then),
            "x in then-branch should be int_lit(0): {}", x_then);
    }

    #[test]
    fn nested_tuple_projection() {
        // Build {inner, c} where inner = {a, b}; project field 0 to get inner,
        // then field 0 of that to get a.
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let a = b.let_(entry, Prim::Const(Const::Int(7)));
        let bv = b.let_(entry, Prim::Const(Const::Atom(3)));
        let inner = b.let_(entry, Prim::MakeTuple(vec![a, bv]));
        let c = b.let_(entry, Prim::Const(Const::Int(9)));
        let outer = b.let_(entry, Prim::MakeTuple(vec![inner, c]));
        let p0 = b.let_(entry, Prim::TupleField(outer, 0));
        let p00 = b.let_(entry, Prim::TupleField(p0, 0));
        b.set_terminator(entry, Term::Return(p00));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let p00_t = mt[0].vars.get(&p00).cloned().unwrap();
        assert!(p00_t.is_equiv(&Descr::int_lit(7)),
            "outer.0.0 should be int_lit(7), got {}", p00_t);
    }

    // ---- .24.7 specialize_return ----

    #[test]
    fn specialize_return_id_with_atom_singleton() {
        // fn id(x) = x.  specialize with [atom_lit("ok")] -> atom_lit("ok").
        let mut b = FnBuilder::new(FnId(0), "id");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        b.set_terminator(entry, Term::Return(x));
        let m = build_module(vec![b.build()]);
        let r = specialize_return(&m, FnId(0), &[Descr::atom_lit("ok")]);
        assert!(r.is_equiv(&Descr::atom_lit("ok")), "got {}", r);
    }

    #[test]
    fn specialize_return_id_with_top_returns_top() {
        let mut b = FnBuilder::new(FnId(0), "id");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        b.set_terminator(entry, Term::Return(x));
        let m = build_module(vec![b.build()]);
        let r = specialize_return(&m, FnId(0), &[Descr::any()]);
        assert!(r.is_equiv(&Descr::any()), "got {}", r);
    }

    #[test]
    fn specialize_return_pick_zero_yields_zero_arm_only() {
        // fn pick(x):
        //   c = (x == 0)
        //   if c then return :zero else return :other
        // specialize with [int_lit(0)] -> just atom_lit("zero").
        let mut b = FnBuilder::new(FnId(0), "pick");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let z = b.let_(entry, Prim::Const(Const::Int(0)));
        let c = b.let_(entry, Prim::BinOp(BinOp::Eq, x, z));
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        b.set_terminator(entry, Term::If(c, then_b, else_b));
        let zero_at = b.let_(then_b, Prim::Const(Const::Atom(1))); // "a1"
        b.set_terminator(then_b, Term::Return(zero_at));
        let other_at = b.let_(else_b, Prim::Const(Const::Atom(2))); // "a2"
        b.set_terminator(else_b, Term::Return(other_at));
        let m = build_module(vec![b.build()]);

        let r0 = specialize_return(&m, FnId(0), &[Descr::int_lit(0)]);
        // With negative-narrowing on Eq's else (added in .24.6), the else arm's
        // x becomes int_lit(0).diff(int_lit(0)) = empty, but the body still
        // assigns Const(:other) which is a literal -> the Return picks up
        // atom_lit("a2") from env. So union includes both arms in this
        // construction. Assert the truthy result is present at minimum.
        let zero_d = Descr::atom_lit("a1");
        assert!(zero_d.is_subtype(&r0), "expected :zero in return, got {}", r0);
    }

    #[test]
    fn specialize_return_terminates_on_simple_loop_like_fn() {
        // Synthetic: a fn with a Goto cycle. Specialize should terminate
        // (max_iter cap + widening).
        let mut b = FnBuilder::new(FnId(0), "loop");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let y = Var(99);
        let bb1 = b.block(vec![y]);
        b.set_terminator(entry, Term::Goto(bb1, vec![x]));
        // Self-cycle via Goto: bb1 -> bb1.
        b.set_terminator(bb1, Term::Goto(bb1, vec![y]));
        // Unreachable but parseable Halt elsewhere wouldn't trigger.
        let bb2 = b.block(vec![]);
        let z = b.let_(bb2, Prim::Const(Const::Int(0)));
        b.set_terminator(bb2, Term::Halt(z));
        let m = build_module(vec![b.build()]);
        // Should return without hanging.
        let _ = specialize_return(&m, FnId(0), &[Descr::int_lit(0)]);
        let _ = bb2;
    }

    // ---- .24.6 unreachable-arm diagnostics ----

    #[test]
    fn list_is_nil_on_int_var_flags_both_branches_unreachable() {
        // entry():
        //   five = 5
        //   c = ListIsNil(five)    -- predicate over an int -> both branches empty
        //   if c then then_b else else_b
        // then_b: halt five    -- env[five] narrowed to int_lit(5) ∩ nil = empty
        // else_b: halt five    -- env[five] narrowed to int_lit(5) ∩ list = empty
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let five = b.let_(entry, Prim::Const(Const::Int(5)));
        let c = b.let_(entry, Prim::ListIsNil(five));
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        b.set_terminator(entry, Term::If(c, then_b, else_b));
        b.set_terminator(then_b, Term::Halt(five));
        b.set_terminator(else_b, Term::Halt(five));
        let m = build_module(vec![b.build()]);
        let t = type_module(&m);
        let diags = collect_diagnostics(&m, &t);
        assert_eq!(diags.len(), 2, "expected two unreachable arms, got {:?}", diags);
        assert!(diags.iter().all(|d| d.code == crate::diag::codes::TYPE_UNREACHABLE_ARM));
    }

    #[test]
    fn happy_path_emits_no_warnings() {
        // entry(): halt 42  -- single-block, no narrowing, no warnings.
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let v = b.let_(entry, Prim::Const(Const::Int(42)));
        b.set_terminator(entry, Term::Halt(v));
        let m = build_module(vec![b.build()]);
        let t = type_module(&m);
        let diags = collect_diagnostics(&m, &t);
        assert!(diags.is_empty(), "expected no warnings, got {:?}", diags);
    }

    #[test]
    fn eq_then_eq_dup_clause_flags_second_arm_unreachable() {
        // entry(x):
        //   z = 0
        //   c1 = (x == z)
        //   if c1 then halt_b else next_check
        // next_check:
        //   z2 = 0
        //   c2 = (x == z2)        -- x's env in next_check = any \ int_lit(0)
        //   if c2 then dead_b else fallback
        // dead_b: this is the unreachable second "fn f(0)" clause.
        //         env[x] narrows to (any \ 0) ∩ 0 = empty.
        let mut b = FnBuilder::new(FnId(0), "f");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let z = b.let_(entry, Prim::Const(Const::Int(0)));
        let c1 = b.let_(entry, Prim::BinOp(BinOp::Eq, x, z));
        let halt_b = b.block(vec![]);
        let next_check = b.block(vec![]);
        b.set_terminator(entry, Term::If(c1, halt_b, next_check));
        b.set_terminator(halt_b, Term::Halt(x));
        let z2 = b.let_(next_check, Prim::Const(Const::Int(0)));
        let c2 = b.let_(next_check, Prim::BinOp(BinOp::Eq, x, z2));
        let dead_b = b.block(vec![]);
        let fallback = b.block(vec![]);
        b.set_terminator(next_check, Term::If(c2, dead_b, fallback));
        b.set_terminator(dead_b, Term::Halt(x));
        b.set_terminator(fallback, Term::Halt(x));

        let m = build_module(vec![b.build()]);
        let t = type_module(&m);
        let diags = collect_diagnostics(&m, &t);
        // The dead-block id is mentioned in the diagnostic's notes (post-
        // .20.5 the message is the headline; details live in notes).
        let needle = format!("bb{}", dead_b.0);
        assert!(
            diags.iter().any(|d| d.notes.iter().any(|n| n.contains(&needle))),
            "expected dead_b (bb{}) flagged, got {:?}", dead_b.0, diags
        );
    }

    // ---- .24.5 vec kind refinement ----

    #[test]
    fn rewrite_vec_kinds_keeps_int_vec_when_all_elems_int() {
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let two = b.let_(entry, Prim::Const(Const::Int(2)));
        let v = b.let_(entry, Prim::MakeVec(VecKindIr::I64, vec![one, two]));
        b.set_terminator(entry, Term::Return(v));
        let mut m = build_module(vec![b.build()]);
        let t = type_module(&m);
        rewrite_vec_kinds(&mut m, &t).expect("no error");
        let stmt = &m.fns[0].blocks[0].stmts[2];
        match stmt {
            crate::fz_ir::Stmt::Let(_, Prim::MakeVec(VecKindIr::I64, _)) => {}
            other => panic!("expected MakeVec(I64), got {:?}", other),
        }
    }

    #[test]
    fn rewrite_vec_kinds_promotes_to_f64_when_elem_typed_float() {
        // Build: f0 = const(1.0); v = MakeVec(I64, [f0])  -- intentionally I64 to test the rewrite.
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let f0 = b.let_(entry, Prim::Const(Const::Float(1.0)));
        let v = b.let_(entry, Prim::MakeVec(VecKindIr::I64, vec![f0]));
        b.set_terminator(entry, Term::Return(v));
        let mut m = build_module(vec![b.build()]);
        let t = type_module(&m);
        rewrite_vec_kinds(&mut m, &t).expect("no error");
        let stmt = &m.fns[0].blocks[0].stmts[1];
        match stmt {
            crate::fz_ir::Stmt::Let(_, Prim::MakeVec(VecKindIr::F64, _)) => {}
            other => panic!("expected MakeVec(F64) after rewrite, got {:?}", other),
        }
    }

    #[test]
    fn rewrite_vec_kinds_errors_on_mixed_int_and_float_elems() {
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let i0 = b.let_(entry, Prim::Const(Const::Int(1)));
        let f0 = b.let_(entry, Prim::Const(Const::Float(2.0)));
        let v = b.let_(entry, Prim::MakeVec(VecKindIr::I64, vec![i0, f0]));
        b.set_terminator(entry, Term::Return(v));
        let mut m = build_module(vec![b.build()]);
        let t = type_module(&m);
        let err = rewrite_vec_kinds(&mut m, &t).expect_err("expected mixed error");
        assert!(err.contains("11.24.5"), "expected ticket reference, got: {}", err);
    }

    #[test]
    fn map_get_with_singleton_key_returns_field_type() {
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let k = b.let_(entry, Prim::Const(Const::Atom(1)));
        let v = b.let_(entry, Prim::Const(Const::Int(42)));
        let mp = b.let_(entry, Prim::MakeMap(vec![(k, v)]));
        let got = b.let_(entry, Prim::MapGet(mp, k));
        b.set_terminator(entry, Term::Return(got));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let got_t = mt[0].vars.get(&got).cloned().unwrap();
        // The map_field_lookup contributes int_lit(42); plus the implicit "may be absent"
        // it can also be any|nil for open-shape semantics. We assert the int_lit(42)
        // is a subtype of the result.
        assert!(Descr::int_lit(42).is_subtype(&got_t),
            "map[k] should include the bound value: {}", got_t);
    }

    // ----- .20.8: type-rendered diagnostic prose -----

    /// The unreachable-arm diagnostic carries two notes: the type the
    /// variable had at the branch, and the type the narrowing demanded.
    /// Both are rendered through `Descr::display_for_diag`, so a user
    /// reading the diagnostic sees set-theoretic vocabulary the typer
    /// reasons in — not block ids and Var indices.
    #[test]
    fn unreachable_arm_diagnostic_includes_type_vocabulary() {
        // Same shape as eq_then_eq_dup_clause_flags_second_arm_unreachable:
        // a `fn f(0); fn f(0)` would dispatch the second clause unreachable.
        let mut b = FnBuilder::new(FnId(0), "f");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let z = b.let_(entry, Prim::Const(Const::Int(0)));
        let c1 = b.let_(entry, Prim::BinOp(BinOp::Eq, x, z));
        let halt_b = b.block(vec![]);
        let next_check = b.block(vec![]);
        b.set_terminator(entry, Term::If(c1, halt_b, next_check));
        b.set_terminator(halt_b, Term::Halt(x));
        let z2 = b.let_(next_check, Prim::Const(Const::Int(0)));
        let c2 = b.let_(next_check, Prim::BinOp(BinOp::Eq, x, z2));
        let dead_b = b.block(vec![]);
        let fallback = b.block(vec![]);
        b.set_terminator(next_check, Term::If(c2, dead_b, fallback));
        b.set_terminator(dead_b, Term::Halt(x));
        b.set_terminator(fallback, Term::Halt(x));

        let m = build_module(vec![b.build()]);
        let t = type_module(&m);
        let diags = collect_diagnostics(&m, &t);
        let d = diags.iter().next().expect("at least one diagnostic");
        // First note: "type `…`" — rendered set-theoretic vocab.
        let type_note = d.notes.iter().find(|n| n.contains("has type"))
            .expect("expected a 'has type' note");
        assert!(type_note.contains('`'),
            "type note should backtick-quote the rendered type, got {:?}", type_note);
        // Second note: the narrowing that's uninhabited.
        let narrow_note = d.notes.iter().find(|n| n.contains("uninhabited"))
            .expect("expected an 'uninhabited' note");
        assert!(narrow_note.contains("would need"),
            "narrow note should mention the would-need type, got {:?}", narrow_note);
    }

    // ---- fz-ul4.27.10: call-site arg narrowing into entry params ----

    #[test]
    fn entry_param_narrows_to_caller_arg_type() {
        // callee: fn id(x), do: return x
        let mut cb = FnBuilder::new(FnId(0), "id");
        let x = cb.fresh_var();
        let centry = cb.block(vec![x]);
        cb.set_terminator(centry, Term::Return(x));

        // caller: fn main, do: TailCall id(42)
        let mut mb = FnBuilder::new(FnId(1), "main");
        let mentry = mb.block(vec![]);
        let v = mb.let_(mentry, Prim::Const(Const::Int(42)));
        mb.set_terminator(mentry, Term::TailCall { callee: FnId(0), args: vec![v] });

        let m = build_module(vec![cb.build(), mb.build()]);
        let mt = type_module(&m);
        // `id`'s entry param x should narrow to int_lit(42).
        let xt = mt[0].vars.get(&x).cloned().unwrap();
        assert!(xt.is_equiv(&Descr::int_lit(42)),
            "x should narrow to int_lit(42), got {}", xt);
    }

    #[test]
    fn entry_param_unions_across_multiple_callers() {
        // callee: fn id(x), do: return x
        let mut cb = FnBuilder::new(FnId(0), "id");
        let x = cb.fresh_var();
        let centry = cb.block(vec![x]);
        cb.set_terminator(centry, Term::Return(x));

        // caller1: TailCall id(1)
        let mut a = FnBuilder::new(FnId(1), "a");
        let aentry = a.block(vec![]);
        let one = a.let_(aentry, Prim::Const(Const::Int(1)));
        a.set_terminator(aentry, Term::TailCall { callee: FnId(0), args: vec![one] });

        // caller2: TailCall id(:atom7)
        let mut bb = FnBuilder::new(FnId(2), "b");
        let bentry = bb.block(vec![]);
        let ok = bb.let_(bentry, Prim::Const(Const::Atom(7)));
        bb.set_terminator(bentry, Term::TailCall { callee: FnId(0), args: vec![ok] });

        let m = build_module(vec![cb.build(), a.build(), bb.build()]);
        let mt = type_module(&m);
        let xt = mt[0].vars.get(&x).cloned().unwrap();
        // x should accept both int_lit(1) and the atom — the union.
        assert!(Descr::int_lit(1).is_subtype(&xt),
            "x should accept int_lit(1), got {}", xt);
        // Cross-axis: the atom side should be present too. Probe via
        // intersection — the int axis alone should NOT cover all of xt.
        assert!(!xt.is_subtype(&Descr::int()),
            "x should also include atom side, got {}", xt);
    }

    #[test]
    fn closure_target_with_no_direct_callers_keeps_any_entry_params() {
        // fn worker(n), do: return n — packed into a closure by main but
        // never reached via a direct Term::Call/TailCall. With no visible
        // direct caller, the lub view (by_fn_idx) leaves the entry param
        // at the initial all-any. The any-key spec in `specs` (which is
        // what closure-invoke dispatches into) is also `any` — same view.
        //
        // fz-ul4.29.3 removed the typer's old `closure_reachable` skip;
        // for closure targets that DO have direct callers, by_fn_idx now
        // gets narrowed by the visible callers (a different test would
        // exercise that), while the any-key spec remains all-any.
        let mut wb = FnBuilder::new(FnId(0), "worker");
        let n = wb.fresh_var();
        let wentry = wb.block(vec![n]);
        wb.set_terminator(wentry, Term::Return(n));

        let mut mb = FnBuilder::new(FnId(1), "main");
        let mentry = mb.block(vec![]);
        let cl = mb.let_(mentry, Prim::MakeClosure(FnId(0), vec![]));
        mb.set_terminator(mentry, Term::Halt(cl));

        let m = build_module(vec![wb.build(), mb.build()]);
        let mt = type_module(&m);
        let nt = mt[0].vars.get(&n).cloned().unwrap();
        assert!(nt.is_equiv(&Descr::any()),
            "worker's n must stay at any (no direct callers), got {}", nt);
    }

    #[test]
    fn closure_target_with_direct_caller_narrows_by_fn_idx_but_any_key_stays_any() {
        // fz-ul4.29.3 regression guard: a fn that's BOTH a closure target
        // AND called directly with a typed arg gets its by_fn_idx narrowed
        // by the visible direct caller; the any-key spec (what the closure
        // path dispatches into) remains all-any.
        let mut wb = FnBuilder::new(FnId(0), "worker");
        let n = wb.fresh_var();
        let wentry = wb.block(vec![n]);
        wb.set_terminator(wentry, Term::Return(n));

        let mut mb = FnBuilder::new(FnId(1), "main");
        let mentry = mb.block(vec![]);
        let _cl = mb.let_(mentry, Prim::MakeClosure(FnId(0), vec![]));
        let lit = mb.let_(mentry, Prim::Const(Const::Int(42)));
        mb.set_terminator(mentry, Term::TailCall { callee: FnId(0), args: vec![lit] });

        let m = build_module(vec![wb.build(), mb.build()]);
        let mt = type_module(&m);
        // by_fn_idx for worker: n narrowed to the direct caller's int.
        let nt = mt[0].vars.get(&n).cloned().unwrap();
        assert!(nt.is_subtype(&Descr::int()),
            "worker's n in by_fn_idx must narrow to int (visible caller), got {}", nt);
        // any-key spec stays at all-any (closure-invoke fallback).
        let any_spec = mt.spec(FnId(0), &[Descr::any()])
            .expect("any-key spec exists");
        let any_n = any_spec.vars.get(&n).cloned().unwrap();
        assert!(any_n.is_equiv(&Descr::any()),
            "worker's any-key spec keeps n at any, got {}", any_n);
    }

    // ----- fz-ul4.29.1: per-callsite specialization map -----

    #[test]
    fn specs_contains_any_key_for_every_fn() {
        // Build a 2-fn module: main() calls add1(int_lit(41)).
        let mut a = FnBuilder::new(FnId(0), "add1");
        let n = a.fresh_var();
        let aentry = a.block(vec![n]);
        let one = a.let_(aentry, Prim::Const(Const::Int(1)));
        let sum = a.let_(aentry, Prim::BinOp(BinOp::Add, n, one));
        a.set_terminator(aentry, Term::Return(sum));

        let mut b = FnBuilder::new(FnId(1), "main");
        let bentry = b.block(vec![]);
        let lit = b.let_(bentry, Prim::Const(Const::Int(41)));
        b.set_terminator(bentry, Term::TailCall { callee: FnId(0), args: vec![lit] });

        let m = build_module(vec![a.build(), b.build()]);
        let mt = type_module(&m);

        // Every fn has an any-key spec (fallback for closure/Spawn/Receive).
        let add1_any = mt.spec(FnId(0), &[Descr::any()]);
        assert!(add1_any.is_some(), "add1 must have an any-key specialization");
        let main_any = mt.spec(FnId(1), &[]);
        assert!(main_any.is_some(), "main must have an any-key specialization");
    }

    #[test]
    fn specs_records_narrow_int_callsite() {
        // main calls add1 with an int literal → expect a specialization
        // keyed on `[int]` (not just `[any]`).
        let mut a = FnBuilder::new(FnId(0), "add1");
        let n = a.fresh_var();
        let aentry = a.block(vec![n]);
        let one = a.let_(aentry, Prim::Const(Const::Int(1)));
        let sum = a.let_(aentry, Prim::BinOp(BinOp::Add, n, one));
        a.set_terminator(aentry, Term::Return(sum));

        let mut b = FnBuilder::new(FnId(1), "main");
        let bentry = b.block(vec![]);
        let lit = b.let_(bentry, Prim::Const(Const::Int(41)));
        b.set_terminator(bentry, Term::TailCall { callee: FnId(0), args: vec![lit] });

        let m = build_module(vec![a.build(), b.build()]);
        let mt = type_module(&m);

        // The callsite passes `int_lit(41)`, which is a subtype of int. The
        // spec key carries exactly that Descr.
        let int41 = Descr::int_lit(41);
        let narrow = mt.spec(FnId(0), &[int41.clone()]);
        assert!(
            narrow.is_some(),
            "add1 must have a specialization keyed on [int_lit(41)]; \
             specs keys present: {:?}",
            mt.specs.keys().filter(|(fid, _)| *fid == FnId(0)).count()
        );
        // The narrowed specialization's `n` should reflect the callsite Descr.
        let nt = narrow.unwrap().vars.get(&n).cloned().unwrap();
        assert!(nt.is_equiv(&int41),
            "add1's narrow spec must type n as int_lit(41), got {}", nt);
    }

    #[test]
    fn module_types_index_preserves_legacy_view() {
        // The Index<usize> impl returns the lub-aggregated `by_fn_idx`
        // entry — same shape consumers have always seen.
        let mut a = FnBuilder::new(FnId(0), "id");
        let x = a.fresh_var();
        let aentry = a.block(vec![x]);
        a.set_terminator(aentry, Term::Return(x));

        let mut b = FnBuilder::new(FnId(1), "main");
        let bentry = b.block(vec![]);
        let lit = b.let_(bentry, Prim::Const(Const::Int(7)));
        b.set_terminator(bentry, Term::TailCall { callee: FnId(0), args: vec![lit] });

        let m = build_module(vec![a.build(), b.build()]);
        let mt = type_module(&m);

        assert_eq!(mt.len(), 2);
        // Legacy view: index 0 → id's narrowed FnTypes.
        let id_x = mt[0].vars.get(&x).cloned().unwrap();
        assert!(id_x.is_subtype(&Descr::int()),
            "id's x must be narrowed to int via callsite, got {}", id_x);
    }

    // ---- fz-ul4.29.12.1 helper tests ----

    fn pipeline(src: &str) -> (Module, ModuleTypes) {
        let toks = crate::lexer::Lexer::new(src).tokenize().expect("lex");
        let prog = crate::parser::Parser::new(toks).parse_program().expect("parse");
        let prog = crate::resolve::flatten_modules(prog).expect("flatten");
        let ir = crate::ir_lower::lower_program(&prog).expect("lower");
        let mt = type_module(&ir);
        (ir, mt)
    }

    /// Helper output for a Call-site Cont must match a key the typer
    /// registered in `module_types.specs` under `cont.fn_id`. This is
    /// the load-bearing invariant for fz-ul4.29.12.1's SpecRegistry
    /// resolve: if it ever fails, the resolve will panic.
    #[test]
    fn cont_input_key_matches_a_registered_spec_for_call() {
        let (m, mt) = pipeline(r#"
fn id(x), do: x
fn main() do
  y = id(7)
  print(y)
end
"#);
        // Find the main fn, locate the Call site, and check the
        // helper's output appears in `mt.specs` for the cont's fn_id.
        let main = m.fns.iter().find(|f| f.name == "main").unwrap();
        let caller_ft = mt.specs.get(&(main.id, vec![])).unwrap();
        let mut found_any = false;
        for blk in &main.blocks {
            if let Term::Call { continuation, .. } = &blk.terminator {
                let key = cont_input_key(blk, continuation, caller_ft, &m, &mt);
                assert!(
                    mt.specs.contains_key(&(continuation.fn_id, key.clone())),
                    "helper key {:?} for cont fn_id {:?} not in specs; \
                     registered keys for this cont: {:?}",
                    key,
                    continuation.fn_id,
                    mt.specs.iter()
                        .filter(|((f, _), _)| *f == continuation.fn_id)
                        .map(|((_, k), _)| k.clone())
                        .collect::<Vec<_>>(),
                );
                found_any = true;
            }
        }
        assert!(found_any, "test premise: main should contain a Call with a Cont");
    }

    /// Direct-Call slot 0 reflects the callee's narrowed return Descr,
    /// not `any` — confirms .29.12.1 actually drives narrow Cont SpecId
    /// resolution at call-sites where the typer has specialized the
    /// callee.
    #[test]
    fn cont_slot0_narrows_to_callee_return_for_direct_call() {
        let (m, mt) = pipeline(r#"
fn add1(n), do: n + 1
fn main(), do: print(add1(40) + 2)
"#);
        let main = m.fns.iter().find(|f| f.name == "main").unwrap();
        let main_ft = mt.specs.get(&(main.id, vec![])).unwrap();
        let mut narrow_found = false;
        for blk in &main.blocks {
            if let Term::Call { .. } = &blk.terminator {
                let s0 = cont_slot0_descr(blk, main_ft, &m, &mt);
                // add1's typer-specialized return for arg int_lit(40) is
                // a strict subtype of `int` — and crucially narrower than
                // `any`.
                assert!(!s0.is_equiv(&Descr::any()),
                    "slot 0 must narrow below any when callee is specialized, got {}", s0);
                assert!(s0.is_subtype(&Descr::int()),
                    "slot 0 should be int-typed, got {}", s0);
                narrow_found = true;
            }
        }
        assert!(narrow_found, "test premise: main should have a direct Call");
    }

    /// Helper's slot 0 for CallClosure / Receive is `Descr::any()` per
    /// the typer's opaque-callee rule.
    #[test]
    fn cont_slot0_is_any_for_call_closure() {
        let (m, mt) = pipeline(r#"
fn apply(f, x) do
  r = f(x)
  r + 1
end
fn main() do
  inc = fn (n) -> n + 1
  z = apply(inc, 3)
  print(z)
end
"#);
        let apply_fn = m.fns.iter().find(|f| f.name == "apply").unwrap();
        let caller_ft = mt.specs.iter()
            .find(|((id, _), _)| *id == apply_fn.id)
            .map(|((_, _), ft)| ft)
            .expect("apply should have at least one spec");
        let mut saw_cc = false;
        for blk in &apply_fn.blocks {
            if matches!(&blk.terminator, Term::CallClosure { .. }) {
                let s0 = cont_slot0_descr(blk, caller_ft, &m, &mt);
                assert!(s0.is_equiv(&Descr::any()),
                    "CallClosure slot 0 must be `any`, got {}", s0);
                saw_cc = true;
            }
        }
        assert!(saw_cc, "test premise: apply should have a CallClosure");
    }
}
