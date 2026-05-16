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
use std::collections::{HashMap, HashSet};

// ============================================================================
// fz-210 — Call-graph + Tarjan SCC for bottom-up spec discovery.
// ============================================================================

/// Build the static call graph for the module under the supplied any-key
/// specs (bootstrap). Edges captured:
///   - direct Term::Call / Term::TailCall callee
///   - continuation fn_id from Term::Call / Term::CallClosure / Term::Receive
///   - Prim::MakeClosure(fn_id, ...) target lambda
///   - fn_constants-resolved Term::CallClosure / TailCallClosure target
///
/// Edges skipped: Term::Return / Term::Halt (dynamic dispatch, no static
/// edge), unknown CallClosure (any-key spec is the fallback).
fn build_call_graph(
    m: &Module,
    specs: &HashMap<(FnId, Vec<Descr>), FnTypes>,
) -> HashMap<FnId, HashSet<FnId>> {
    let mut g: HashMap<FnId, HashSet<FnId>> = HashMap::new();
    for f in &m.fns {
        g.entry(f.id).or_default();
    }
    for f in &m.fns {
        let n = f.block(f.entry).params.len();
        let any_key = vec![Descr::any(); n];
        let Some(ft) = specs.get(&(f.id, any_key)) else {
            continue;
        };
        let edges = g.entry(f.id).or_default();
        for b in &f.blocks {
            for stmt in &b.stmts {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeClosure(lam_fn_id, _) = prim {
                    edges.insert(*lam_fn_id);
                }
            }
            match &b.terminator {
                Term::Call {
                    callee,
                    continuation,
                    ..
                } => {
                    edges.insert(*callee);
                    edges.insert(continuation.fn_id);
                }
                Term::TailCall { callee, .. } => {
                    edges.insert(*callee);
                }
                Term::CallClosure {
                    closure,
                    continuation,
                    ..
                } => {
                    if let Some(&target) = ft.fn_constants.get(closure) {
                        edges.insert(target);
                    }
                    edges.insert(continuation.fn_id);
                }
                Term::TailCallClosure { closure, .. } => {
                    if let Some(&target) = ft.fn_constants.get(closure) {
                        edges.insert(target);
                    }
                }
                Term::Receive { continuation } => {
                    edges.insert(continuation.fn_id);
                }
                _ => {}
            }
        }
    }
    g
}

/// Tarjan strongly-connected components. Returns SCCs in
/// reverse-topological order (leaves first) — caller reverses for
/// caller-first processing.
fn tarjan_scc(graph: &HashMap<FnId, HashSet<FnId>>) -> Vec<Vec<FnId>> {
    struct State<'a> {
        graph: &'a HashMap<FnId, HashSet<FnId>>,
        index_of: HashMap<FnId, u32>,
        lowlink: HashMap<FnId, u32>,
        on_stack: HashSet<FnId>,
        stack: Vec<FnId>,
        next_idx: u32,
        sccs: Vec<Vec<FnId>>,
    }
    fn strong(s: &mut State, v: FnId) {
        s.index_of.insert(v, s.next_idx);
        s.lowlink.insert(v, s.next_idx);
        s.next_idx += 1;
        s.stack.push(v);
        s.on_stack.insert(v);
        if let Some(succs) = s.graph.get(&v) {
            let succs: Vec<FnId> = succs.iter().copied().collect();
            for w in succs {
                if !s.index_of.contains_key(&w) {
                    strong(s, w);
                    let wl = *s.lowlink.get(&w).unwrap();
                    let vl = *s.lowlink.get(&v).unwrap();
                    s.lowlink.insert(v, vl.min(wl));
                } else if s.on_stack.contains(&w) {
                    let wi = *s.index_of.get(&w).unwrap();
                    let vl = *s.lowlink.get(&v).unwrap();
                    s.lowlink.insert(v, vl.min(wi));
                }
            }
        }
        if s.index_of.get(&v) == s.lowlink.get(&v) {
            let mut comp = Vec::new();
            loop {
                let w = s.stack.pop().unwrap();
                s.on_stack.remove(&w);
                comp.push(w);
                if w == v {
                    break;
                }
            }
            s.sccs.push(comp);
        }
    }
    let mut s = State {
        graph,
        index_of: HashMap::new(),
        lowlink: HashMap::new(),
        on_stack: HashSet::new(),
        stack: Vec::new(),
        next_idx: 0,
        sccs: Vec::new(),
    };
    // Stable iteration order so SCC numbering is deterministic across runs.
    let mut nodes: Vec<FnId> = graph.keys().copied().collect();
    nodes.sort_by_key(|f| f.0);
    for v in nodes {
        if !s.index_of.contains_key(&v) {
            strong(&mut s, v);
        }
    }
    s.sccs
}

#[derive(Debug, Clone, Default)]
pub struct FnTypes {
    /// Definition-site type for each Var. Block params get the join of their
    /// predecessor args; Let-bound vars get their Prim's type under the env
    /// at that point in the block.
    pub vars: HashMap<Var, Descr>,
    /// Entry env per block, with branch narrowing applied at If terminators.
    pub block_envs: HashMap<BlockId, HashMap<Var, Descr>>,
    /// fz-ul4.29.10.1 — side-channel: vars known to hold a specific
    /// top-level fn identity (zero-capture `MakeClosure(F, [])` only).
    /// Used by `.29.10.2`/`.3` to register narrow specs and rewrite
    /// known-target `CallClosure → Call`. `Descr` deliberately carries
    /// no FnId identity; this map lives alongside it.
    pub fn_constants: HashMap<Var, FnId>,
    /// Blocks provably reachable from the entry under the inferred types.
    /// If terminators whose condition is a singleton bool prune the dead
    /// branch. Used by `compute_effective_returns` to ignore returns that
    /// can never execute.
    pub reachable_blocks: HashSet<BlockId>,
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
    pub specs: HashMap<(FnId, Vec<Descr>), FnTypes>,
    /// fz-2yw.2 — Kleene LFP of every spec's effective return Descr.
    /// Populated once at the end of `type_module` via
    /// `compute_effective_returns`. Consumers (cont_slot0_descr,
    /// pretty_module_types, walker slot0_descr) read here instead of
    /// recursing on demand.
    pub effective_returns: HashMap<(FnId, Vec<Descr>), Descr>,
    /// fz-afs.12 — secondary index: FnId → all-any key for that fn.
    /// Populated in `type_module` from the final specs map. Enables O(1)
    /// any-key lookup without the per-element is_equiv scan.
    pub any_key_specs: HashMap<FnId, Vec<Descr>>,
    /// fz-02r.4 — SCC index for back-edge detection. Two FnIds share a
    /// back-edge (i.e., the call is on a loop) iff `scc_of[a] == scc_of[b]`.
    /// Self-recursion maps a fn to its own SCC (singleton). Populated at the
    /// start of `type_module` from the initial Tarjan run; stable thereafter.
    #[allow(dead_code)] // consumed by ir_codegen back-edge check (fz-02r.5)
    pub scc_of: HashMap<FnId, usize>,
}

impl ModuleTypes {
    /// Look up a specific specialization. Returns `None` if no callsite
    /// has requested this exact input-Descr-tuple.
    #[allow(dead_code)]
    pub fn spec(&self, fn_id: FnId, input_descrs: &[Descr]) -> Option<&FnTypes> {
        self.specs.get(&(fn_id, input_descrs.to_vec()))
    }

    /// fz-pky.2 — return the any-key spec for `fn_id` if registered.
    /// Under the reachability-driven model (fz-vw4), the any-key only
    /// exists when the fn is closure-reachable, entry-seeded, or
    /// genuinely needs the opaque-dispatch fallback. Direct-call-only
    /// fns have no any-key.
    #[allow(dead_code)]
    pub fn any_key_spec(&self, fn_id: FnId) -> Option<&FnTypes> {
        let key = self.any_key_specs.get(&fn_id)?;
        self.specs.get(&(fn_id, key.clone()))
    }

    /// fz-pky.2 — return any registered spec for `fn_id` (for callers
    /// that just need "the typer's view of this fn under some
    /// reachable callsite"). Prefers the any-key spec when available;
    /// falls back to a deterministic linear scan over remaining specs.
    #[allow(dead_code)]
    pub fn any_spec_for(&self, fn_id: FnId) -> Option<&FnTypes> {
        if let Some(ft) = self.any_key_spec(fn_id) {
            return Some(ft);
        }
        // No any-key: pick the spec whose key Display-string is smallest.
        let mut best: Option<(String, &FnTypes)> = None;
        for ((fid, key), ft) in &self.specs {
            if *fid != fn_id {
                continue;
            }
            let ks: String = key
                .iter()
                .map(|d| format!("{}", d))
                .collect::<Vec<_>>()
                .join(",");
            match &best {
                None => best = Some((ks, ft)),
                Some((bk, _)) if &ks < bk => best = Some((ks, ft)),
                _ => {}
            }
        }
        best.map(|(_, ft)| ft)
    }
}

/// fz-ul4.27.22.9 — closure-aware return resolution. Given a closure
/// Var's `Descr` and the actual `arg_descrs` at a call site, compute the
/// joined return Descr.
///
/// For each positive arrow clause in `closure_descr.funcs`:
///   - If the clause carries a `ClosureLit { fn_id, captures }`, build the
///     full body key `[captures..., arg_descrs...]` and look up
///     `effective_returns[(fn_id, full_key)]`. JOIN into the accumulator.
///   - Otherwise, JOIN `sig.ret` (the existing `arrow_join_return` path).
///
/// Returns `None` when a lit-tagged clause's spec has not yet been
/// registered — caller treats this as a fixpoint deferral (same convention
/// as `cont_slot0_descr` today). Returns `Some(Descr::any())` for
/// pathological inputs (empty funcs, negated arrows, saturated `Conj::top`
/// pos clauses) — those convey no narrowing information so the broadest
/// result is sound.
///
/// `arg_descrs` length must match the closure's apparent arity for lit
/// clauses; mismatch falls back to `Descr::any()` for that clause.
#[allow(dead_code)] // Wired into cont_slot0_descr / codegen in fz-ul4.27.22.10/11.
pub fn resolve_closure_return(
    closure_descr: &Descr,
    effective_returns: &HashMap<(FnId, Vec<Descr>), Descr>,
    arg_descrs: &[Descr],
) -> Option<Descr> {
    if closure_descr.funcs.is_empty() {
        return Some(Descr::any());
    }
    let mut acc = Descr::none();
    for c in &closure_descr.funcs {
        if !c.neg.is_empty() || c.pos.is_empty() {
            return Some(Descr::any());
        }
        for sig in &c.pos {
            match &sig.lit {
                None => acc = acc.union(&sig.ret),
                Some(lit) => {
                    if sig.args.len() != arg_descrs.len() {
                        // Arity mismatch (shouldn't happen if MakeClosure
                        // typing is consistent); fall back broad rather
                        // than miss-look-up.
                        return Some(Descr::any());
                    }
                    let mut full_key: Vec<Descr> = lit.captures.clone();
                    full_key.extend_from_slice(arg_descrs);
                    match effective_returns.get(&(lit.fn_id, full_key)) {
                        Some(r) => acc = acc.union(r),
                        None => return None, // defer to next fixpoint iter
                    }
                }
            }
        }
    }
    Some(acc)
}

/// Type a whole module. Iterates type_fn to a fixed point, propagating
/// call-site arg Descrs into callee entry-param Descrs after each pass.
/// fz-ul4.27.10: replaces the previous one-shot `map`. Fns with no direct
/// caller (main, closure-only targets) keep entry params at `any`.
/// fz-vw4 step 1 — explicit reachability roots for the spec set.
///
/// Today only `main` is invoked from Rust without an IR caller
/// (`Runtime::spawn(main_fn)` in main.rs). Other fns become reachable
/// by IR-level discovery: direct callsites, MakeClosure / Spawn (via
/// the lambda's any-key), and Receive cont sites.
///
/// Wired in alongside the existing unconditional bootstrap; step 2
/// replaces the bootstrap with these seeds alone.
fn entry_seeds(m: &Module) -> Vec<(FnId, Vec<Descr>)> {
    let mut seeds = Vec::new();
    if let Some(main) = m.fns.iter().find(|f| f.name == "main") {
        let n_params = main.block(main.entry).params.len();
        seeds.push((main.id, vec![Descr::any(); n_params]));
    }
    seeds
}

/// fz-vw4.5a — scan converged specs for unresolved closure dispatch.
///
/// At every `Term::CallClosure { closure, args, .. }` and
/// `Term::TailCallClosure { closure, args }` site in every registered
/// spec's body, check whether the spec's `fn_constants` resolves
/// `closure` to a specific FnId. Sites that DON'T resolve are
/// "opaque consumers" — at runtime they dispatch to whichever lambda
/// is encoded in the closure value, which we cannot pin down
/// statically. This function returns the set of `n_params` arities
/// reachable via such opaque dispatch.
///
/// A lambda `F` with `n_params(F) == captures + opaque_arity`
/// could land at any opaque consumer whose `args.len() == opaque_arity`.
/// step 5c uses this to gate MakeClosure-side any-key registration:
/// closure targets with no opaque consumer never need the defensive
/// `(F, [captures..., any...])` spec.
#[allow(dead_code)] // step 5b/c consume; lint quiets when wired in.
fn opaque_consumer_arities(
    m: &Module,
    specs: &HashMap<(FnId, Vec<Descr>), FnTypes>,
) -> std::collections::HashSet<usize> {
    let mut arities = std::collections::HashSet::new();
    for ((fid, _key), ft) in specs {
        let Some(&i) = m.fn_idx.get(fid) else {
            continue;
        };
        let f = &m.fns[i];
        for b in &f.blocks {
            // Terminator-level opaque dispatch.
            let (closure_var, args): (Option<Var>, &[Var]) = match &b.terminator {
                Term::CallClosure { closure, args, .. }
                | Term::TailCallClosure { closure, args } => (Some(*closure), args.as_slice()),
                _ => (None, &[]),
            };
            if let Some(cv) = closure_var
                && !ft.fn_constants.contains_key(&cv)
            {
                // fz-1pq.5 — skip closures whose type is fully resolvable
                // via closure_lit (path b in walk_spec_for_discovery).
                // Those callers register narrow specs; the MakeClosure sweep's
                // any-arg spec is redundant for them.
                let fully_lit = ft.vars.get(&cv).is_some_and(|d| {
                    !d.funcs.is_empty()
                        && d.funcs.iter().all(|c| {
                            c.neg.is_empty()
                                && !c.pos.is_empty()
                                && c.pos.iter().all(|s| s.lit.is_some())
                        })
                });
                if !fully_lit {
                    arities.insert(args.len());
                }
            }
            // Stmt-level opaque dispatch: spawn calls hand the closure to
            // the runtime, which invokes it with zero args. Track as
            // arity-0 opaque dispatch keyed off the closure operand's
            // fn_constants.
            //
            // fz-ext.7: spawn now emits Prim::Extern(fz_spawn/fz_spawn_opt)
            // instead of Prim::Builtin(Spawn). Both forms are checked here.
            for stmt in &b.stmts {
                let Stmt::Let(_, prim) = stmt;
                let spawn_cv: Option<Var> = match prim {
                    Prim::Builtin(bid, args)
                        if *bid == BuiltinKind::Spawn.id()
                            && (args.len() == 1 || args.len() == 2) =>
                    {
                        Some(args[0])
                    }
                    Prim::Extern(eid, args)
                        if (args.len() == 1 || args.len() == 2)
                            && m.externs
                                .get(eid.0 as usize)
                                .map(|d| d.symbol == "fz_spawn" || d.symbol == "fz_spawn_opt")
                                .unwrap_or(false) =>
                    {
                        Some(args[0])
                    }
                    _ => None,
                };
                if let Some(cv) = spawn_cv
                    && !ft.fn_constants.contains_key(&cv)
                {
                    arities.insert(0);
                }
            }
        }
    }
    arities
}

fn build_any_key_index(specs: &HashMap<(FnId, Vec<Descr>), FnTypes>) -> HashMap<FnId, Vec<Descr>> {
    let mut idx: HashMap<FnId, Vec<Descr>> = HashMap::new();
    for (fid, key) in specs.keys() {
        if key.iter().all(|d| d.is_equiv(&Descr::any())) {
            idx.entry(*fid).or_insert_with(|| key.clone());
        }
    }
    idx
}

pub fn type_module(m: &Module) -> ModuleTypes {
    // fz-02r.4 — compute SCC once from the structural call graph. The call
    // graph structure is fixed (the module doesn't change during typing), so
    // we compute it here with an empty specs map — the same starting point
    // type_module_pass uses. Exposed via ModuleTypes.scc_of for ir_lower to
    // annotate Term::TailCall with is_back_edge.
    let initial_specs: HashMap<(FnId, Vec<Descr>), FnTypes> = HashMap::new();
    let call_graph = build_call_graph(m, &initial_specs);
    let mut sccs = tarjan_scc(&call_graph);
    sccs.reverse(); // caller-first (matches type_module_pass ordering)
    let mut scc_of: HashMap<FnId, usize> = HashMap::new();
    for (i, scc) in sccs.iter().enumerate() {
        for fid in scc {
            scc_of.insert(*fid, i);
        }
    }

    // fz-3zx — outer fixpoint over (specs, effective_returns).
    // Each pass rebuilds `specs` from scratch using `prev_returns` as
    // the slot-0 source for cont-key construction. After each pass we
    // compute the LFP; convergence is reached when the LFP equals the
    // input. Per fz-8ki the LFP itself is honest about "unknown" vs
    // "none," so the walker can DEFER cont pushes on missing entries
    // instead of falling back to Descr::any (which would lock in
    // spurious widening — e.g. sum's k_2 to `int | float`).
    let mut prev_returns: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
    for _ in 0..16 {
        let specs = type_module_pass(m, &prev_returns);
        let effective_returns = compute_effective_returns(m, &specs, &prev_returns);
        if effective_returns == prev_returns {
            let any_key_specs = build_any_key_index(&specs);
            return ModuleTypes {
                specs,
                effective_returns,
                any_key_specs,
                scc_of,
            };
        }
        prev_returns = effective_returns;
    }
    // Safety bound — return last computed state. The 16-iter cap is a
    // belt-and-braces guard; in practice convergence is 2-3 iters on
    // every fixture we've seen.
    let specs = type_module_pass(m, &prev_returns);
    let effective_returns = compute_effective_returns(m, &specs, &prev_returns);
    let any_key_specs = build_any_key_index(&specs);
    ModuleTypes {
        specs,
        effective_returns,
        any_key_specs,
        scc_of,
    }
}

/// Drain every pending key into `specs`. For each key not already
/// present, call `type_fn`, apply accumulated `callsite_fn_consts`,
/// and insert the resulting `FnTypes`. Returns the newly-registered
/// `(FnId, key)` pairs — specs that did not exist before this call.
/// An empty return means nothing new was registered (pending was
/// already empty or all drained keys were already in specs).
fn drain_and_register(
    pending: &mut HashMap<FnId, std::collections::HashSet<Vec<Descr>>>,
    specs: &mut HashMap<(FnId, Vec<Descr>), FnTypes>,
    m: &Module,
    callsite_fn_consts: &mut HashMap<(FnId, Vec<Descr>), Vec<Option<FnId>>>,
) -> Vec<(FnId, Vec<Descr>)> {
    let to_process: Vec<(FnId, Vec<Descr>)> = pending
        .iter_mut()
        .flat_map(|(fid, keys)| {
            let v: Vec<Vec<Descr>> = keys.drain().collect();
            v.into_iter().map(move |k| (*fid, k))
        })
        .collect();
    let mut newly_registered = Vec::new();
    for (fid, key) in to_process {
        let Some(&j) = m.fn_idx.get(&fid) else {
            continue;
        };
        let entry_key = (fid, key.clone());
        if !specs.contains_key(&entry_key) {
            let mut ft = type_fn(&m.fns[j], m, Some(&key));
            if let Some(arg_consts) = callsite_fn_consts.get(&entry_key) {
                let entry = m.fns[j].entry;
                let entry_params = &m.fns[j].block(entry).params;
                for (slot, p) in entry_params.iter().enumerate() {
                    if let Some(Some(fid_const)) = arg_consts.get(slot) {
                        ft.fn_constants.insert(*p, *fid_const);
                    }
                }
            }
            specs.insert(entry_key.clone(), ft);
            newly_registered.push(entry_key);
        }
    }
    newly_registered
}

fn type_module_pass(
    m: &Module,
    prev_returns: &HashMap<(FnId, Vec<Descr>), Descr>,
) -> HashMap<(FnId, Vec<Descr>), FnTypes> {
    // fz-vw4.2: per-callsite specialization map. Specs are inserted only
    // when a real reachability seed (entry_seeds) or a discovered callsite
    // demands them. No phantom any-key bootstrap; orphan any-key bodies
    // can't spawn polluting narrow specs because they're never typed.
    let mut specs: HashMap<(FnId, Vec<Descr>), FnTypes> = HashMap::new();

    // fz-210 — bottom-up SCC-driven spec discovery. Replaces the
    // capped global fixpoint with caller-first per-SCC processing.
    // Build call graph from bootstrap any-key specs, Tarjan SCC, then
    // for each SCC in caller-first topological order run a local
    // fixpoint with widening at iter >= WIDEN_AT for SCC-internal keys.
    let call_graph = build_call_graph(m, &specs);
    let mut sccs = tarjan_scc(&call_graph);
    sccs.reverse(); // caller-first
    let mut scc_of: HashMap<FnId, usize> = HashMap::new();
    for (i, scc) in sccs.iter().enumerate() {
        for fid in scc {
            scc_of.insert(*fid, i);
        }
    }

    // fz-vw4.2: pending is seeded ONLY from entry_seeds (reachability
    // roots). Every other spec is discovered by walking already-registered
    // spec bodies — direct callsites, fn_constants-resolved
    // CallClosure/TailCallClosure, MakeClosure (closure-target any-keys),
    // and Receive cont sites.
    let mut pending: HashMap<FnId, std::collections::HashSet<Vec<Descr>>> = HashMap::new();
    for (fid, key) in entry_seeds(m) {
        pending.entry(fid).or_default().insert(key);
    }
    // Callsite fn-constants accumulated across walks (unified across
    // multiple callsites sharing the same (callee, key)).
    let mut callsite_fn_consts: HashMap<(FnId, Vec<Descr>), Vec<Option<FnId>>> = HashMap::new();
    // LUB-narrowed entry-param Descrs per fn — built up across all
    // direct callsites for the legacy by_fn_idx view.

    const WIDEN_AT: usize = 3;
    for scc in sccs.iter() {
        let scc_set: std::collections::HashSet<FnId> = scc.iter().copied().collect();
        for iter in 0.. {
            // Snapshot pending keys for fns IN this SCC and drain.
            let mut to_process: Vec<(FnId, Vec<Descr>)> = Vec::new();
            for fid in scc.iter() {
                if let Some(keys) = pending.get_mut(fid) {
                    for k in keys.drain() {
                        to_process.push((*fid, k));
                    }
                }
            }
            if to_process.is_empty() {
                break;
            }
            // Process each (fn, key) — register spec if new, walk body,
            // emit pending entries for discovered callsite keys.
            for (fid, key) in to_process {
                let Some(&j) = m.fn_idx.get(&fid) else {
                    continue;
                };
                let entry_key = (fid, key.clone());
                if !specs.contains_key(&entry_key) {
                    let mut ft = type_fn(&m.fns[j], m, Some(&key));
                    if let Some(arg_consts) = callsite_fn_consts.get(&entry_key) {
                        let entry = m.fns[j].entry;
                        let entry_params = &m.fns[j].block(entry).params;
                        for (slot, p) in entry_params.iter().enumerate() {
                            if let Some(Some(fid_const)) = arg_consts.get(slot) {
                                ft.fn_constants.insert(*p, *fid_const);
                            }
                        }
                    }
                    specs.insert(entry_key.clone(), ft);
                }
                // Walk this spec's body for discovery. Use a snapshot
                // borrow so we can mutate `specs` / `pending` inside.
                let caller_ft = specs.get(&entry_key).unwrap();
                walk_spec_for_discovery(
                    &m.fns[j],
                    caller_ft,
                    m,
                    &specs,
                    prev_returns,
                    &scc_set,
                    iter >= WIDEN_AT,
                    &mut pending,
                    &mut callsite_fn_consts,
                );
            }
        }
    }
    let _ = scc_of;
    // fz-vw4.2 — closure-to-fixpoint. The SCC pass above is best-effort
    // ordering; under the entry-seed model many specs are discovered
    // *during* the walk and end up in `pending` rather than draining
    // through their SCC. We loop: register every pending key as a spec
    // (at its narrow Descr — no widening, the typer's job is to be as
    // precise as it can), then re-walk every registered spec to surface
    // further discoveries. Terminate when a full round produces no new
    // registrations AND no new pending entries.
    //
    // Cap iterations as a safety bound; in practice convergence is fast
    // since `push_key` filters keys already in specs and pending is a
    // HashSet (duplicates collapse).
    // Worklist: walk only newly-registered specs each round instead of
    // re-walking all specs. Terminates when drain produces no new registrations.
    let mut worklist = drain_and_register(&mut pending, &mut specs, m, &mut callsite_fn_consts);
    loop {
        if worklist.is_empty() {
            break;
        }
        for (fid, key) in &worklist {
            let Some(&j) = m.fn_idx.get(fid) else {
                continue;
            };
            let entry_key = (*fid, key.clone());
            let caller_ft = specs.get(&entry_key).unwrap();
            walk_spec_for_discovery(
                &m.fns[j],
                caller_ft,
                m,
                &specs,
                prev_returns,
                &std::collections::HashSet::new(),
                false,
                &mut pending,
                &mut callsite_fn_consts,
            );
        }
        worklist = drain_and_register(&mut pending, &mut specs, m, &mut callsite_fn_consts);
    }

    // fz-vw4.5b — phase 2: MakeClosure-side any-key registration.
    // Phase 1 (above) registered only direct + resolved-closure
    // specs. Now sweep every registered spec's body for
    // `Prim::MakeClosure(F, captures)` and push
    // `(F, [capture_descrs..., any...])` — but ONLY when the lambda's
    // expected invocation arity (`n_params(F) - captures.len()`) is
    // present in `opaque_consumer_arities`. Closures whose every
    // consumer resolves via fn_constants don't need a defensive
    // any-key body: the resolved direct-Call registration emitted by
    // phase 1 covers every runtime invocation.
    //
    // Computed once: phase-2 registrations are MakeClosure-side any-key
    // bodies; they can't introduce new unresolved CallClosure sites,
    // so the opaque-arity set is stable across phase-2 iterations.
    let opaque_arities = opaque_consumer_arities(m, &specs);
    for _ in 0..64 {
        let snapshot: Vec<(FnId, Vec<Descr>)> = specs.keys().cloned().collect();
        for (fid, key) in &snapshot {
            let Some(&j) = m.fn_idx.get(fid) else {
                continue;
            };
            let entry_key = (*fid, key.clone());
            let caller_ft = specs.get(&entry_key).unwrap();
            let f = &m.fns[j];
            for b in &f.blocks {
                let mut env = caller_ft.block_envs.get(&b.id).cloned().unwrap_or_default();
                for stmt in &b.stmts {
                    let Stmt::Let(v, prim) = stmt;
                    if let Prim::MakeClosure(lam_fn_id, captured) = prim
                        && let Some(&jj) = m.fn_idx.get(lam_fn_id)
                    {
                        let lam = &m.fns[jj];
                        let n_params = lam.block(lam.entry).params.len();
                        let opaque_arity = n_params.saturating_sub(captured.len());
                        if !opaque_arities.contains(&opaque_arity) {
                            env.insert(*v, type_prim(prim, &env, m, &HashSet::new()));
                            continue;
                        }
                        let mut k: Vec<Descr> = vec![Descr::any(); n_params];
                        for (i, cv) in captured.iter().enumerate() {
                            if let Some(slot) = k.get_mut(i) {
                                *slot = env.get(cv).cloned().unwrap_or_else(Descr::any);
                            }
                        }
                        if !specs.contains_key(&(*lam_fn_id, k.clone())) {
                            pending.entry(*lam_fn_id).or_default().insert(k);
                        }
                    }
                    env.insert(*v, type_prim(prim, &env, m, &HashSet::new()));
                }
            }
        }

        // Drain pending → register new specs (no further walking
        // beyond MakeClosure sweep; direct callsites of these new
        // any-key bodies will be discovered when we loop).
        let new_specs = drain_and_register(&mut pending, &mut specs, m, &mut callsite_fn_consts);
        let drained_anything = !new_specs.is_empty();

        // Re-run the phase-1 closure-to-fixpoint on the new specs so
        // direct callsites inside the newly-registered any-key
        // bodies get their downstream specs registered too.
        for _ in 0..16 {
            let snapshot: Vec<(FnId, Vec<Descr>)> = specs.keys().cloned().collect();
            for (fid, key) in &snapshot {
                let Some(&j) = m.fn_idx.get(fid) else {
                    continue;
                };
                let entry_key = (*fid, key.clone());
                let caller_ft = specs.get(&entry_key).unwrap();
                walk_spec_for_discovery(
                    &m.fns[j],
                    caller_ft,
                    m,
                    &specs,
                    prev_returns,
                    &std::collections::HashSet::new(),
                    false,
                    &mut pending,
                    &mut callsite_fn_consts,
                );
            }
            if drain_and_register(&mut pending, &mut specs, m, &mut callsite_fn_consts).is_empty() {
                break;
            }
        }

        if !drained_anything {
            break;
        }
    }

    specs
}

/// fz-210 — discovery walk for one spec. Walks the spec's body and
/// records:
///   - For each direct Term::Call / Term::TailCall (callee, args):
///     append `args_key` to `pending[callee]`. Unify per-arg
///     fn-constants into `callsite_fn_consts[(callee, args_key)]`.
///   - For each cont site (Call / CallClosure / Receive), append the
///     cont's `[slot0, captures...]` key to `pending[cont.fn_id]`.
///   - For each MakeClosure(target, captures), append the lambda's
///     `[capture_descrs..., any...]` key to `pending[target]`.
///   - For each TailCallClosure / CallClosure with fn_constants-known
///     target, append `args_key` to `pending[target]`.
///
/// When `caller_scc` is non-empty AND `widen_now` is true, any key
/// destined for a fn IN `caller_scc` gets `widen()` applied
/// per-element before being pushed. This bounds termination for
/// self-recursive / mutually-recursive fns whose argument Descrs
/// shrink each iter (list-walks).
fn walk_spec_for_discovery(
    f: &FnIr,
    caller_ft: &FnTypes,
    m: &Module,
    specs: &HashMap<(FnId, Vec<Descr>), FnTypes>,
    effective_returns: &HashMap<(FnId, Vec<Descr>), Descr>,
    caller_scc: &std::collections::HashSet<FnId>,
    widen_now: bool,
    pending: &mut HashMap<FnId, std::collections::HashSet<Vec<Descr>>>,
    callsite_fn_consts: &mut HashMap<(FnId, Vec<Descr>), Vec<Option<FnId>>>,
) {
    let maybe_widen = |k: Vec<Descr>, callee: FnId| -> Vec<Descr> {
        if widen_now && caller_scc.contains(&callee) {
            k.into_iter().map(|d| crate::typer::widen(&d)).collect()
        } else {
            k
        }
    };

    let push_key = |pending: &mut HashMap<FnId, std::collections::HashSet<Vec<Descr>>>,
                    callee: FnId,
                    key: Vec<Descr>| {
        if !specs.contains_key(&(callee, key.clone())) {
            pending.entry(callee).or_default().insert(key);
        }
    };

    for b in &f.blocks {
        let mut env = caller_ft.block_envs.get(&b.id).cloned().unwrap_or_default();
        for stmt in &b.stmts {
            let Stmt::Let(v, prim) = stmt;
            // fz-vw4.5b — MakeClosure-side any-key registration moved
            // to a dedicated phase-2 sweep after phase-1 converges. The
            // walker now only discovers direct + resolved-closure
            // dispatch.
            env.insert(*v, type_prim(prim, &env, m, &HashSet::new()));
        }

        // Direct Call / TailCall.
        match &b.terminator {
            Term::Call { callee, args, .. } | Term::TailCall { callee, args, .. } => {
                if let Some(&j) = m.fn_idx.get(callee) {
                    let callee_fn = &m.fns[j];
                    let n_params = callee_fn.block(callee_fn.entry).params.len();
                    let mut key: Vec<Descr> = args
                        .iter()
                        .map(|av| env.get(av).cloned().unwrap_or_else(Descr::any))
                        .collect();
                    while key.len() < n_params {
                        key.push(Descr::any());
                    }
                    key.truncate(n_params);
                    let key = maybe_widen(key, *callee);
                    // fn_constants propagation.
                    let mut per_arg: Vec<Option<FnId>> = args
                        .iter()
                        .map(|av| caller_ft.fn_constants.get(av).copied())
                        .collect();
                    while per_arg.len() < n_params {
                        per_arg.push(None);
                    }
                    per_arg.truncate(n_params);
                    let entry_key = (*callee, key.clone());
                    match callsite_fn_consts.get(&entry_key) {
                        None => {
                            callsite_fn_consts.insert(entry_key.clone(), per_arg);
                        }
                        Some(prev) => {
                            let merged: Vec<Option<FnId>> = prev
                                .iter()
                                .zip(per_arg.iter())
                                .map(|(a, b)| if a == b { *a } else { None })
                                .collect();
                            callsite_fn_consts.insert(entry_key.clone(), merged);
                        }
                    }
                    push_key(pending, *callee, key);
                }
            }
            _ => {}
        }

        // CallClosure / TailCallClosure with known target via fn_constants
        // OR via closure_lit Descr (fz-ul4.27.22.10). Both paths fire to
        // register narrow specs at the resolved body — fn_constants
        // covers zero-capture references discovered pre-22.10; closure_lit
        // covers all MakeClosure-typed closures (including non-zero capture)
        // by inspecting the closure Var's own Descr.
        let (closure_var, closure_args): (Option<Var>, &[Var]) = match &b.terminator {
            Term::CallClosure { closure, args, .. } | Term::TailCallClosure { closure, args } => {
                (Some(*closure), args.as_slice())
            }
            _ => (None, &[]),
        };
        if let Some(cv) = closure_var {
            // (a) fn_constants path — legacy, zero-capture only.
            if let Some(&target_fn) = caller_ft.fn_constants.get(&cv)
                && let Some(&j) = m.fn_idx.get(&target_fn)
            {
                let target = &m.fns[j];
                let n_params = target.block(target.entry).params.len();
                let mut key: Vec<Descr> = closure_args
                    .iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(Descr::any))
                    .collect();
                while key.len() < n_params {
                    key.push(Descr::any());
                }
                key.truncate(n_params);
                let key = maybe_widen(key, target_fn);
                push_key(pending, target_fn, key);
            }
            // (b) closure_lit path — narrow per (fn_id, captures + args).
            // Fires for every pos closure_lit clause in cv's Descr.
            if let Some(cv_descr) = env.get(&cv).cloned() {
                let arg_descrs: Vec<Descr> = closure_args
                    .iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(Descr::any))
                    .collect();
                for clause in &cv_descr.funcs {
                    if !clause.neg.is_empty() {
                        continue;
                    }
                    for sig in &clause.pos {
                        let Some(lit) = &sig.lit else {
                            continue;
                        };
                        let Some(&j) = m.fn_idx.get(&lit.fn_id) else {
                            continue;
                        };
                        let target = &m.fns[j];
                        let n_params = target.block(target.entry).params.len();
                        let mut key: Vec<Descr> = lit.captures.clone();
                        key.extend(arg_descrs.iter().cloned());
                        while key.len() < n_params {
                            key.push(Descr::any());
                        }
                        key.truncate(n_params);
                        let key = maybe_widen(key, lit.fn_id);
                        push_key(pending, lit.fn_id, key);
                    }
                }
            }
        }

        // Cont keying. Slot 0 = callee's effective return (Call only);
        // any (CallClosure / Receive). Slots 1+ = per-spec captures.
        //
        // fz-3zx — slot 0 reads from the LFP cache `effective_returns`
        // (carried across outer type_module iterations via fz-8ki's
        // InferredReturn discipline). A missing entry == Unknown ==
        // "we don't know yet, defer the cont push until next outer
        // iter." Genuinely opaque sites (unresolved CallClosure /
        // Receive) still use `any` directly — they're not LFP-bottom,
        // they're proven-cannot-narrow.
        //
        // fz-vw4.5d — also defer when the callee spec itself is not
        // yet registered. Both conditions are fixpoint deferrals;
        // either landing this iter pushes a polluting wide spec
        // alongside the narrower one the next iter would produce.
        let cont = match &b.terminator {
            Term::Call { continuation, .. } => Some(continuation),
            Term::CallClosure { continuation, .. } => Some(continuation),
            Term::Receive { continuation } => Some(continuation),
            _ => None,
        };
        let slot0_descr: Option<Descr> = match &b.terminator {
            Term::Call { callee, args, .. } => {
                let arg_descrs: Vec<Descr> = args
                    .iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(Descr::any))
                    .collect();
                let callee_key = (*callee, arg_descrs);
                if !specs.contains_key(&callee_key) {
                    None
                } else {
                    effective_returns.get(&callee_key).cloned()
                }
            }
            Term::CallClosure { closure, args, .. } => {
                // fz-vw4.5d — if fn_constants resolves the closure
                // operand, treat like Term::Call for slot-0 narrowing.
                if let Some(&target) = caller_ft.fn_constants.get(closure) {
                    let target_fn = m.fn_by_id(target);
                    let n_params = target_fn.block(target_fn.entry).params.len();
                    let mut arg_descrs: Vec<Descr> = args
                        .iter()
                        .map(|av| env.get(av).cloned().unwrap_or_else(Descr::any))
                        .collect();
                    while arg_descrs.len() < n_params {
                        arg_descrs.push(Descr::any());
                    }
                    arg_descrs.truncate(n_params);
                    let callee_key = (target, arg_descrs);
                    if !specs.contains_key(&callee_key) {
                        None
                    } else {
                        effective_returns.get(&callee_key).cloned()
                    }
                } else if let Some(cv_descr) = env.get(closure) {
                    // fz-ul4.27.22.10 — closure_lit-driven slot-0 narrowing.
                    // If the closure Var's Descr carries a closure_lit
                    // (singleton or union of singletons), look up each
                    // resolved body's return at the matching (captures + args)
                    // key. Falls back to any() for unresolved arrows.
                    let arg_descrs: Vec<Descr> = args
                        .iter()
                        .map(|av| env.get(av).cloned().unwrap_or_else(Descr::any))
                        .collect();
                    resolve_closure_return(cv_descr, effective_returns, &arg_descrs)
                } else {
                    Some(Descr::any())
                }
            }
            Term::Receive { .. } => Some(Descr::any()),
            _ => None,
        };
        if let (Some(cont), Some(slot0)) = (cont, slot0_descr)
            && let Some(&j) = m.fn_idx.get(&cont.fn_id)
        {
            let cont_fn = &m.fns[j];
            let n_params = cont_fn.block(cont_fn.entry).params.len();
            let mut key: Vec<Descr> = vec![Descr::any(); n_params];
            if !key.is_empty() {
                key[0] = slot0;
            }
            for (k, cvv) in cont.captured.iter().enumerate() {
                if let Some(p) = key.get_mut(k + 1) {
                    *p = env.get(cvv).cloned().unwrap_or_else(Descr::any);
                }
            }
            let key = maybe_widen(key, cont.fn_id);
            // fz-vw4.5d — propagate fn_constants from captured
            // vars into the cont spec's callsite_fn_consts. The
            // cont's entry param i+1 receives captured[i] at
            // runtime; if the caller has fn_constants for that
            // capture, the cont's entry param inherits it. Without
            // this, conts that pass closures via captures lose the
            // resolution info, and the cont's body sees an opaque
            // closure-typed var — which forces an unwanted any-key
            // for the closure target (step 5c gating fires).
            let mut per_param: Vec<Option<FnId>> = vec![None; n_params];
            // Slot 0 (the awaited value) carries no captured-side
            // fn_constants — it comes from the callee's return.
            for (k, cvv) in cont.captured.iter().enumerate() {
                if let Some(slot) = per_param.get_mut(k + 1) {
                    *slot = caller_ft.fn_constants.get(cvv).copied();
                }
            }
            let entry_key = (cont.fn_id, key.clone());
            match callsite_fn_consts.get(&entry_key) {
                None => {
                    callsite_fn_consts.insert(entry_key.clone(), per_param);
                }
                Some(prev) => {
                    let merged: Vec<Option<FnId>> = prev
                        .iter()
                        .zip(per_param.iter())
                        .map(|(a, b)| if a == b { *a } else { None })
                        .collect();
                    callsite_fn_consts.insert(entry_key.clone(), merged);
                }
            }
            push_key(pending, cont.fn_id, key);
        }
    }
}

/// fz-ul4.29.10.3 — rewrite `Term::CallClosure(v, args, cont)` →
/// `Term::Call(F, args, cont)` (and `TailCallClosure` → `TailCall`)
/// when `types.specs[..].fn_constants[v] = F` agrees across every spec
/// of the enclosing FnIr that has an opinion on `v`. Disagreement
/// (different specs of the same fn body see different FnIds for the
/// same Var) leaves the terminator untouched — safe fallback.
///
/// Module mutation only; callers re-run `type_module` afterwards to
/// refresh `ModuleTypes` against the rewritten IR (so the typed-spec
/// landscape reflects direct dispatch and `.29.12.6` can drop dead
/// any-keys).
pub fn rewrite_known_target_closures(module: &mut Module, types: &ModuleTypes) {
    let mut unified: HashMap<FnId, HashMap<Var, Option<FnId>>> = HashMap::new();
    for ((fid, _), ft) in &types.specs {
        let entry = unified.entry(*fid).or_default();
        for (v, fnid) in &ft.fn_constants {
            match entry.get(v).copied() {
                None => {
                    entry.insert(*v, Some(*fnid));
                }
                Some(Some(prev)) if prev == *fnid => {}
                Some(_) => {
                    entry.insert(*v, None);
                }
            }
        }
    }
    for f in &mut module.fns {
        let Some(map) = unified.get(&f.id) else {
            continue;
        };
        for b in &mut f.blocks {
            let new_term = match &b.terminator {
                Term::CallClosure {
                    closure,
                    args,
                    continuation,
                } => {
                    if let Some(Some(target)) = map.get(closure).copied() {
                        Some(Term::Call {
                            callee: target,
                            args: args.clone(),
                            continuation: continuation.clone(),
                        })
                    } else {
                        None
                    }
                }
                Term::TailCallClosure { closure, args } => {
                    if let Some(Some(target)) = map.get(closure).copied() {
                        Some(Term::TailCall {
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
}

/// BFS from entry; returns blocks in topological order for all forward edges.
/// Back-edges (to already-visited blocks) are skipped — the outer fixpoint
/// in `type_fn` handles them by iterating until convergence.
/// Unreachable blocks (dead-code match-error branches etc.) are appended
/// after the reachable prefix so their vars still get typed.
fn topo_order(f: &FnIr) -> Vec<BlockId> {
    let mut visited: HashSet<BlockId> = HashSet::new();
    let mut order: Vec<BlockId> = Vec::with_capacity(f.blocks.len());
    let mut queue: std::collections::VecDeque<BlockId> = std::collections::VecDeque::new();
    queue.push_back(f.entry);
    visited.insert(f.entry);
    while let Some(bid) = queue.pop_front() {
        order.push(bid);
        let b = f.block(bid);
        let succs: &[BlockId] = match &b.terminator {
            Term::Goto(t, _) => std::slice::from_ref(t),
            Term::If(_, t, e) => &[*t, *e],
            _ => &[],
        };
        for &s in succs {
            if visited.insert(s) {
                queue.push_back(s);
            }
        }
    }
    // Append unreachable blocks so their vars are still typed.
    for b in &f.blocks {
        if visited.insert(b.id) {
            order.push(b.id);
        }
    }
    order
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

    let topo = topo_order(f);
    loop {
        let mut changed = false;

        for &bid in &topo {
            let b = f.block(bid);
            // Re-derive env at each stmt position.
            let mut env = block_envs[&b.id].clone();
            // Track vars provably derived from IR-level Prim::Const stmts
            // within this block. Used to enable literal folding in
            // numeric_result_fold without cascading spec keys (fz-1pq.6).
            let mut const_vars: HashSet<Var> = HashSet::new();
            for stmt in &b.stmts {
                let Stmt::Let(v, prim) = stmt;
                let t = type_prim(prim, &env, m, &const_vars);
                // Propagate const-derivation: a Const is trivially const; a
                // BinOp/UnOp on const vars is also const.
                match prim {
                    Prim::Const(_) => {
                        const_vars.insert(*v);
                    }
                    Prim::BinOp(_, a, b) if const_vars.contains(a) && const_vars.contains(b) => {
                        const_vars.insert(*v);
                    }
                    Prim::UnOp(_, a) if const_vars.contains(a) => {
                        const_vars.insert(*v);
                    }
                    _ => {}
                }
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
                    for &p in target_b.params.iter() {
                        let from_env = block_envs[target]
                            .get(&p)
                            .cloned()
                            .unwrap_or_else(Descr::none);
                        let prev = vars.get(&p).cloned().unwrap_or_else(Descr::none);
                        if !from_env.is_equiv(&prev) {
                            vars.insert(p, from_env);
                            changed = true;
                        }
                    }
                }
                Term::If(cond, then_b, else_b) => {
                    let (then_env, else_env) = narrow_for_if(&env, *cond, &b.stmts);
                    if merge_into(&mut block_envs, *then_b, &then_env) {
                        changed = true;
                    }
                    if merge_into(&mut block_envs, *else_b, &else_env) {
                        changed = true;
                    }
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

        if !changed {
            break;
        }
    }

    // fz-ul4.29.10.1 — populate fn_constants from zero-capture
    // `MakeClosure(F, [])` Let-bindings. Single forward pass; SSA
    // means each Var is bound at one site.
    let mut fn_constants: HashMap<Var, FnId> = HashMap::new();
    for b in &f.blocks {
        for stmt in &b.stmts {
            let Stmt::Let(v, prim) = stmt;
            if let Prim::MakeClosure(fid, captured) = prim
                && captured.is_empty()
            {
                fn_constants.insert(*v, *fid);
            }
        }
    }

    // fz-1pq.3 — post-convergence reachability pass. Worklist from
    // entry; at If terminators, use the post-stmt env (stmts may define
    // the condition var) to prune branches whose condition is a singleton
    // boolean (folded by compare_result).
    let mut reachable_blocks: HashSet<BlockId> = HashSet::new();
    let mut worklist: Vec<BlockId> = vec![f.entry];
    while let Some(bid) = worklist.pop() {
        if !reachable_blocks.insert(bid) {
            continue;
        }
        let b = f.block(bid);
        match &b.terminator {
            Term::Goto(target, _) => worklist.push(*target),
            Term::If(cond, then_b, else_b) => {
                // Re-evaluate stmts to get the env at the terminator.
                let mut env = block_envs[&bid].clone();
                for stmt in &b.stmts {
                    let Stmt::Let(v, prim) = stmt;
                    env.insert(*v, type_prim(prim, &env, m, &HashSet::new()));
                }
                let ct = env.get(cond).cloned().unwrap_or_else(Descr::any);
                // Use is_subtype to check provable branch deadness.
                // `ct ⊆ atom_lit("true")` means ct can ONLY be true →
                // else-branch dead. `ct ⊆ atom_lit("false")` → then dead.
                // bool_t()/any()/etc. are NOT subtypes of either singleton,
                // so both branches remain reachable.
                if !ct.is_subtype(&Descr::atom_lit("false")) {
                    worklist.push(*then_b);
                }
                if !ct.is_subtype(&Descr::atom_lit("true")) {
                    worklist.push(*else_b);
                }
            }
            _ => {}
        }
    }

    FnTypes {
        vars,
        block_envs,
        fn_constants,
        reachable_blocks,
    }
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
fn union_envs(a: HashMap<Var, Descr>, b: &HashMap<Var, Descr>) -> HashMap<Var, Descr> {
    let mut out = a;
    for (v, dt) in b {
        let entry = out.entry(*v).or_insert_with(Descr::none);
        *entry = entry.union(dt);
    }
    out
}

/// Recursive core for if-condition narrowing.
/// Returns (then_env, else_env) with variable types refined for each branch.
fn narrow_for_cond(
    cond: Var,
    env: &HashMap<Var, Descr>,
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
        Prim::BinOp(BinOp::And, a, b) => {
            // Truthy: both sub-conditions hold — narrow by a, then by b.
            let (then_a, else_a) = narrow_for_cond(*a, env, stmts);
            let (then_ab, _) = narrow_for_cond(*b, &then_a, stmts);
            // Falsy: at least one fails — union of the individual false branches.
            let (_, else_b) = narrow_for_cond(*b, env, stmts);
            return (then_ab, union_envs(else_a, &else_b));
        }
        Prim::BinOp(BinOp::Or, a, b) => {
            // Truthy: at least one holds — union of individual true branches.
            let (then_a, else_a) = narrow_for_cond(*a, env, stmts);
            let (then_b, _) = narrow_for_cond(*b, env, stmts);
            // Falsy: both fail — narrow by a's false, then b's false.
            let (_, else_ab) = narrow_for_cond(*b, &else_a, stmts);
            return (union_envs(then_a, &then_b), else_ab);
        }
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

fn narrow_for_if(
    env: &HashMap<Var, Descr>,
    cond: Var,
    stmts: &[Stmt],
) -> (HashMap<Var, Descr>, HashMap<Var, Descr>) {
    narrow_for_cond(cond, env, stmts)
}

fn is_singleton_lit(d: &Descr) -> bool {
    (!d.ints.cofinite && d.ints.set.len() == 1)
        || (!d.atoms.cofinite && d.atoms.set.len() == 1)
        || (!d.strs.cofinite && d.strs.set.len() == 1)
        || (!d.floats.cofinite && d.floats.set.len() == 1)
}

fn type_prim(
    prim: &Prim,
    env: &HashMap<Var, Descr>,
    m: &Module,
    const_vars: &HashSet<Var>,
) -> Descr {
    match prim {
        Prim::Const(c) => type_const(c, &m.atom_names),

        Prim::BinOp(op, a, b) => {
            let at = lookup(env, *a);
            let bt = lookup(env, *b);
            let fold = const_vars.contains(a) && const_vars.contains(b);
            type_binop(*op, &at, &bt, fold)
        }
        Prim::UnOp(op, v) => {
            let vt = lookup(env, *v);
            match op {
                UnOp::Neg => {
                    if const_vars.contains(v) {
                        numeric_result_fold(BinOp::Sub, &Descr::int_lit(0), &vt)
                    } else {
                        numeric_result(&vt, &vt)
                    }
                }
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
                comps
                    .into_iter()
                    .nth(*i as usize)
                    .unwrap_or_else(Descr::any)
            } else {
                Descr::any()
            }
        }

        Prim::MakeList(els, tail) => {
            let mut elem = Descr::none();
            for v in els {
                elem = elem.union(&lookup(env, *v));
            }
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
                    Some(mk) => {
                        fields.insert(mk, vt);
                    }
                    None => {
                        all_static = false;
                        break;
                    }
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
        Prim::ConstBitstring(_, _) => Descr::vec_u8().union(&Descr::vec_bit()),

        Prim::MakeClosure(fn_id, captured) => {
            // fz-ul4.27.22.10 — type MakeClosure's result as a closure
            // literal: a singleton-typed arrow tagged with (fn_id,
            // capture_descrs). Downstream consumers (cont_slot0_descr,
            // codegen chain_repr / TailCallClosure lowering) read the lit
            // to resolve the body spec by exact-key lookup instead of
            // joining over the saturated arrow's return.
            let callee = m.fn_by_id(*fn_id);
            let entry = callee.block(callee.entry);
            let arity = entry.params.len();
            let n_caps = captured.len();
            let n_args = arity.saturating_sub(n_caps);
            let capture_descrs: Vec<Descr> = captured
                .iter()
                .map(|cv| env.get(cv).cloned().unwrap_or_else(Descr::any))
                .collect();
            Descr::closure_lit(*fn_id, capture_descrs, n_args)
        }

        Prim::Builtin(bid, args) => {
            // send(pid, msg) returns msg — passthrough on arg[1].
            if matches!(BuiltinKind::from_id(*bid), Some(BuiltinKind::Send)) {
                args.get(1)
                    .map(|v| lookup(env, *v))
                    .unwrap_or_else(Descr::any)
            } else {
                type_builtin(*bid)
            }
        }

        Prim::Extern(_, _) => Descr::any(),

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

fn type_const(c: &Const, atom_names: &[String]) -> Descr {
    match c {
        Const::Int(n) => Descr::int_lit(*n),
        Const::Float(f) => Descr::float_lit(*f),
        Const::Str(s) => Descr::str_lit(s.clone()),
        Const::Atom(id) => {
            let name = atom_names
                .get(*id as usize)
                .map(String::as_str)
                .unwrap_or("?");
            Descr::atom_lit(name)
        }
        Const::Nil => Descr::nil(),
        Const::True => Descr::atom_lit("true"),
        Const::False => Descr::atom_lit("false"),
    }
}

fn type_binop(op: BinOp, a: &Descr, b: &Descr, fold: bool) -> Descr {
    use BinOp::*;
    match op {
        Add | Sub | Mul | Div | Mod => {
            if fold {
                numeric_result_fold(op, a, b)
            } else {
                numeric_result(a, b)
            }
        }
        Eq | Neq | Lt | Le | Gt | Ge => compare_result(op, a, b),
        And | Or => a.union(b),
    }
}

fn float_singleton(d: &Descr) -> Option<f64> {
    if !d.floats.cofinite && d.floats.set.len() == 1 {
        d.floats.set.iter().next().map(|f| f.get())
    } else {
        None
    }
}

fn compare_result(op: BinOp, a: &Descr, b: &Descr) -> Descr {
    use BinOp::*;
    if let (Some(ai), Some(bi)) = (a.as_int_singleton(), b.as_int_singleton()) {
        let result = match op {
            Eq => ai == bi,
            Neq => ai != bi,
            Lt => ai < bi,
            Le => ai <= bi,
            Gt => ai > bi,
            Ge => ai >= bi,
            _ => return Descr::bool_t(),
        };
        return if result {
            Descr::atom_lit("true")
        } else {
            Descr::atom_lit("false")
        };
    }
    if let (Some(af), Some(bf)) = (float_singleton(a), float_singleton(b)) {
        let result = match op {
            Eq => af == bf,
            Neq => af != bf,
            Lt => af < bf,
            Le => af <= bf,
            Gt => af > bf,
            Ge => af >= bf,
            _ => return Descr::bool_t(),
        };
        return if result {
            Descr::atom_lit("true")
        } else {
            Descr::atom_lit("false")
        };
    }
    Descr::bool_t()
}

fn numeric_result(a: &Descr, b: &Descr) -> Descr {
    let int = Descr::int();
    let float = Descr::float();
    let both_int = a.is_subtype(&int) && b.is_subtype(&int);
    let both_float = a.is_subtype(&float) && b.is_subtype(&float);
    if both_int {
        int
    } else if both_float {
        float
    } else {
        int.union(&float)
    }
}

/// Like `numeric_result` but folds singleton operands to a literal result.
/// Only called when both operands are known IR-level constants (const_vars),
/// so the result cannot cascade into new narrow spec keys (fz-1pq.6).
fn numeric_result_fold(op: BinOp, a: &Descr, b: &Descr) -> Descr {
    use BinOp::*;
    if let (Some(ai), Some(bi)) = (a.as_int_singleton(), b.as_int_singleton()) {
        let result = match op {
            Add => ai.checked_add(bi),
            Sub => ai.checked_sub(bi),
            Mul => ai.checked_mul(bi),
            Div => {
                if bi != 0 {
                    ai.checked_div(bi)
                } else {
                    None
                }
            }
            Mod => {
                if bi != 0 {
                    ai.checked_rem(bi)
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some(r) = result {
            return Descr::int_lit(r);
        }
    }
    if let (Some(af), Some(bf)) = (float_singleton(a), float_singleton(b)) {
        let result = match op {
            Add => Some(af + bf),
            Sub => Some(af - bf),
            Mul => Some(af * bf),
            Div => Some(af / bf),
            Mod => Some(af % bf),
            _ => None,
        };
        if let Some(r) = result {
            return Descr::float_lit(r);
        }
    }
    numeric_result(a, b)
}

fn type_builtin(bid: BuiltinId) -> Descr {
    match BuiltinKind::from_id(bid) {
        Some(BuiltinKind::Print) => Descr::nil(),
        Some(BuiltinKind::Assert) | Some(BuiltinKind::AssertEq) | Some(BuiltinKind::AssertNeq) => {
            Descr::nil()
        }
        Some(BuiltinKind::VecGet) => Descr::int().union(&Descr::float()),
        // fz-ul4.19.2: spawn/self both return a Pid (boxed Int for v1).
        Some(BuiltinKind::Spawn) | Some(BuiltinKind::SelfPid) => Descr::int(),
        Some(BuiltinKind::Send) => Descr::any(), // unreachable; handled in type_prim
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

/// fz-l01 — synthetic match-error halt block detector. ir_lower
/// inserts a fail block that does `Halt(:match_error)` as the
/// pattern-match-failure landing pad. When the typer proves no clause
/// fails (every input is covered), that block becomes unreachable,
/// triggering an unreachable-arm warning attributed to a source
/// position the user didn't directly write. Suppress those.
///
/// Shape: a single-stmt block where the Let binds an atom Const
/// named `"match_error"`, and the terminator Halts that Var.
fn is_synthetic_match_error_block(f: &FnIr, bid: BlockId) -> bool {
    let b = f.block(bid);
    let Term::Halt(halt_var) = &b.terminator else {
        return false;
    };
    for stmt in &b.stmts {
        let Stmt::Let(v, prim) = stmt;
        if v != halt_var {
            continue;
        }
        // The atom Const for match_error carries an interned atom ID,
        // not a string. We can't compare names without an atom table.
        // Use a weaker but sufficient check: the block is a 1-stmt
        // block whose Let binds an Atom Const and is the Halt operand.
        // Real user code halting on an atom never goes through this
        // exact shape (CPS lowering wouldn't put the atom literal in
        // the same block as the Halt without intervening structure).
        if matches!(prim, Prim::Const(Const::Atom(_))) && b.stmts.len() == 1 {
            return true;
        }
    }
    false
}

/// fz-pky.1 — within ONE spec's narrowed env, find the first Var
/// whose type became empty post-narrowing. Returns (Var, old_t, new_t)
/// if found; None if narrowing kept every var inhabited.
fn find_emptied_var(
    pre_env: &HashMap<crate::fz_ir::Var, Descr>,
    branch_env: &HashMap<crate::fz_ir::Var, Descr>,
) -> Option<(crate::fz_ir::Var, Descr, Descr)> {
    let mut keys: Vec<crate::fz_ir::Var> = branch_env.keys().copied().collect();
    keys.sort_by_key(|v| v.0);
    for v in keys {
        let new_t = branch_env.get(&v).unwrap();
        let old_t = pre_env.get(&v).cloned().unwrap_or_else(Descr::any);
        if !new_t.is_equiv(&old_t) && new_t.is_empty() && !old_t.is_empty() {
            return Some((v, old_t, new_t.clone()));
        }
    }
    None
}

/// fz-pky.1 — build the unreachable-arm diagnostic from per-spec
/// dead-var records. We join old_t across specs so the type-note
/// reflects every specialization that contributed; new_t is similarly
/// joined for the narrow-note (in practice, when ALL specs found a
/// branch dead, each spec's new_t is `none` — joined, still `none`).
fn emit_unreachable(
    module: &Module,
    fn_name: &str,
    term_span: crate::diag::Span,
    tag: &str,
    bb_id: crate::fz_ir::BlockId,
    dead_records: &[(crate::fz_ir::Var, Descr, Descr)],
) -> crate::diag::Diagnostic {
    use crate::diag::{Diagnostic, codes::TYPE_UNREACHABLE_ARM};
    // Pick the lowest-id Var across all records for label attribution
    // (stable, matches old single-spec behavior when only one spec).
    let pick = dead_records.iter().min_by_key(|(v, _, _)| v.0).unwrap();
    let (v, _, _) = pick;
    // Join the offending Var's pre-narrow types across every spec that
    // dropped this branch — that's the source-level view of the value.
    let mut joined_old = Descr::none();
    for (vv, ot, _) in dead_records {
        if *vv == *v {
            joined_old = joined_old.union(ot);
        }
    }
    let var_name = module.source.var_name_of(*v);
    let label_subject = match var_name {
        Some(n) => format!("`{}`", n),
        None => "this value".to_string(),
    };
    let var_span = module.source.var_span_of(*v);

    let message = format!("the {} branch is never reachable", tag);
    let type_note = format!(
        "{} here has type `{}`",
        label_subject,
        joined_old.display_for_diag(),
    );
    let narrow_note = format!(
        "narrowing for this branch would need `none`, but that intersection \
         is uninhabited (unreachable arm at bb{})",
        bb_id.0,
    );

    let mut d = Diagnostic::warning(TYPE_UNREACHABLE_ARM, message, term_span)
        .with_label(format!("in fn `{}`", fn_name))
        .with_note(type_note)
        .with_note(narrow_note);
    if !var_span.is_dummy() && var_span != term_span {
        d = d.with_secondary(var_span, format!("{} bound here", label_subject));
    }
    d
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
pub fn collect_diagnostics(module: &Module, types: &ModuleTypes) -> crate::diag::Diagnostics {
    use crate::diag::codes::TYPE_DEAD_BINOP;
    use crate::diag::{Diagnostic, Diagnostics, Span};

    let mut out = Diagnostics::new();

    // fz-pky.1 — per-spec unreachable-arm. A branch is source-level
    // unreachable iff EVERY registered spec of the enclosing fn agrees
    // it's dead. A branch dead in some specs but live in others (e.g.
    // sum's `[]` arm under the narrow `[list(int_set)]` spec, but live
    // under the recursive `[nil | list(int_set)]` spec) is reachable
    // source-side and must NOT warn.
    //
    // Algorithm: for each (FnId, Term::If, branch), count specs where
    // dead vs total specs of the fn. Emit when dead-count equals total.
    //
    // Group specs by FnId.
    let mut specs_by_fn: HashMap<crate::fz_ir::FnId, Vec<Vec<Descr>>> = HashMap::new();
    for (fid, key) in types.specs.keys() {
        specs_by_fn.entry(*fid).or_default().push(key.clone());
    }

    // For diagnostic purposes only: fns with no registered spec
    // (no IR caller, not closure-reachable, not entry-seeded) still
    // contain code the user wrote. Type them under their any-key
    // ad-hoc and run diagnostics against that. This doesn't pollute
    // module_types.specs — codegen never sees these specs because
    // codegen only compiles reachable fns.
    let mut adhoc_specs: HashMap<crate::fz_ir::FnId, FnTypes> = HashMap::new();
    for f in &module.fns {
        if specs_by_fn.contains_key(&f.id) {
            continue;
        }
        let n_params = f.block(f.entry).params.len();
        let any_key: Vec<Descr> = vec![Descr::any(); n_params];
        let ft = type_fn(f, module, Some(&any_key));
        adhoc_specs.insert(f.id, ft);
        specs_by_fn.entry(f.id).or_default().push(any_key);
    }

    let mut fns_sorted: Vec<&crate::fz_ir::FnIr> = module.fns.iter().collect();
    fns_sorted.sort_by_key(|f| f.id.0);
    for f in fns_sorted {
        let Some(keys) = specs_by_fn.get(&f.id) else {
            continue;
        };
        let total_specs = keys.len();
        if total_specs == 0 {
            continue;
        }

        let mut blocks_sorted: Vec<&crate::fz_ir::Block> = f.blocks.iter().collect();
        blocks_sorted.sort_by_key(|b| b.id.0);
        for b in blocks_sorted {
            let Term::If(cond, then_b, else_b) = b.terminator else {
                continue;
            };

            let term_span = module
                .source
                .term_span
                .get(&(f.id, b.id))
                .copied()
                .unwrap_or(Span::DUMMY);

            // For each spec, narrow this If and record whether each
            // branch is dead (and which Var made it dead, for the
            // diagnostic note).
            let mut dead_then: Vec<(crate::fz_ir::Var, Descr, Descr)> = Vec::new();
            let mut dead_else: Vec<(crate::fz_ir::Var, Descr, Descr)> = Vec::new();
            for key in keys {
                let ft = types
                    .specs
                    .get(&(f.id, key.clone()))
                    .or_else(|| adhoc_specs.get(&f.id))
                    .unwrap();
                let mut env = ft.block_envs.get(&b.id).cloned().unwrap_or_default();
                for stmt in &b.stmts {
                    let Stmt::Let(v, prim) = stmt;
                    let t = type_prim(prim, &env, module, &HashSet::new());
                    env.insert(*v, t);
                }
                let (then_env, else_env) = narrow_for_if(&env, cond, &b.stmts);
                if let Some(d) = find_emptied_var(&env, &then_env) {
                    dead_then.push(d);
                }
                if let Some(d) = find_emptied_var(&env, &else_env) {
                    dead_else.push(d);
                }
            }

            // Emit only when EVERY spec found the branch dead AND
            // the target block isn't a synthetic match-error halt
            // (lowering inserts those defensively; when the typer
            // proves no clause fails, the warning is just noise about
            // a check the user didn't write).
            if dead_then.len() == total_specs && !is_synthetic_match_error_block(f, then_b) {
                out.push(emit_unreachable(
                    module, &f.name, term_span, "then", then_b, &dead_then,
                ));
            }
            if dead_else.len() == total_specs && !is_synthetic_match_error_block(f, else_b) {
                out.push(emit_unreachable(
                    module, &f.name, term_span, "else", else_b, &dead_else,
                ));
            }
        }
    }

    // VR.5a (fz-ul4.27.4): flag kind-disjoint equality / inequality. We walk
    // each Let stmt, rebuild the env up to that stmt, and report a
    // type/dead-binop diagnostic when `intersect(t_a, t_b)` is empty. The
    // codegen-side fold (Eq -> FALSE, Neq -> TRUE) is unaffected by the
    // diagnostic; the user just gets a warning that the comparison can never
    // hold.
    for f in module.fns.iter() {
        // Pick any registered spec, or fall back to ad-hoc any-key
        // (same rule as the unreachable-arm scan above).
        let ft_owned: Option<FnTypes>;
        let ft: &FnTypes = match types.any_spec_for(f.id) {
            Some(ft) => ft,
            None => {
                let n_params = f.block(f.entry).params.len();
                let any_key: Vec<Descr> = vec![Descr::any(); n_params];
                ft_owned = Some(type_fn(f, module, Some(&any_key)));
                ft_owned.as_ref().unwrap()
            }
        };
        let mut blocks_sorted: Vec<&crate::fz_ir::Block> = f.blocks.iter().collect();
        blocks_sorted.sort_by_key(|b| b.id.0);
        for b in blocks_sorted {
            let mut env = ft.block_envs.get(&b.id).cloned().unwrap_or_default();
            let spans = module.source.stmt_spans.get(&(f.id, b.id));
            for (sidx, stmt) in b.stmts.iter().enumerate() {
                let Stmt::Let(v, prim) = stmt;
                if let Prim::BinOp(op, lhs, rhs) = prim
                    && matches!(op, BinOp::Eq | BinOp::Neq)
                {
                    let ta = env.get(lhs).cloned().unwrap_or_else(Descr::any);
                    let tb = env.get(rhs).cloned().unwrap_or_else(Descr::any);
                    // Lint only on cross-kind disjointness (int vs atom,
                    // float vs nil, etc.). Within a single axis, two
                    // disjoint literal sets (e.g. `1 == 2`) still fold to
                    // false at codegen but are not surprising to the
                    // reader, so we keep them silent.
                    let cross_kind = !ta.is_empty() && !tb.is_empty() && !axes_overlap(&ta, &tb);
                    if cross_kind {
                        let span = spans
                            .and_then(|s| s.get(sidx).copied())
                            .unwrap_or(Span::DUMMY);
                        let constant = if matches!(op, BinOp::Eq) {
                            "false"
                        } else {
                            "true"
                        };
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
                let t = type_prim(prim, &env, module, &HashSet::new());
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
        || (!a.atoms.is_none() && !b.atoms.is_none())
        || (!a.ints.is_none() && !b.ints.is_none())
        || (!a.floats.is_none() && !b.floats.is_none())
        || (!a.strs.is_none() && !b.strs.is_none())
        || (!a.tuples.is_empty() && !b.tuples.is_empty())
        || (!a.lists.is_empty() && !b.lists.is_empty())
        || (!a.funcs.is_empty() && !b.funcs.is_empty())
        || (!a.maps.is_empty() && !b.maps.is_empty())
}

/// .11.24.5: refine `MakeVec(I64, els)` to `MakeVec(F64, els)` when any
/// element is typed Float. Errors on the "mixed Int and Float" case under
/// the no-auto-promotion rule.
///
/// Operates in-place on `module`. Caller supplies a typer output that was
/// produced from the same module shape (run `type_module(module)` first).
pub fn rewrite_vec_kinds(module: &mut Module, types: &ModuleTypes) -> Result<(), String> {
    use crate::fz_ir::Stmt;
    // fz-pky.2 — for each fn, use the registered spec if any, else
    // type ad-hoc under all-any. This pass runs as a pre-codegen
    // diagnostic; even unreachable fns need their MakeVec kinds
    // validated (the error is "you wrote a mixed-element vec," not
    // "this code runs.")
    let fn_types: HashMap<FnId, FnTypes> = module
        .fns
        .iter()
        .map(|f| {
            let ft = match types.any_spec_for(f.id) {
                Some(ft) => ft.clone(),
                None => {
                    let n_params = f.block(f.entry).params.len();
                    let any_key: Vec<Descr> = vec![Descr::any(); n_params];
                    type_fn(f, module, Some(&any_key))
                }
            };
            (f.id, ft)
        })
        .collect();
    for f in module.fns.iter_mut() {
        let Some(ft) = fn_types.get(&f.id) else {
            continue;
        };
        let vars = &ft.vars;
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
fn env_at_terminator(caller_ft: &FnTypes, block: &Block, module: &Module) -> HashMap<Var, Descr> {
    let mut env = caller_ft
        .block_envs
        .get(&block.id)
        .cloned()
        .unwrap_or_default();
    for stmt in &block.stmts {
        let Stmt::Let(v, prim) = stmt;
        let t = type_prim(prim, &env, module, &HashSet::new());
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
    match &block.terminator {
        Term::Call { callee, args, .. } => {
            let env = env_at_terminator(caller_ft, block, module);
            let arg_descrs: Vec<Descr> = args
                .iter()
                .map(|av| env.get(av).cloned().unwrap_or_else(Descr::any))
                .collect();
            // fz-3zx — read the converged LFP cache that type_module's outer
            // fixpoint produced. Cycle-cut effective_return_descr is retired.
            module_types
                .effective_returns
                .get(&(*callee, arg_descrs))
                .cloned()
                .unwrap_or_else(Descr::any)
        }
        // fz-ul4.27.22.6 — at a CallClosure seam, the closure's static
        // Descr names the body's possible return shapes. JOIN the return
        // Descrs across positive arrow clauses; this is the value the
        // body's Term::Return passes to the cont's slot 0.
        Term::CallClosure { closure, .. } => {
            let env = env_at_terminator(caller_ft, block, module);
            let closure_d = env.get(closure).cloned().unwrap_or_else(Descr::any);
            closure_d.arrow_join_return()
        }
        _ => Descr::any(),
    }
}

/// fz-ul4.27.21.4 — JOIN of a spec's effective return Descrs, following
/// every exit path. Each `Term::Return` contributes the returned var's
/// Descr; each `Term::TailCall` recursively contributes the callee spec's
/// effective return. Mirrors the codegen-side return-descr fixpoint at
/// `src/ir_codegen.rs:2070-2107` so the typer's cont keying agrees with
/// what the producer actually passes at runtime.
///
/// Without this, a fn whose only direct `Term::Return` is narrow (int)
/// but whose `Term::TailCall` reaches a wider spec (Any/Tagged) appears
/// narrow to the cont keying — the cont's param[0] gets typed `int`,
/// but the producer returns Tagged at runtime, and bits-in-flight are
/// misinterpreted. This bug is what blocked fz-ul4.27.21.1 (see the
/// epic's comments). `effective_return_descr` is the fix.
///
/// Cycle guard: `visiting` tracks specs currently being computed. A
/// spec re-entered through `Term::TailCall` recursion contributes
/// `Descr::none()` (the bottom of the lattice) — the join across other
/// exit paths still produces a sound bound, and external callers of
/// the cycle widen it on the next fixpoint iteration as needed.
///
/// Specs not yet registered in `specs` (the fixpoint hasn't reached
/// them) contribute `Descr::any()` — conservative widening that the
/// outer fixpoint can later refine.
/// fz-2yw.1 — compute the Kleene least-fixpoint of every registered
/// spec's effective return Descr. Under fz's CPS-lowered IR, a spec's
/// "effective return" is the value its caller's cont eventually
/// receives. Every block-terminator contributes:
///
///   Term::Return(v)                ⇒ ft.vars[v]              (direct return)
///   Term::TailCall(G, A)           ⇒ return(G, callee_key)   (transfer to G)
///   Term::Call(_, _, cont)         ⇒ return(cont.fn_id, k)   (G's result feeds K;
///                                                              K eventually returns
///                                                              to our caller's cont)
///   Term::CallClosure(_, _, cont)  ⇒ return(cont.fn_id, k)   (same)
///   Term::Receive { cont }         ⇒ return(cont.fn_id, k)   (msg feeds K)
///   Term::TailCallClosure(c, A)    ⇒ return(target?, A) | any (resolved via
///                                                              fn_constants
///                                                              when possible)
///   Term::Halt / Goto / If         ⇒ no exit-level contribution
///
/// The cont_key is computed via the existing `cont_input_key` helper
/// using each block's per-spec env.
///
/// Termination: the Descr lattice has finite height per module
/// (DNF clauses bounded by program structure + neg-closure). Monotone
/// updates terminate in ≤ N × height iterations.
///
/// Replaces the old cycle-cut-to-⊥ approach: that was sound but
/// dropped the entire recursive contribution. With CPS, recursive
/// flow runs THROUGH the cont chain — without lifting cont contributions
/// to F's return, recursive fns like `sum` reported `return = 0` (base
/// case only) even though every caller's cont actually received `int`.
/// fz-3zx.1 (fz-8ki) — explicit two-state lattice value for the LFP table.
///
/// `Unknown` is the Kleene-bottom for the iteration ("we haven't computed
/// this yet"). `Known(d)` is the converged value (possibly `Descr::none`,
/// which means "this spec has been examined and proven to produce no
/// values" — logically distinct from "we don't know yet").
///
/// Keeping these distinct lets us:
///   1. Assert convergence: at end-of-LFP, no reachable key may remain
///      `Unknown`. A leftover `Unknown` is a non-convergence bug.
///   2. Have type-rule consumers (the walker's slot-0 lookup, fz-3zx)
///      DEFER on `Unknown` instead of falling back to `Descr::any` —
///      avoiding the spurious widening that originally pushed sum's
///      cont slot 0 to `int | float`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum InferredReturn {
    Unknown,
    Known(Box<Descr>),
}

impl InferredReturn {
    /// LFP-join contribution. `Unknown` contributes `Descr::none()` —
    /// the join identity — so an unknown sibling exit doesn't perturb
    /// other contributions. This is the "skip until known" semantics.
    fn as_contribution(&self) -> Descr {
        match self {
            InferredReturn::Unknown => Descr::none(),
            InferredReturn::Known(d) => (**d).clone(),
        }
    }
}

pub fn compute_effective_returns(
    module: &Module,
    specs: &HashMap<(FnId, Vec<Descr>), FnTypes>,
    prev_returns: &HashMap<(FnId, Vec<Descr>), Descr>,
) -> HashMap<(FnId, Vec<Descr>), Descr> {
    // Init every registered spec to Unknown. Reads on missing keys
    // (callee not registered) also resolve to Unknown via the
    // `lookup` helper — same Kleene-bottom semantics.
    let mut ret: HashMap<(FnId, Vec<Descr>), InferredReturn> = HashMap::new();
    for key in specs.keys() {
        ret.insert(key.clone(), InferredReturn::Unknown);
    }
    let lookup =
        |ret: &HashMap<(FnId, Vec<Descr>), InferredReturn>, key: &(FnId, Vec<Descr>)| -> Descr {
            ret.get(key)
                .map(|ir| ir.as_contribution())
                .unwrap_or_else(Descr::none)
        };

    // Helper: cont_input_key matching the registered spec. Uses
    // `prev_returns` (the outer-iter LFP cache) for slot 0 — the same
    // source the walker used when it registered the cont spec, so the
    // keys we look up here are structurally aligned with the registered
    // specs. fz-3zx: cycle-cut effective_return_descr is gone; missing
    // entries in prev_returns fall back to Descr::any (the Receive /
    // opaque-CallClosure default).
    let cont_key_at = |b: &Block, cont: &crate::fz_ir::Cont, ft: &FnTypes| -> Vec<Descr> {
        let Some(_) = module.fn_idx.get(&cont.fn_id) else {
            return vec![];
        };
        let cont_fn = module.fn_by_id(cont.fn_id);
        let n_params = cont_fn.block(cont_fn.entry).params.len();
        let mut key: Vec<Descr> = vec![Descr::any(); n_params];

        let env = env_at_terminator(ft, b, module);
        let slot0 = match &b.terminator {
            Term::Call { callee, args, .. } => {
                let arg_descrs: Vec<Descr> = args
                    .iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(Descr::any))
                    .collect();
                prev_returns
                    .get(&(*callee, arg_descrs))
                    .cloned()
                    .unwrap_or_else(Descr::any)
            }
            Term::CallClosure { closure, args, .. } => {
                if let Some(&target) = ft.fn_constants.get(closure) {
                    let target_fn = module.fn_by_id(target);
                    let np = target_fn.block(target_fn.entry).params.len();
                    let mut ad: Vec<Descr> = args
                        .iter()
                        .map(|av| env.get(av).cloned().unwrap_or_else(Descr::any))
                        .collect();
                    while ad.len() < np {
                        ad.push(Descr::any());
                    }
                    ad.truncate(np);
                    prev_returns
                        .get(&(target, ad))
                        .cloned()
                        .unwrap_or_else(Descr::any)
                } else {
                    Descr::any()
                }
            }
            _ => Descr::any(),
        };
        if !key.is_empty() {
            key[0] = slot0;
        }
        for (k, cv) in cont.captured.iter().enumerate() {
            if let Some(p) = key.get_mut(k + 1) {
                *p = env.get(cv).cloned().unwrap_or_else(Descr::any);
            }
        }
        key
    };

    // Bounded outer iterations as safety. In practice convergence is
    // fast (≤ spec_count iterations).
    for _ in 0..(specs.len() * 4 + 16) {
        let mut changed = false;
        for spec_key in specs.keys() {
            let (fid, _) = spec_key;
            let Some(&j) = module.fn_idx.get(fid) else {
                continue;
            };
            let Some(ft) = specs.get(spec_key) else {
                continue;
            };
            let f = &module.fns[j];

            let mut joined = Descr::none();
            for b in &f.blocks {
                if !ft.reachable_blocks.contains(&b.id) {
                    continue;
                }
                match &b.terminator {
                    Term::Return(rv) => {
                        let d = ft.vars.get(rv).cloned().unwrap_or_else(Descr::any);
                        joined = joined.union(&d);
                    }
                    Term::TailCall { callee, args, .. } => {
                        let arg_descrs: Vec<Descr> = args
                            .iter()
                            .map(|av| ft.vars.get(av).cloned().unwrap_or_else(Descr::any))
                            .collect();
                        joined = joined.union(&lookup(&ret, &(*callee, arg_descrs)));
                    }
                    Term::TailCallClosure { closure, args } => {
                        if let Some(&target) = ft.fn_constants.get(closure) {
                            let target_fn = module.fn_by_id(target);
                            let np = target_fn.block(target_fn.entry).params.len();
                            let mut ad: Vec<Descr> = args
                                .iter()
                                .map(|av| ft.vars.get(av).cloned().unwrap_or_else(Descr::any))
                                .collect();
                            while ad.len() < np {
                                ad.push(Descr::any());
                            }
                            ad.truncate(np);
                            joined = joined.union(&lookup(&ret, &(target, ad)));
                        } else if let Some(cv_descr) = ft.vars.get(closure) {
                            // fz-ul4.27.22.12 — closure_lit-driven path:
                            // resolve each lit clause's body return via
                            // the spec map. Mirrors resolve_closure_return
                            // but inlined here to share the lookup helper's
                            // Unknown-vs-any semantics.
                            let mut all_lit = !cv_descr.funcs.is_empty();
                            let mut acc = Descr::none();
                            'clauses: for c in &cv_descr.funcs {
                                if !c.neg.is_empty() || c.pos.is_empty() {
                                    all_lit = false;
                                    break 'clauses;
                                }
                                for sig in &c.pos {
                                    let Some(lit) = &sig.lit else {
                                        all_lit = false;
                                        break 'clauses;
                                    };
                                    let target_fn = module.fn_by_id(lit.fn_id);
                                    let np = target_fn.block(target_fn.entry).params.len();
                                    let mut full_key: Vec<Descr> = lit.captures.clone();
                                    for av in args.iter() {
                                        full_key.push(
                                            ft.vars.get(av).cloned().unwrap_or_else(Descr::any),
                                        );
                                    }
                                    while full_key.len() < np {
                                        full_key.push(Descr::any());
                                    }
                                    full_key.truncate(np);
                                    acc = acc.union(&lookup(&ret, &(lit.fn_id, full_key)));
                                }
                            }
                            if all_lit {
                                joined = joined.union(&acc);
                            } else {
                                joined = joined.union(&Descr::any());
                            }
                        } else {
                            // Genuinely opaque target (no fn_constants
                            // resolution, no closure_lit) — not a fixpoint
                            // deferral but a real "we cannot prove a
                            // bound." `any` is the honest answer here,
                            // NOT the Unknown sentinel.
                            joined = joined.union(&Descr::any());
                        }
                    }
                    Term::Call { continuation, .. }
                    | Term::CallClosure { continuation, .. }
                    | Term::Receive { continuation } => {
                        let cont_k = cont_key_at(b, continuation, ft);
                        joined = joined.union(&lookup(&ret, &(continuation.fn_id, cont_k)));
                    }
                    Term::Halt(_) | Term::Goto(_, _) | Term::If(_, _, _) => {}
                }
            }
            // First visit (Unknown) always transitions to Known, even
            // when joined == Descr::none() — that's an honest "proven
            // empty" result, not a non-result. Subsequent visits update
            // only when joined widens.
            let should_update = match ret.get(spec_key) {
                Some(InferredReturn::Unknown) => true,
                Some(InferredReturn::Known(prev)) => !joined.is_equiv(prev),
                None => true,
            };
            if should_update {
                ret.insert(spec_key.clone(), InferredReturn::Known(Box::new(joined)));
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Post-convergence assertion: every registered spec must be Known.
    // An Unknown leftover means the LFP body never visited this key —
    // a non-convergence bug, not an honest "no values" answer.
    for (k, v) in &ret {
        debug_assert!(
            matches!(v, InferredReturn::Known(_)),
            "compute_effective_returns: spec {:?} left Unknown after \
             LFP convergence — non-convergence bug",
            k
        );
    }

    // Strip the Known shell for downstream consumers. The
    // Unknown-to-Descr coercion via as_contribution() yields none(),
    // matching the invariant we just asserted under release builds.
    ret.into_iter()
        .map(|(k, v)| {
            (
                k,
                match v {
                    InferredReturn::Known(d) => *d,
                    InferredReturn::Unknown => Descr::none(),
                },
            )
        })
        .collect()
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
// fz-73m — pretty-printer for ModuleTypes (golden spec dump).
// ----------------------------------------------------------------------

/// Deterministic text dump of `ModuleTypes`. One stanza per (FnId, key)
/// spec; specs are sorted by FnId, then by lexicographic Descr-string of
/// the key so the output is stable across runs and HashMap iteration
/// orders.
///
/// Format is intended for golden-file diffing — every line is a comment
/// (`;` prefix) so the file reads like an annotated CLIF dump. Consumers
/// should treat the output as opaque text; the goal is that a human can
/// eyeball "are the inferred types what I expect for this fixture?"
/// without running codegen.
pub fn pretty_module_types(m: &Module, t: &ModuleTypes) -> String {
    let fn_name = |fid: FnId| -> String {
        m.fns
            .iter()
            .find(|f| f.id == fid)
            .map(|f| f.name.clone())
            .unwrap_or_else(|| format!("?fn{}", fid.0))
    };
    let descrs_str = |ds: &[Descr]| -> String {
        let parts: Vec<String> = ds.iter().map(|d| format!("{}", d)).collect();
        format!("[{}]", parts.join(", "))
    };

    let mut keys: Vec<&(FnId, Vec<Descr>)> = t.specs.keys().collect();
    keys.sort_by(|a, b| {
        a.0.0
            .cmp(&b.0.0)
            .then_with(|| descrs_str(&a.1).cmp(&descrs_str(&b.1)))
    });

    let mut out = String::new();
    for spec_key in keys {
        let (fid, key) = spec_key;
        let ft = &t.specs[spec_key];
        let f = m.fn_by_id(*fid);
        let entry = f.block(f.entry);
        let arity = entry.params.len();

        out.push_str(&format!("; spec {}({}) #fn={}\n", f.name, arity, fid.0));
        out.push_str(&format!(";   key:    {}\n", descrs_str(key)));

        let ret = t
            .effective_returns
            .get(spec_key)
            .cloned()
            .unwrap_or_else(Descr::any);
        out.push_str(&format!(";   return: {}\n", ret));

        if !ft.fn_constants.is_empty() {
            let mut fcs: Vec<(&Var, &FnId)> = ft.fn_constants.iter().collect();
            fcs.sort_by_key(|(v, _)| v.0);
            out.push_str(";   fn_constants:\n");
            for (v, fc) in fcs {
                out.push_str(&format!(";     Var({}) = {}#{}\n", v.0, fn_name(*fc), fc.0));
            }
        }

        let mut vars: Vec<(&Var, &Descr)> = ft.vars.iter().collect();
        vars.sort_by_key(|(v, _)| v.0);
        out.push_str(";   vars:\n");
        for (v, d) in vars {
            out.push_str(&format!(";     Var({}) :: {}\n", v.0, d));
        }

        let mut blocks: Vec<&Block> = f.blocks.iter().collect();
        blocks.sort_by_key(|b| b.id.0);
        out.push_str(";   exits:\n");
        for b in blocks {
            let bid = b.id.0;
            match &b.terminator {
                Term::Return(v) => {
                    let d = ft.vars.get(v).cloned().unwrap_or_else(Descr::any);
                    out.push_str(&format!(
                        ";     blk{} Return Var({})    :: {}\n",
                        bid, v.0, d
                    ));
                }
                Term::Halt(v) => {
                    let d = ft.vars.get(v).cloned().unwrap_or_else(Descr::any);
                    out.push_str(&format!(
                        ";     blk{} Halt Var({})      :: {}\n",
                        bid, v.0, d
                    ));
                }
                Term::TailCall { callee, args, .. } => {
                    let arg_descrs: Vec<Descr> = args
                        .iter()
                        .map(|av| ft.vars.get(av).cloned().unwrap_or_else(Descr::any))
                        .collect();
                    let arg_vars: Vec<String> =
                        args.iter().map(|v| format!("Var({})", v.0)).collect();
                    out.push_str(&format!(
                        ";     blk{} TailCall {}#{}({})\n",
                        bid,
                        fn_name(*callee),
                        callee.0,
                        arg_vars.join(", ")
                    ));
                    out.push_str(&format!(
                        ";              callee_key={}\n",
                        descrs_str(&arg_descrs)
                    ));
                }
                Term::Call {
                    callee,
                    args,
                    continuation,
                } => {
                    let arg_descrs: Vec<Descr> = args
                        .iter()
                        .map(|av| ft.vars.get(av).cloned().unwrap_or_else(Descr::any))
                        .collect();
                    let arg_vars: Vec<String> =
                        args.iter().map(|v| format!("Var({})", v.0)).collect();
                    let cap_vars: Vec<String> = continuation
                        .captured
                        .iter()
                        .map(|v| format!("Var({})", v.0))
                        .collect();
                    let ck = cont_input_key(b, continuation, ft, m, t);
                    out.push_str(&format!(
                        ";     blk{} Call {}#{}({})\n",
                        bid,
                        fn_name(*callee),
                        callee.0,
                        arg_vars.join(", ")
                    ));
                    out.push_str(&format!(
                        ";              callee_key={}\n",
                        descrs_str(&arg_descrs)
                    ));
                    out.push_str(&format!(
                        ";              cont {}#{} captured=[{}]\n",
                        fn_name(continuation.fn_id),
                        continuation.fn_id.0,
                        cap_vars.join(", ")
                    ));
                    out.push_str(&format!(";              cont_key={}\n", descrs_str(&ck)));
                }
                Term::CallClosure {
                    closure,
                    args,
                    continuation,
                } => {
                    let arg_vars: Vec<String> =
                        args.iter().map(|v| format!("Var({})", v.0)).collect();
                    let cap_vars: Vec<String> = continuation
                        .captured
                        .iter()
                        .map(|v| format!("Var({})", v.0))
                        .collect();
                    let ck = cont_input_key(b, continuation, ft, m, t);
                    let target = ft.fn_constants.get(closure).copied();
                    let target_str = match target {
                        Some(fid) => format!(" [resolved={}#{}]", fn_name(fid), fid.0),
                        None => String::new(),
                    };
                    out.push_str(&format!(
                        ";     blk{} CallClosure Var({})({}){}\n",
                        bid,
                        closure.0,
                        arg_vars.join(", "),
                        target_str
                    ));
                    out.push_str(&format!(
                        ";              cont {}#{} captured=[{}]\n",
                        fn_name(continuation.fn_id),
                        continuation.fn_id.0,
                        cap_vars.join(", ")
                    ));
                    out.push_str(&format!(";              cont_key={}\n", descrs_str(&ck)));
                }
                Term::TailCallClosure { closure, args } => {
                    let arg_vars: Vec<String> =
                        args.iter().map(|v| format!("Var({})", v.0)).collect();
                    let target = ft.fn_constants.get(closure).copied();
                    let target_str = match target {
                        Some(fid) => format!(" [resolved={}#{}]", fn_name(fid), fid.0),
                        None => String::new(),
                    };
                    out.push_str(&format!(
                        ";     blk{} TailCallClosure Var({})({}){}\n",
                        bid,
                        closure.0,
                        arg_vars.join(", "),
                        target_str
                    ));
                }
                Term::Receive { continuation } => {
                    let cap_vars: Vec<String> = continuation
                        .captured
                        .iter()
                        .map(|v| format!("Var({})", v.0))
                        .collect();
                    let ck = cont_input_key(b, continuation, ft, m, t);
                    out.push_str(&format!(
                        ";     blk{} Receive cont {}#{} captured=[{}]\n",
                        bid,
                        fn_name(continuation.fn_id),
                        continuation.fn_id.0,
                        cap_vars.join(", ")
                    ));
                    out.push_str(&format!(";              cont_key={}\n", descrs_str(&ck)));
                }
                Term::Goto(target, args) => {
                    let arg_vars: Vec<String> =
                        args.iter().map(|v| format!("Var({})", v.0)).collect();
                    out.push_str(&format!(
                        ";     blk{} Goto blk{}({})\n",
                        bid,
                        target.0,
                        arg_vars.join(", ")
                    ));
                }
                Term::If(cond, t_blk, e_blk) => {
                    out.push_str(&format!(
                        ";     blk{} If Var({}) ? blk{} : blk{}\n",
                        bid, cond.0, t_blk.0, e_blk.0
                    ));
                }
            }
        }
        out.push('\n');
    }
    out
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
        for f in fns {
            mb.add_fn(f);
        }
        mb.build()
    }

    /// fz-pky.2 — test helper. Returns "the most narrow registered
    /// spec for fn at index i, or an ad-hoc any-key view if unregistered."
    /// Replaces the legacy `mt[i]` access; the underlying by_fn_idx
    /// field has been retired.
    fn fn_view(m: &Module, mt: &ModuleTypes, i: usize) -> FnTypes {
        let fid = m.fns[i].id;
        if let Some(ft) = mt.any_spec_for(fid) {
            return ft.clone();
        }
        // Unreachable fn — type ad-hoc under all-any.
        let n_params = m.fns[i].block(m.fns[i].entry).params.len();
        let any_key: Vec<Descr> = vec![Descr::any(); n_params];
        type_fn(&m.fns[i], m, Some(&any_key))
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
        assert!(
            fn_view(&m, &mt, 0)
                .vars
                .get(&v)
                .unwrap()
                .is_equiv(&Descr::int_lit(42))
        );
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
        let sum_t = fn_view(&m, &mt, 0).vars.get(&sum).cloned().unwrap();
        assert!(
            sum_t.is_equiv(&Descr::int().union(&Descr::float())),
            "got {}",
            sum_t
        );
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
        let lt = fn_view(&m, &mt, 0).vars.get(&l).cloned().unwrap();
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
        let join_t = fn_view(&m, &mt, 0).vars.get(&joined).cloned().unwrap();
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
        let f0_t = fn_view(&m, &mt, 0).vars.get(&f0).cloned().unwrap();
        assert!(
            f0_t.is_subtype(&Descr::int_lit(1)) && Descr::int_lit(1).is_subtype(&f0_t),
            "field 0 should be int_lit(1), got {}",
            f0_t
        );
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
        let h_t = fn_view(&m, &mt, 0).vars.get(&h).cloned().unwrap();
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
        let ft = fn_view(&m, &mt, 0);
        let then_env = ft.block_envs.get(&then_b).unwrap();
        let l_then = then_env.get(&l).cloned().unwrap();
        assert!(
            l_then.is_subtype(&Descr::nil()) && Descr::nil().is_subtype(&l_then),
            "l in then-branch should be nil: {}",
            l_then
        );

        // In else_b's entry env, l should be narrowed to list_top (no nil).
        let else_env = ft.block_envs.get(&else_b).unwrap();
        let l_else = else_env.get(&l).cloned().unwrap();
        // Subtype of list_of(any) (loosely: at least the list portion).
        assert!(
            l_else.is_subtype(&Descr::list_of(Descr::any())),
            "l in else-branch should be list-shaped: {}",
            l_else
        );
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

        let ft = fn_view(&m, &mt, 0);
        let then_env = ft.block_envs.get(&then_b).unwrap();
        let x_then = then_env.get(&x).cloned().unwrap();
        assert!(
            x_then.is_subtype(&Descr::int_lit(0)) && Descr::int_lit(0).is_subtype(&x_then),
            "x in then-branch should be int_lit(0): {}",
            x_then
        );
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
        let p00_t = fn_view(&m, &mt, 0).vars.get(&p00).cloned().unwrap();
        assert!(
            p00_t.is_equiv(&Descr::int_lit(7)),
            "outer.0.0 should be int_lit(7), got {}",
            p00_t
        );
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
        assert_eq!(
            diags.len(),
            2,
            "expected two unreachable arms, got {:?}",
            diags
        );
        assert!(
            diags
                .iter()
                .all(|d| d.code == crate::diag::codes::TYPE_UNREACHABLE_ARM)
        );
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
            diags
                .iter()
                .any(|d| d.notes.iter().any(|n| n.contains(&needle))),
            "expected dead_b (bb{}) flagged, got {:?}",
            dead_b.0,
            diags
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
        assert!(
            err.contains("11.24.5"),
            "expected ticket reference, got: {}",
            err
        );
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
        let got_t = fn_view(&m, &mt, 0).vars.get(&got).cloned().unwrap();
        // The map_field_lookup contributes int_lit(42); plus the implicit "may be absent"
        // it can also be any|nil for open-shape semantics. We assert the int_lit(42)
        // is a subtype of the result.
        assert!(
            Descr::int_lit(42).is_subtype(&got_t),
            "map[k] should include the bound value: {}",
            got_t
        );
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
        let type_note = d
            .notes
            .iter()
            .find(|n| n.contains("has type"))
            .expect("expected a 'has type' note");
        assert!(
            type_note.contains('`'),
            "type note should backtick-quote the rendered type, got {:?}",
            type_note
        );
        // Second note: the narrowing that's uninhabited.
        let narrow_note = d
            .notes
            .iter()
            .find(|n| n.contains("uninhabited"))
            .expect("expected an 'uninhabited' note");
        assert!(
            narrow_note.contains("would need"),
            "narrow note should mention the would-need type, got {:?}",
            narrow_note
        );
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
        mb.set_terminator(
            mentry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![v],
                is_back_edge: false,
            },
        );

        let m = build_module(vec![cb.build(), mb.build()]);
        let mt = type_module(&m);
        // `id`'s entry param x should narrow to int_lit(42).
        let xt = fn_view(&m, &mt, 0).vars.get(&x).cloned().unwrap();
        assert!(
            xt.is_equiv(&Descr::int_lit(42)),
            "x should narrow to int_lit(42), got {}",
            xt
        );
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
        a.set_terminator(
            aentry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![one],
                is_back_edge: false,
            },
        );

        // caller2: TailCall id(:atom7)
        let mut bb = FnBuilder::new(FnId(2), "b");
        let bentry = bb.block(vec![]);
        let ok = bb.let_(bentry, Prim::Const(Const::Atom(7)));
        bb.set_terminator(
            bentry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![ok],
                is_back_edge: false,
            },
        );

        let m = build_module(vec![cb.build(), a.build(), bb.build()]);
        let mt = type_module(&m);
        let xt = fn_view(&m, &mt, 0).vars.get(&x).cloned().unwrap();
        // x should accept both int_lit(1) and the atom — the union.
        assert!(
            Descr::int_lit(1).is_subtype(&xt),
            "x should accept int_lit(1), got {}",
            xt
        );
        // Cross-axis: the atom side should be present too. Probe via
        // intersection — the int axis alone should NOT cover all of xt.
        assert!(
            !xt.is_subtype(&Descr::int()),
            "x should also include atom side, got {}",
            xt
        );
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
        let nt = fn_view(&m, &mt, 0).vars.get(&n).cloned().unwrap();
        assert!(
            nt.is_equiv(&Descr::any()),
            "worker's n must stay at any (no direct callers), got {}",
            nt
        );
    }

    #[test]
    fn closure_target_with_direct_caller_narrows_by_fn_idx_and_drops_unused_any_key() {
        // fz-ul4.29.3 / .29.10.3: a fn that's both a MakeClosure target
        // and called directly with a typed arg gets its by_fn_idx
        // narrowed by the visible direct caller. Post-.29.10.3, the
        // unused closure-bound `_cl` is detected as fully resolvable
        // (no invocation), the MakeClosure any-key registration is
        // suppressed, and .29.12.6 drops worker's any-key.
        let mut wb = FnBuilder::new(FnId(0), "worker");
        let n = wb.fresh_var();
        let wentry = wb.block(vec![n]);
        wb.set_terminator(wentry, Term::Return(n));

        let mut mb = FnBuilder::new(FnId(1), "main");
        let mentry = mb.block(vec![]);
        let _cl = mb.let_(mentry, Prim::MakeClosure(FnId(0), vec![]));
        let lit = mb.let_(mentry, Prim::Const(Const::Int(42)));
        mb.set_terminator(
            mentry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![lit],
                is_back_edge: false,
            },
        );

        let m = build_module(vec![wb.build(), mb.build()]);
        let mt = type_module(&m);
        // by_fn_idx for worker: n narrowed to the direct caller's int.
        let nt = fn_view(&m, &mt, 0).vars.get(&n).cloned().unwrap();
        assert!(
            nt.is_subtype(&Descr::int()),
            "worker's n in by_fn_idx must narrow to int (visible caller), got {}",
            nt
        );
        // any-key dropped: no callsite (direct or indirect) queries
        // worker with [any].
        assert!(
            mt.spec(FnId(0), &[Descr::any()]).is_none(),
            "worker's any-key must be dropped — only narrow [int_lit(42)] callsite exists; \
             specs: {:?}",
            mt.specs
                .keys()
                .filter(|(fid, _)| *fid == FnId(0))
                .collect::<Vec<_>>()
        );
    }

    // ----- fz-ul4.29.1: per-callsite specialization map -----

    #[test]
    fn entry_points_keep_any_key_callees_with_typed_callsites_drop() {
        // fz-ul4.29.12.6 — any-keys are pruned when every callsite has
        // typed coverage. `main` is entry-point-like (no IR caller) and
        // keeps its any-key. `add1` is only called from main with
        // `[int_lit(41)]`; its any-key body is dead → dropped.
        let mut a = FnBuilder::new(FnId(0), "add1");
        let n = a.fresh_var();
        let aentry = a.block(vec![n]);
        let one = a.let_(aentry, Prim::Const(Const::Int(1)));
        let sum = a.let_(aentry, Prim::BinOp(BinOp::Add, n, one));
        a.set_terminator(aentry, Term::Return(sum));

        let mut b = FnBuilder::new(FnId(1), "main");
        let bentry = b.block(vec![]);
        let lit = b.let_(bentry, Prim::Const(Const::Int(41)));
        b.set_terminator(
            bentry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![lit],
                is_back_edge: false,
            },
        );

        let m = build_module(vec![a.build(), b.build()]);
        let mt = type_module(&m);

        let main_any = mt.spec(FnId(1), &[]);
        assert!(
            main_any.is_some(),
            "main (entry-point) must keep its any-key"
        );

        let add1_any = mt.spec(FnId(0), &[Descr::any()]);
        assert!(
            add1_any.is_none(),
            "add1's any-key is dead (only caller passes int_lit(41)) → dropped"
        );
        let add1_narrow = mt.spec(FnId(0), &[Descr::int_lit(41)]);
        assert!(
            add1_narrow.is_some(),
            "add1 must have its narrow callsite-driven spec"
        );
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
        b.set_terminator(
            bentry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![lit],
                is_back_edge: false,
            },
        );

        let m = build_module(vec![a.build(), b.build()]);
        let mt = type_module(&m);

        // The callsite passes `int_lit(41)`, which is a subtype of int. The
        // spec key carries exactly that Descr.
        let int41 = Descr::int_lit(41);
        let narrow = mt.spec(FnId(0), std::slice::from_ref(&int41));
        assert!(
            narrow.is_some(),
            "add1 must have a specialization keyed on [int_lit(41)]; \
             specs keys present: {:?}",
            mt.specs.keys().filter(|(fid, _)| *fid == FnId(0)).count()
        );
        // The narrowed specialization's `n` should reflect the callsite Descr.
        let nt = narrow.unwrap().vars.get(&n).cloned().unwrap();
        assert!(
            nt.is_equiv(&int41),
            "add1's narrow spec must type n as int_lit(41), got {}",
            nt
        );
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
        b.set_terminator(
            bentry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![lit],
                is_back_edge: false,
            },
        );

        let m = build_module(vec![a.build(), b.build()]);
        let mt = type_module(&m);

        assert_eq!(mt.specs.len(), 2);
        // Legacy view: index 0 → id's narrowed FnTypes.
        let id_x = fn_view(&m, &mt, 0).vars.get(&x).cloned().unwrap();
        assert!(
            id_x.is_subtype(&Descr::int()),
            "id's x must be narrowed to int via callsite, got {}",
            id_x
        );
    }

    // ---- fz-ul4.29.12.1 helper tests ----

    fn pipeline(src: &str) -> (Module, ModuleTypes) {
        let toks = crate::lexer::Lexer::new(src).tokenize().expect("lex");
        let prog = crate::parser::Parser::new(toks)
            .parse_program()
            .expect("parse");
        let prog = crate::resolve::flatten_modules(prog).expect("flatten");
        let ir = crate::ir_lower::lower_program(&prog).expect("lower");
        let mt = type_module(&ir);
        (ir, mt)
    }

    /// fz-2yw.1 — recursive sum's effective return must be the LFP
    /// (`int`, joined from base case 0 plus recursive case h + sum(t))
    /// — NOT just the base case (0) which is what cycle-cut would give.
    #[test]
    fn effective_return_lfp_for_recursive_sum() {
        let (m, mt) = pipeline(
            r#"
fn sum([]), do: 0
fn sum([h | t]), do: h + sum(t)
fn main(), do: print(sum([1, 2, 3, 4, 5]))
"#,
        );
        let returns = mt.effective_returns.clone();
        let sum_fn = m.fns.iter().find(|f| f.name == "sum").unwrap();
        // At least one of sum's specs has a non-trivial return.
        let any_int = returns
            .iter()
            .any(|((fid, _), d)| *fid == sum_fn.id && d.is_subtype(&Descr::int()) && !d.is_empty());
        assert!(
            any_int,
            "expected at least one sum spec with return ⊆ int, got: {:?}",
            returns
                .iter()
                .filter(|((fid, _), _)| *fid == sum_fn.id)
                .collect::<Vec<_>>()
        );
        // CRUCIAL: no spec should claim return = singleton 0 (the
        // base case alone). That would mean cycle-cut leaked through.
        for ((fid, _), d) in &returns {
            if *fid != sum_fn.id {
                continue;
            }
            assert!(
                !d.is_equiv(&Descr::int_lit(0)),
                "sum spec return must NOT be just int_lit(0); LFP should \
                 lift recursive contribution. Got: {}",
                d
            );
        }
    }

    /// fz-vw4.5a — when every closure-dispatch site resolves via
    /// fn_constants (or there are no closures at all), the
    /// opaque-consumer arity set is empty. Under step 5c this means
    /// MakeClosure-side any-key registration can be skipped for the
    /// fixture's closure targets.
    #[test]
    fn opaque_consumer_arities_empty_when_no_opaque_dispatch() {
        let (m, mt) = pipeline(
            r#"
fn add1(n), do: n + 1
fn main(), do: print(add1(40) + 2)
"#,
        );
        let arities = opaque_consumer_arities(&m, &mt.specs);
        assert!(
            arities.is_empty(),
            "expected no opaque consumers (only direct calls), got {:?}",
            arities
        );
    }

    /// fz-vw4.5a — when a closure flows through Receive (message from
    /// an unknown sender), invoking it produces an unresolved
    /// TailCallClosure. The analysis must surface its arity. Built
    /// directly in IR since fz lacks a from-message lambda invocation
    /// surface syntax.
    #[test]
    fn opaque_consumer_arities_picks_up_receive_dispatched_closure() {
        // Build:
        //   fn lam(x), do: x       (FnId 0, arity 1)
        //   fn dispatcher() do
        //     receive(); cont k_recv(f) { TailCallClosure(f, [const(7)]) }
        //   end
        //   fn main(): TailCall dispatcher
        let mut lam = FnBuilder::new(FnId(0), "lam");
        let x = lam.fresh_var();
        let le = lam.block(vec![x]);
        lam.set_terminator(le, Term::Return(x));

        let mut k_recv = FnBuilder::new(FnId(1), "k_recv");
        let f = k_recv.fresh_var();
        let kre = k_recv.block(vec![f]);
        let seven = k_recv.let_(kre, Prim::Const(Const::Int(7)));
        k_recv.set_terminator(
            kre,
            Term::TailCallClosure {
                closure: f,
                args: vec![seven],
            },
        );

        let mut disp = FnBuilder::new(FnId(2), "dispatcher");
        let de = disp.block(vec![]);
        disp.set_terminator(
            de,
            Term::Receive {
                continuation: crate::fz_ir::Cont {
                    fn_id: FnId(1),
                    captured: vec![],
                },
            },
        );

        let mut main_b = FnBuilder::new(FnId(3), "main");
        let me = main_b.block(vec![]);
        main_b.set_terminator(
            me,
            Term::TailCall {
                callee: FnId(2),
                args: vec![],
                is_back_edge: false,
            },
        );

        let m = build_module(vec![
            lam.build(),
            k_recv.build(),
            disp.build(),
            main_b.build(),
        ]);
        let mt = type_module(&m);
        let arities = opaque_consumer_arities(&m, &mt.specs);
        assert!(
            arities.contains(&1),
            "expected arity-1 opaque consumer from receive-dispatched closure, got {:?}",
            arities
        );
    }

    /// Helper output for a Call-site Cont must match a key the typer
    /// registered in `module_types.specs` under `cont.fn_id`. This is
    /// the load-bearing invariant for fz-ul4.29.12.1's SpecRegistry
    /// resolve: if it ever fails, the resolve will panic.
    #[test]
    fn cont_input_key_matches_a_registered_spec_for_call() {
        let (m, mt) = pipeline(
            r#"
fn id(x), do: x
fn main() do
  y = id(7)
  print(y)
end
"#,
        );
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
                    mt.specs
                        .iter()
                        .filter(|((f, _), _)| *f == continuation.fn_id)
                        .map(|((_, k), _)| k.clone())
                        .collect::<Vec<_>>(),
                );
                found_any = true;
            }
        }
        assert!(
            found_any,
            "test premise: main should contain a Call with a Cont"
        );
    }

    /// Direct-Call slot 0 reflects the callee's narrowed return Descr,
    /// not `any` — confirms .29.12.1 actually drives narrow Cont SpecId
    /// resolution at call-sites where the typer has specialized the
    /// callee.
    #[test]
    fn cont_slot0_narrows_to_callee_return_for_direct_call() {
        let (m, mt) = pipeline(
            r#"
fn add1(n), do: n + 1
fn main(), do: print(add1(40) + 2)
"#,
        );
        let main = m.fns.iter().find(|f| f.name == "main").unwrap();
        let main_ft = mt.specs.get(&(main.id, vec![])).unwrap();
        let mut narrow_found = false;
        for blk in &main.blocks {
            if let Term::Call { .. } = &blk.terminator {
                let s0 = cont_slot0_descr(blk, main_ft, &m, &mt);
                // add1's typer-specialized return for arg int_lit(40) is
                // a strict subtype of `int` — and crucially narrower than
                // `any`.
                assert!(
                    !s0.is_equiv(&Descr::any()),
                    "slot 0 must narrow below any when callee is specialized, got {}",
                    s0
                );
                assert!(
                    s0.is_subtype(&Descr::int()),
                    "slot 0 should be int-typed, got {}",
                    s0
                );
                narrow_found = true;
            }
        }
        assert!(narrow_found, "test premise: main should have a direct Call");
    }

    /// fz-ul4.29.10 — when a top-level fn is passed as a closure value
    /// (`apply2(double, …)`), `ir_lower` synthesizes
    /// `MakeClosure(double, [])`. .29.10.1 propagates `fn_constants[f]
    /// = double` into apply2's spec; .29.10.2 registers double's narrow
    /// spec for the typed arg from apply2's CallClosure; .29.10.3
    /// suppresses the MakeClosure-side any-key registration (because
    /// main's closure-var is fully resolvable) and rewrites apply2's
    /// `CallClosure` into a direct `Call(double, …)`. Net result:
    /// double's any-key is dropped.
    #[test]
    fn higher_order_callee_drops_any_key_for_fn_as_value() {
        let (m, mt) = pipeline(
            r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f(x)
fn main() do
  print(apply2(double, 21))
end
"#,
        );
        let double = m.fns.iter().find(|f| f.name == "double").unwrap();
        let any_key: Vec<Descr> = vec![Descr::any(); 1];
        assert!(
            !mt.specs.contains_key(&(double.id, any_key)),
            "expected double's any-key to be dropped post-.29.10.3; \
             registered specs for double: {:?}",
            mt.specs
                .keys()
                .filter(|(fid, _)| *fid == double.id)
                .collect::<Vec<_>>()
        );
    }

    /// fz-ul4.29.12.6 — a fn whose every IR callsite has typed coverage
    /// should NOT have its any-key spec registered in `module_types.specs`.
    /// `add` here is only called directly with `[int_lit(1), int_lit(2)]`;
    /// no callsite queries with `[any, any]`, so the any-key body is dead.
    #[test]
    fn fn_with_only_typed_callsites_drops_any_key() {
        let (m, mt) = pipeline(
            r#"
fn add(a, b), do: a + b
fn main(), do: print(add(1, 2))
"#,
        );
        let add = m.fns.iter().find(|f| f.name == "add").unwrap();
        let any_key: Vec<Descr> = vec![Descr::any(); 2];
        assert!(
            !mt.specs.contains_key(&(add.id, any_key.clone())),
            "expected add's any-key to be dropped (no [any, any] callsite); \
             registered specs for add: {:?}",
            mt.specs
                .keys()
                .filter(|(fid, _)| *fid == add.id)
                .collect::<Vec<_>>()
        );
    }

    /// fz-ul4.29.12.6 — an entry-point-like fn (no IR caller) must keep
    /// its any-key. `main` here has zero callsites in the module; the
    /// runtime `Runtime::spawn(main_fn_id)` path queries via FnId.0 →
    /// SpecId.0, so dropping main's any-key would break runtime entry.
    #[test]
    fn entry_point_fn_keeps_any_key() {
        let (m, mt) = pipeline(
            r#"
fn main(), do: print(42)
"#,
        );
        let main = m.fns.iter().find(|f| f.name == "main").unwrap();
        let any_key: Vec<Descr> = vec![];
        assert!(
            mt.specs.contains_key(&(main.id, any_key)),
            "main must keep its any-key (entry-point)"
        );
    }

    /// fz-ul4.29.12.5 — a `Term::Receive` cont with a typed capture must
    /// have a narrow spec registered (slot 0 = `any` per the opaque-
    /// sender rule, slot 1+ narrowed from the caller's env). .29.12.1's
    /// `emit_receive` resolves through subsumption against this spec to
    /// pick a narrow cont SpecId for `fz_alloc_frame`; this test pins
    /// the typer precondition.
    #[test]
    fn receive_cont_with_typed_capture_gets_narrow_spec() {
        let (m, mt) = pipeline(
            r#"
fn waiter(tag) do
  m = receive()
  print(m)
  tag
end
fn main() do
  waiter(7)
end
"#,
        );
        // The receive's cont fn is synthesized by ir_lower's CPS split.
        // Find any cont fn referenced from a Term::Receive in waiter.
        let waiter = m.fns.iter().find(|f| f.name == "waiter").unwrap();
        let mut cont_fn_ids: Vec<FnId> = Vec::new();
        for b in &waiter.blocks {
            if let Term::Receive { continuation } = &b.terminator {
                cont_fn_ids.push(continuation.fn_id);
            }
        }
        assert!(
            !cont_fn_ids.is_empty(),
            "test premise: waiter has a Receive"
        );
        // At least one of those cont fns has a narrow spec where slot 1
        // (= the captured `tag`) is `int_lit(7)` (typed via the call
        // `waiter(7)`).
        let mut any_narrow = false;
        for cont_id in cont_fn_ids {
            for (fid, key) in mt.specs.keys() {
                if *fid != cont_id {
                    continue;
                }
                if key.is_empty() {
                    continue;
                }
                // slot 0 must be `any` (receive opaque).
                if !key[0].is_equiv(&Descr::any()) {
                    continue;
                }
                // slot 1+ must include at least one int-typed entry
                // (the propagated `tag` capture).
                if key
                    .iter()
                    .skip(1)
                    .any(|d| d.is_subtype(&Descr::int()) && !d.is_equiv(&Descr::any()))
                {
                    any_narrow = true;
                }
            }
        }
        assert!(
            any_narrow,
            "expected ≥1 narrow Receive-cont spec with typed capture; \
             specs for cont fns: {:?}",
            mt.specs
                .iter()
                .filter(|((fid, _), _)| m
                    .fns
                    .iter()
                    .any(|f| f.id == *fid && f.name.contains("waiter")))
                .map(|((fid, k), _)| (*fid, k.clone()))
                .collect::<Vec<_>>()
        );
    }

    /// fz-ul4.29.12.4 — spawn-with-captures registers a narrow spec for
    /// `fz_spawn_thunk` keyed by the spawned closure's Descr. .29.12.2's
    /// typed-stub keying then routes spawn dispatch through that narrow
    /// stub (verified by the spawn_with_captures fixture across jit /
    /// interp / aot). This test asserts the typer prerequisite.
    #[test]
    fn spawn_with_captures_registers_narrow_fz_spawn_thunk_spec() {
        let (m, mt) = pipeline(
            r#"
fn parent(tag) do
  spawn(fn () -> send(1, tag))
  receive()
end
fn main() do
  print(parent(99))
end
"#,
        );
        let thunk = m.fns.iter().find(|f| f.name == "fz_spawn_thunk").unwrap();
        let narrow: Vec<&Vec<Descr>> = mt
            .specs
            .iter()
            .filter(|((fid, _), _)| *fid == thunk.id)
            .map(|((_, k), _)| k)
            .filter(|k| !k.iter().all(|d| d.is_equiv(&Descr::any())))
            .collect();
        assert!(
            !narrow.is_empty(),
            "expected ≥1 narrow fz_spawn_thunk spec, got 0 (only any-key)"
        );
    }

    /// fz-ul4.29.12.2 — two MakeClosure sites of the same lambda with
    /// different capture Descrs must register two distinct narrow specs
    /// for the lambda. Codegen keys typed closure stubs off these
    /// SpecIds, so this is the load-bearing precondition for typed
    /// closure dispatch.
    #[test]
    fn make_closure_with_distinct_captures_registers_distinct_specs() {
        // Two top-level fns each return a closure that captures a
        // value of a different type. Both target the *same* lambda
        // (well, two different lambdas — adjust below). To force "same
        // lambda, different captures", we use a curried-style helper.
        let (m, mt) = pipeline(
            r#"
fn add_to(x), do: fn (y) -> x + y
fn main() do
  f = add_to(7)
  g = add_to(3.5)
  print(f(1))
  print(g(2.0))
end
"#,
        );
        // Find the lambda FnId — it's the one fn whose name starts
        // with "lambda_".
        let lam = m
            .fns
            .iter()
            .find(|f| f.name.starts_with("lambda_"))
            .expect("expected a lambda fn");
        let registered_keys: Vec<&Vec<Descr>> = mt
            .specs
            .iter()
            .filter(|((fid, _), _)| *fid == lam.id)
            .map(|((_, k), _)| k)
            .collect();
        // fz-vw4.2: any-key is no longer unconditionally registered for
        // every fn — it's only present when reachability demands. The
        // two narrow specs (one per distinct capture Descr) are what
        // codegen actually keys off; that's what this test guards.
        let narrow: Vec<&Vec<Descr>> = registered_keys
            .iter()
            .filter(|k| !k.iter().all(|d| d.is_equiv(&Descr::any())))
            .copied()
            .collect();
        assert!(
            narrow.len() >= 2,
            "expected ≥2 narrow specs for the lambda, got {}: {:?}",
            narrow.len(),
            narrow
        );
    }

    /// Helper's slot 0 for CallClosure / Receive is `Descr::any()` per
    /// the typer's opaque-callee rule.
    #[test]
    fn cont_slot0_is_any_for_call_closure() {
        let (m, mt) = pipeline(
            r#"
fn apply(f, x) do
  r = f(x)
  r + 1
end
fn main() do
  inc = fn (n) -> n + 1
  z = apply(inc, 3)
  print(z)
end
"#,
        );
        let apply_fn = m.fns.iter().find(|f| f.name == "apply").unwrap();
        let caller_ft = mt
            .specs
            .iter()
            .find(|((id, _), _)| *id == apply_fn.id)
            .map(|((_, _), ft)| ft)
            .expect("apply should have at least one spec");
        let mut saw_cc = false;
        for blk in &apply_fn.blocks {
            if matches!(&blk.terminator, Term::CallClosure { .. }) {
                let s0 = cont_slot0_descr(blk, caller_ft, &m, &mt);
                assert!(
                    s0.is_equiv(&Descr::any()),
                    "CallClosure slot 0 must be `any`, got {}",
                    s0
                );
                saw_cc = true;
            }
        }
        assert!(saw_cc, "test premise: apply should have a CallClosure");
    }

    // ---- fz-ul4.29.10.1 — fn_constants side-channel ----

    /// A zero-capture `MakeClosure(F, [])` (synthesized by ir_lower when
    /// a bare top-level fn name is used as a value) populates
    /// `fn_constants[v] = F` on the Let-bound var.
    #[test]
    fn fn_constant_from_makeclosure_zero_captures() {
        let (m, mt) = pipeline(
            r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f(x)
fn main() do
  print(apply2(double, 21))
end
"#,
        );
        let main = m.fns.iter().find(|f| f.name == "main").unwrap();
        let double = m.fns.iter().find(|f| f.name == "double").unwrap();
        // Find the Var bound to MakeClosure(double, []) in main.
        let mut closure_var: Option<Var> = None;
        for b in &main.blocks {
            for stmt in &b.stmts {
                let Stmt::Let(v, prim) = stmt;
                if let Prim::MakeClosure(fid, captured) = prim
                    && *fid == double.id
                    && captured.is_empty()
                {
                    closure_var = Some(*v);
                }
            }
        }
        let v = closure_var.expect("test premise: main has MakeClosure(double, [])");
        let main_ft = mt
            .specs
            .iter()
            .find(|((id, _), _)| *id == main.id)
            .map(|(_, ft)| ft)
            .expect("main spec exists");
        assert_eq!(
            main_ft.fn_constants.get(&v).copied(),
            Some(double.id),
            "zero-capture MakeClosure should populate fn_constants"
        );
    }

    /// A `MakeClosure` with captures is a real closure value, not a
    /// fn-as-value. No `fn_constants` entry.
    #[test]
    fn fn_constant_not_set_for_captures() {
        let (m, mt) = pipeline(
            r#"
fn main() do
  k = 7
  f = fn (n) -> n + k
  print(f(3))
end
"#,
        );
        let main = m.fns.iter().find(|f| f.name == "main").unwrap();
        let main_ft = mt
            .specs
            .iter()
            .find(|((id, _), _)| *id == main.id)
            .map(|(_, ft)| ft)
            .expect("main spec exists");
        // Find the Var bound to the MakeClosure (the synthesized lambda
        // has captures of [k]).
        let mut closure_var: Option<Var> = None;
        for b in &main.blocks {
            for stmt in &b.stmts {
                let Stmt::Let(v, prim) = stmt;
                if let Prim::MakeClosure(_, captured) = prim
                    && !captured.is_empty()
                {
                    closure_var = Some(*v);
                }
            }
        }
        let v = closure_var.expect("test premise: a captured-MakeClosure in main");
        assert!(
            !main_ft.fn_constants.contains_key(&v),
            "MakeClosure with captures must NOT set fn_constants"
        );
    }

    /// `apply2(double, 21)` — in apply2's specialized FnTypes, the
    /// `f` entry param has `fn_constants[f_param] = double.id`,
    /// propagated from main's callsite.
    #[test]
    fn fn_constant_propagates_via_direct_call() {
        let (m, mt) = pipeline(
            r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f(x)
fn main() do
  print(apply2(double, 21))
end
"#,
        );
        let apply2 = m.fns.iter().find(|f| f.name == "apply2").unwrap();
        let double = m.fns.iter().find(|f| f.name == "double").unwrap();
        let apply2_entry = apply2.block(apply2.entry);
        let f_param = apply2_entry.params[0]; // first param is `f`
        // Look at every spec of apply2 — at least one must carry the
        // propagated fn_constant.
        let mut saw_propagation = false;
        for ((fid, _), ft) in &mt.specs {
            if *fid != apply2.id {
                continue;
            }
            if ft.fn_constants.get(&f_param).copied() == Some(double.id) {
                saw_propagation = true;
            }
        }
        assert!(
            saw_propagation,
            "expected apply2's spec to carry fn_constants[f] = double; \
             specs for apply2: {:?}",
            mt.specs
                .iter()
                .filter(|((fid, _), _)| *fid == apply2.id)
                .map(|((_, k), ft)| (k.clone(), ft.fn_constants.clone()))
                .collect::<Vec<_>>()
        );
    }

    // ---- fz-ul4.29.10.2 — narrow F-spec from known-target CallClosure ----

    // ---- fz-ul4.29.10.3 — IR rewrite of known-target closures ----

    /// `rewrite_known_target_closures` replaces `Term::CallClosure(v, …)`
    /// with `Term::Call(F, …)` when every spec of the enclosing FnIr
    /// agrees that `fn_constants[v] = F`.
    #[test]
    fn closure_call_rewritten_to_direct_call() {
        let (mut m, mt) = pipeline(
            r#"
fn double(x), do: x * 2
fn apply_plus1(f, x) do
  r = f(x)
  r + 1
end
fn main() do
  print(apply_plus1(double, 21))
end
"#,
        );
        rewrite_known_target_closures(&mut m, &mt);
        let apply2 = m.fns.iter().find(|f| f.name == "apply_plus1").unwrap();
        let double_id = m.fns.iter().find(|f| f.name == "double").unwrap().id;
        let mut saw_direct = false;
        for b in &apply2.blocks {
            match &b.terminator {
                Term::Call { callee, .. } if *callee == double_id => {
                    saw_direct = true;
                }
                Term::CallClosure { .. } | Term::TailCallClosure { .. } => {
                    panic!("apply2 body still contains a closure-call after rewrite");
                }
                _ => {}
            }
        }
        assert!(
            saw_direct,
            "expected at least one direct Call(double, …) in apply2's body"
        );
    }

    /// Same rewrite for `Term::TailCallClosure → Term::TailCall`.
    #[test]
    fn tailcall_closure_variant_rewritten() {
        let (mut m, mt) = pipeline(
            r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f(x)
fn main() do
  apply2(double, 21)
end
"#,
        );
        rewrite_known_target_closures(&mut m, &mt);
        let apply2 = m.fns.iter().find(|f| f.name == "apply2").unwrap();
        let double_id = m.fns.iter().find(|f| f.name == "double").unwrap().id;
        let mut saw_direct = false;
        for b in &apply2.blocks {
            match &b.terminator {
                Term::TailCall { callee, .. } if *callee == double_id => {
                    saw_direct = true;
                }
                Term::Call { callee, .. } if *callee == double_id => {
                    saw_direct = true;
                }
                Term::CallClosure { .. } | Term::TailCallClosure { .. } => {
                    panic!("apply2 body still contains a closure-call after rewrite");
                }
                _ => {}
            }
        }
        assert!(
            saw_direct,
            "expected apply2 body to dispatch directly to double after rewrite"
        );
    }

    /// `apply2(double, 21)` — apply2's body has `CallClosure(f, [x])`.
    /// With `fn_constants[f] = double` propagated from main, the typer's
    /// queried-set walk should register `(double, [int_lit(21)])` as a
    /// narrow spec for double — alongside its any-key (which .29.10.3
    /// will drop). This guarantees a narrow spec exists for the IR
    /// rewrite to dispatch into.
    #[test]
    fn callclosure_with_fn_constant_registers_narrow_spec() {
        let (m, mt) = pipeline(
            r#"
fn double(x), do: x * 2
fn apply2(f, x), do: f(x)
fn main() do
  print(apply2(double, 21))
end
"#,
        );
        let double = m.fns.iter().find(|f| f.name == "double").unwrap();
        let mut saw_narrow = false;
        for (fid, key) in mt.specs.keys() {
            if *fid != double.id {
                continue;
            }
            if key.len() != 1 {
                continue;
            }
            if !key[0].is_equiv(&Descr::any()) && key[0].is_subtype(&Descr::int()) {
                saw_narrow = true;
            }
        }
        assert!(
            saw_narrow,
            "expected a narrow int-typed spec for double from \
             apply2's CallClosure with fn_constants[f] = double; \
             registered specs for double: {:?}",
            mt.specs
                .iter()
                .filter(|((fid, _), _)| *fid == double.id)
                .map(|((_, k), _)| k.clone())
                .collect::<Vec<_>>()
        );
    }

    // ---- fz-ul4.27.22.9 resolve_closure_return tests ----

    fn fid(n: u32) -> FnId {
        FnId(n)
    }

    #[test]
    fn resolve_closure_return_singleton_lookup_hits() {
        // closure_lit(F=7, []) with arg [int_lit(21)]; effective_returns has
        // (7, [int_lit(21)]) -> int. Helper returns Some(int).
        let descr = Descr::closure_lit(fid(7), vec![], 1);
        let mut er: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
        er.insert((fid(7), vec![Descr::int_lit(21)]), Descr::int());
        let r = resolve_closure_return(&descr, &er, &[Descr::int_lit(21)]);
        assert_eq!(r, Some(Descr::int()));
    }

    #[test]
    fn resolve_closure_return_singleton_miss_returns_none() {
        // Singleton with no matching effective_returns entry → None (defer).
        let descr = Descr::closure_lit(fid(7), vec![], 1);
        let er: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
        let r = resolve_closure_return(&descr, &er, &[Descr::int_lit(21)]);
        assert_eq!(r, None);
    }

    #[test]
    fn resolve_closure_return_singleton_with_captures() {
        // closure_lit(F=8, [int_lit(10), int_lit(20)]) — captures + arg form
        // the full body key.
        let descr = Descr::closure_lit(fid(8), vec![Descr::int_lit(10), Descr::int_lit(20)], 1);
        let mut er: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
        er.insert(
            (
                fid(8),
                vec![Descr::int_lit(10), Descr::int_lit(20), Descr::int_lit(12)],
            ),
            Descr::int_lit(42),
        );
        let r = resolve_closure_return(&descr, &er, &[Descr::int_lit(12)]);
        assert_eq!(r, Some(Descr::int_lit(42)));
    }

    #[test]
    fn resolve_closure_return_plain_arrow_uses_sig_ret() {
        // Lit-free arrow: ret comes straight from sig.ret (matches
        // arrow_join_return).
        let descr = Descr::arrow([Descr::any()], Descr::int());
        let er: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
        let r = resolve_closure_return(&descr, &er, &[Descr::int_lit(21)]);
        assert_eq!(r, Some(Descr::int()));
    }

    #[test]
    fn resolve_closure_return_union_of_singletons_joins() {
        // Two clauses: lit(7,[]) returning int, lit(8,[]) returning atom.
        // JOIN = int | atom.
        let a = Descr::closure_lit(fid(7), vec![], 1);
        let b = Descr::closure_lit(fid(8), vec![], 1);
        let descr = a.union(&b);
        assert_eq!(descr.funcs.len(), 2, "expect two clauses: {}", descr);
        let mut er: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
        er.insert((fid(7), vec![Descr::int_lit(21)]), Descr::int());
        er.insert((fid(8), vec![Descr::int_lit(21)]), Descr::atom_lit("ok"));
        let r = resolve_closure_return(&descr, &er, &[Descr::int_lit(21)]);
        let expected = Descr::int().union(&Descr::atom_lit("ok"));
        assert_eq!(r, Some(expected));
    }

    #[test]
    fn resolve_closure_return_union_one_miss_defers() {
        // Two clauses; one has a registered spec, the other doesn't. The
        // helper conservatively defers (returns None) so the typer's
        // fixpoint can re-try after the missing spec is registered.
        let a = Descr::closure_lit(fid(7), vec![], 1);
        let b = Descr::closure_lit(fid(8), vec![], 1);
        let descr = a.union(&b);
        let mut er: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
        er.insert((fid(7), vec![Descr::int_lit(21)]), Descr::int());
        // No entry for (8, _) → defer.
        let r = resolve_closure_return(&descr, &er, &[Descr::int_lit(21)]);
        assert_eq!(r, None);
    }

    #[test]
    fn resolve_closure_return_empty_funcs_is_any() {
        // Descr with no funcs at all: arrow_join_return-style any default.
        let descr = Descr::none();
        let er: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
        let r = resolve_closure_return(&descr, &er, &[]);
        assert_eq!(r, Some(Descr::any()));
    }

    #[test]
    fn resolve_closure_return_saturated_arrow_is_any() {
        // Descr::any() has funcs = [Conj::top()] — pos empty, no narrowing.
        let descr = Descr::any();
        let er: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
        let r = resolve_closure_return(&descr, &er, &[Descr::int_lit(21)]);
        assert_eq!(r, Some(Descr::any()));
    }

    #[test]
    fn narrow_for_cond_and_narrows_both_operands_in_then_branch() {
        use crate::fz_ir::{BinOp, Prim, Stmt, Var};
        // Simulate: if x == :ok && y == 1 do … end
        // cx = Eq(x, lit_ok), cy = Eq(y, lit_one), cand = And(cx, cy)
        let x = Var(0);
        let y = Var(1);
        let lit_ok = Var(2);
        let lit_one = Var(3);
        let cx = Var(4);
        let cy = Var(5);
        let cand = Var(6);

        let stmts = vec![
            Stmt::Let(cx, Prim::BinOp(BinOp::Eq, x, lit_ok)),
            Stmt::Let(cy, Prim::BinOp(BinOp::Eq, y, lit_one)),
            Stmt::Let(cand, Prim::BinOp(BinOp::And, cx, cy)),
        ];

        let mut env: HashMap<Var, Descr> = HashMap::new();
        env.insert(x, Descr::any());
        env.insert(y, Descr::any());
        // lit_ok and lit_one already have singleton types in env.
        env.insert(lit_ok, Descr::atom_lit("ok"));
        env.insert(lit_one, Descr::int_lit(1));
        env.insert(cx, Descr::bool_t());
        env.insert(cy, Descr::bool_t());
        env.insert(cand, Descr::bool_t());

        let (then_env, else_env) = narrow_for_cond(cand, &env, &stmts);

        // Then branch: x must be :ok and y must be 1.
        assert_eq!(
            then_env.get(&x).cloned().unwrap_or_else(Descr::any),
            Descr::atom_lit("ok"),
            "then: x should be narrowed to :ok"
        );
        assert_eq!(
            then_env.get(&y).cloned().unwrap_or_else(Descr::any),
            Descr::int_lit(1),
            "then: y should be narrowed to 1"
        );

        // Else branch: at least one failed — union of "x != :ok" and "y != 1".
        // Neither is fully pinned to the singleton.
        let x_else = else_env.get(&x).cloned().unwrap_or_else(Descr::any);
        let y_else = else_env.get(&y).cloned().unwrap_or_else(Descr::any);
        assert!(
            x_else != Descr::atom_lit("ok"),
            "else: x should not be pinned to :ok"
        );
        assert!(
            y_else != Descr::int_lit(1),
            "else: y should not be pinned to 1"
        );
    }
}
