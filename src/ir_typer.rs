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
    BinOp, Block, BlockId, Const, Cont, FnId, FnIr, Module, Prim, Stmt, Term, UnOp, Var, VecKindIr,
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
/// fz-qbg.1: purely structural call graph derived from terminator
/// shape + `Prim::MakeClosure` edges. Previously coupled to any-key
/// spec registration — that coupling silently regressed SCC analysis
/// whenever new fns were introduced mid-lowering (cps_split_call's
/// continuations, fz-duq's per-arm cont fns, fz-qbg.2's per-clause
/// body cont fns). The lower pass already does structural-only
/// graph building in `annotate_back_edges` (src/ir_lower.rs:615);
/// the typer now matches that discipline.
///
/// Closure call edges become continuation-only (the call's
/// continuation fn). The closure *target* isn't resolved here — it
/// was resolved via `fn_constants`, which required an any-key spec
/// that may not exist yet at graph-build time. Recursion through
/// closures (Y-combinator-style) gets a looser SCC; not a concern
/// for current fz code. If it becomes one, structural
/// over-approximation via `Prim::MakeClosure` edges (already
/// included here) covers the common case.
fn build_call_graph(m: &Module) -> HashMap<FnId, HashSet<FnId>> {
    let mut g: HashMap<FnId, HashSet<FnId>> = HashMap::new();
    for f in &m.fns {
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
                Term::CallClosure { continuation, .. } => {
                    edges.insert(continuation.fn_id);
                }
                Term::TailCallClosure { .. } => {}
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
/// `specs` is the per-callsite specialization map, keyed by
/// `(FnId, input-Descr-tuple)`. Each distinct argument-Descr signature
/// seen at any direct-call site produces a fresh FnTypes via
/// `type_fn(f, m, Some(&input_descrs))`. An any-key specialization
/// (`vec![Descr::any(); n_params]`) is registered for fns that are
/// closure-reachable, entry-seeded, or otherwise need the opaque-dispatch
/// fallback; direct-call-only fns have no any-key (see fz-ul4.29.12.6).
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
            // fz-ext.7: spawn emits Prim::Extern(fz_spawn/fz_spawn_opt).
            for stmt in &b.stmts {
                let Stmt::Let(_, prim) = stmt;
                let spawn_cv: Option<Var> = match prim {
                    Prim::Extern(eid, args)
                        if (args.len() == 1 || args.len() == 2)
                            && m.extern_idx
                                .get(eid)
                                .map(|&i| {
                                    m.externs[i].symbol == "fz_spawn"
                                        || m.externs[i].symbol == "fz_spawn_opt"
                                })
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

#[cfg(test)]
thread_local! {
    pub static TYPE_MODULE_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// fz-5j5.3 — type a module via one worklist over `(FnId, Vec<Descr>)`
/// specs. The worklist drives spec registration, body typing, and
/// effective-return propagation as a single unified data-flow LFP.
///
/// Two triggers add a spec back to the worklist:
///   1. The spec is freshly discovered (newly-emitted pending key).
///   2. A callee whose effective return this spec reads has *changed*
///      that return. Tracked via the `return_readers` reverse index
///      populated during walks at every cont-site slot-0 lookup.
///
/// `type_fn` is pure in `(FnIr, entry_key)`; once a spec's `FnTypes`
/// is computed, it's cached and reused across worklist visits — only
/// the walk + return-recompute re-run when triggered.
///
/// MakeClosure-side any-key registration is folded in as a separate
/// post-drain sweep (it depends on the converged `opaque_consumer_arities`,
/// a global computation). After the sweep enqueues any-keys for
/// opaque-consumed lambdas, the worklist re-drains; over-specialized
/// stale specs that the walks accumulate are pruned by a final
/// reachability sweep keyed off the converged effective_returns.
pub fn type_module(m: &Module) -> ModuleTypes {
    #[cfg(test)]
    TYPE_MODULE_CALLS.with(|c| c.set(c.get() + 1));

    let call_graph = build_call_graph(m);
    let mut sccs = tarjan_scc(&call_graph);
    sccs.reverse();
    let mut scc_of: HashMap<FnId, usize> = HashMap::new();
    let mut scc_members: HashMap<usize, std::collections::HashSet<FnId>> = HashMap::new();
    for (i, scc) in sccs.iter().enumerate() {
        let mset: std::collections::HashSet<FnId> = scc.iter().copied().collect();
        for fid in scc {
            scc_of.insert(*fid, i);
        }
        scc_members.insert(i, mset);
    }

    let mut specs: HashMap<(FnId, Vec<Descr>), FnTypes> = HashMap::new();
    let mut effective_returns: HashMap<(FnId, Vec<Descr>), Descr> = HashMap::new();
    let mut callsite_fn_consts: HashMap<(FnId, Vec<Descr>), Vec<Option<FnId>>> = HashMap::new();
    // (callee_key) → set of spec_keys whose walk read its effective_return
    // for cont slot-0. When the callee's return changes, every reader is
    // re-enqueued so its cont specs get re-registered against fresh slot-0.
    let mut return_readers: HashMap<(FnId, Vec<Descr>), std::collections::HashSet<(FnId, Vec<Descr>)>> =
        HashMap::new();
    // Per-spec visit count, drives SCC widening for recursive list-walks.
    let mut visit_count: HashMap<(FnId, Vec<Descr>), usize> = HashMap::new();

    let mut work: std::collections::VecDeque<(FnId, Vec<Descr>)> =
        entry_seeds(m).into_iter().collect();
    let mut in_work: std::collections::HashSet<(FnId, Vec<Descr>)> =
        work.iter().cloned().collect();

    process_worklist(
        m,
        &scc_of,
        &scc_members,
        &mut work,
        &mut in_work,
        &mut specs,
        &mut effective_returns,
        &mut callsite_fn_consts,
        &mut return_readers,
        &mut visit_count,
    );

    // MakeClosure-side any-key registration. Iterates because both
    // `opaque_consumer_arities` and `specs` grow monotonically as new
    // any-key bodies surface new unresolved CallClosure sites of new
    // arities. Loop terminates when a full sweep registers nothing.
    loop {
        let opaque_arities = opaque_consumer_arities(m, &specs);
        let snapshot: Vec<(FnId, Vec<Descr>)> = specs.keys().cloned().collect();
        let work_len_before = specs.len();
        for spec_key in snapshot {
            let (fid, _) = &spec_key;
            let Some(&j) = m.fn_idx.get(fid) else { continue };
            let caller_ft = specs.get(&spec_key).unwrap();
            sweep_makeclosure(
                &m.fns[j],
                caller_ft,
                m,
                &opaque_arities,
                &specs,
                &mut work,
                &mut in_work,
            );
        }
        process_worklist(
            m,
            &scc_of,
            &scc_members,
            &mut work,
            &mut in_work,
            &mut specs,
            &mut effective_returns,
            &mut callsite_fn_consts,
            &mut return_readers,
            &mut visit_count,
        );
        if specs.len() == work_len_before {
            break;
        }
    }

    if std::env::var("FZ_TYPER_DUMP").is_ok() {
        eprintln!("[TYPER] before sweep: {} specs", specs.len());
        let mut sorted: Vec<_> = specs.keys().cloned().collect();
        sorted.sort_by_key(|(f, _)| f.0);
        for k in &sorted {
            eprintln!("  fnid={} name={} key=[{}]", k.0.0,
                m.fn_idx.get(&k.0).map(|&j| m.fns[j].name.as_str()).unwrap_or("?"),
                k.1.iter().map(|d| format!("{}", d)).collect::<Vec<_>>().join(", "));
        }
    }
    // Final reachability sweep — the worklist accumulates stale
    // cont specs whose slot-0 was keyed by an old effective_return
    // that has since changed. Walk from entry_seeds under the
    // *converged* effective_returns; drop specs not visited.
    let reachable = compute_reachable_specs(m, &specs, &effective_returns);
    specs.retain(|k, _| reachable.contains(k));
    effective_returns.retain(|k, _| reachable.contains(k));
    let any_key_specs = build_any_key_index(&specs);
    ModuleTypes {
        specs,
        effective_returns,
        any_key_specs,
        scc_of,
    }
}

const WIDEN_AT: usize = 3;

#[allow(clippy::too_many_arguments)]
fn process_worklist(
    m: &Module,
    scc_of: &HashMap<FnId, usize>,
    scc_members: &HashMap<usize, std::collections::HashSet<FnId>>,
    work: &mut std::collections::VecDeque<(FnId, Vec<Descr>)>,
    in_work: &mut std::collections::HashSet<(FnId, Vec<Descr>)>,
    specs: &mut HashMap<(FnId, Vec<Descr>), FnTypes>,
    effective_returns: &mut HashMap<(FnId, Vec<Descr>), Descr>,
    callsite_fn_consts: &mut HashMap<(FnId, Vec<Descr>), Vec<Option<FnId>>>,
    return_readers: &mut HashMap<(FnId, Vec<Descr>), std::collections::HashSet<(FnId, Vec<Descr>)>>,
    visit_count: &mut HashMap<(FnId, Vec<Descr>), usize>,
) {
    while let Some(spec_key) = work.pop_front() {
        in_work.remove(&spec_key);

        let (fid, key) = spec_key.clone();
        let Some(&j) = m.fn_idx.get(&fid) else { continue };

        // type_fn is pure in (FnIr, entry_key) — cache by spec_key.
        if !specs.contains_key(&spec_key) {
            let mut ft = type_fn(&m.fns[j], m, Some(&key));
            if let Some(arg_consts) = callsite_fn_consts.get(&spec_key) {
                let entry = m.fns[j].entry;
                let entry_params = &m.fns[j].block(entry).params;
                for (slot, p) in entry_params.iter().enumerate() {
                    if let Some(Some(fid_const)) = arg_consts.get(slot) {
                        ft.fn_constants.insert(*p, *fid_const);
                    }
                }
            }
            specs.insert(spec_key.clone(), ft);
        }

        let count = visit_count.entry(spec_key.clone()).or_insert(0);
        *count += 1;
        let scc_id = scc_of.get(&fid).copied().unwrap_or(usize::MAX);
        let scc_set = scc_members
            .get(&scc_id)
            .cloned()
            .unwrap_or_default();
        let widen_now = *count > WIDEN_AT;

        // Walk to discover dependencies. cont_return_deps captures every
        // (callee_key) whose effective_return this walk consulted at a
        // cont-site slot-0 — folded below into the reverse readers index.
        //
        // fz-rh5.3 — no clone of caller_ft needed. The walk takes
        // &specs (immutable) and the only mutations in this iter body
        // are to effective_returns (different HashMap) and to specs at
        // the TOP of the loop (already completed before this borrow).
        let caller_ft = specs.get(&spec_key).unwrap();
        let mut pending: HashMap<FnId, std::collections::HashSet<Vec<Descr>>> = HashMap::new();
        let mut cont_return_deps: Vec<(FnId, Vec<Descr>)> = Vec::new();
        walk_spec_for_discovery(
            &m.fns[j],
            caller_ft,
            m,
            specs,
            effective_returns,
            &scc_set,
            widen_now,
            &mut pending,
            callsite_fn_consts,
            &mut cont_return_deps,
        );

        for (callee, keys) in pending {
            for k in keys {
                let new_spec = (callee, k);
                if !specs.contains_key(&new_spec) && in_work.insert(new_spec.clone()) {
                    work.push_back(new_spec);
                }
            }
        }

        // Recompute this spec's effective return. compute_return_for_spec
        // also pushes every (callee_key) it consults into `return_reads`;
        // combined with the walk's cont-site reads above, this is the
        // complete set of (callee_key)s whose return change affects this
        // spec's processing.
        let mut return_reads: Vec<(FnId, Vec<Descr>)> = Vec::new();
        let new_ret =
            compute_return_for_spec(m, &spec_key, specs, effective_returns, &mut return_reads);
        for callee_key in cont_return_deps.into_iter().chain(return_reads.into_iter()) {
            return_readers
                .entry(callee_key)
                .or_default()
                .insert(spec_key.clone());
        }
        let changed = match effective_returns.get(&spec_key) {
            Some(prev) => !new_ret.is_equiv(prev),
            None => true,
        };
        if changed {
            effective_returns.insert(spec_key.clone(), new_ret);
            if let Some(readers) = return_readers.get(&spec_key).cloned() {
                for reader in readers {
                    if specs.contains_key(&reader) && in_work.insert(reader.clone()) {
                        work.push_back(reader);
                    }
                }
            }
        }
    }
}

/// fz-5j5.3 — single-spec effective-return computation. Joins every
/// reachable Return / TailCall / TailCallClosure / cont-bearing
/// terminator into a Descr using `effective_returns` for downstream
/// reads. Missing entries contribute `Descr::none()` (Kleene bottom)
/// so partial state doesn't spuriously widen.
///
/// Every (callee_key) whose return is consulted is pushed into
/// `reads`. The worklist driver folds these into `return_readers`
/// so callee-return changes re-enqueue this spec.
fn compute_return_for_spec(
    module: &Module,
    spec_key: &(FnId, Vec<Descr>),
    specs: &HashMap<(FnId, Vec<Descr>), FnTypes>,
    effective_returns: &HashMap<(FnId, Vec<Descr>), Descr>,
    reads: &mut Vec<(FnId, Vec<Descr>)>,
) -> Descr {
    let mut lookup = |k: (FnId, Vec<Descr>)| -> Descr {
        let v = effective_returns.get(&k).cloned().unwrap_or_else(Descr::none);
        reads.push(k);
        v
    };
    let (fid, _) = spec_key;
    let Some(&j) = module.fn_idx.get(fid) else {
        return Descr::none();
    };
    let Some(ft) = specs.get(spec_key) else {
        return Descr::none();
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
                joined = joined.union(&lookup((*callee, arg_descrs)));
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
                    joined = joined.union(&lookup((target, ad)));
                } else if let Some(cv_descr) = ft.vars.get(closure) {
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
                            acc = acc.union(&lookup((lit.fn_id, full_key)));
                        }
                    }
                    if all_lit {
                        joined = joined.union(&acc);
                    } else {
                        joined = joined.union(&Descr::any());
                    }
                } else {
                    joined = joined.union(&Descr::any());
                }
            }
            Term::Call { continuation, .. }
            | Term::CallClosure { continuation, .. }
            | Term::Receive { continuation } => {
                let cont_k = cont_key_for_spec(b, continuation, ft, module, effective_returns);
                joined = joined.union(&lookup((continuation.fn_id, cont_k)));
            }
            Term::Halt(_) | Term::Goto(_, _) | Term::If(_, _, _) => {}
        }
    }
    joined
}

/// fz-5j5.3 — reconstruct the cont's input-Descr key at this block's
/// terminator using current `effective_returns` for slot 0. Mirrors
/// the walker's cont-key construction so the keys we look up are
/// structurally aligned with the registered specs.
fn cont_key_for_spec(
    block: &Block,
    cont: &crate::fz_ir::Cont,
    ft: &FnTypes,
    module: &Module,
    effective_returns: &HashMap<(FnId, Vec<Descr>), Descr>,
) -> Vec<Descr> {
    let Some(_) = module.fn_idx.get(&cont.fn_id) else {
        return vec![];
    };
    let cont_fn = module.fn_by_id(cont.fn_id);
    let n_params = cont_fn.block(cont_fn.entry).params.len();
    let mut key: Vec<Descr> = vec![Descr::any(); n_params];

    let env = env_at_terminator(ft, block, module);
    let slot0 = match &block.terminator {
        Term::Call { callee, args, .. } => {
            let arg_descrs: Vec<Descr> = args
                .iter()
                .map(|av| env.get(av).cloned().unwrap_or_else(Descr::any))
                .collect();
            effective_returns
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
                effective_returns
                    .get(&(target, ad))
                    .cloned()
                    .unwrap_or_else(Descr::any)
            } else if let Some(cv_descr) = env.get(closure) {
                // fz-5j5.3 — mirror walker's closure_lit slot-0 path
                // (resolve_closure_return). Without this, sweep computes
                // [any] where walker computed the closure's real return,
                // diverging from registered cont keys.
                let arg_descrs: Vec<Descr> = args
                    .iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(Descr::any))
                    .collect();
                resolve_closure_return(cv_descr, effective_returns, &arg_descrs)
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
}

/// fz-5j5.3 — MakeClosure-side any-key registration for one spec body.
/// For each `MakeClosure(F, captures)` whose opaque-invocation arity
/// is in `opaque_arities`, enqueue `(F, [capture_descrs..., any...])`
/// as an any-key spec for the lambda target.
fn sweep_makeclosure(
    f: &FnIr,
    caller_ft: &FnTypes,
    m: &Module,
    opaque_arities: &std::collections::HashSet<usize>,
    specs: &HashMap<(FnId, Vec<Descr>), FnTypes>,
    work: &mut std::collections::VecDeque<(FnId, Vec<Descr>)>,
    in_work: &mut std::collections::HashSet<(FnId, Vec<Descr>)>,
) {
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
                if opaque_arities.contains(&opaque_arity) {
                    let mut k: Vec<Descr> = vec![Descr::any(); n_params];
                    for (i, cv) in captured.iter().enumerate() {
                        if let Some(slot) = k.get_mut(i) {
                            *slot = env.get(cv).cloned().unwrap_or_else(Descr::any);
                        }
                    }
                    let new_spec = (*lam_fn_id, k);
                    if !specs.contains_key(&new_spec) && in_work.insert(new_spec.clone()) {
                        work.push_back(new_spec);
                    }
                }
            }
            env.insert(*v, type_prim(prim, &env, m, &HashSet::new()));
        }
    }
}

/// fz-5j5.3 — final reachability sweep. Worklist accumulation can
/// leave stale specs whose cont-key was built against old slot-0
/// effective_returns. Walk from entry seeds enumerating every
/// direct-call / cont / closure_lit / MakeClosure target under the
/// *converged* `effective_returns`. Specs not visited get dropped.
///
/// Distinct from `walk_spec_for_discovery`: that one filters out
/// already-registered specs (its job is incremental discovery);
/// reachability needs to *traverse* registered specs to reach more.
fn compute_reachable_specs(
    m: &Module,
    specs: &HashMap<(FnId, Vec<Descr>), FnTypes>,
    effective_returns: &HashMap<(FnId, Vec<Descr>), Descr>,
) -> std::collections::HashSet<(FnId, Vec<Descr>)> {
    let mut reachable: std::collections::HashSet<(FnId, Vec<Descr>)> =
        entry_seeds(m).into_iter().collect();
    let mut work: std::collections::VecDeque<(FnId, Vec<Descr>)> =
        reachable.iter().cloned().collect();
    while let Some(spec_key) = work.pop_front() {
        let (fid, _) = &spec_key;
        let Some(&j) = m.fn_idx.get(fid) else { continue };
        let Some(caller_ft) = specs.get(&spec_key) else {
            continue;
        };
        let f = &m.fns[j];
        let visit = |target: (FnId, Vec<Descr>),
                     reachable: &mut std::collections::HashSet<_>,
                     work: &mut std::collections::VecDeque<_>| {
            if specs.contains_key(&target) && reachable.insert(target.clone()) {
                work.push_back(target);
            }
        };
        for b in &f.blocks {
            let env = env_at_terminator(caller_ft, b, m);
            // Direct callees
            match &b.terminator {
                Term::Call { callee, args, .. } | Term::TailCall { callee, args, .. } => {
                    let callee_fn = m.fn_by_id(*callee);
                    let n_params = callee_fn.block(callee_fn.entry).params.len();
                    let mut key: Vec<Descr> = args
                        .iter()
                        .map(|av| env.get(av).cloned().unwrap_or_else(Descr::any))
                        .collect();
                    while key.len() < n_params {
                        key.push(Descr::any());
                    }
                    key.truncate(n_params);
                    visit((*callee, key), &mut reachable, &mut work);
                }
                _ => {}
            }
            // Closure-resolved callees (fn_constants + closure_lit)
            let (closure_var, closure_args): (Option<Var>, &[Var]) = match &b.terminator {
                Term::CallClosure { closure, args, .. }
                | Term::TailCallClosure { closure, args } => (Some(*closure), args.as_slice()),
                _ => (None, &[]),
            };
            if let Some(cv) = closure_var {
                if let Some(&target_fn) = caller_ft.fn_constants.get(&cv) {
                    let target = m.fn_by_id(target_fn);
                    let n_params = target.block(target.entry).params.len();
                    let mut key: Vec<Descr> = closure_args
                        .iter()
                        .map(|av| env.get(av).cloned().unwrap_or_else(Descr::any))
                        .collect();
                    while key.len() < n_params {
                        key.push(Descr::any());
                    }
                    key.truncate(n_params);
                    visit((target_fn, key), &mut reachable, &mut work);
                }
                if let Some(cv_descr) = env.get(&cv) {
                    let arg_descrs: Vec<Descr> = closure_args
                        .iter()
                        .map(|av| env.get(av).cloned().unwrap_or_else(Descr::any))
                        .collect();
                    for clause in &cv_descr.funcs {
                        if !clause.neg.is_empty() {
                            continue;
                        }
                        for sig in &clause.pos {
                            if let Some(lit) = &sig.lit {
                                let target = m.fn_by_id(lit.fn_id);
                                let n_params = target.block(target.entry).params.len();
                                let mut key: Vec<Descr> = lit.captures.clone();
                                key.extend(arg_descrs.iter().cloned());
                                while key.len() < n_params {
                                    key.push(Descr::any());
                                }
                                key.truncate(n_params);
                                visit((lit.fn_id, key), &mut reachable, &mut work);
                            }
                        }
                    }
                }
            }
            // Cont target: build the key the worklist would have built
            // under the converged effective_returns.
            let cont = match &b.terminator {
                Term::Call { continuation, .. }
                | Term::CallClosure { continuation, .. }
                | Term::Receive { continuation } => Some(continuation),
                _ => None,
            };
            if let Some(cont) = cont {
                let key = cont_key_for_spec(b, cont, caller_ft, m, effective_returns);
                visit((cont.fn_id, key), &mut reachable, &mut work);
            }
            // MakeClosure-side reachability: lambda's any-key spec.
            for stmt in &b.stmts {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeClosure(lam_fn_id, captured) = prim
                    && let Some(&jj) = m.fn_idx.get(lam_fn_id)
                {
                    let lam = &m.fns[jj];
                    let n_params = lam.block(lam.entry).params.len();
                    let mut k: Vec<Descr> = vec![Descr::any(); n_params];
                    for (i, cv) in captured.iter().enumerate() {
                        if let Some(slot) = k.get_mut(i) {
                            *slot = env.get(cv).cloned().unwrap_or_else(Descr::any);
                        }
                    }
                    visit((*lam_fn_id, k), &mut reachable, &mut work);
                }
            }
        }
    }
    reachable
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
    // fz-5j5.3 — every (callee, callee_key) whose effective_return this
    // walk consulted for cont slot-0 keying. The worklist driver folds
    // these into a reverse `(callee_key) → readers` index so that when
    // a callee's return later changes, only its readers get re-walked.
    cont_return_deps: &mut Vec<(FnId, Vec<Descr>)>,
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
                cont_return_deps.push(callee_key.clone());
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
                    cont_return_deps.push(callee_key.clone());
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
                    // fz-5j5.3 — record deps on every lit body return
                    // resolve_closure_return would consult, so future
                    // changes to those returns re-trigger this walk.
                    for c in &cv_descr.funcs {
                        if !c.neg.is_empty() {
                            continue;
                        }
                        for sig in &c.pos {
                            if let Some(lit) = &sig.lit
                                && sig.args.len() == arg_descrs.len()
                            {
                                let mut full_key: Vec<Descr> = lit.captures.clone();
                                full_key.extend_from_slice(&arg_descrs);
                                cont_return_deps.push((lit.fn_id, full_key));
                            }
                        }
                    }
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
        Prim::TypeTest(v, descr) => {
            let current = env.get(v).cloned().unwrap_or_else(Descr::any);
            then_env.insert(*v, current.intersect(descr));
            else_env.insert(*v, current.diff(descr));
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

        Prim::Extern(eid, _) => m
            .extern_idx
            .get(eid)
            .map(|&i| m.externs[i].ret_descr.clone())
            .unwrap_or_else(Descr::any),

        Prim::TypeTest(v, descr) => {
            let vt = lookup(env, *v);
            // If vt ⊆ descr → always true; if vt ∩ descr = ∅ → always false;
            // otherwise unknown bool. Branch pruning in the typer's If-rewriting
            // pass then eliminates dead branches when the result is a singleton.
            if vt.is_subtype(descr) {
                Descr::atom_lit("true")
            } else if vt.intersect(descr).is_empty() {
                Descr::atom_lit("false")
            } else {
                Descr::bool_t()
            }
        }

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
pub fn reachable_specs(
    module: &Module,
    spec_registry: &crate::spec_registry::SpecRegistry,
    module_types: &ModuleTypes,
    extra_seeds: impl IntoIterator<Item = u32>,
) -> HashSet<u32> {
    let mut reached: HashSet<u32> = HashSet::new();
    let mut worklist: Vec<u32> = Vec::new();

    // Build spec_fn_types lookup keyed by SpecId.
    let spec_keys: Vec<(FnId, Vec<Descr>)> = spec_registry
        .iter()
        .map(|(_, f, k)| (f, k.to_vec()))
        .collect();
    let ft_of = |sid: u32| -> Option<&FnTypes> {
        let (fid, key) = spec_keys.get(sid as usize)?;
        module_types.specs.get(&(*fid, key.clone()))
    };
    let fn_of = |sid: u32| -> Option<&FnIr> {
        let (fid, _) = spec_keys.get(sid as usize)?;
        let &j = module.fn_idx.get(fid)?;
        Some(&module.fns[j])
    };

    // Seed: main + every registered any-key spec.
    //
    // The any-key seed is the conservative bias for v1: any spec keyed by
    // `[any; n]` represents the wide-callable form of its fn — invocable
    // through opaque closure dispatch, spawn entry, mid-flight resume
    // shim, scheduler hook, MakeClosure consumer, or test entry. We don't
    // model each of those source-of-entry channels precisely; we just
    // declare every any-key reachable and let downstream callsite BFS
    // pick up the narrow specs.
    //
    // This still drops every value-narrowed spec that no callsite
    // resolves to — the actual fz-ul4.42 win — because narrow specs
    // require an explicit `resolve(fid, narrow_key)` match somewhere in
    // a reachable body to be marked.
    for (sid, fid, key) in spec_registry.iter() {
        let is_any_key = key
            .iter()
            .all(|d| d.is_subtype(&Descr::any()) && Descr::any().is_subtype(d));
        let _ = fid;
        if is_any_key {
            worklist.push(sid.0);
        }
    }
    if let Some(main_fn) = module.fns.iter().find(|f| f.name == "main") {
        let n_params = main_fn.block(main_fn.entry).params.len();
        let key: Vec<Descr> = vec![Descr::any(); n_params];
        if let Some(sid) = spec_registry.resolve(main_fn.id, &key) {
            worklist.push(sid.0);
        }
    }
    // Caller-supplied seeds: closure-target specs (dispatched via stub_fp
    // at runtime), spawn thunks, scheduler hooks, etc. — anything codegen
    // knows is an entry point that our IR-body BFS can't see.
    worklist.extend(extra_seeds);
    // Closure-lit dispatch: any fn whose id appears in a MakeClosure prim
    // could be invoked through a closure-typed Var whose Descr carries a
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
                if let Prim::MakeClosure(lam_id, _) = prim {
                    closure_target_fns.insert(*lam_id);
                }
            }
        }
    }
    for (sid, fid, _) in spec_registry.iter() {
        if closure_target_fns.contains(&fid) {
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
            let env = env_at_terminator(ft, blk, module);
            let arg_descrs = |args: &[Var]| -> Vec<Descr> {
                args.iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(Descr::any))
                    .collect()
            };
            let pad_to_arity = |callee: FnId, mut ad: Vec<Descr>| -> Vec<Descr> {
                if let Some(&j) = module.fn_idx.get(&callee) {
                    let np = module.fns[j].block(module.fns[j].entry).params.len();
                    while ad.len() < np {
                        ad.push(Descr::any());
                    }
                    ad.truncate(np);
                }
                ad
            };
            match &blk.terminator {
                Term::Call {
                    callee,
                    args,
                    continuation,
                } => {
                    let key = pad_to_arity(*callee, arg_descrs(args));
                    if let Some(sid) = spec_registry.resolve(*callee, &key) {
                        worklist.push(sid.0);
                    }
                    let cont_key = cont_input_key(blk, continuation, ft, module, module_types);
                    if let Some(sid) = spec_registry.resolve(continuation.fn_id, &cont_key) {
                        worklist.push(sid.0);
                    }
                }
                Term::TailCall { callee, args, .. } => {
                    let key = pad_to_arity(*callee, arg_descrs(args));
                    if let Some(sid) = spec_registry.resolve(*callee, &key) {
                        worklist.push(sid.0);
                    }
                }
                Term::CallClosure {
                    closure,
                    args,
                    continuation,
                } => {
                    if let Some(&target) = ft.fn_constants.get(closure) {
                        let key = pad_to_arity(target, arg_descrs(args));
                        if let Some(sid) = spec_registry.resolve(target, &key) {
                            worklist.push(sid.0);
                        }
                    }
                    let cont_key = cont_input_key(blk, continuation, ft, module, module_types);
                    if let Some(sid) = spec_registry.resolve(continuation.fn_id, &cont_key) {
                        worklist.push(sid.0);
                    }
                }
                Term::TailCallClosure { closure, args } => {
                    if let Some(&target) = ft.fn_constants.get(closure) {
                        let key = pad_to_arity(target, arg_descrs(args));
                        if let Some(sid) = spec_registry.resolve(target, &key) {
                            worklist.push(sid.0);
                        }
                    }
                }
                Term::Receive { continuation } => {
                    let cont_key = cont_input_key(blk, continuation, ft, module, module_types);
                    if let Some(sid) = spec_registry.resolve(continuation.fn_id, &cont_key) {
                        worklist.push(sid.0);
                    }
                }
                _ => {}
            }
        }
    }
    reached
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
#[path = "ir_typer_tests.rs"]
mod tests;
