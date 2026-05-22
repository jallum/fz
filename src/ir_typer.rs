//! Flow-sensitive type inference over `fz_ir::Module`.
//!
//! For each `FnIr`, walks blocks to a fixed point producing two views:
//!
//!   * `vars: HashMap<Var, Ty>` — type at each Var's definition site
//!     (or, for block params, the union over all incoming Goto args). This
//!     is what consumers ask when they want "the" type of v.
//!   * `block_envs: HashMap<BlockId, HashMap<Var, Ty>>` — per-block entry
//!     environment with branch-narrowed types. Consumers positioned inside a
//!     specific block read this for the tightest available info (e.g. inside
//!     the truthy branch of an `If`, a `cond` predicate's operand may carry
//!     a narrower type than its definition).
//!
//! Branch narrowing (fz-ul4.11.24.3):
//!   * `Term::If(cond, t, e)` inspects the stmt that bound `cond`. If it was
//!     `IsEmptyList(v)`, the truthy branch refines `v` to `nil`; the falsy
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

use crate::callsite_walk::{BlockCallsite, CallsiteKind, ContSource, block_callsites};
use crate::fz_ir::{
    BinOp, Block, BlockId, CallsiteId, Const, Cont, EmitSlot, FnId, FnIr, Module, Prim, Stmt, Term,
    UnOp, Var, VecKindIr,
};
use crate::ir_callgraph::{build_call_graph, entry_seeds};
use crate::types::MapKey;
use std::collections::{HashMap, HashSet};

// ============================================================================
// fz-210 — Tarjan SCC for bottom-up spec discovery. Call-graph construction
// + entry-seed selection live in `crate::ir_callgraph` (fz-0z4.1) so
// reachability is no longer tangled with type inference.
// ============================================================================

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
    pub vars: HashMap<Var, crate::types::Ty>,
    /// Entry env per block, with branch narrowing applied at If terminators.
    pub block_envs: HashMap<BlockId, HashMap<Var, crate::types::Ty>>,
    /// fz-ul4.29.10.1 — side-channel: vars known to hold a specific
    /// top-level fn identity (zero-capture `MakeClosure(F, [])` only).
    /// Used by `.29.10.2`/`.3` to register narrow specs and rewrite
    /// known-target `CallClosure → Call`. The type token deliberately carries
    /// no FnId identity; this map lives alongside it.
    pub fn_constants: HashMap<Var, FnId>,
    /// Blocks provably reachable from the entry under the inferred types.
    /// If terminators whose condition is a singleton bool prune the dead
    /// branch. Used by `compute_return_for_spec` to ignore returns that
    /// can never execute.
    pub reachable_blocks: HashSet<BlockId>,
    /// fz-uwq.3 — per-callsite dispatch table for this spec.
    ///
    /// For every `Direct` / `ClosureLit` / `CallClosureKnown` callsite
    /// in this spec's reachable IR, records the `(callee_fn, callee_key)`
    /// the typer elected to dispatch to. Empty for `Cont` and
    /// `MakeClosure` slots — those aren't dispatch sites.
    ///
    /// Authoritative source for codegen's dispatch decisions. Two
    /// caller specs can dispatch the *same* `CallsiteId` to *different*
    /// targets — this table keeps both views distinct.
    ///
    /// Populated during the worklist diff in `type_module`. Read by the
    /// fz-uwq.5+ codegen migration. See `docs/typer-authoritative-
    /// dispatch.md` for the broader rationale.
    pub dispatches: HashMap<crate::fz_ir::CallsiteId, (FnId, Vec<crate::types::Ty>)>,
}

/// Per-module type information.
///
/// `specs` is the per-callsite specialization map, keyed by
/// `(FnId, input-type-tuple)`. Each distinct argument-type signature
/// seen at any direct-call site produces a fresh FnTypes via
/// `type_fn(f, m, Some(&input_descrs))`. An any-key specialization
/// (`vec![any(); n_params]`) is registered for fns that are
/// closure-reachable, entry-seeded, or otherwise need the opaque-dispatch
/// fallback; direct-call-only fns have no any-key (see fz-ul4.29.12.6).
pub struct ModuleTypes {
    pub specs: HashMap<(FnId, Vec<crate::types::Ty>), FnTypes>,
    /// fz-2yw.2 — Kleene LFP of every spec's effective return type.
    /// Maintained incrementally by the worklist (fz-5j5.3): each spec's
    /// return is recomputed (via `compute_return_for_spec`) after every
    /// visit, and changes re-enqueue the spec's `return_readers`.
    /// Consumers (cont_slot0_descr, pretty_module_types, walker
    /// slot0_descr) read here instead of recursing on demand.
    pub effective_returns: HashMap<(FnId, Vec<crate::types::Ty>), crate::types::Ty>,
    /// fz-afs.12 — secondary index: FnId → all-any key for that fn.
    /// Populated in `type_module` from the final specs map. Enables O(1)
    /// any-key lookup without the per-element is_equiv scan.
    pub any_key_specs: HashMap<FnId, Vec<crate::types::Ty>>,
    /// Stable per-family precedence for specialization selection.
    pub spec_precedence: HashMap<(FnId, Vec<crate::types::Ty>), u32>,
    /// fz-02r.4 — SCC index for back-edge detection. Two FnIds share a
    /// back-edge (i.e., the call is on a loop) iff `scc_of[a] == scc_of[b]`.
    /// Self-recursion maps a fn to its own SCC (singleton). Populated at the
    /// start of `type_module` from the initial Tarjan run; stable thereafter.
    #[allow(dead_code)] // consumed by ir_codegen back-edge check (fz-02r.5)
    pub scc_of: HashMap<FnId, usize>,
    /// fz-fyq.2 — per-If dead-branch facts under cross-spec consensus.
    /// Populated at the end of `type_module` by `compute_dead_branches`.
    /// Keyed by `(FnId, BlockId)` where the block ends in a `Term::If`;
    /// value names which branch is provably never taken. Read by the
    /// dead-branch fold (fz-fyq.4) and by `collect_diagnostics` (fz-fyq.3).
    /// Only covers registered-spec fns — the diagnostic re-runs analysis
    /// on its own ad-hoc spec typing for fns with no registered spec.
    pub dead_branches: HashMap<(FnId, crate::fz_ir::BlockId), crate::fz_ir::DeadBranch>,
    /// fz-try B1+B2 — closure-handle registry. Records every distinct
    /// `(lambda FnId, captures)` shape that any reachable MakeClosure
    /// can produce. Separate from `specs` (which is body specs only);
    /// handles describe closure *values*, not compiled bodies.
    ///
    /// Consumers: the outcomes formatter renders handle identity for
    /// MakeClosure callsites; C3 will hang a polymorphic arrow
    /// signature off each entry.
    ///
    /// Codegen does *not* read this — it resolves the lambda body via
    /// `SpecId.0 == FnId.0` alignment for the any-key body spec.
    #[allow(dead_code)]
    // consumed by tests + future formatter (E-arc); unused in release codegen
    pub closure_handles: std::collections::HashSet<(FnId, Vec<crate::types::Ty>)>,
}

impl ModuleTypes {
    #[allow(dead_code)]
    pub fn spec_ty(&self, fn_id: FnId, input_tys: &[crate::types::Ty]) -> Option<&FnTypes> {
        self.specs.get(&(fn_id, input_tys.to_vec()))
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
        let mut best: Option<(u32, &FnTypes)> = None;
        for ((fid, key), ft) in &self.specs {
            if *fid != fn_id {
                continue;
            }
            let precedence = *self
                .spec_precedence
                .get(&(*fid, key.clone()))
                .unwrap_or(&u32::MAX);
            match &best {
                None => best = Some((precedence, ft)),
                Some((bp, _)) if precedence < *bp => best = Some((precedence, ft)),
                _ => {}
            }
        }
        best.map(|(_, ft)| ft)
    }

    pub fn effective_return_for_call_ty<
        T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
    >(
        &self,
        t: &T,
        callee: FnId,
        arg_tys: &[crate::types::Ty],
    ) -> Option<crate::types::Ty> {
        // Fast path: exact match.
        if let Some(d) = self.effective_returns.get(&(callee, arg_tys.to_vec())) {
            return Some(d.clone());
        }
        let candidates: Vec<
            crate::spec_registry::BestCoverCandidate<'_, &(FnId, Vec<crate::types::Ty>)>,
        > = self
            .effective_returns
            .keys()
            .filter(|(fid, _)| *fid == callee)
            .map(|key| crate::spec_registry::BestCoverCandidate {
                id: key,
                key: key.1.as_slice(),
                key_var_count: t.key_var_count(key.1.as_slice()),
                precedence: *self.spec_precedence.get(key).unwrap_or(&u32::MAX),
            })
            .collect();
        let best = crate::spec_registry::best_covering_candidate(t, arg_tys, candidates)?;
        self.effective_returns.get(best).cloned()
    }
}

fn key_precedence_order(
    specs: &HashMap<(FnId, Vec<crate::types::Ty>), FnTypes>,
    any_key_specs: &HashMap<FnId, Vec<crate::types::Ty>>,
) -> HashMap<(FnId, Vec<crate::types::Ty>), u32> {
    let mut keys_by_fn: HashMap<FnId, Vec<Vec<crate::types::Ty>>> = HashMap::new();
    for (fid, key) in specs.keys() {
        keys_by_fn.entry(*fid).or_default().push(key.clone());
    }
    let mut precedence = HashMap::new();
    for (fid, mut keys) in keys_by_fn {
        keys.sort_by(|a, b| {
            let a_is_any = any_key_specs.get(&fid) == Some(a);
            let b_is_any = any_key_specs.get(&fid) == Some(b);
            b_is_any
                .cmp(&a_is_any)
                .then_with(|| format!("{:?}", a).cmp(&format!("{:?}", b)))
        });
        for (idx, key) in keys.into_iter().enumerate() {
            precedence.insert((fid, key), idx as u32);
        }
    }
    precedence
}

/// fz-ul4.27.22.9 — closure-aware return resolution. Given a closure
/// Var's type and the actual `arg_tys` at a call site, compute the
/// joined return type.
///
/// For each positive arrow clause in `closure_descr.funcs`:
///   - If the clause carries a `ClosureLit { fn_id, captures }`, build the
///     full body key `[captures..., arg_tys...]` and look up
///     `effective_returns[(fn_id, full_key)]`. JOIN into the accumulator.
///   - Otherwise, JOIN `sig.ret` (the existing `arrow_join_return` path).
///
/// Returns `None` when a lit-tagged clause's spec has not yet been
/// registered — caller treats this as a fixpoint deferral (same convention
/// as `cont_slot0_descr` today). Returns `Some(any())` for
/// pathological inputs (empty funcs, negated arrows, saturated `Conj::top`
/// pos clauses) — those convey no narrowing information so the broadest
/// result is sound.
///
/// `arg_tys` length must match the closure's apparent arity for lit
/// clauses; mismatch falls back to `any()` for that clause.
#[allow(dead_code)] // Wired into cont_slot0_descr / codegen in fz-ul4.27.22.10/11.
pub fn resolve_closure_return<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    closure_ty: &crate::types::Ty,
    effective_returns: &HashMap<(FnId, Vec<crate::types::Ty>), crate::types::Ty>,
    arg_tys: &[crate::types::Ty],
) -> Option<T::Ty> {
    let translated: HashMap<
        (crate::types::ClosureTarget, Vec<crate::types::Ty>),
        crate::types::Ty,
    > = effective_returns
        .iter()
        .map(|((fn_id, key), ty)| (((*fn_id).into(), key.clone()), ty.clone()))
        .collect();
    t.resolve_closure_return(closure_ty, &translated, arg_tys)
}

fn build_any_key_index<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    specs: &HashMap<(FnId, Vec<crate::types::Ty>), FnTypes>,
) -> HashMap<FnId, Vec<crate::types::Ty>> {
    let any = t.any();
    let mut idx: HashMap<FnId, Vec<crate::types::Ty>> = HashMap::new();
    for (fid, key) in specs.keys() {
        if key.iter().all(|d| *d == any) {
            idx.entry(*fid).or_insert_with(|| key.clone());
        }
    }
    idx
}

thread_local! {
    pub static TYPE_MODULE_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// fz-rh5.4 — worklist pops in `process_worklist`. Each pop = one
    /// walk + one return-recompute. The single best proxy for "how
    /// much the typer churned" on a given program.
    pub static WORKLIST_POPS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// fz-rh5.4 — calls to `type_fn` from the worklist (= unique specs
    /// registered, since type_fn results are cached one-per-spec).
    pub static TYPE_FN_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// fz-rh5.4 — invocations of `walk_spec_for_discovery`.
    pub static WALK_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// fz-rh5.6 — the unique identity of a place that emits a spec.
///
/// Provenance is the invariant that fz-5j5 lacked: every spec in
/// `specs` exists because ≥1 `EmitterSite` (in some caller's body)
/// currently produces it. When a caller spec re-walks with different
/// state, its emitters may produce different targets; the driver
/// diffs against `produces[E]` and transitions `holders` accordingly.
/// Orphan cycles are pruned at end-of-typing by a forward BFS from
/// `entry_seeds` through the emits graph — no key recomputation,
/// so walker/sweep divergence (the closure_lit bug from fz-5j5.3)
/// is impossible by construction.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct EmitterSite {
    pub caller: (FnId, Vec<crate::types::Ty>),
    pub ident: crate::fz_ir::CallsiteIdent,
    pub slot: EmitSlot,
}

impl EmitterSite {
    /// fz-9pr.1 — project out the spec-aware `EmitterSite` to a
    /// spec-agnostic `CallsiteId`. The caller's spec-key is dropped;
    /// the `(FnId, CallsiteIdent, EmitSlot)` triple survives. Round-trips
    /// with `CallsiteId::with_spec_key`.
    #[allow(dead_code)]
    pub fn callsite_id(&self) -> CallsiteId {
        CallsiteId {
            caller: self.caller.0,
            ident: self.ident.clone(),
            slot: self.slot,
        }
    }
}

impl CallsiteId {
    /// fz-9pr.1 — re-attach a spec-key to recover the full
    /// `EmitterSite`. The new site's FnId is asserted to match the
    /// CallsiteId's caller; only the input-type tuple is supplied
    /// fresh. Pre-wire users are tests only; see `EmitterSite::callsite_id`.
    #[allow(dead_code)]
    pub fn with_spec_key(self, spec_key: (FnId, Vec<crate::types::Ty>)) -> EmitterSite {
        debug_assert_eq!(self.caller, spec_key.0);
        EmitterSite {
            caller: spec_key,
            ident: self.ident,
            slot: self.slot,
        }
    }
}

/// fz-rh5.6 — worklist-internal type aliases. Spec keys, the reverse
/// `return_readers` index, the `holders`/`emits_by_caller` indices,
/// and the `callsite_fn_consts` map all share these shapes; aliasing
/// satisfies clippy::type_complexity without sacrificing readability.
pub(crate) type SpecKey = (FnId, Vec<crate::types::Ty>);
pub(crate) type SpecKeySet = std::collections::HashSet<SpecKey>;
pub(crate) type ReturnReaders = HashMap<SpecKey, SpecKeySet>;
pub(crate) type CallsiteFnConsts = HashMap<SpecKey, Vec<Option<FnId>>>;
pub(crate) type EmitterSiteSet = std::collections::HashSet<EmitterSite>;
pub(crate) type HoldersMap = HashMap<SpecKey, EmitterSiteSet>;
pub(crate) type EmitsByCaller = HashMap<SpecKey, EmitterSiteSet>;
pub(crate) type ProducesMap = HashMap<EmitterSite, SpecKey>;

/// fz-rh5.6 — output of one discovery walk. The driver folds this
/// into worklist state.
#[derive(Default)]
struct WalkResult {
    /// Every `(site, target_spec_key)` this walk emits. The driver
    /// diffs against `produces[site]` to detect transitions.
    ///
    /// fz-uwq.3+ note: `target` here is the **enqueue key** — possibly
    /// widened by `widen_direct` for recursive calls. This is the key
    /// the worklist enqueues for typing so the fixpoint terminates.
    /// It is *not* the dispatch fact a downstream consumer should
    /// resolve at codegen time; see `dispatch_targets`.
    emits: Vec<(EmitterSite, (FnId, Vec<crate::types::Ty>))>,
    /// fz-uwq.3+ — per-callsite **dispatch fact**: the un-widened
    /// `(callee_fn, callee_key)` the typer would resolve at this site
    /// using `block_env` alone, with no worklist-control widening.
    /// This is the same key codegen recomputes from `block_envs`, so
    /// `spec_registry.resolve(target.0, &target.1)` lands on the same
    /// SpecId from either side — making `FnTypes.dispatches` and the
    /// codegen path agree by construction.
    ///
    /// Only populated for dispatch-shaped slots
    /// (`Direct` / `ClosureLit` / `CallClosureKnown`). `Cont` slot
    /// inputs are tracked through `cont_input_key` and aren't widened.
    dispatch_targets: HashMap<crate::fz_ir::CallsiteId, (FnId, Vec<crate::types::Ty>)>,
    /// `callee_key`s whose `effective_return` was consulted (for
    /// cont slot-0 keying or closure_lit return-join). Driver folds
    /// into the `return_readers` reverse index so changes
    /// re-enqueue this caller.
    return_reads: Vec<(FnId, Vec<crate::types::Ty>)>,
    /// fz-try B1+B2 — closure handles produced by MakeClosure in this
    /// walk, as `(lambda FnId, capture-types)`. Driver folds into
    /// `ModuleTypes.closure_handles`.
    closure_handles: HashSet<(FnId, Vec<crate::types::Ty>)>,
}

/// fz-5j5.3 — type a module via one worklist over `(FnId, Vec<crate::types::Ty>)`
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
///
/// ## Termination (fz-rh5.7)
///
/// The worklist terminates because:
///
///   (a) `effective_returns` is updated only via `union`,
///       which is monotone w.r.t. lattice inclusion. So
///       `effective_returns` is monotonically non-decreasing in
///       the product type lattice.
///
///   (b) The type lattice has finite height H, bounded by the
///       count of distinct type-axis values in the program
///       (atoms, ints, floats, tuple shapes, list shapes, etc —
///       all finite for a closed program).
///
///   (c) A spec is enqueued only on:
///         (i)   First emission — happens at most once per spec key.
///         (ii)  A callee's effective return that this spec reads
///               has changed — happens at most H× per
///               (spec, return-edge) pair, by (a) and (b).
///
///   (d) SCC-internal recursive spec keys (where args could shrink
///       structurally each iteration) are widened via
///       recursive spec-key widening after `WIDEN_AT` visits, forcing
///       convergence within a bounded number of iterations.
///
/// Therefore total worklist pops is bounded by
///   O(|specs| · (1 + H · |return-edges per spec|))
/// which is finite. `VISIT_HARD_BOUND` below is a debug-only
/// tripwire for invariant violation, NOT a release safety net.
pub fn type_module<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
    t: &mut T,
    m: &Module,
    tel: &dyn crate::telemetry::Telemetry,
) -> ModuleTypes {
    // fz-mm2.7 — verified: body has no direct concrete operations. The seam
    // handle is threaded into the worklist driver (process_worklist),
    // which fans it out to type_fn and the per-call typing work.
    TYPE_MODULE_CALLS.with(|c| c.set(c.get() + 1));
    WORKLIST_POPS.with(|c| c.set(0));
    TYPE_FN_CALLS.with(|c| c.set(0));
    WALK_CALLS.with(|c| c.set(0));

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

    let mut specs: HashMap<SpecKey, FnTypes> = HashMap::new();
    let mut effective_returns: HashMap<SpecKey, crate::types::Ty> = HashMap::new();
    let mut callsite_fn_consts: CallsiteFnConsts = HashMap::new();
    let mut return_readers: ReturnReaders = HashMap::new();
    let mut visit_count: HashMap<SpecKey, usize> = HashMap::new();

    // fz-rh5.6 — provenance state.
    let mut produces: ProducesMap = HashMap::new();
    let mut holders: HoldersMap = HashMap::new();
    let mut emits_by_caller: EmitsByCaller = HashMap::new();
    let mut closure_handles: std::collections::HashSet<(FnId, Vec<crate::types::Ty>)> =
        std::collections::HashSet::new();

    let mut work: std::collections::VecDeque<(FnId, Vec<crate::types::Ty>)> =
        entry_seeds(t, m).into_iter().collect();
    let mut in_work: std::collections::HashSet<(FnId, Vec<crate::types::Ty>)> =
        work.iter().cloned().collect();

    process_worklist(
        t,
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
        &mut produces,
        &mut holders,
        &mut emits_by_caller,
        &mut closure_handles,
    );

    // Forward reachability from entry_seeds via emits_by_caller +
    // produces. Specs not reached are orphans — their holders chain
    // ends in a spec that itself fell out of reach, or they form a
    // recursive cycle without an entry_seed anchor.
    let mut reachable: std::collections::HashSet<(FnId, Vec<crate::types::Ty>)> =
        entry_seeds(t, m).into_iter().collect();
    let mut bfs: std::collections::VecDeque<(FnId, Vec<crate::types::Ty>)> =
        reachable.iter().cloned().collect();
    while let Some(spec) = bfs.pop_front() {
        if let Some(sites) = emits_by_caller.get(&spec) {
            for site in sites {
                if let Some(target) = produces.get(site).cloned()
                    && reachable.insert(target.clone())
                {
                    bfs.push_back(target);
                }
            }
        }
    }
    specs.retain(|k, _| reachable.contains(k));
    effective_returns.retain(|k, _| reachable.contains(k));

    let any_key_specs = build_any_key_index(t, &specs);
    let spec_precedence = key_precedence_order(&specs, &any_key_specs);

    let mut mt = ModuleTypes {
        specs,
        effective_returns,
        any_key_specs,
        spec_precedence,
        scc_of,
        dead_branches: HashMap::new(),
        closure_handles,
    };
    mt.dead_branches = compute_dead_branches(t, m, &mt);
    {
        let pops = WORKLIST_POPS.with(|c| c.get()) as u64;
        let walks = WALK_CALLS.with(|c| c.get()) as u64;
        let type_fns = TYPE_FN_CALLS.with(|c| c.get()) as u64;
        let stats = module_type_stats(m, &mt);
        tel.execute(
            &["fz", "typer", "typed"],
            &crate::measurements! {
                worklist_pops: pops,
                walk_calls: walks,
                type_fn_calls: type_fns,
                spec_count: mt.specs.len() as u64,
                matcher_spec_count: stats.matcher_spec_count as u64,
                spec_var_count: stats.spec_var_count as u64,
                spec_block_count: stats.spec_block_count as u64,
                spec_stmt_count: stats.spec_stmt_count as u64,
                dispatch_count: stats.dispatch_count as u64,
                direct_call_count: stats.direct_call_count as u64,
                tail_call_count: stats.tail_call_count as u64,
                if_count: stats.if_count as u64,
                receive_count: stats.receive_count as u64,
                receive_matched_count: stats.receive_matched_count as u64,
            },
            &crate::metadata! {
                module_path: m.module_path().to_owned(),
                module: crate::telemetry::value::opaque(m),
                module_types: crate::telemetry::value::opaque(&mt),
            },
        );
    }
    mt
}

#[derive(Default)]
struct ModuleTypeStats {
    matcher_spec_count: usize,
    spec_var_count: usize,
    spec_block_count: usize,
    spec_stmt_count: usize,
    dispatch_count: usize,
    direct_call_count: usize,
    tail_call_count: usize,
    if_count: usize,
    receive_count: usize,
    receive_matched_count: usize,
}

fn module_type_stats(m: &Module, mt: &ModuleTypes) -> ModuleTypeStats {
    let mut stats = ModuleTypeStats::default();
    for ((fid, _), ft) in &mt.specs {
        let f = m.fn_by_id(*fid);
        if matches!(
            f.category,
            crate::fz_ir::FnCategory::Matcher | crate::fz_ir::FnCategory::ExternMatcher
        ) {
            stats.matcher_spec_count += 1;
        }
        stats.spec_var_count += ft.vars.len();
        stats.dispatch_count += ft.dispatches.len();
        for block in &f.blocks {
            if !ft.reachable_blocks.contains(&block.id) {
                continue;
            }
            stats.spec_block_count += 1;
            stats.spec_stmt_count += block.stmts.len();
            match &block.terminator {
                Term::Call { .. } => stats.direct_call_count += 1,
                Term::TailCall { .. } => stats.tail_call_count += 1,
                Term::If { .. } => stats.if_count += 1,
                Term::Receive { .. } => stats.receive_count += 1,
                Term::ReceiveMatched { .. } => stats.receive_matched_count += 1,
                Term::Goto(..)
                | Term::CallClosure { .. }
                | Term::TailCallClosure { .. }
                | Term::Return(_)
                | Term::Halt(_) => {}
            }
        }
    }
    stats
}

/// fz-fyq.2 — for every `Term::If` in a registered-spec fn, decide whether
/// the typer can prove one branch unreachable under cross-spec consensus.
/// A branch is published as `Dead` only when every spec of the enclosing
/// fn agreed the scrutinee narrows to `none` on that side; the rule
/// matches `collect_diagnostics` (fz-pky.1) which is what made the
/// `unreachable-arm` warning sound. Consumers: `ir_branch_fold`
/// (fz-fyq.4) and the unreachable-arm diagnostic (fz-fyq.3).
fn compute_dead_branches<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    m: &Module,
    mt: &ModuleTypes,
) -> HashMap<(FnId, crate::fz_ir::BlockId), crate::fz_ir::DeadBranch> {
    let mut specs_by_fn: HashMap<FnId, Vec<Vec<crate::types::Ty>>> = HashMap::new();
    for (fid, key) in mt.specs.keys() {
        specs_by_fn.entry(*fid).or_default().push(key.clone());
    }

    let mut out: HashMap<(FnId, crate::fz_ir::BlockId), crate::fz_ir::DeadBranch> = HashMap::new();

    for f in &m.fns {
        let Some(keys) = specs_by_fn.get(&f.id) else {
            continue;
        };
        let total = keys.len();
        if total == 0 {
            continue;
        }
        for b in &f.blocks {
            let Term::If { cond, .. } = b.terminator else {
                continue;
            };
            let mut dead_then = 0usize;
            let mut dead_else = 0usize;
            for key in keys {
                let Some(ft) = mt.spec_ty(f.id, key) else {
                    continue;
                };
                let mut env: HashMap<Var, crate::types::Ty> =
                    ft.block_envs.get(&b.id).cloned().unwrap_or_default();
                for stmt in &b.stmts {
                    let Stmt::Let(v, prim) = stmt;
                    let pt_ty = type_prim(t, prim, &env, m, &HashSet::new());
                    env.insert(*v, pt_ty);
                }
                let (then_env, else_env) = narrow_for_if(t, &env, cond, &b.stmts);
                let mut then_dead = find_emptied_var(t, &env, &then_env).is_some();
                let mut else_dead = find_emptied_var(t, &env, &else_env).is_some();
                // Fallback: when cond's own type is a singleton truthy/
                // falsy value, the opposite branch is unreachable even if
                // narrow_for_cond didn't fire (e.g. cond bound directly
                // to a `Const::True`/`Const::False`/`Const::Nil`). This
                // subsumes the cond-singleton fold ir_fold used to do.
                let ct = env.get(&cond).cloned().unwrap_or_else(|| t.any());
                let true_ty = t.atom_lit("true");
                let false_ty = t.atom_lit("false");
                let nil_ty = t.nil();
                if t.is_subtype(&ct, &true_ty) {
                    else_dead = true;
                } else if t.is_subtype(&ct, &false_ty) || t.is_subtype(&ct, &nil_ty) {
                    then_dead = true;
                }
                if then_dead {
                    dead_then += 1;
                }
                if else_dead {
                    dead_else += 1;
                }
            }
            // Both-dead means the If itself is unreachable — leave to DCE.
            if dead_then == total && dead_else < total {
                out.insert((f.id, b.id), crate::fz_ir::DeadBranch::Then);
            } else if dead_else == total && dead_then < total {
                out.insert((f.id, b.id), crate::fz_ir::DeadBranch::Else);
            }
        }
    }
    out
}

const WIDEN_AT: usize = 3;

/// fz-rh5.7 — debug-only termination tripwire. The proof above
/// (see `type_module`'s doc) shows the worklist terminates in
/// O(|specs| · H · |edges|) pops. This bound is comfortably above
/// any realistic program — a hit indicates a violated invariant
/// (non-monotone concrete op, an `is_equiv` slow-path returning false
/// on inputs that should be equiv, a missing WIDEN_AT trigger),
/// not a too-tight margin. Zero release-build cost.
const VISIT_HARD_BOUND: usize = 4096;

/// fz-rh5.6 — worklist driver with provenance.
///
/// Each pop:
///   1. type_fn the spec if new (cached by spec_key).
///   2. Walk for discovery → fills `WalkResult`.
///   3. Diff `result.emits` against the spec's prior emits
///      (`emits_by_caller[spec_key]`). Transition `produces` and
///      `holders`. Enqueue new target specs.
///   4. Fold `result.closure_handles` into the module-level handle
///      set (fz-try B1+B2).
///   5. Recompute this spec's effective return. If changed, enqueue
///      every spec in `return_readers[spec]`.
#[allow(clippy::too_many_arguments)]
fn process_worklist<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
    t: &mut T,
    m: &Module,
    scc_of: &HashMap<FnId, usize>,
    scc_members: &HashMap<usize, std::collections::HashSet<FnId>>,
    work: &mut std::collections::VecDeque<(FnId, Vec<crate::types::Ty>)>,
    in_work: &mut SpecKeySet,
    specs: &mut HashMap<SpecKey, FnTypes>,
    effective_returns: &mut HashMap<SpecKey, crate::types::Ty>,
    callsite_fn_consts: &mut CallsiteFnConsts,
    return_readers: &mut ReturnReaders,
    visit_count: &mut HashMap<SpecKey, usize>,
    produces: &mut ProducesMap,
    holders: &mut HoldersMap,
    emits_by_caller: &mut EmitsByCaller,
    closure_handles: &mut std::collections::HashSet<(FnId, Vec<crate::types::Ty>)>,
) {
    while let Some(spec_key) = work.pop_front() {
        in_work.remove(&spec_key);
        WORKLIST_POPS.with(|c| c.set(c.get() + 1));

        let (fid, key) = spec_key.clone();
        let Some(&j) = m.fn_idx.get(&fid) else {
            continue;
        };

        // type_fn is pure in (FnIr, entry_key) — cache by spec_key.
        if !specs.contains_key(&spec_key) {
            TYPE_FN_CALLS.with(|c| c.set(c.get() + 1));
            let mut ft = type_fn(t, &m.fns[j], m, Some(&key));
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
        // fz-rh5.7 — termination invariant tripwire. See proof in
        // `type_module`'s doc comment.
        debug_assert!(
            *count < VISIT_HARD_BOUND,
            "spec {:?} visited {} times — termination invariant violated",
            spec_key,
            *count
        );
        let scc_id = scc_of.get(&fid).copied().unwrap_or(usize::MAX);
        let scc_set = scc_members.get(&scc_id).cloned().unwrap_or_default();
        let widen_now = *count > WIDEN_AT;

        // Walk → emits + return_reads + closure_handles.
        let caller_ft = specs.get(&spec_key).unwrap();
        let mut result = WalkResult::default();
        walk_spec_for_discovery(
            t,
            &m.fns[j],
            caller_ft,
            m,
            effective_returns,
            &scc_set,
            widen_now,
            &spec_key,
            callsite_fn_consts,
            &mut result,
        );

        // Diff emits against this caller's prior emit set. Transitions
        // update produces + holders + emits_by_caller.
        //
        // fz-uwq.3 — install this spec's `FnTypes.dispatches` from
        // `result.dispatch_targets` (un-widened dispatch facts; see
        // `WalkResult.dispatch_targets` for why these differ from
        // `result.emits`'s widened enqueue keys).
        let prev_sites = emits_by_caller.remove(&spec_key).unwrap_or_default();
        let mut new_sites: std::collections::HashSet<EmitterSite> =
            std::collections::HashSet::new();
        for (site, target) in result.emits {
            new_sites.insert(site.clone());
            match produces.get(&site).cloned() {
                Some(prev_target) if prev_target == target => {
                    // Stable — no transition.
                }
                Some(prev_target) => {
                    // Retarget: detach from old, attach to new.
                    if let Some(h) = holders.get_mut(&prev_target) {
                        h.remove(&site);
                    }
                    holders
                        .entry(target.clone())
                        .or_default()
                        .insert(site.clone());
                    produces.insert(site, target.clone());
                }
                None => {
                    holders
                        .entry(target.clone())
                        .or_default()
                        .insert(site.clone());
                    produces.insert(site, target.clone());
                }
            }
            if !specs.contains_key(&target) && in_work.insert(target.clone()) {
                work.push_back(target);
            }
        }
        if let Some(ft) = specs.get_mut(&spec_key) {
            ft.dispatches = result.dispatch_targets;
        }
        // Sites present in prev but absent in new: this walk no longer
        // emits them. Detach from holders; clear produces.
        for site in prev_sites.difference(&new_sites) {
            if let Some(prev_target) = produces.remove(site)
                && let Some(h) = holders.get_mut(&prev_target)
            {
                h.remove(site);
            }
        }
        emits_by_caller.insert(spec_key.clone(), new_sites);

        // fz-try B1+B2 — accumulate handle registrations from this walk.
        for handle in result.closure_handles {
            closure_handles.insert(handle);
        }

        // Recompute effective return. compute_return_for_spec records
        // every callee return it consults; together with the walk's
        // return_reads, that's the full set of edges whose change
        // affects this spec.
        let mut compute_reads: Vec<(FnId, Vec<crate::types::Ty>)> = Vec::new();
        let new_ret = compute_return_for_spec(
            t,
            m,
            &spec_key,
            specs,
            effective_returns,
            &mut compute_reads,
        );
        for callee_key in result.return_reads.into_iter().chain(compute_reads) {
            return_readers
                .entry(callee_key)
                .or_default()
                .insert(spec_key.clone());
        }
        let changed = match effective_returns.get(&spec_key) {
            Some(prev) => !t.is_equivalent(&new_ret, prev),
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
/// terminator into a type using `effective_returns` for downstream
/// reads. Missing entries contribute `none()` (Kleene bottom)
/// so partial state doesn't spuriously widen.
///
/// Every (callee_key) whose return is consulted is pushed into
/// `reads`. The worklist driver folds these into `return_readers`
/// so callee-return changes re-enqueue this spec.
fn compute_return_for_spec<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    spec_key: &(FnId, Vec<crate::types::Ty>),
    specs: &HashMap<(FnId, Vec<crate::types::Ty>), FnTypes>,
    effective_returns: &HashMap<(FnId, Vec<crate::types::Ty>), crate::types::Ty>,
    reads: &mut Vec<(FnId, Vec<crate::types::Ty>)>,
) -> T::Ty {
    let (fid, _) = spec_key;
    let Some(&j) = module.fn_idx.get(fid) else {
        return t.none();
    };
    let Some(ft) = specs.get(spec_key) else {
        return t.none();
    };
    let f = &module.fns[j];

    let mut joined = t.none();
    for b in &f.blocks {
        if !ft.reachable_blocks.contains(&b.id) {
            continue;
        }
        match &b.terminator {
            Term::Return(rv) => {
                let dy = ft.vars.get(rv).cloned().unwrap_or_else(|| t.any());
                joined = t.union(joined, dy);
            }
            Term::TailCall { callee, args, .. } => {
                let arg_tys: Vec<crate::types::Ty> = args
                    .iter()
                    .map(|av| ft.vars.get(av).cloned().unwrap_or_else(|| t.any()))
                    .collect();
                let key = (*callee, arg_tys);
                let d = effective_returns.get(&key);
                reads.push(key);
                let dy = d.cloned().unwrap_or_else(|| t.none());
                joined = t.union(joined, dy);
            }
            Term::TailCallClosure {
                closure,
                args,
                ident: _,
            } => {
                if let Some(&target) = ft.fn_constants.get(closure) {
                    let target_fn = module.fn_by_id(target);
                    let np = target_fn.block(target_fn.entry).params.len();
                    let mut ad: Vec<crate::types::Ty> = args
                        .iter()
                        .map(|av| ft.vars.get(av).cloned().unwrap_or_else(|| t.any()))
                        .collect();
                    while ad.len() < np {
                        ad.push(t.any());
                    }
                    ad.truncate(np);
                    let key = (target, ad);
                    let d = effective_returns.get(&key);
                    reads.push(key);
                    let dy = d.cloned().unwrap_or_else(|| t.none());
                    joined = t.union(joined, dy);
                } else if let Some(cv_ty) = ft.vars.get(closure) {
                    let clauses = t.callable_clauses(cv_ty);
                    let mut all_lit = clauses.is_some();
                    let mut acc = t.none();
                    if let Some(clauses) = clauses {
                        for clause in clauses {
                            let Some(crate::types::ClosureLitInfo { target, captures }) =
                                clause.closure
                            else {
                                all_lit = false;
                                break;
                            };
                            let fn_id: FnId = target.into();
                            let target_fn = module.fn_by_id(fn_id);
                            let np = target_fn.block(target_fn.entry).params.len();
                            let mut full_key: Vec<crate::types::Ty> = captures.clone();
                            for av in args.iter() {
                                full_key.push(ft.vars.get(av).cloned().unwrap_or_else(|| t.any()));
                            }
                            while full_key.len() < np {
                                full_key.push(t.any());
                            }
                            full_key.truncate(np);
                            let key = (fn_id, full_key);
                            let d = effective_returns.get(&key);
                            reads.push(key);
                            let dy = d.cloned().unwrap_or_else(|| t.none());
                            acc = t.union(acc, dy);
                        }
                    }
                    if all_lit {
                        joined = t.union(joined, acc);
                    } else {
                        let any_ty = t.any();
                        joined = t.union(joined, any_ty);
                    }
                } else {
                    let any_ty = t.any();
                    joined = t.union(joined, any_ty);
                }
            }
            Term::Call { continuation, .. }
            | Term::CallClosure { continuation, .. }
            | Term::Receive {
                continuation,
                ident: _,
            } => {
                let cont_k = cont_key_for_spec(t, b, continuation, ft, module, effective_returns);
                let key = (continuation.fn_id, cont_k);
                let d = effective_returns.get(&key);
                reads.push(key);
                let dy = d.cloned().unwrap_or_else(|| t.none());
                joined = t.union(joined, dy);
            }
            // fz-yxs — selective receive: union over each outcome body's
            // return type. Receive outcomes resume from an opaque closure
            // env, so their callable key is the all-`any` shape pinned by
            // `receive_outcome_spec_key` rather than the caller's current
            // capture types.
            Term::ReceiveMatched {
                clauses,
                after,
                captures: _,
                ..
            } => {
                let any = t.any();
                for c in clauses {
                    let body_fn = module.fn_by_id(c.body);
                    let np = body_fn.block(body_fn.entry).params.len();
                    let key = crate::fz_ir::receive_outcome_spec_key(&any, np);
                    let lookup_key = (c.body, key);
                    let d = effective_returns.get(&lookup_key);
                    reads.push(lookup_key);
                    let dy = d.cloned().unwrap_or_else(|| t.none());
                    joined = t.union(joined, dy);
                }
                if let Some(a) = after {
                    let body_fn = module.fn_by_id(a.body);
                    let np = body_fn.block(body_fn.entry).params.len();
                    let key = crate::fz_ir::receive_outcome_spec_key(&any, np);
                    let lookup_key = (a.body, key);
                    let d = effective_returns.get(&lookup_key);
                    reads.push(lookup_key);
                    let dy = d.cloned().unwrap_or_else(|| t.none());
                    joined = t.union(joined, dy);
                }
            }
            Term::Halt(_) | Term::Goto(_, _) | Term::If { .. } => {}
        }
    }
    joined
}

/// fz-5j5.3 — reconstruct the cont's input-type key at this block's
/// terminator using current `effective_returns` for slot 0. Mirrors
/// the walker's cont-key construction so the keys we look up are
/// structurally aligned with the registered specs.
fn cont_key_for_spec<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
    t: &mut T,
    block: &Block,
    cont: &crate::fz_ir::Cont,
    ft: &FnTypes,
    module: &Module,
    effective_returns: &HashMap<(FnId, Vec<crate::types::Ty>), crate::types::Ty>,
) -> Vec<crate::types::Ty> {
    use crate::types::Ty;
    let Some(_) = module.fn_idx.get(&cont.fn_id) else {
        return vec![];
    };
    let any_t = t.any();
    let cont_fn = module.fn_by_id(cont.fn_id);
    let n_params = cont_fn.block(cont_fn.entry).params.len();
    let mut key: Vec<Ty> = vec![any_t.clone(); n_params];

    let env = env_at_terminator(t, ft, block, module);
    let slot0: Ty = match &block.terminator {
        Term::Call { callee, args, .. } => {
            let arg_tys: Vec<Ty> = args
                .iter()
                .map(|av| env.get(av).cloned().unwrap_or_else(|| any_t.clone()))
                .collect();
            effective_returns
                .get(&(*callee, arg_tys))
                .cloned()
                .unwrap_or_else(|| any_t.clone())
        }
        Term::CallClosure { closure, args, .. } => {
            if let Some(&target) = ft.fn_constants.get(closure) {
                let target_fn = module.fn_by_id(target);
                let np = target_fn.block(target_fn.entry).params.len();
                let mut ad: Vec<Ty> = args
                    .iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(|| any_t.clone()))
                    .collect();
                while ad.len() < np {
                    ad.push(any_t.clone());
                }
                ad.truncate(np);
                effective_returns
                    .get(&(target, ad))
                    .cloned()
                    .unwrap_or_else(|| any_t.clone())
            } else if let Some(cv_descr) = env.get(closure) {
                // fz-5j5.3 — mirror walker's closure_lit slot-0 path
                // (resolve_closure_return). Without this, sweep computes
                // [any] where walker computed the closure's real return,
                // diverging from registered cont keys.
                let arg_tys: Vec<Ty> = args
                    .iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(|| any_t.clone()))
                    .collect();
                resolve_closure_return(t, cv_descr, effective_returns, &arg_tys)
                    .unwrap_or_else(|| any_t.clone())
            } else {
                any_t.clone()
            }
        }
        _ => any_t.clone(),
    };
    if !key.is_empty() {
        key[0] = slot0;
    }
    for (k, cv) in cont.captured.iter().enumerate() {
        if let Some(p) = key.get_mut(k + 1) {
            *p = env.get(cv).cloned().unwrap_or_else(|| any_t.clone());
        }
    }
    key
}

/// fz-rh5.6 — discovery walk for one spec. Walks the spec's body and
/// records every spec it currently emits into `out.emits`, tagged by
/// `EmitterSite`. The driver diffs against the spec's previous emits
/// (via `produces`/`holders`/`emits_by_caller`) and transitions
/// provenance.
///
/// Emit kinds:
///   - `EmitSlot::Direct` for `Term::Call` / `Term::TailCall`.
///   - `EmitSlot::ClosureCall` for `Term::CallClosure` / `Term::TailCallClosure`
///     callsites. Pre-fz-try.11 this was split into `CallClosureKnown`
///     (fn_constants resolved) and `ClosureLit(c, s)` (per closure-lit
///     clause); now both paths share the uniform structural slot and
///     dispatch variation lives on the Dispatch enum at row time.
///   - `EmitSlot::Cont` for the continuation of Call/CallClosure/Receive.
///
/// `Prim::MakeClosure` is *not* an emit kind — it constructs a closure
/// value (a *handle*), recorded in `out.closure_handles`. The lambda's
/// compiled body is the any-key body spec (SpecId.0 == FnId.0); codegen
/// resolves it directly without indirection through a MakeClosure-side
/// padded spec.
///
/// `caller_scc` + `widen_now`: SCC-internal recursive Direct args
/// are per-element widened-for-recursive-spec-key after `WIDEN_AT`
/// visits to force
/// termination on shrinking-arg recursion. (See fz-rh5.6 design
/// note: cont/closure_lit emits are NOT widened — under provenance,
/// widening replaces an emit, and codegen's lookup uses the
/// narrow caller-derived form.)
#[allow(clippy::too_many_arguments)]
fn walk_spec_for_discovery<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    f: &FnIr,
    caller_ft: &FnTypes,
    m: &Module,
    effective_returns: &HashMap<(FnId, Vec<crate::types::Ty>), crate::types::Ty>,
    caller_scc: &std::collections::HashSet<FnId>,
    widen_now: bool,
    caller_spec_key: &(FnId, Vec<crate::types::Ty>),
    callsite_fn_consts: &mut HashMap<(FnId, Vec<crate::types::Ty>), Vec<Option<FnId>>>,
    out: &mut WalkResult,
) {
    WALK_CALLS.with(|c| c.set(c.get() + 1));
    let any_ty = t.any();
    fn widen_direct<T: crate::types::Types<Ty = crate::types::Ty>>(
        t: &mut T,
        widen_now: bool,
        caller_scc: &std::collections::HashSet<FnId>,
        k: Vec<crate::types::Ty>,
        caller: FnId,
        callee: FnId,
        module: &Module,
    ) -> Vec<crate::types::Ty> {
        if !(widen_now && caller_scc.contains(&callee)) {
            return k;
        }
        // fz-puj.43 (X2) — matcher fns are pure pass-through routers
        // (Matcher-driven dispatch, no value transforms — F3 / G1 enforced).
        // When a matcher fn participates in an SCC with its
        // calling user fn, widening across EITHER edge erases
        // closure-lit precision (and other narrow lits) that the matcher
        // forwards unchanged. Skip widening when either end of the edge
        // is a Matcher: the matcher's own spec stays narrow
        // (caller→matcher skipped), AND the clause-cont specs see the
        // narrow keys the matcher dispatched on (matcher→callee
        // skipped). Termination still holds via the SCC's matcher-free
        // edges, which continue to widen normally.
        let is_matcher = |fid: FnId| -> bool {
            module
                .fn_idx
                .get(&fid)
                .is_some_and(|&j| module.fns[j].category == crate::fz_ir::FnCategory::Matcher)
        };
        if is_matcher(callee) || is_matcher(caller) {
            return k;
        }
        k.into_iter()
            .map(|ty| t.widen_for_recursive_spec_key(&ty))
            .collect()
    }

    let emit = |slot: EmitSlot,
                ident: crate::fz_ir::CallsiteIdent,
                target: (FnId, Vec<crate::types::Ty>),
                out: &mut WalkResult| {
        out.emits.push((
            EmitterSite {
                caller: caller_spec_key.clone(),
                ident,
                slot,
            },
            target,
        ));
    };

    for b in &f.blocks {
        let mut env: HashMap<Var, crate::types::Ty> =
            caller_ft.block_envs.get(&b.id).cloned().unwrap_or_default();

        // Stmt-level work: MakeClosure handle registration (fz-try
        // B1+B2). No stmt-level emits — closure construction is a
        // value event, not a body-spec dispatch.
        for stmt in b.stmts.iter() {
            let Stmt::Let(v, prim) = stmt;
            // fz-try B1+B2 — MakeClosure is closure-value construction. Two
            // effects:
            //   (a) Register a handle `(lam_fn_id, captures)` — closure-value
            //       identity, disjoint from body specs.
            //   (b) Emit the lambda's any-key body spec onto the worklist —
            //       uniform across every MakeClosure site of the same lambda,
            //       no captures-padding. The emit drives the typer to type
            //       the body; codegen registers one compiled body per
            //       closure-target at SpecId.0 == FnId.0. The closure-target
            //       ABI seam speaks Tagged (fz-try.15), so no per-capture
            //       body specialization is needed for wire-format
            //       synchronization.
            if let Prim::MakeClosure(mk_ident, lam_fn_id, captured) = prim
                && let Some(&jj) = m.fn_idx.get(lam_fn_id)
            {
                let lam = &m.fns[jj];
                let n_params = lam.block(lam.entry).params.len();
                let captures: Vec<crate::types::Ty> = captured
                    .iter()
                    .map(|cv| {
                        env.get(cv)
                            .cloned()
                            .expect("MakeClosure: captured var unbound")
                    })
                    .collect();
                out.closure_handles.insert((*lam_fn_id, captures));
                let any_key: Vec<crate::types::Ty> = vec![any_ty.clone(); n_params];
                let site = EmitterSite {
                    caller: caller_spec_key.clone(),
                    ident: mk_ident.clone(),
                    slot: EmitSlot::MakeClosure,
                };
                out.emits.push((site, (*lam_fn_id, any_key)));
            }
            {
                let pt_ty = type_prim(t, prim, &env, m, &HashSet::new());
                env.insert(*v, pt_ty);
            }
        }

        // fz-9pr.17 — opaque-arity detection for unresolved closure
        // fz-9pr.17 — terminator-derived callsites. One match site
        // (callsite_walk::block_callsites) replaces the four arms that
        // used to live here (Direct, CallClosureKnown, ClosureLit,
        // Cont). Per-spec key building and callsite_fn_consts tracking
        // stay typer-side because they depend on caller_ft.block_envs
        // and caller_ft.fn_constants.
        // fz-kgk — every slot in `block_callsites` shares the
        // terminator's intrinsic ident; non-call terminators have no
        // callsites and don't reach here.
        let term_ident = match b.terminator.ident() {
            Some(i) => i.clone(),
            None => continue,
        };
        let cs_list = block_callsites(t, &b.terminator, &env, &caller_ft.fn_constants);
        for BlockCallsite { slot, kind } in cs_list {
            match kind {
                CallsiteKind::Direct { callee, args } => {
                    let Some(&j) = m.fn_idx.get(&callee) else {
                        continue;
                    };
                    let callee_fn = &m.fns[j];
                    let n_params = callee_fn.block(callee_fn.entry).params.len();
                    let mut dispatch_key: Vec<crate::types::Ty> = args
                        .iter()
                        .map(|av| env.get(av).cloned().unwrap_or_else(|| any_ty.clone()))
                        .collect();
                    while dispatch_key.len() < n_params {
                        dispatch_key.push(any_ty.clone());
                    }
                    dispatch_key.truncate(n_params);
                    // fz-uwq.3+ — record the dispatch fact (un-widened)
                    // before widening for the worklist enqueue key.
                    out.dispatch_targets.insert(
                        crate::fz_ir::CallsiteId {
                            caller: caller_spec_key.0,
                            ident: term_ident.clone(),
                            slot,
                        },
                        (callee, dispatch_key.clone()),
                    );
                    let enqueue_key = widen_direct(
                        t,
                        widen_now,
                        caller_scc,
                        dispatch_key,
                        caller_spec_key.0,
                        callee,
                        m,
                    );
                    let mut per_arg: Vec<Option<FnId>> = args
                        .iter()
                        .map(|av| caller_ft.fn_constants.get(av).copied())
                        .collect();
                    while per_arg.len() < n_params {
                        per_arg.push(None);
                    }
                    per_arg.truncate(n_params);
                    let entry_key = (callee, enqueue_key.clone());
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
                    emit(slot, term_ident.clone(), (callee, enqueue_key), out);
                }
                CallsiteKind::CallClosureKnown { target, args } => {
                    let Some(&j) = m.fn_idx.get(&target) else {
                        continue;
                    };
                    let target_fn = &m.fns[j];
                    let n_params = target_fn.block(target_fn.entry).params.len();
                    let mut dispatch_key: Vec<crate::types::Ty> = args
                        .iter()
                        .map(|av| env.get(av).cloned().unwrap_or_else(|| any_ty.clone()))
                        .collect();
                    while dispatch_key.len() < n_params {
                        dispatch_key.push(any_ty.clone());
                    }
                    dispatch_key.truncate(n_params);
                    out.dispatch_targets.insert(
                        crate::fz_ir::CallsiteId {
                            caller: caller_spec_key.0,
                            ident: term_ident.clone(),
                            slot,
                        },
                        (target, dispatch_key.clone()),
                    );
                    let enqueue_key = widen_direct(
                        t,
                        widen_now,
                        caller_scc,
                        dispatch_key,
                        caller_spec_key.0,
                        target,
                        m,
                    );
                    emit(slot, term_ident.clone(), (target, enqueue_key), out);
                }
                CallsiteKind::ClosureLit {
                    fn_id,
                    captures,
                    args,
                } => {
                    let Some(&j) = m.fn_idx.get(&fn_id) else {
                        continue;
                    };
                    let target_fn = &m.fns[j];
                    let n_params = target_fn.block(target_fn.entry).params.len();
                    let mut dispatch_key: Vec<crate::types::Ty> = captures.clone();
                    let arg_tys = args
                        .iter()
                        .map(|av| env.get(av).cloned().unwrap_or_else(|| any_ty.clone()));
                    dispatch_key.extend(arg_tys);
                    while dispatch_key.len() < n_params {
                        dispatch_key.push(any_ty.clone());
                    }
                    dispatch_key.truncate(n_params);
                    out.dispatch_targets.insert(
                        crate::fz_ir::CallsiteId {
                            caller: caller_spec_key.0,
                            ident: term_ident.clone(),
                            slot,
                        },
                        (fn_id, dispatch_key.clone()),
                    );
                    let enqueue_key = widen_direct(
                        t,
                        widen_now,
                        caller_scc,
                        dispatch_key,
                        caller_spec_key.0,
                        fn_id,
                        m,
                    );
                    emit(slot, term_ident.clone(), (fn_id, enqueue_key), out);
                }
                CallsiteKind::Cont { cont, source } => {
                    // slot 0 derivation by Cont source. Receive is
                    // opaque (`any`); Call reads effective_returns;
                    // CallClosure either reads effective_returns of
                    // the fn_constants-resolved target or resolves
                    // via the closure-lit lattice.
                    let slot0_ty: Option<crate::types::Ty> = match source {
                        ContSource::Call { callee, args } => {
                            let arg_tys: Vec<crate::types::Ty> = args
                                .iter()
                                .map(|av| env.get(av).cloned().unwrap_or_else(|| any_ty.clone()))
                                .collect();
                            let callee_key = (callee, arg_tys);
                            out.return_reads.push(callee_key.clone());
                            effective_returns.get(&callee_key).cloned()
                        }
                        ContSource::CallClosure { closure, args } => {
                            if let Some(&target) = caller_ft.fn_constants.get(&closure) {
                                let target_fn = m.fn_by_id(target);
                                let n_params = target_fn.block(target_fn.entry).params.len();
                                let mut arg_tys: Vec<crate::types::Ty> = args
                                    .iter()
                                    .map(|av| {
                                        env.get(av).cloned().unwrap_or_else(|| any_ty.clone())
                                    })
                                    .collect();
                                while arg_tys.len() < n_params {
                                    arg_tys.push(any_ty.clone());
                                }
                                arg_tys.truncate(n_params);
                                let callee_key = (target, arg_tys);
                                out.return_reads.push(callee_key.clone());
                                effective_returns.get(&callee_key).cloned()
                            } else if let Some(cv_descr) = env.get(&closure) {
                                let arg_tys: Vec<crate::types::Ty> = args
                                    .iter()
                                    .map(|av| {
                                        env.get(av).cloned().unwrap_or_else(|| any_ty.clone())
                                    })
                                    .collect();
                                if let Some(clauses) = t.callable_clauses(cv_descr) {
                                    for clause in clauses {
                                        if let Some(crate::types::ClosureLitInfo {
                                            target,
                                            captures,
                                        }) = clause.closure
                                            && clause.args.len() == arg_tys.len()
                                        {
                                            let mut full_key: Vec<crate::types::Ty> =
                                                captures.clone();
                                            full_key.extend_from_slice(&arg_tys);
                                            out.return_reads.push((target.into(), full_key));
                                        }
                                    }
                                }
                                resolve_closure_return(t, cv_descr, effective_returns, &arg_tys)
                            } else {
                                Some(any_ty.clone())
                            }
                        }
                        ContSource::Receive => Some(any_ty.clone()),
                    };
                    let Some(slot0) = slot0_ty else {
                        // Deferred: return_readers will re-enqueue
                        // this caller when the callee return arrives.
                        continue;
                    };
                    let none_ty = t.none();
                    if t.is_equivalent(&slot0, &none_ty) {
                        // Bottom means the continuation is unreachable
                        // unless the callee return grows later; the
                        // return_readers edge above will requeue us then.
                        continue;
                    }
                    let Some(&j) = m.fn_idx.get(&cont.fn_id) else {
                        continue;
                    };
                    let cont_fn = &m.fns[j];
                    let n_params = cont_fn.block(cont_fn.entry).params.len();
                    let mut key: Vec<crate::types::Ty> = vec![any_ty.clone(); n_params];
                    if !key.is_empty() {
                        key[0] = slot0;
                    }
                    for (k, cvv) in cont.captured.iter().enumerate() {
                        if let Some(p) = key.get_mut(k + 1) {
                            *p = env.get(cvv).cloned().unwrap_or_else(|| any_ty.clone());
                        }
                    }
                    // fz-rh5.6 — do NOT widen cont keys. See pre-refactor
                    // commentary preserved in callsite_walk docs.
                    let mut per_param: Vec<Option<FnId>> = vec![None; n_params];
                    for (k, cvv) in cont.captured.iter().enumerate() {
                        if let Some(p) = per_param.get_mut(k + 1) {
                            *p = caller_ft.fn_constants.get(cvv).copied();
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
                    // fz-uwq.5+ — Cont keys aren't widened, so the
                    // dispatch fact equals the emit key. Record it for
                    // codegen's `resolve_cont_sid` to read.
                    out.dispatch_targets.insert(
                        crate::fz_ir::CallsiteId {
                            caller: caller_spec_key.0,
                            ident: term_ident.clone(),
                            slot,
                        },
                        (cont.fn_id, key.clone()),
                    );
                    emit(slot, term_ident.clone(), (cont.fn_id, key), out);
                }
            }
        }

        // fz-70q.3 — selective-receive bodies aren't expressed in
        // `block_callsites` (they're FnId fields on the terminator,
        // not Cont structs). Walk them inline so the typer's spec
        // worklist seeds (FnId, key) for each clause body / guard /
        // after; without this codegen never sees their FuncIds and
        // the park-site fn_addr lookup faults.
        //
        // Key shape mirrors `compute_return_for_spec`'s lookup:
        // receive outcomes resume from an opaque closure env, so the
        // body key is all-`any` at the body's entry-block arity.
        if let Term::ReceiveMatched {
            clauses,
            after,
            captures: _,
            ..
        } = &b.terminator
        {
            let mut enq = |fid: FnId, _bound_arity: usize, ident: crate::fz_ir::CallsiteIdent| {
                let Some(&j) = m.fn_idx.get(&fid) else {
                    return;
                };
                let body = &m.fns[j];
                let np = body.block(body.entry).params.len();
                let key = crate::fz_ir::receive_outcome_spec_key(&any_ty, np);
                emit(EmitSlot::Cont, ident, (fid, key), out);
            };
            // EmitterSite is keyed (caller, ident, slot); a single
            // ReceiveMatched term has N clause/after sub-targets but
            // shares one term_ident, so we synthesize per-target
            // idents from each body fn's span. Without this the
            // `produces` HashMap collapses to the last emit and
            // earlier targets fall out of reachability.
            for c in clauses {
                enq(
                    c.body,
                    c.bound_names.len(),
                    crate::fz_ir::CallsiteIdent::from_source(c.span),
                );
                if let Some(g) = c.guard {
                    enq(
                        g,
                        c.bound_names.len(),
                        crate::fz_ir::CallsiteIdent::from_source(c.span),
                    );
                }
            }
            if let Some(a) = after {
                enq(a.body, 0, crate::fz_ir::CallsiteIdent::from_source(a.span));
            }
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
pub fn rewrite_known_target_closures<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    // fz-mm2.6 — verified: body has no concrete representation operations. The seam handle
    // is preserved on the signature so the function stays uniform with
    // its siblings; if a future concrete op lands here, it routes through t.
    _t: &mut T,
    module: &mut Module,
    types: &ModuleTypes,
) {
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
        let if_pair;
        let succs: &[BlockId] = match &b.terminator {
            Term::Goto(t, _) => std::slice::from_ref(t),
            Term::If { then_b, else_b, .. } => {
                if_pair = [*then_b, *else_b];
                &if_pair
            }
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

pub fn type_fn<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
    t: &mut T,
    f: &FnIr,
    m: &Module,
    entry_param_types: Option<&[crate::types::Ty]>,
) -> FnTypes {
    // Pre-materialized fallbacks for the many `unwrap_or_else(any/none)`
    // sites. Re-cloned per fallback hit; future passes (when locals become Ty)
    // will let these flow as values instead of clone-on-fallback.
    let mut vars: HashMap<Var, crate::types::Ty> = HashMap::new();
    let mut block_envs: HashMap<BlockId, HashMap<Var, crate::types::Ty>> = HashMap::new();

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
                let pt = entry_param_types
                    .and_then(|ts| ts.get(i))
                    .cloned()
                    .unwrap_or_else(|| t.any());
                env.insert(p, pt.clone());
                vars.insert(p, pt);
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
                let pt_ty = type_prim(t, prim, &env, m, &const_vars);
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
                let pt = pt_ty.clone();
                env.insert(*v, pt.clone());
                // vars is the definition-site type; single assignment so
                // we just overwrite each iteration (will converge).
                let prev_ty = vars.get(v).cloned().unwrap_or_else(|| t.none());
                if !t.is_equivalent(&pt_ty, &prev_ty) {
                    vars.insert(*v, pt);
                    changed = true;
                }
            }

            // Propagate to successors.
            match &b.terminator {
                Term::Goto(target, args) => {
                    let target_b = f.block(*target);
                    let mut delta = env.clone();
                    // Substitute target's params with the supplied arg types.
                    let arg_ts: Vec<crate::types::Ty> = args
                        .iter()
                        .map(|a| env.get(a).cloned().unwrap_or_else(|| t.any()))
                        .collect();
                    // Remove anything keyed by the source-block's view of
                    // the args (they're not the same Vars as target params).
                    for (i, &p) in target_b.params.iter().enumerate() {
                        if let Some(at) = arg_ts.get(i) {
                            delta.insert(p, at.clone());
                        }
                    }
                    if merge_into(t, &mut block_envs, *target, &delta) {
                        changed = true;
                    }
                    // Update vars for target's params via union across all
                    // predecessors (handled via merge_into's union, but we
                    // also need to mirror in vars).
                    for &p in target_b.params.iter() {
                        let from_env = block_envs[target]
                            .get(&p)
                            .cloned()
                            .unwrap_or_else(|| t.none());
                        let prev_ty = vars.get(&p).cloned().unwrap_or_else(|| t.none());
                        if !t.is_equivalent(&from_env, &prev_ty) {
                            vars.insert(p, from_env);
                            changed = true;
                        }
                    }
                }
                Term::If {
                    cond,
                    then_b,
                    else_b,
                    ..
                } => {
                    let (then_env, else_env) = narrow_for_if(t, &env, *cond, &b.stmts);
                    if merge_into(t, &mut block_envs, *then_b, &then_env) {
                        changed = true;
                    }
                    if merge_into(t, &mut block_envs, *else_b, &else_env) {
                        changed = true;
                    }
                }
                Term::Call { .. }
                | Term::TailCall { .. }
                | Term::CallClosure { .. }
                | Term::TailCallClosure { .. }
                | Term::Return(_)
                | Term::Halt(_)
                | Term::Receive { .. }
                | Term::ReceiveMatched { .. } => {
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
            if let Prim::MakeClosure(_, fid, captured) = prim
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
            Term::If {
                cond,
                then_b,
                else_b,
                ..
            } => {
                // Re-evaluate stmts to get the env at the terminator.
                let mut env = block_envs[&bid].clone();
                for stmt in &b.stmts {
                    let Stmt::Let(v, prim) = stmt;
                    let pt_ty = type_prim(t, prim, &env, m, &HashSet::new());
                    env.insert(*v, pt_ty);
                }
                // Use is_subtype to check provable branch deadness.
                // `ct ⊆ atom_lit("true")` means ct can ONLY be true →
                // else-branch dead. `ct ⊆ atom_lit("false")` → then dead.
                // bool_t()/any()/etc. are NOT subtypes of either singleton,
                // so both branches remain reachable.
                let ct_ty = env.get(cond).cloned().unwrap_or_else(|| t.none());
                let false_ty = t.atom_lit("false");
                if !t.is_subtype(&ct_ty, &false_ty) {
                    worklist.push(*then_b);
                }
                let true_ty = t.atom_lit("true");
                if !t.is_subtype(&ct_ty, &true_ty) {
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
        dispatches: HashMap::new(),
    }
}

/// Union `delta` into `block_envs[target]`. Returns true if anything changed.
fn merge_into<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    block_envs: &mut HashMap<BlockId, HashMap<Var, crate::types::Ty>>,
    target: BlockId,
    delta: &HashMap<Var, crate::types::Ty>,
) -> bool {
    let env = block_envs.entry(target).or_default();
    let mut changed = false;
    for (v, dt) in delta {
        let prev_ty = env.get(v).cloned().unwrap_or_else(|| t.none());
        let unioned = t.union(prev_ty.clone(), dt.clone());
        if !t.is_equivalent(&unioned, &prev_ty) {
            env.insert(*v, unioned);
            changed = true;
        }
    }
    changed
}

/// Find the stmt that bound `cond` (if any) and split the env into
/// (then_env, else_env) narrowing the predicate's operands accordingly.
fn union_envs<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    a: HashMap<Var, crate::types::Ty>,
    b: &HashMap<Var, crate::types::Ty>,
) -> HashMap<Var, crate::types::Ty> {
    let mut out = a;
    for (v, dt) in b {
        let prev_ty = out.remove(v).unwrap_or_else(|| t.none());
        let unioned = t.union(prev_ty, dt.clone());
        out.insert(*v, unioned);
    }
    out
}

/// Recursive core for if-condition narrowing.
/// Returns (then_env, else_env) with variable types refined for each branch.
fn narrow_for_cond<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    cond: Var,
    env: &HashMap<Var, crate::types::Ty>,
    stmts: &[Stmt],
) -> (
    HashMap<Var, crate::types::Ty>,
    HashMap<Var, crate::types::Ty>,
) {
    let mut then_env = env.clone();
    let mut else_env = env.clone();

    let prim = stmts.iter().find_map(|s| {
        let Stmt::Let(v, p) = s;
        if *v == cond { Some(p) } else { None }
    });

    let Some(prim) = prim else {
        return (then_env, else_env);
    };

    // Helper: env-lookup → T::Ty with `any` fallback.
    let lookup_ty = |t: &mut T, env: &HashMap<Var, crate::types::Ty>, v: &Var| -> T::Ty {
        env.get(v).cloned().unwrap_or_else(|| t.any())
    };

    match prim {
        Prim::BinOp(BinOp::And, a, b) => {
            // Truthy: both sub-conditions hold — narrow by a, then by b.
            let (then_a, else_a) = narrow_for_cond(t, *a, env, stmts);
            let (then_ab, _) = narrow_for_cond(t, *b, &then_a, stmts);
            // Falsy: at least one fails — union of the individual false branches.
            let (_, else_b) = narrow_for_cond(t, *b, env, stmts);
            return (then_ab, union_envs(t, else_a, &else_b));
        }
        Prim::BinOp(BinOp::Or, a, b) => {
            // Truthy: at least one holds — union of individual true branches.
            let (then_a, else_a) = narrow_for_cond(t, *a, env, stmts);
            let (then_b, _) = narrow_for_cond(t, *b, env, stmts);
            // Falsy: both fail — narrow by a's false, then b's false.
            let (_, else_ab) = narrow_for_cond(t, *b, &else_a, stmts);
            return (union_envs(t, then_a, &then_b), else_ab);
        }
        Prim::IsEmptyList(v) => {
            // fz-s9y.3 — when IsEmptyList returns true, the value is the
            // empty list `[]`, represented in the lattice as
            // `list_of(none())` (a list whose element type is uninhabited
            // — so only the empty list itself is in that set). Pre-s9y.3
            // this narrowed to `nil()`, which is the nil atom-like
            // value — at the time it was harmless because nil and [] shared
            // bits at runtime, but it produced `nil | list(X)` artifacts
            // throughout inferred spec types.
            let current_ty = lookup_ty(t, env, v);
            let none_inner = t.none();
            let empty_list = t.list(none_inner);
            let then_t = t.intersect(current_ty.clone(), empty_list);
            let any_inner = t.any();
            let any_list = t.list(any_inner);
            let else_t = t.intersect(current_ty, any_list);
            then_env.insert(*v, then_t);
            else_env.insert(*v, else_t);
        }
        Prim::BinOp(BinOp::Eq, a, b) => {
            let at = lookup_ty(t, env, a);
            let bt = lookup_ty(t, env, b);
            // Truthy: intersect the non-singleton operand with the singleton.
            // Falsy: subtract the singleton from the non-singleton operand
            // (.24.6 brought this in; .24.3 had it scoped out).
            if t.is_singleton_lit(&at) {
                let then_b = t.intersect(bt.clone(), at.clone());
                let else_b = t.difference(bt.clone(), at.clone());
                then_env.insert(*b, then_b);
                else_env.insert(*b, else_b);
            }
            if t.is_singleton_lit(&bt) {
                let then_a = t.intersect(at.clone(), bt.clone());
                let else_a = t.difference(at.clone(), bt.clone());
                then_env.insert(*a, then_a);
                else_env.insert(*a, else_a);
            }
        }
        Prim::BinOp(BinOp::Neq, a, b) => {
            // Mirror of Eq: narrow on the else branch (truthy) and diff on
            // then.
            let at = lookup_ty(t, env, a);
            let bt = lookup_ty(t, env, b);
            if t.is_singleton_lit(&at) {
                let else_b = t.intersect(bt.clone(), at.clone());
                let then_b = t.difference(bt.clone(), at.clone());
                else_env.insert(*b, else_b);
                then_env.insert(*b, then_b);
            }
            if t.is_singleton_lit(&bt) {
                let else_a = t.intersect(at.clone(), bt.clone());
                let then_a = t.difference(at.clone(), bt.clone());
                else_env.insert(*a, else_a);
                then_env.insert(*a, then_a);
            }
        }
        Prim::TypeTest(v, descr) => {
            let current_ty = lookup_ty(t, env, v);
            let then_t = t.intersect(current_ty.clone(), (**descr).clone());
            let else_t = t.difference(current_ty, (**descr).clone());
            then_env.insert(*v, then_t);
            else_env.insert(*v, else_t);
        }
        _ => {}
    }

    (then_env, else_env)
}

fn narrow_for_if<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    env: &HashMap<Var, crate::types::Ty>,
    cond: Var,
    stmts: &[Stmt],
) -> (
    HashMap<Var, crate::types::Ty>,
    HashMap<Var, crate::types::Ty>,
) {
    narrow_for_cond(t, cond, env, stmts)
}

fn type_prim<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
    t: &mut T,
    prim: &Prim,
    env: &HashMap<Var, crate::types::Ty>,
    m: &Module,
    const_vars: &HashSet<Var>,
) -> T::Ty {
    match prim {
        Prim::Const(c) => type_const(t, c, &m.atom_names),

        Prim::BinOp(op, a, b) => {
            let at = lookup(t, env, *a);
            let bt = lookup(t, env, *b);
            let fold = const_vars.contains(a) && const_vars.contains(b);
            type_binop(t, *op, &at, &bt, fold)
        }
        Prim::UnOp(op, v) => {
            let vt = lookup(t, env, *v);
            match op {
                UnOp::Neg => {
                    if const_vars.contains(v) {
                        let zero = t.int_lit(0);
                        numeric_result_fold(t, BinOp::Sub, &zero, &vt)
                    } else {
                        numeric_result(t, &vt, &vt)
                    }
                }
                UnOp::Not => t.bool(),
            }
        }

        Prim::MakeTuple(vs) => {
            let elem_tys: Vec<T::Ty> = vs.iter().map(|v| lookup(t, env, *v)).collect();
            t.tuple(&elem_tys)
        }
        Prim::TupleField(v, i) => {
            let vt = lookup(t, env, *v);
            // Find the widest arity in v's tuple clauses that covers index i;
            // project that component. Falls back to any when there's no
            // matching tuple shape.
            let max_arity = t.max_tuple_arity(&vt);
            if (*i as usize) < max_arity {
                let comps = t.tuple_projections(&vt, max_arity);
                comps
                    .into_iter()
                    .nth(*i as usize)
                    .unwrap_or_else(|| t.any())
            } else {
                t.any()
            }
        }

        Prim::MakeList(els, tail) => {
            let mut elem = t.none();
            for v in els {
                let vy = lookup(t, env, *v);
                elem = t.union(elem, vy);
            }
            if let Some(tl) = tail {
                let tt = lookup(t, env, *tl);
                let tail_elem_ty = t.list_element_type(&tt);
                elem = t.union(elem, tail_elem_ty);
            }
            t.list(elem)
        }
        Prim::ListCons(h, tl) => {
            let hy = lookup(t, env, *h);
            let tt = lookup(t, env, *tl);
            let ty_tail = t.list_element_type(&tt);
            let elem_ty = t.union(hy, ty_tail);
            t.list(elem_ty)
        }
        Prim::ListHead(l) => {
            let dy = lookup(t, env, *l);
            t.list_element_type(&dy)
        }
        Prim::ListTail(l) => {
            // fz-s9y.3 — the tail of a list is a list (possibly empty).
            // `list_of(elem)` covers the empty list via the
            // list_of(none()) subtype rule (see types::list_clause_empty);
            // no `| nil` union needed. Pre-s9y.3 we unioned with
            // `nil()` because empty list and nil shared bits, but
            // that artifact polluted inferred spec types with `nil | list(_)`.
            let lt = lookup(t, env, *l);
            let elem_ty = t.list_element_type(&lt);
            t.list(elem_ty)
        }
        Prim::IsEmptyList(_) => t.bool(),

        Prim::MakeMap(entries) => {
            let mut fields: Vec<(MapKey, T::Ty)> = Vec::new();
            let mut all_static = true;
            for (k, v) in entries {
                let vy = lookup(t, env, *v);
                match var_as_map_key(t, *k, env) {
                    Some(mk) => {
                        fields.push((mk, vy));
                    }
                    None => {
                        all_static = false;
                        break;
                    }
                }
            }
            if all_static && !entries.is_empty() {
                t.map(&fields)
            } else if entries.is_empty() {
                t.map(&[])
            } else {
                t.map_top()
            }
        }
        Prim::MapUpdate(base, entries) => {
            let mut dy = lookup(t, env, *base);
            for (k, v) in entries {
                let vt_ty = lookup(t, env, *v);
                if let Some(mk) = var_as_map_key(t, *k, env) {
                    dy = t.refine_map_field(&dy, &mk, &vt_ty);
                }
            }
            dy
        }
        Prim::MapGet(map, k) => {
            let mt = lookup(t, env, *map);
            // fz-swt.8 — `handle.value` on an opaque-typed handle.
            // When the subject is a singleton opaque and the key is
            // the atom `:value`, the typer answers with the inner
            // type T recorded for that opaque tag at alias
            // resolution. Visibility gating (declaring module vs
            // using module) is a *separate* concern surfaced in
            // `collect_diagnostics`; the lookup itself is unconditional
            // so out-of-module access reads its true T in the dead
            // path before the diagnostic fires.
            if let (Some(tag), Some(MapKey::Atom(key))) =
                (t.opaque_singleton(&mt), var_as_map_key(t, *k, env).as_ref())
                && key == "value"
                && let Some(inner) = m.opaque_inners.get(&tag)
            {
                return inner.clone();
            }
            let a = t.any();
            let n = t.nil();
            let fallback = t.union(a, n);
            if let Some(mk) = var_as_map_key(t, *k, env) {
                t.map_field_lookup(&mt, &mk).unwrap_or(fallback)
            } else {
                fallback
            }
        }
        Prim::MatcherMapGet(map, k) => {
            let mt = lookup(t, env, *map);
            let a = t.any();
            let n = t.nil();
            let fallback = t.union(a, n);
            if let Some(mk) = var_as_map_key(t, *k, env) {
                t.map_field_lookup(&mt, &mk).unwrap_or(fallback)
            } else {
                fallback
            }
        }
        Prim::IsMatcherMapMiss(_) => t.bool(),

        Prim::MakeVec(kind, _) => t.vec(match kind {
            VecKindIr::I64 => crate::types::VectorElem::Integer,
            VecKindIr::F64 => crate::types::VectorElem::Float,
            VecKindIr::U8 => crate::types::VectorElem::U8,
            VecKindIr::Bit => crate::types::VectorElem::Bit,
        }),
        // fz-axu.1 (K0) — bitstring construction types as the binary/bitstring
        // top (`str_t()`). Branded subset types (e.g. `utf8`) will layer on top
        // of this in later tickets. vec_u8/vec_bit remain reserved for explicit
        // vector(u8)/vector(bit) values.
        Prim::MakeBitstring(_) => t.str_t(),
        Prim::ConstBitstring(_, _) => t.str_t(),

        Prim::MakeClosure(_, fn_id, captured) => {
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
            let captures: Vec<T::Ty> = captured
                .iter()
                .map(|cv| env.get(cv).cloned().unwrap_or_else(|| t.any()))
                .collect();
            t.closure_lit((*fn_id).into(), captures, n_args)
        }

        Prim::Extern(eid, _) => {
            let ret_ty = m
                .extern_idx
                .get(eid)
                .map(|&i| m.externs[i].ret_descr.clone());
            ret_ty.unwrap_or_else(|| t.any())
        }

        Prim::TypeTest(v, descr) => {
            let vy = lookup(t, env, *v);
            // If vt ⊆ descr → always true; if vt ∩ descr = ∅ → always false;
            // otherwise unknown bool. Branch pruning in the typer's If-rewriting
            // pass then eliminates dead branches when the result is a singleton.
            if t.is_subtype(&vy, descr) {
                t.atom_lit("true")
            } else {
                let inter = t.intersect(vy, (**descr).clone());
                if t.is_empty(&inter) {
                    t.atom_lit("false")
                } else {
                    t.bool()
                }
            }
        }

        // fz-axu.4 (K3) — brand-mint. Take the source's structural type
        // and overlay `brands = {name}`. The result is a *minted brand
        // value*: its type carries both the brand tag (for nominal
        // identity / visibility) and the underlying structural axes (so
        // it remains usable as the underlying type wherever the K4 rule
        // grants `brand(name) ⊆ inner`). Pre-K4, the structural axes
        // alone keep it usable; the brand tag is just an extra label.
        Prim::Brand(v, name) => {
            let inner = lookup(t, env, *v);
            t.mint_brand(inner, name)
        }

        // Reader and struct ops: conservative Top until later tickets refine.
        Prim::AllocStruct(_, _) => t.any(),
        Prim::BitReaderInit(_) => t.any(),
        Prim::BitReadField { ty, .. } => {
            use crate::ast::BitType;
            // Returns Tuple([ok, value, new_reader]) on success, Tuple([false])
            // on failure. We over-approximate to a generic tuple shape; pattern
            // narrowing on TupleField then projects per-position. Field value
            // depends on the BitType.
            let value_t = match ty {
                BitType::Integer | BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => t.int(),
                BitType::Float => t.float(),
                BitType::Binary => t.vec(crate::types::VectorElem::U8),
                BitType::Bits => {
                    let u8 = t.vec(crate::types::VectorElem::U8);
                    let bit = t.vec(crate::types::VectorElem::Bit);
                    t.union(u8, bit)
                }
            };
            let bool1 = t.bool();
            let any_ty = t.any();
            let success = t.tuple(&[bool1, value_t, any_ty]);
            let bool2 = t.bool();
            let failure = t.tuple(&[bool2]);
            t.union(success, failure)
        }
        Prim::BitReaderDone(_) => t.bool(),
    }
}

fn type_const<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    c: &Const,
    atom_names: &[String],
) -> T::Ty {
    match c {
        Const::Int(n) => t.int_lit(*n),
        Const::Float(f) => t.float_lit(*f),
        Const::Atom(id) => {
            let name = atom_names
                .get(*id as usize)
                .map(String::as_str)
                .unwrap_or("?");
            t.atom_lit(name)
        }
        Const::Nil => t.nil(),
        Const::True => t.atom_lit("true"),
        Const::False => t.atom_lit("false"),
    }
}

fn type_binop<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    op: BinOp,
    a: &T::Ty,
    b: &T::Ty,
    fold: bool,
) -> T::Ty {
    use BinOp::*;
    match op {
        Add | Sub | Mul | Div | Mod => {
            if fold {
                numeric_result_fold(t, op, a, b)
            } else {
                numeric_result(t, a, b)
            }
        }
        Eq | Neq | Lt | Le | Gt | Ge => compare_result(t, op, a, b),
        And | Or => t.union(a.clone(), b.clone()),
    }
}

fn compare_result<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    op: BinOp,
    a: &T::Ty,
    b: &T::Ty,
) -> T::Ty {
    use BinOp::*;
    if let (Some(ai), Some(bi)) = (t.as_int_singleton(a), t.as_int_singleton(b)) {
        let result = match op {
            Eq => ai == bi,
            Neq => ai != bi,
            Lt => ai < bi,
            Le => ai <= bi,
            Gt => ai > bi,
            Ge => ai >= bi,
            _ => return t.bool(),
        };
        return if result {
            t.atom_lit("true")
        } else {
            t.atom_lit("false")
        };
    }
    if let (Some(af), Some(bf)) = (t.as_float_singleton(a), t.as_float_singleton(b)) {
        let result = match op {
            Eq => af == bf,
            Neq => af != bf,
            Lt => af < bf,
            Le => af <= bf,
            Gt => af > bf,
            Ge => af >= bf,
            _ => return t.bool(),
        };
        return if result {
            t.atom_lit("true")
        } else {
            t.atom_lit("false")
        };
    }
    t.bool()
}

fn numeric_result<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    a: &T::Ty,
    b: &T::Ty,
) -> T::Ty {
    let int_ty = t.int();
    let float_ty = t.float();
    let both_int = t.is_subtype(a, &int_ty) && t.is_subtype(b, &int_ty);
    let both_float = t.is_subtype(a, &float_ty) && t.is_subtype(b, &float_ty);
    if both_int {
        int_ty
    } else if both_float {
        float_ty
    } else {
        t.union(int_ty, float_ty)
    }
}

/// Like `numeric_result` but folds singleton operands to a literal result.
/// Only called when both operands are known IR-level constants (const_vars),
/// so the result cannot cascade into new narrow spec keys (fz-1pq.6).
fn numeric_result_fold<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    op: BinOp,
    a: &T::Ty,
    b: &T::Ty,
) -> T::Ty {
    use BinOp::*;
    if let (Some(ai), Some(bi)) = (t.as_int_singleton(a), t.as_int_singleton(b)) {
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
            return t.int_lit(r);
        }
    }
    if let (Some(af), Some(bf)) = (t.as_float_singleton(a), t.as_float_singleton(b)) {
        let result = match op {
            Add => Some(af + bf),
            Sub => Some(af - bf),
            Mul => Some(af * bf),
            Div => Some(af / bf),
            Mod => Some(af % bf),
            _ => None,
        };
        if let Some(r) = result {
            return t.float_lit(r);
        }
    }
    numeric_result(t, a, b)
}

fn lookup<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    env: &HashMap<Var, crate::types::Ty>,
    v: Var,
) -> T::Ty {
    env.get(&v).cloned().unwrap_or_else(|| t.any())
}

fn var_as_map_key<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &T,
    v: Var,
    env: &HashMap<Var, crate::types::Ty>,
) -> Option<MapKey> {
    env.get(&v).and_then(|ty| t.as_map_key(ty))
}

// Suppress unused imports under cfg(not(test)).
#[allow(dead_code)]
fn _suppress_block(_: &Block) {}

/// fz-pky.1 — within ONE spec's narrowed env, find the first Var
/// whose type became empty post-narrowing. Returns (Var, old_t, new_t)
/// if found; None if narrowing kept every var inhabited.
fn find_emptied_var<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    pre_env: &HashMap<crate::fz_ir::Var, crate::types::Ty>,
    branch_env: &HashMap<crate::fz_ir::Var, crate::types::Ty>,
) -> Option<(crate::fz_ir::Var, T::Ty, T::Ty)> {
    let mut keys: Vec<crate::fz_ir::Var> = branch_env.keys().copied().collect();
    keys.sort_by_key(|v| v.0);
    for v in keys {
        let new_ty = branch_env.get(&v).unwrap().clone();
        let old_ty = pre_env.get(&v).cloned().unwrap_or_else(|| t.any());
        if !t.is_equivalent(&new_ty, &old_ty) && t.is_empty(&new_ty) && !t.is_empty(&old_ty) {
            return Some((v, old_ty, new_ty));
        }
    }
    None
}

/// fz-pky.1 — build the unreachable-arm diagnostic from per-spec
/// dead-var records. We join old_t across specs so the type-note
/// reflects every specialization that contributed; new_t is similarly
/// joined for the narrow-note (in practice, when ALL specs found a
/// branch dead, each spec's new_t is `none` — joined, still `none`).
fn emit_unreachable<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::RenderTypes>(
    t: &mut T,
    module: &Module,
    fn_name: &str,
    term_span: crate::diag::Span,
    tag: &str,
    bb_id: crate::fz_ir::BlockId,
    dead_records: &[(crate::fz_ir::Var, T::Ty, T::Ty)],
) -> crate::diag::Diagnostic {
    use crate::diag::{Diagnostic, codes::TYPE_UNREACHABLE_ARM};
    // Pick the lowest-id Var across all records for label attribution
    // (stable, matches old single-spec behavior when only one spec).
    let pick = dead_records.iter().min_by_key(|(v, _, _)| v.0).unwrap();
    let (v, _, _) = pick;
    // Join the offending Var's pre-narrow types across every spec that
    // dropped this branch — that's the source-level view of the value.
    let mut joined_old = t.none();
    for (vv, ot, _) in dead_records {
        if *vv == *v {
            joined_old = t.union(joined_old, ot.clone());
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
        t.display_for_diag(&joined_old),
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
pub fn collect_diagnostics<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes
        + crate::types::VisibilityTypes,
>(
    t: &mut T,
    module: &Module,
    types: &ModuleTypes,
) -> crate::diag::Diagnostics {
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
    let mut specs_by_fn: HashMap<crate::fz_ir::FnId, Vec<Vec<crate::types::Ty>>> = HashMap::new();
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
        let any_key_ty = {
            let any = t.any();
            t.repeat(any, n_params)
        };
        let ft = type_fn(t, f, module, Some(&any_key_ty));
        adhoc_specs.insert(f.id, ft);
        specs_by_fn.entry(f.id).or_default().push(any_key_ty);
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
            let Term::If {
                cond,
                then_b,
                else_b,
                origin,
            } = b.terminator
            else {
                continue;
            };

            // fz-fyq.3 — only warn on user-authored Ifs. Synthesized
            // dispatch (pattern-bind, fn-clause selection, param guards)
            // is scaffolding the programmer didn't write; the typer can
            // prove some of its branches dead, but that's a property of
            // the lowering, not a bug in the source.
            if !matches!(origin, crate::fz_ir::BranchOrigin::User) {
                continue;
            }

            let term_span = module
                .source
                .term_span
                .get(&(f.id, b.id))
                .copied()
                .unwrap_or(Span::DUMMY);

            // For each spec, narrow this If and record whether each
            // branch is dead (and which Var made it dead, for the
            // diagnostic note).
            let mut dead_then: Vec<(crate::fz_ir::Var, T::Ty, T::Ty)> = Vec::new();
            let mut dead_else: Vec<(crate::fz_ir::Var, T::Ty, T::Ty)> = Vec::new();
            for key in keys {
                let ft = types
                    .spec_ty(f.id, key)
                    .or_else(|| adhoc_specs.get(&f.id))
                    .unwrap();
                let mut env: HashMap<Var, crate::types::Ty> =
                    ft.block_envs.get(&b.id).cloned().unwrap_or_default();
                for stmt in &b.stmts {
                    let Stmt::Let(v, prim) = stmt;
                    let pt_ty = type_prim(t, prim, &env, module, &HashSet::new());
                    env.insert(*v, pt_ty);
                }
                let (then_env, else_env) = narrow_for_if(t, &env, cond, &b.stmts);
                if let Some(d) = find_emptied_var(t, &env, &then_env) {
                    dead_then.push(d);
                }
                if let Some(d) = find_emptied_var(t, &env, &else_env) {
                    dead_else.push(d);
                }
            }

            // Emit only when EVERY spec found the branch dead.
            if dead_then.len() == total_specs {
                out.push(emit_unreachable(
                    t, module, &f.name, term_span, "then", then_b, &dead_then,
                ));
            }
            if dead_else.len() == total_specs {
                out.push(emit_unreachable(
                    t, module, &f.name, term_span, "else", else_b, &dead_else,
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
                let any_key = {
                    let any = t.any();
                    t.repeat(any, n_params)
                };
                ft_owned = Some(type_fn(t, f, module, Some(&any_key)));
                ft_owned.as_ref().unwrap()
            }
        };
        let mut blocks_sorted: Vec<&crate::fz_ir::Block> = f.blocks.iter().collect();
        blocks_sorted.sort_by_key(|b| b.id.0);
        for b in blocks_sorted {
            let mut env: HashMap<Var, crate::types::Ty> =
                ft.block_envs.get(&b.id).cloned().unwrap_or_default();
            let spans = module.source.stmt_spans.get(&(f.id, b.id));
            for (sidx, stmt) in b.stmts.iter().enumerate() {
                let Stmt::Let(v, prim) = stmt;
                if let Prim::BinOp(op, lhs, rhs) = prim
                    && matches!(op, BinOp::Eq | BinOp::Neq)
                {
                    // Lint only on cross-kind disjointness (int vs atom,
                    // float vs nil, etc.). Within a single axis, two
                    // disjoint literal sets (e.g. `1 == 2`) still fold to
                    // false at codegen but are not surprising to the
                    // reader, so we keep them silent.
                    let ta_ty = env.get(lhs).cloned().unwrap_or_else(|| t.none());
                    let tb_ty = env.get(rhs).cloned().unwrap_or_else(|| t.none());
                    let cross_kind = !t.is_empty(&ta_ty)
                        && !t.is_empty(&tb_ty)
                        && !t.kinds_overlap(&ta_ty, &tb_ty);
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
                            t.display_for_diag(&ta_ty),
                            t.display_for_diag(&tb_ty),
                        );
                        let d = Diagnostic::warning(TYPE_DEAD_BINOP, message, span)
                            .with_label(format!("in fn `{}`", f.name))
                            .with_note(note);
                        out.push(d);
                    }
                }
                // fz-l4c — arithmetic on opaque-typed operands is a
                // soundness leak. `pid`, `ref`, and user opaque aliases
                // happen to share bit-tag space with `int`, so `self() + 1`
                // computes a number today; reject it at type-check time.
                // Comparisons (`==`, `!=`) remain permitted — pid/ref
                // equality is load-bearing for the selective-receive
                // matcher.
                if let Prim::BinOp(op, lhs, rhs) = prim
                    && matches!(
                        op,
                        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod
                    )
                {
                    let ta_ty = env.get(lhs).cloned().unwrap_or_else(|| t.none());
                    let tb_ty = env.get(rhs).cloned().unwrap_or_else(|| t.none());
                    let lhs_opaque = t.opaque_singleton(&ta_ty);
                    let rhs_opaque = t.opaque_singleton(&tb_ty);
                    if lhs_opaque.is_some() || rhs_opaque.is_some() {
                        let span = spans
                            .and_then(|s| s.get(sidx).copied())
                            .unwrap_or(Span::DUMMY);
                        let opname = match op {
                            BinOp::Add => "+",
                            BinOp::Sub => "-",
                            BinOp::Mul => "*",
                            BinOp::Div => "/",
                            BinOp::Mod => "%",
                            _ => unreachable!(),
                        };
                        let (which, tag) = match (&lhs_opaque, &rhs_opaque) {
                            (Some(name), _) => ("left", name.as_str()),
                            (_, Some(name)) => ("right", name.as_str()),
                            _ => unreachable!(),
                        };
                        let message = format!(
                            "arithmetic `{}` is not defined for opaque type `{}`",
                            opname, tag
                        );
                        let note = format!(
                            "{} operand has type `{}`; opaque types are nominally \
                             disjoint from `int` and `float`. Use `==` / `!=` for \
                             identity comparison.",
                            which,
                            t.display_for_diag(if which == "left" { &ta_ty } else { &tb_ty }),
                        );
                        let d = Diagnostic::error(
                            crate::diag::codes::TYPE_OPAQUE_ARITHMETIC,
                            message,
                            span,
                        )
                        .with_label(format!("in fn `{}`", f.name))
                        .with_note(note);
                        out.push(d);
                    }
                }
                // fz-swt.8 — `handle.value` outside the declaring
                // module is a type error. Detect at MapGet sites where
                // the subject is a singleton opaque, the key is the
                // atom `:value`, the opaque has a recorded inner type
                // (i.e. was declared via `@type t :: opaque T`), and
                // the enclosing fn's module isn't the declaring module.
                if let Prim::MapGet(map_v, key_v) = prim {
                    let mt_ty = env.get(map_v).cloned().unwrap_or_else(|| t.none());
                    let opaque_tag = t.opaque_singleton(&mt_ty);
                    if let (Some(tag), Some(MapKey::Atom(key))) = (
                        opaque_tag.as_ref(),
                        var_as_map_key(t, *key_v, &env).as_ref(),
                    ) && key == "value"
                        && module.opaque_inners.contains_key(tag.as_str())
                        && let Err(err) = t.check_opaque_visibility(&mt_ty, fn_module_of(&f.name))
                    {
                        let span = spans
                            .and_then(|s| s.get(sidx).copied())
                            .unwrap_or(Span::DUMMY);
                        let d = Diagnostic::error(
                            crate::diag::codes::TYPE_OPAQUE_VISIBILITY,
                            format!("{}", err),
                            span,
                        )
                        .with_label(format!("in fn `{}`", f.name));
                        out.push(d);
                    }
                }
                let pt_ty = type_prim(t, prim, &env, module, &HashSet::new());
                env.insert(*v, pt_ty);
            }
        }
    }

    // fz-yxs — pure-codegen invariant for receive matchers and guards.
    // Walk every Term::ReceiveMatched; for each clause's guard FnId, walk
    // every block in the guard fn body and reject any impure Prim or
    // impure terminator (Call / Receive / Halt). The matcher itself is
    // backend-materialised from the pattern AST in B3, so there is nothing
    // to check at the IR level for patterns today; the pattern AST
    // grammar already forbids fn calls inside patterns, so the second
    // acceptance bullet ("typer rejects impure pattern") is vacuously
    // satisfied at parse/lowering.
    for f in &module.fns {
        for b in &f.blocks {
            let Term::ReceiveMatched { clauses, .. } = &b.terminator else {
                continue;
            };
            for c in clauses {
                let Some(g_fid) = c.guard else { continue };
                let g_fn = module.fn_by_id(g_fid);
                let guard_span = c.span;
                let mut impure: Option<String> = None;
                for gb in &g_fn.blocks {
                    if let Err(e) = check_pure_codegen(&gb.stmts) {
                        impure = Some(match e {
                            ImpureError::Stmt { kind, .. } => match kind {
                                ImpureKind::Allocates(what) => {
                                    format!("guard expression allocates via `{}`", what)
                                }
                                ImpureKind::Extern => "guard expression calls an extern".into(),
                            },
                            ImpureError::Term(_) => unreachable!(),
                        });
                        break;
                    }
                    if let Err(e) = check_pure_term(&gb.terminator) {
                        impure = Some(match e {
                            ImpureError::Term(ImpureTerm::Call) => {
                                "guard expression invokes a function (calls are not allowed)".into()
                            }
                            ImpureError::Term(ImpureTerm::Receive) => {
                                "guard expression contains a `receive` (not allowed)".into()
                            }
                            ImpureError::Term(ImpureTerm::Halt) => {
                                "guard expression halts (not allowed)".into()
                            }
                            ImpureError::Stmt { .. } => unreachable!(),
                        });
                        break;
                    }
                }
                if let Some(reason) = impure {
                    let d = Diagnostic::error(
                        crate::diag::codes::TYPE_IMPURE_RECEIVE_GUARD,
                        reason,
                        guard_span,
                    )
                    .with_label(format!("in fn `{}`", f.name))
                    .with_note(
                        "guards in `receive` must stay in the pure-codegen subset: \
                         constants, comparisons, type tests, and accessors — \
                         no function calls or allocations",
                    );
                    out.push(d);
                }
            }
        }
    }

    // fz-puj.30 (G1) — purity check for every FnCategory::Matcher fn.
    for d in check_matcher_purity(module) {
        out.push(d);
    }

    out
}

/// fz-puj.30 (G1) — verify every FnCategory::Matcher fn stays pure.
///
/// Matcher fns own matcher dispatch for case / multi-clause / with-else
/// (and ExternMatcher will join when receive migrates to a real IR fn).
/// Stmts must obey the pure-codegen subset (no alloc, no extern).
/// Terminators are laxer than for receive guards:
/// TailCall / Goto / If / Halt / Return are all allowed (TailCall is
/// the matcher's primary leaf dispatch); Call / CallClosure /
/// TailCallClosure / Receive / ReceiveMatched are forbidden because
/// they introduce side effects or allocate continuations.
pub fn check_matcher_purity(module: &Module) -> Vec<crate::diag::Diagnostic> {
    use crate::diag::{Diagnostic, Span};
    use crate::fz_ir::{FnCategory, Term};

    let mut out: Vec<Diagnostic> = Vec::new();
    for f in &module.fns {
        if f.category != FnCategory::Matcher {
            continue;
        }
        let mut reason: Option<String> = None;
        for blk in &f.blocks {
            if let Err(e) = check_pure_codegen(&blk.stmts) {
                reason = Some(match e {
                    ImpureError::Stmt {
                        kind: ImpureKind::Allocates(what),
                        ..
                    } => format!("matcher fn body allocates via `{}`", what),
                    ImpureError::Stmt {
                        kind: ImpureKind::Extern,
                        ..
                    } => "matcher fn body calls an extern".into(),
                    ImpureError::Term(_) => unreachable!(),
                });
                break;
            }
            match &blk.terminator {
                Term::Call { .. } | Term::CallClosure { .. } | Term::TailCallClosure { .. } => {
                    reason = Some("matcher fn body invokes a function via Call/CallClosure".into());
                    break;
                }
                Term::Receive { .. } | Term::ReceiveMatched { .. } => {
                    reason = Some("matcher fn body contains a `receive`".into());
                    break;
                }
                Term::Goto(..)
                | Term::If { .. }
                | Term::TailCall { .. }
                | Term::Halt(_)
                | Term::Return(_) => {}
            }
        }
        if let Some(msg) = reason {
            let d = Diagnostic::error(crate::diag::codes::TYPE_IMPURE_MATCHER, msg, Span::DUMMY)
                .with_label(format!("in matcher fn `{}`", f.name))
                .with_note(
                    "Matcher fns own matcher dispatch and must stay pure: no allocation, \
                     no extern, no Call / CallClosure / Receive. Side effects break the \
                     matcher's ability to be inlined back at trivial sites and the eli5 \
                     'matchers are pure routers' guarantee.",
                );
            out.push(d);
        }
    }
    out
}

/// fz-swt.8 — module path of a qualified fn name. The IR-side
/// `FnIr.name` is dotted (`"Mod.fname"` or `"A.B.fname"`); the typer's
/// opaque-visibility gate compares against the `"Mod"` prefix of the
/// alias's qualified tag (which uses `::` to separate the module from
/// the alias). Top-level fns return the empty string, matching the
/// owner-module convention for top-level / runtime-prelude opaques.
fn fn_module_of(fn_name: &str) -> &str {
    match fn_name.rfind('.') {
        Some(i) => &fn_name[..i],
        None => "",
    }
}

/// True iff `a` and `b` have at least one axis on which both are
/// non-empty. Used by the VR.5a `type/dead-binop` lint to distinguish
/// "different kinds" (worth surfacing) from "same kind, narrowed to
/// disjoint literals" (silent fold).
/// .11.24.5: refine `MakeVec(I64, els)` to `MakeVec(F64, els)` when any
/// element is typed Float. Errors on the "mixed Int and Float" case under
/// the no-auto-promotion rule.
///
/// Operates in-place on `module`. Caller supplies a typer output that was
/// produced from the same module shape (run `type_module(module)` first).
pub fn rewrite_vec_kinds<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &mut Module,
    types: &ModuleTypes,
) -> Result<(), String> {
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
                    let any_key = {
                        let any = t.any();
                        t.repeat(any, n_params)
                    };
                    type_fn(t, f, module, Some(&any_key))
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
                        let d_ty: T::Ty = vars.get(&ev).cloned().unwrap_or_else(|| t.any());
                        let f_ty = t.float();
                        let i_ty = t.int();
                        let d_inter_f = t.intersect(d_ty.clone(), f_ty);
                        let d_inter_i = t.intersect(d_ty.clone(), i_ty.clone());
                        let meets_float = !t.is_empty(&d_inter_f);
                        let misses_int = t.is_empty(&d_inter_i);
                        if meets_float && misses_int {
                            any_float = true;
                        } else if t.is_subtype(&d_ty, &i_ty) {
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
// fz-ul4.29.12.1 — Cont input-type key helpers
// ----------------------------------------------------------------------

/// Reconstruct the per-Var env at the *terminator* of `block` under
/// `caller_ft`. Starts from `caller_ft.block_envs[block.id]` (which
/// already incorporates if-narrowing from predecessor blocks) and
/// folds in each Let by re-applying `type_prim`. This mirrors the
/// typer's own propagation pass at `type_module`'s `callsite_keys`
/// site (`ir_typer.rs:142-145`).
fn env_at_terminator<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
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
    for stmt in &block.stmts {
        let Stmt::Let(v, prim) = stmt;
        let pt_ty = type_prim(t, prim, &env, module, &HashSet::new());
        env.insert(*v, pt_ty);
    }
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
    let spec_keys: Vec<(FnId, Vec<crate::types::Ty>)> = spec_registry
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
        if let Some(sid) = spec_registry.resolve(main_fn.id, &key) {
            worklist.push(sid.0);
        }
    }
    // Caller-supplied seeds: closure-target specs (dispatched via stub_fp
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
            match &blk.terminator {
                Term::Call {
                    ident: _,
                    callee,
                    args,
                    continuation,
                } => {
                    let key = pad_to_arity(*callee, arg_tys(args));
                    if let Some(sid) = spec_registry.resolve(*callee, &key) {
                        worklist.push(sid.0);
                    }
                    let cont_key = cont_input_key(t, blk, continuation, ft, module, module_types);
                    if let Some(sid) = spec_registry.resolve(continuation.fn_id, &cont_key) {
                        worklist.push(sid.0);
                    }
                }
                Term::TailCall { callee, args, .. } => {
                    let key = pad_to_arity(*callee, arg_tys(args));
                    if let Some(sid) = spec_registry.resolve(*callee, &key) {
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
                        if let Some(sid) = spec_registry.resolve(target, &key) {
                            worklist.push(sid.0);
                        }
                    }
                    let cont_key = cont_input_key(t, blk, continuation, ft, module, module_types);
                    if let Some(sid) = spec_registry.resolve(continuation.fn_id, &cont_key) {
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
                        if let Some(sid) = spec_registry.resolve(target, &key) {
                            worklist.push(sid.0);
                        }
                    }
                }
                Term::Receive {
                    continuation,
                    ident: _,
                } => {
                    let cont_key = cont_input_key(t, blk, continuation, ft, module, module_types);
                    if let Some(sid) = spec_registry.resolve(continuation.fn_id, &cont_key) {
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
                        if let Some(sid) = spec_registry.resolve(fid, &key) {
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

// ----------------------------------------------------------------------
// fz-73m — pretty-printer for ModuleTypes (golden spec dump).
// ----------------------------------------------------------------------

/// Deterministic text dump of `ModuleTypes`. One stanza per (FnId, key)
/// spec; specs are sorted by FnId, then by lexicographic display-string of
/// the key so the output is stable across runs and HashMap iteration
/// orders.
///
/// Format is intended for golden-file diffing — every line is a comment
/// (`;` prefix) so the file reads like an annotated CLIF dump. Consumers
/// should treat the output as opaque text; the goal is that a human can
/// eyeball "are the inferred types what I expect for this fixture?"
/// without running codegen.
pub fn pretty_module_types<
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::RenderTypes,
>(
    t: &mut T,
    m: &Module,
    mt: &ModuleTypes,
) -> String {
    fn tys_str<
        T: crate::types::Types<Ty = crate::types::Ty>
            + crate::types::ClosureTypes
            + crate::types::RenderTypes,
    >(
        t: &T,
        ts: &[crate::types::Ty],
    ) -> String {
        let parts: Vec<String> = ts.iter().map(|ty| t.display(ty)).collect();
        format!("[{}]", parts.join(", "))
    }

    let any_ty = t.any();
    let fn_name = |fid: FnId| -> String {
        m.fns
            .iter()
            .find(|f| f.id == fid)
            .map(|f| f.name.clone())
            .unwrap_or_else(|| format!("?fn{}", fid.0))
    };

    let mut keys: Vec<&(FnId, Vec<crate::types::Ty>)> = mt.specs.keys().collect();
    keys.sort_by(|a, b| {
        a.0.0
            .cmp(&b.0.0)
            .then_with(|| tys_str(&*t, &a.1).cmp(&tys_str(&*t, &b.1)))
    });

    let mut out = String::new();
    for spec_key in keys {
        let (fid, key) = spec_key;
        let ft = &mt.specs[spec_key];
        let f = m.fn_by_id(*fid);
        let entry = f.block(f.entry);
        let arity = entry.params.len();

        out.push_str(&format!("; spec {}({}) #fn={}\n", f.name, arity, fid.0));
        out.push_str(&format!(";   key:    {}\n", tys_str(&*t, key)));

        let ret = mt.effective_returns.get(spec_key);
        out.push_str(&format!(
            ";   return: {}\n",
            ret.map(|ty| t.display(ty))
                .unwrap_or_else(|| t.display(&any_ty))
        ));

        if !ft.fn_constants.is_empty() {
            let mut fcs: Vec<(&Var, &FnId)> = ft.fn_constants.iter().collect();
            fcs.sort_by_key(|(v, _)| v.0);
            out.push_str(";   fn_constants:\n");
            for (v, fc) in fcs {
                out.push_str(&format!(";     Var({}) = {}#{}\n", v.0, fn_name(*fc), fc.0));
            }
        }

        let mut vars: Vec<(&Var, &crate::types::Ty)> = ft.vars.iter().collect();
        vars.sort_by_key(|(v, _)| v.0);
        out.push_str(";   vars:\n");
        for (v, ty) in vars {
            out.push_str(&format!(";     Var({}) :: {}\n", v.0, t.display(ty)));
        }

        let mut blocks: Vec<&Block> = f.blocks.iter().collect();
        blocks.sort_by_key(|b| b.id.0);
        out.push_str(";   exits:\n");
        for b in blocks {
            let bid = b.id.0;
            match &b.terminator {
                Term::Return(v) => {
                    let d = ft.vars.get(v).unwrap_or(&any_ty);
                    out.push_str(&format!(
                        ";     blk{} Return Var({})    :: {}\n",
                        bid,
                        v.0,
                        t.display(d)
                    ));
                }
                Term::Halt(v) => {
                    let d = ft.vars.get(v).unwrap_or(&any_ty);
                    out.push_str(&format!(
                        ";     blk{} Halt Var({})      :: {}\n",
                        bid,
                        v.0,
                        t.display(d)
                    ));
                }
                Term::TailCall { callee, args, .. } => {
                    let arg_tys: Vec<crate::types::Ty> = args
                        .iter()
                        .map(|av| ft.vars.get(av).cloned().unwrap_or_else(|| any_ty.clone()))
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
                        tys_str(&*t, &arg_tys)
                    ));
                }
                Term::Call {
                    ident: _,
                    callee,
                    args,
                    continuation,
                } => {
                    let arg_tys: Vec<crate::types::Ty> = args
                        .iter()
                        .map(|av| ft.vars.get(av).cloned().unwrap_or_else(|| any_ty.clone()))
                        .collect();
                    let arg_vars: Vec<String> =
                        args.iter().map(|v| format!("Var({})", v.0)).collect();
                    let cap_vars: Vec<String> = continuation
                        .captured
                        .iter()
                        .map(|v| format!("Var({})", v.0))
                        .collect();
                    let ck = cont_input_key(t, b, continuation, ft, m, mt);
                    out.push_str(&format!(
                        ";     blk{} Call {}#{}({})\n",
                        bid,
                        fn_name(*callee),
                        callee.0,
                        arg_vars.join(", ")
                    ));
                    out.push_str(&format!(
                        ";              callee_key={}\n",
                        tys_str(&*t, &arg_tys)
                    ));
                    out.push_str(&format!(
                        ";              cont {}#{} captured=[{}]\n",
                        fn_name(continuation.fn_id),
                        continuation.fn_id.0,
                        cap_vars.join(", ")
                    ));
                    out.push_str(&format!(";              cont_key={}\n", tys_str(&*t, &ck)));
                }
                Term::CallClosure {
                    ident: _,
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
                    let ck = cont_input_key(t, b, continuation, ft, m, mt);
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
                    out.push_str(&format!(";              cont_key={}\n", tys_str(&*t, &ck)));
                }
                Term::TailCallClosure {
                    closure,
                    args,
                    ident: _,
                } => {
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
                Term::Receive {
                    continuation,
                    ident: _,
                } => {
                    let cap_vars: Vec<String> = continuation
                        .captured
                        .iter()
                        .map(|v| format!("Var({})", v.0))
                        .collect();
                    let ck = cont_input_key(t, b, continuation, ft, m, mt);
                    out.push_str(&format!(
                        ";     blk{} Receive cont {}#{} captured=[{}]\n",
                        bid,
                        fn_name(continuation.fn_id),
                        continuation.fn_id.0,
                        cap_vars.join(", ")
                    ));
                    out.push_str(&format!(";              cont_key={}\n", tys_str(&*t, &ck)));
                }
                // fz-yxs — selective receive: render clauses (with body
                // fn ids + bound names) and the after clause if present.
                Term::ReceiveMatched {
                    clauses,
                    after,
                    pinned,
                    captures,
                    ..
                } => {
                    let pin_vars: Vec<String> = pinned
                        .iter()
                        .map(|(n, v)| format!("^{}=Var({})", n, v.0))
                        .collect();
                    let cap_vars: Vec<String> =
                        captures.iter().map(|v| format!("Var({})", v.0)).collect();
                    out.push_str(&format!(
                        ";     blk{} ReceiveMatched pinned=[{}] caps=[{}]\n",
                        bid,
                        pin_vars.join(", "),
                        cap_vars.join(", "),
                    ));
                    for (i, c) in clauses.iter().enumerate() {
                        out.push_str(&format!(
                            ";              clause[{}] body={}#{} bound=[{}]{}\n",
                            i,
                            fn_name(c.body),
                            c.body.0,
                            c.bound_names.join(", "),
                            match c.guard {
                                Some(g) => format!(" guard={}#{}", fn_name(g), g.0),
                                None => String::new(),
                            },
                        ));
                    }
                    if let Some(a) = after {
                        out.push_str(&format!(
                            ";              after timeout=Var({}) body={}#{}\n",
                            a.timeout.0,
                            fn_name(a.body),
                            a.body.0,
                        ));
                    }
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
                Term::If {
                    cond,
                    then_b,
                    else_b,
                    ..
                } => {
                    out.push_str(&format!(
                        ";     blk{} If Var({}) ? blk{} : blk{}\n",
                        bid, cond.0, then_b.0, else_b.0
                    ));
                }
            }
        }
        out.push('\n');
    }
    out
}

// ----------------------------------------------------------------------
// fz-e4u — pure-codegen subset check
// ----------------------------------------------------------------------
//
// Used by fz-recv to enforce that pattern arms and guard expressions in
// `receive do … end` lower only to read-only / non-allocating primitives.
// When this property holds for an expression, its compiled matcher can be
// invoked from the sender thread (per docs/receive-matched.md §2.3,
// §3.4) with no allocator interaction, no FFI re-entry, and no GC race.
//
// The check is a pure structural walk over `&[Stmt]` and an optional
// terminator. It does **not** consult the typer's worklist results; it
// runs strictly on the IR produced by lowering. fz-yxs (E2) wires the
// check into the `Term::ReceiveMatched` typer rule.
//
// The API below is consumed by `collect_diagnostics`' Term::ReceiveMatched
// guard scan (fz-yxs).

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImpureKind {
    /// The prim allocates on the per-process heap. Variant name is the
    /// offending Prim's variant label for diagnostics.
    Allocates(&'static str),
    /// `Prim::Extern(_)` — any FFI call. Even a side-effect-free FFI is
    /// rejected because the check has no way to verify its body, and a
    /// rogue FFI can allocate, send, receive, or re-enter the scheduler.
    Extern,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImpureTerm {
    /// `Call` / `TailCall` / `CallClosure` / `TailCallClosure` — invoke
    /// arbitrary user code with arbitrary effects.
    Call,
    /// `Receive` — a matcher invoking receive would deadlock the scheduler.
    Receive,
    /// `Halt` — exits the task; meaningless inside a matcher.
    Halt,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImpureError {
    Stmt { index: usize, kind: ImpureKind },
    Term(ImpureTerm),
}

/// True iff `p` is in the pure-codegen subset. See module-level comment
/// for the rationale; see `docs/receive-matched.md §2.3` for the design
/// constraint this enforces.
pub fn prim_is_pure(p: &crate::fz_ir::Prim) -> Result<(), ImpureKind> {
    use crate::fz_ir::Prim::*;
    match p {
        Const(_)
        | BinOp(_, _, _)
        | UnOp(_, _)
        | ListHead(_)
        | ListTail(_)
        | IsEmptyList(_)
        | TupleField(_, _)
        | MapGet(_, _)
        | MatcherMapGet(_, _)
        | IsMatcherMapMiss(_)
        | BitReaderInit(_)
        | BitReadField { .. }
        | BitReaderDone(_)
        | TypeTest(_, _)
        | Brand(_, _) => Ok(()),

        AllocStruct(_, _) => Err(ImpureKind::Allocates("AllocStruct")),
        ListCons(_, _) => Err(ImpureKind::Allocates("ListCons")),
        MakeTuple(_) => Err(ImpureKind::Allocates("MakeTuple")),
        MakeList(_, _) => Err(ImpureKind::Allocates("MakeList")),
        MakeClosure(_, _, _) => Err(ImpureKind::Allocates("MakeClosure")),
        MakeMap(_) => Err(ImpureKind::Allocates("MakeMap")),
        MapUpdate(_, _) => Err(ImpureKind::Allocates("MapUpdate")),
        MakeVec(_, _) => Err(ImpureKind::Allocates("MakeVec")),
        MakeBitstring(_) => Err(ImpureKind::Allocates("MakeBitstring")),
        ConstBitstring(_, _) => Err(ImpureKind::Allocates("ConstBitstring")),

        Extern(_, _) => Err(ImpureKind::Extern),
    }
}

/// Walk every Let-bound Prim in `stmts`; first offender wins.
pub fn check_pure_codegen(stmts: &[crate::fz_ir::Stmt]) -> Result<(), ImpureError> {
    use crate::fz_ir::Stmt;
    for (i, s) in stmts.iter().enumerate() {
        let Stmt::Let(_, p) = s;
        prim_is_pure(p).map_err(|kind| ImpureError::Stmt { index: i, kind })?;
    }
    Ok(())
}

/// Only Goto / If / Return are allowed in matcher / guard lowering.
pub fn check_pure_term(term: &crate::fz_ir::Term) -> Result<(), ImpureError> {
    use crate::fz_ir::Term::*;
    match term {
        Goto(_, _) | If { .. } | Return(_) => Ok(()),
        Call { .. } | TailCall { .. } | CallClosure { .. } | TailCallClosure { .. } => {
            Err(ImpureError::Term(ImpureTerm::Call))
        }
        Receive { .. } | ReceiveMatched { .. } => Err(ImpureError::Term(ImpureTerm::Receive)),
        Halt(_) => Err(ImpureError::Term(ImpureTerm::Halt)),
    }
}

#[cfg(test)]
mod purity_tests {
    use super::*;
    use crate::fz_ir::{BinOp, BlockId, BranchOrigin, Const, ExternId, Prim, Stmt, Term, Var};
    use crate::types::Types;

    fn v(n: u32) -> Var {
        Var(n)
    }
    fn s(p: Prim) -> Stmt {
        Stmt::Let(v(0), p)
    }

    #[test]
    fn pure_const_int_accepted() {
        assert!(check_pure_codegen(&[s(Prim::Const(Const::Int(42)))]).is_ok());
    }

    #[test]
    fn pure_tuple_field_accepted() {
        assert!(check_pure_codegen(&[s(Prim::TupleField(v(1), 0))]).is_ok());
    }

    #[test]
    fn pure_list_head_tail_is_empty_accepted() {
        let stmts = vec![
            s(Prim::ListHead(v(1))),
            s(Prim::ListTail(v(1))),
            s(Prim::IsEmptyList(v(1))),
        ];
        assert!(check_pure_codegen(&stmts).is_ok());
    }

    #[test]
    fn pure_binop_unop_accepted() {
        let stmts = vec![
            s(Prim::BinOp(BinOp::Eq, v(1), v(2))),
            s(Prim::BinOp(BinOp::Add, v(1), v(2))),
        ];
        assert!(check_pure_codegen(&stmts).is_ok());
    }

    #[test]
    fn pure_type_test_accepted() {
        let mut t = crate::types::ConcreteTypes;
        let stmts = vec![s(Prim::TypeTest(v(1), Box::new(t.int())))];
        assert!(check_pure_codegen(&stmts).is_ok());
    }

    #[test]
    fn pure_map_get_accepted() {
        assert!(check_pure_codegen(&[s(Prim::MapGet(v(1), v(2)))]).is_ok());
    }

    #[test]
    fn alloc_struct_rejected() {
        match check_pure_codegen(&[s(Prim::AllocStruct(0, vec![]))]) {
            Err(ImpureError::Stmt {
                index: 0,
                kind: ImpureKind::Allocates("AllocStruct"),
            }) => {}
            other => panic!("expected AllocStruct rejection, got {:?}", other),
        }
    }

    #[test]
    fn make_tuple_rejected() {
        assert!(matches!(
            check_pure_codegen(&[s(Prim::MakeTuple(vec![v(1), v(2)]))]),
            Err(ImpureError::Stmt {
                kind: ImpureKind::Allocates("MakeTuple"),
                ..
            })
        ));
    }

    #[test]
    fn make_list_rejected() {
        assert!(matches!(
            check_pure_codegen(&[s(Prim::MakeList(vec![v(1)], None))]),
            Err(ImpureError::Stmt {
                kind: ImpureKind::Allocates("MakeList"),
                ..
            })
        ));
    }

    #[test]
    fn list_cons_rejected() {
        assert!(matches!(
            check_pure_codegen(&[s(Prim::ListCons(v(1), v(2)))]),
            Err(ImpureError::Stmt {
                kind: ImpureKind::Allocates("ListCons"),
                ..
            })
        ));
    }

    #[test]
    fn make_map_and_update_rejected() {
        assert!(matches!(
            check_pure_codegen(&[s(Prim::MakeMap(vec![]))]),
            Err(ImpureError::Stmt {
                kind: ImpureKind::Allocates("MakeMap"),
                ..
            })
        ));
        assert!(matches!(
            check_pure_codegen(&[s(Prim::MapUpdate(v(1), vec![]))]),
            Err(ImpureError::Stmt {
                kind: ImpureKind::Allocates("MapUpdate"),
                ..
            })
        ));
    }

    #[test]
    fn make_bitstring_rejected() {
        assert!(matches!(
            check_pure_codegen(&[s(Prim::MakeBitstring(vec![]))]),
            Err(ImpureError::Stmt {
                kind: ImpureKind::Allocates("MakeBitstring"),
                ..
            })
        ));
    }

    #[test]
    fn extern_rejected_even_if_harmless() {
        assert!(matches!(
            check_pure_codegen(&[s(Prim::Extern(ExternId(0), vec![]))]),
            Err(ImpureError::Stmt {
                kind: ImpureKind::Extern,
                ..
            })
        ));
    }

    #[test]
    fn first_impure_stmt_index_reported() {
        let stmts = vec![
            s(Prim::Const(Const::Int(1))),
            s(Prim::TupleField(v(1), 0)),
            s(Prim::MakeTuple(vec![v(1)])),
            s(Prim::MakeList(vec![v(1)], None)),
        ];
        match check_pure_codegen(&stmts) {
            Err(ImpureError::Stmt { index, .. }) => assert_eq!(index, 2),
            other => panic!("expected Stmt error at index 2, got {:?}", other),
        }
    }

    #[test]
    fn term_goto_if_return_accepted() {
        assert!(check_pure_term(&Term::Goto(BlockId(0), vec![])).is_ok());
        assert!(check_pure_term(&Term::Return(v(0))).is_ok());
        assert!(
            check_pure_term(&Term::If {
                cond: v(0),
                then_b: BlockId(0),
                else_b: BlockId(1),
                origin: BranchOrigin::PatternBind,
            })
            .is_ok()
        );
    }

    #[test]
    fn term_halt_rejected() {
        assert!(matches!(
            check_pure_term(&Term::Halt(v(0))),
            Err(ImpureError::Term(ImpureTerm::Halt))
        ));
    }

    // fz-puj.30 (G1) — module-level matcher purity check.

    fn build_module_with_matcher(extra_let: Option<Prim>, term: Term) -> crate::fz_ir::Module {
        use crate::fz_ir::{FnBuilder, FnCategory, FnId, Module};
        let mut m = Module::default();
        let fid = FnId(100);
        let mut b = FnBuilder::new(fid, "match_x").with_category(FnCategory::Matcher);
        let p = b.fresh_var();
        let entry = b.block(vec![p]);
        if let Some(prim) = extra_let {
            let _ = b.let_(entry, prim);
        }
        b.set_terminator(entry, term);
        let f = b.build();
        m.fn_idx.insert(f.id, m.fns.len());
        m.fns.push(f);
        m
    }

    #[test]
    fn matcher_purity_accepts_pure_router() {
        let module =
            build_module_with_matcher(Some(Prim::Const(Const::Int(0))), Term::Return(v(0)));
        let diags = crate::ir_typer::check_matcher_purity(&module);
        assert!(
            diags.is_empty(),
            "pure matcher should produce no diags: {:?}",
            diags
        );
    }

    #[test]
    fn matcher_purity_rejects_extern_stmt() {
        let module =
            build_module_with_matcher(Some(Prim::Extern(ExternId(0), vec![])), Term::Return(v(0)));
        let diags = crate::ir_typer::check_matcher_purity(&module);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, crate::diag::codes::TYPE_IMPURE_MATCHER);
        assert!(diags[0].message.contains("extern"));
    }

    #[test]
    fn matcher_purity_rejects_call_terminator() {
        use crate::fz_ir::{CallsiteIdent, Cont, FnId};
        let module = build_module_with_matcher(
            None,
            Term::Call {
                ident: CallsiteIdent::from_source(crate::diag::Span::DUMMY),
                callee: FnId(99),
                args: vec![v(0)],
                continuation: Cont {
                    fn_id: FnId(98),
                    captured: vec![],
                },
            },
        );
        let diags = crate::ir_typer::check_matcher_purity(&module);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("Call"));
    }

    #[test]
    fn matcher_purity_allows_tailcall() {
        use crate::fz_ir::{CallsiteIdent, FnId};
        let module = build_module_with_matcher(
            None,
            Term::TailCall {
                ident: CallsiteIdent::from_source(crate::diag::Span::DUMMY),
                callee: FnId(99),
                args: vec![v(0)],
                is_back_edge: false,
            },
        );
        let diags = crate::ir_typer::check_matcher_purity(&module);
        assert!(
            diags.is_empty(),
            "matcher with TailCall terminator should be pure: {:?}",
            diags
        );
    }
}

// ----------------------------------------------------------------------
// Tests
// ----------------------------------------------------------------------

#[cfg(test)]
#[path = "ir_typer_tests.rs"]
mod tests;
