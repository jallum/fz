use crate::fz_ir::{CallsiteId, EmitSlot, FnId, FnIr, Module};
use std::collections::HashMap;

#[derive(Debug, Clone, Default)]
pub struct FnTypes {
    /// Definition-site type for each Var. Block params get the join of their
    /// predecessor args; Let-bound vars get their Prim's type under the env
    /// at that point in the block.
    pub vars: HashMap<crate::fz_ir::Var, crate::types::Ty>,
    /// Entry env per block, with branch narrowing applied at If terminators.
    pub block_envs: HashMap<crate::fz_ir::BlockId, HashMap<crate::fz_ir::Var, crate::types::Ty>>,
    /// fz-ul4.29.10.1 — side-channel: vars known to hold a specific
    /// top-level fn identity (zero-capture `MakeClosure(F, [])` only).
    /// Used by `.29.10.2`/`.3` to register narrow specs and rewrite
    /// known-target `CallClosure → Call`. The type token deliberately carries
    /// no FnId identity; this map lives alongside it.
    pub fn_constants: HashMap<crate::fz_ir::Var, FnId>,
    /// Blocks provably reachable from the entry under the inferred types.
    /// If terminators whose condition is a singleton bool prune the dead
    /// branch. Used by `compute_return_for_spec` to ignore returns that
    /// can never execute.
    pub reachable_blocks: std::collections::HashSet<crate::fz_ir::BlockId>,
    /// Per-spec branch facts used by per-spec codegen folding. These are
    /// stricter than `ModuleTypes::dead_branches`: a branch can be dead for
    /// one specialization even when another specialization keeps it live.
    pub dead_branches: HashMap<crate::fz_ir::BlockId, crate::fz_ir::DeadBranch>,
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
    pub dispatches: HashMap<crate::fz_ir::CallsiteId, SpecKey>,
    /// Per-spec facts about how a call result is consumed by its return
    /// edge. This is intentionally parallel to `dispatches`: two caller
    /// specs can visit the same source callsite with different result-hole
    /// capabilities, and demand selection must follow this edge fact rather
    /// than blindly inheriting the caller spec's demand.
    pub return_uses: HashMap<crate::fz_ir::CallsiteId, ReturnUse>,
    /// Typed executable plan for ListTail return-use edges. Kept separate
    /// from `return_uses` because not every return-use fact needs lowering
    /// help; plans name the concrete source operands the eventual backend
    /// lowering must consume. Plans are caller-spec keyed because one
    /// syntactic callsite can be visited under multiple return demands.
    pub return_context_plans: HashMap<ReturnContextPlanKey, ReturnContextPlan>,
    /// Per-spec concrete C marshal classes for extern call arguments.
    ///
    /// Variadic `Auto` args are resolved after this `FnTypes` has inferred
    /// Var types. The map is per spec because the same syntactic call can be
    /// reached under different argument types in different specializations.
    pub extern_marshals: HashMap<crate::fz_ir::ExternMarshalSite, crate::fz_ir::ExternTy>,
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
    pub specs: HashMap<SpecKey, FnTypes>,
    /// fz-2yw.2 — Kleene LFP of every spec's effective return type.
    /// Maintained incrementally by the worklist (fz-5j5.3): each spec's
    /// return is recomputed (via `compute_return_for_spec`) after every
    /// visit, and changes re-enqueue the spec's `return_readers`.
    /// Consumers (cont_slot0_descr, pretty_module_types, walker
    /// slot0_descr) read here instead of recursing on demand.
    pub effective_returns: HashMap<SpecKey, crate::types::Ty>,
    /// fz-afs.12 — secondary index: FnId → all-any key for that fn.
    /// Populated in `type_module` from the final specs map. Enables O(1)
    /// any-key lookup without the per-element is_equiv scan.
    pub any_key_specs: HashMap<FnId, Vec<crate::types::KeySlot>>,
    /// Stable per-family precedence for specialization selection.
    pub spec_precedence: HashMap<SpecKey, u32>,
    /// Per-spec summary of effects that are relevant to return-demand
    /// scheduling. Allocation is tracked separately from externally
    /// observable barriers so future demand selection can move allocation
    /// only when no runtime-visible operation can observe the move.
    pub effect_summaries: HashMap<SpecKey, EffectSummary>,
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

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct EffectSummary {
    /// Allocates on the current process heap. Allocation by itself is not
    /// externally observable; it becomes scheduling-relevant when paired with
    /// an observer such as Process.heap_alloc_stats().
    pub allocates: bool,
    /// Performs an externally observable operation or reaches one through a
    /// call. Externs, receive/send/spawn hooks, and halt are barriers.
    pub observable: bool,
    /// Reads process allocation counters. This is the precise runtime observer
    /// that makes allocation timing visible to source programs.
    pub reads_allocation_stats: bool,
    /// Interacts with scheduler/mailbox/process identity state.
    pub scheduler_visible: bool,
    /// May halt/abort instead of returning normally.
    pub halts: bool,
}

impl EffectSummary {
    pub fn blocks_return_context_motion(self) -> bool {
        self.observable || self.reads_allocation_stats || self.scheduler_visible || self.halts
    }

    pub fn union_with(&mut self, other: EffectSummary) -> bool {
        let before = *self;
        self.allocates |= other.allocates;
        self.observable |= other.observable;
        self.reads_allocation_stats |= other.reads_allocation_stats;
        self.scheduler_visible |= other.scheduler_visible;
        self.halts |= other.halts;
        *self != before
    }
}

#[cfg(test)]
mod tests {
    use super::EffectSummary;

    #[test]
    fn return_context_motion_barrier_uses_effect_summary_predicate() {
        assert!(
            !EffectSummary {
                allocates: true,
                ..EffectSummary::default()
            }
            .blocks_return_context_motion()
        );

        for summary in [
            EffectSummary {
                observable: true,
                ..EffectSummary::default()
            },
            EffectSummary {
                reads_allocation_stats: true,
                ..EffectSummary::default()
            },
            EffectSummary {
                scheduler_visible: true,
                ..EffectSummary::default()
            },
            EffectSummary {
                halts: true,
                ..EffectSummary::default()
            },
        ] {
            assert!(summary.blocks_return_context_motion());
        }
    }
}

impl ModuleTypes {
    #[allow(dead_code)]
    pub fn spec_ty(&self, fn_id: FnId, input_tys: &[crate::types::Ty]) -> Option<&FnTypes> {
        let key = self.specs.keys().find(|spec_key| {
            spec_key.fn_id == fn_id
                && spec_key.demand.is_value()
                && spec_key.input.len() == input_tys.len()
                && spec_key
                    .input
                    .iter()
                    .zip(input_tys.iter())
                    .all(|(slot, ty)| match slot {
                        None => true,
                        Some(k) => k == ty,
                    })
        })?;
        self.specs.get(key)
    }

    /// fz-pky.2 — return the any-key spec for `fn_id` if registered.
    /// Under the reachability-driven model (fz-vw4), the any-key only
    /// exists when the fn is closure-reachable, entry-seeded, or
    /// genuinely needs the opaque-dispatch fallback. Direct-call-only
    /// fns have no any-key.
    #[allow(dead_code)]
    pub fn any_key_spec(&self, fn_id: FnId) -> Option<&FnTypes> {
        let key = self.any_key_specs.get(&fn_id)?;
        self.specs.get(&SpecKey::value(fn_id, key.clone()))
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
        for (key, ft) in &self.specs {
            if key.fn_id != fn_id || !key.demand.is_value() {
                continue;
            }
            let precedence = *self.spec_precedence.get(key).unwrap_or(&u32::MAX);
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
        let candidates: Vec<crate::spec_registry::BestCoverCandidate<'_, &SpecKey>> = self
            .effective_returns
            .keys()
            .filter(|key| key.fn_id == callee && key.demand.is_value())
            .map(|key| crate::spec_registry::BestCoverCandidate {
                id: key,
                key: key.input.as_slice(),
                key_var_count: crate::types::key_slot_var_count(t, key.input.as_slice()),
                precedence: *self.spec_precedence.get(key).unwrap_or(&u32::MAX),
            })
            .collect();
        let best = crate::spec_registry::best_covering_candidate(t, arg_tys, candidates)?;
        self.effective_returns.get(best).cloned()
    }
}

pub(crate) fn spec_key_for_fn(f: &FnIr, input_tys: Vec<crate::types::Ty>) -> SpecKey {
    SpecKey::value(f.id, f.semantic_key(input_tys))
}

pub(crate) fn spec_key_for_fn_id(
    m: &Module,
    fid: FnId,
    input_tys: Vec<crate::types::Ty>,
) -> SpecKey {
    spec_key_for_fn(m.fn_by_id(fid), input_tys)
}

pub(crate) fn spec_key_input_tys<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    key: &SpecKey,
) -> Vec<crate::types::Ty> {
    crate::types::key_slots_to_tys(t, &key.input)
}

pub(crate) fn key_precedence_order(
    specs: &HashMap<SpecKey, FnTypes>,
    any_key_specs: &HashMap<FnId, Vec<crate::types::KeySlot>>,
) -> HashMap<SpecKey, u32> {
    let mut keys_by_fn: HashMap<FnId, Vec<SpecKey>> = HashMap::new();
    for key in specs.keys() {
        keys_by_fn.entry(key.fn_id).or_default().push(key.clone());
    }
    let mut precedence = HashMap::new();
    for (fid, mut keys) in keys_by_fn {
        keys.sort_by(|a, b| {
            let a_is_any = a.demand.is_value() && any_key_specs.get(&fid) == Some(&a.input);
            let b_is_any = b.demand.is_value() && any_key_specs.get(&fid) == Some(&b.input);
            b_is_any
                .cmp(&a_is_any)
                .then_with(|| format!("{:?}", a).cmp(&format!("{:?}", b)))
        });
        for (idx, key) in keys.into_iter().enumerate() {
            precedence.insert(key, idx as u32);
        }
    }
    precedence
}

pub(crate) fn build_any_key_index<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    m: &Module,
    specs: &HashMap<SpecKey, FnTypes>,
) -> HashMap<FnId, Vec<crate::types::KeySlot>> {
    let any = t.any();
    let mut idx: HashMap<FnId, Vec<crate::types::KeySlot>> = HashMap::new();
    for key in specs.keys() {
        if !key.demand.is_value() {
            continue;
        }
        let Some(&j) = m.fn_idx.get(&key.fn_id) else {
            continue;
        };
        let expected = spec_key_for_fn(&m.fns[j], vec![any.clone(); key.input.len()]);
        if key.input == expected.input {
            idx.entry(key.fn_id).or_insert_with(|| key.input.clone());
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
    pub caller: SpecKey,
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
            caller: self.caller.fn_id,
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
    pub fn with_spec_key(self, spec_key: SpecKey) -> EmitterSite {
        debug_assert_eq!(self.caller, spec_key.fn_id);
        EmitterSite {
            caller: spec_key,
            ident: self.ident,
            slot: self.slot,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ReturnDelivery {
    Value,
    TupleFields(usize),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ReturnContext {
    None,
    ListTail(crate::types::Ty),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ReturnDemand {
    pub delivery: ReturnDelivery,
    pub context: ReturnContext,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ReturnUse {
    pub delivery: ReturnDelivery,
    pub context: ReturnContext,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ReturnContextPlanKey {
    pub caller: SpecKey,
    pub callsite: crate::fz_ir::CallsiteId,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ReturnContextPlan {
    DirectContinuation {
        continuation: FnId,
        result_param: crate::fz_ir::Var,
        tail_ty: crate::types::Ty,
    },
    ConsThenDirect {
        continuation: FnId,
        pivot: crate::fz_ir::Var,
        tail: crate::fz_ir::Var,
        tail_ty: crate::types::Ty,
    },
    ContinuationListTailBridge {
        continuation: FnId,
        pivot: crate::fz_ir::Var,
        tail: crate::fz_ir::Var,
        tail_ty: crate::types::Ty,
    },
    ContinuationEmptyTail {
        continuation: FnId,
        target: SpecKey,
        tail_ty: crate::types::Ty,
    },
    TailCallDestination {
        callee: FnId,
        source: crate::fz_ir::Var,
        tail: crate::fz_ir::Var,
        tail_ty: crate::types::Ty,
    },
}

impl ReturnUse {
    pub fn from_demand(demand: &ReturnDemand) -> Self {
        Self {
            delivery: demand.delivery.clone(),
            context: demand.context.clone(),
        }
    }

    pub fn as_demand(&self) -> ReturnDemand {
        ReturnDemand {
            delivery: self.delivery.clone(),
            context: self.context.clone(),
        }
    }
}

impl ReturnDemand {
    pub fn value() -> Self {
        Self {
            delivery: ReturnDelivery::Value,
            context: ReturnContext::None,
        }
    }

    pub fn tuple_fields(arity: usize) -> Self {
        Self {
            delivery: ReturnDelivery::TupleFields(arity),
            context: ReturnContext::None,
        }
    }

    pub fn list_tail(tail_ty: crate::types::Ty) -> Self {
        Self {
            delivery: ReturnDelivery::Value,
            context: ReturnContext::ListTail(tail_ty),
        }
    }

    pub fn tuple_fields_list_tail(arity: usize, tail_ty: crate::types::Ty) -> Self {
        Self {
            delivery: ReturnDelivery::TupleFields(arity),
            context: ReturnContext::ListTail(tail_ty),
        }
    }

    pub fn is_value(&self) -> bool {
        self.delivery == ReturnDelivery::Value && self.context == ReturnContext::None
    }

    pub fn tuple_field_arity(&self) -> Option<usize> {
        match self.delivery {
            ReturnDelivery::TupleFields(arity) => Some(arity),
            ReturnDelivery::Value => None,
        }
    }

    pub fn list_tail_ty(&self) -> Option<&crate::types::Ty> {
        match &self.context {
            ReturnContext::ListTail(ty) => Some(ty),
            ReturnContext::None => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SpecKey {
    pub fn_id: FnId,
    pub input: Vec<crate::types::KeySlot>,
    pub demand: ReturnDemand,
}

impl SpecKey {
    pub fn value(fn_id: FnId, input: Vec<crate::types::KeySlot>) -> Self {
        Self {
            fn_id,
            input,
            demand: ReturnDemand::value(),
        }
    }
}

pub(crate) fn display_return_demand<
    T: crate::types::RenderTypes + crate::types::Types<Ty = crate::types::Ty>,
>(
    t: &T,
    demand: &ReturnDemand,
) -> String {
    match (&demand.delivery, &demand.context) {
        (ReturnDelivery::Value, ReturnContext::None) => "value".to_string(),
        (ReturnDelivery::TupleFields(n), ReturnContext::None) => format!("tuple_fields({})", n),
        (ReturnDelivery::TupleFields(n), ReturnContext::ListTail(ty)) => {
            format!("tuple_fields({}, list_tail({}))", n, t.display(ty))
        }
        (ReturnDelivery::Value, ReturnContext::ListTail(ty)) => {
            format!("list_tail({})", t.display(ty))
        }
    }
}

pub(crate) fn display_return_use<
    T: crate::types::RenderTypes + crate::types::Types<Ty = crate::types::Ty>,
>(
    t: &T,
    return_use: &ReturnUse,
) -> String {
    display_return_demand(t, &return_use.as_demand())
}

pub(crate) fn display_return_context_plan<
    T: crate::types::RenderTypes + crate::types::Types<Ty = crate::types::Ty>,
>(
    t: &T,
    plan: &ReturnContextPlan,
) -> String {
    match plan {
        ReturnContextPlan::DirectContinuation {
            continuation,
            result_param,
            tail_ty,
        } => format!(
            "direct_cont(cont=#{} result=Var({}) tail_ty={})",
            continuation.0,
            result_param.0,
            t.display(tail_ty)
        ),
        ReturnContextPlan::ConsThenDirect {
            continuation,
            pivot,
            tail,
            tail_ty,
        } => format!(
            "cons_then_direct(cont=#{} pivot=Var({}) tail=Var({}) tail_ty={})",
            continuation.0,
            pivot.0,
            tail.0,
            t.display(tail_ty)
        ),
        ReturnContextPlan::ContinuationListTailBridge {
            continuation,
            pivot,
            tail,
            tail_ty,
        } => format!(
            "cont_list_tail_bridge(cont=#{} pivot=Var({}) tail=Var({}) tail_ty={})",
            continuation.0,
            pivot.0,
            tail.0,
            t.display(tail_ty)
        ),
        ReturnContextPlan::ContinuationEmptyTail {
            continuation,
            target,
            tail_ty,
        } => format!(
            "empty_tail_cont(cont=#{} target_demand={} tail_ty={})",
            continuation.0,
            display_return_demand(t, &target.demand),
            t.display(tail_ty)
        ),
        ReturnContextPlan::TailCallDestination {
            callee,
            source,
            tail,
            tail_ty,
        } => format!(
            "tail_call_dest(callee=#{} source=Var({}) tail=Var({}) tail_ty={})",
            callee.0,
            source.0,
            tail.0,
            t.display(tail_ty)
        ),
    }
}

/// fz-rh5.6 — worklist-internal type aliases. Spec keys, the reverse
/// `return_readers` index, the `holders`/`emits_by_caller` indices,
/// and the `callsite_fn_consts` map all share these shapes; aliasing
/// satisfies clippy::type_complexity without sacrificing readability.
pub(crate) type SpecKeySet = std::collections::HashSet<SpecKey>;
pub(crate) type ReturnReaders = HashMap<SpecKey, SpecKeySet>;
pub(crate) type CallsiteFnConsts = HashMap<SpecKey, Vec<Option<FnId>>>;
pub(crate) type EmitterSiteSet = std::collections::HashSet<EmitterSite>;
pub(crate) type HoldersMap = HashMap<SpecKey, EmitterSiteSet>;
pub(crate) type EmitsByCaller = HashMap<SpecKey, EmitterSiteSet>;
pub(crate) type ProducesMap = HashMap<EmitterSite, SpecKey>;

/// fz-rh5.7 termination tripwire. The proof above (see `type_module`'s
/// doc) shows the worklist terminates in O(|specs| · H · |edges|) pops.
/// This bound is comfortably above any realistic program — a hit indicates
/// a violated invariant (non-monotone concrete op, an `is_equiv` slow-path
/// returning false on inputs that should be equiv, or a missing recursive-key
/// normalization), not a too-tight margin.
pub(crate) const VISIT_HARD_BOUND: usize = 4096;

pub(crate) fn normalize_recursive_direct_key<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    recursive_fns: &std::collections::HashSet<FnId>,
    k: Vec<crate::types::Ty>,
    caller: FnId,
    callee: FnId,
    module: &Module,
) -> Vec<crate::types::Ty> {
    if !recursive_fns.contains(&callee) {
        return k;
    }
    // Matcher fns are pass-through routers. Widening across either side of
    // a matcher edge erases the narrow facts the matcher exists to route.
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

pub(crate) fn recursive_direct_spec_key<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    caller: FnId,
    callee: FnId,
    key: Vec<crate::types::Ty>,
) -> SpecKey {
    let key = normalize_recursive_direct_key(t, recursive_fns, key, caller, callee, module);
    spec_key_for_fn_id(module, callee, key)
}
