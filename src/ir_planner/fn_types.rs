use crate::fz_ir::{CallsiteId, EmitSlot, FnId, FnIr, Module};
use std::collections::HashMap;

#[derive(Debug, Clone, Default)]
pub struct SpecPlan {
    /// Definition-site type for each Var. Block params get the join of their
    /// predecessor args; Let-bound vars get their Prim's type under the env
    /// at that point in the block.
    pub vars: HashMap<crate::fz_ir::Var, crate::types::Ty>,
    /// Entry env per block, with branch narrowing applied at If terminators.
    pub block_envs: HashMap<crate::fz_ir::BlockId, HashMap<crate::fz_ir::Var, crate::types::Ty>>,
    /// Vars known to hold a specific top-level fn identity from
    /// zero-capture `MakeClosure(F, [])`. The type token carries no FnId
    /// identity, so direct-call specialization keeps this side-channel.
    pub fn_constants: HashMap<crate::fz_ir::Var, FnId>,
    /// Blocks provably reachable from the entry under the inferred types.
    /// If terminators whose condition is a singleton bool prune the dead
    /// branch. Used by `compute_return_for_spec` to ignore returns that
    /// can never execute.
    pub reachable_blocks: std::collections::HashSet<crate::fz_ir::BlockId>,
    /// Per-spec branch facts used by per-spec codegen folding. These are
    /// stricter than `ModulePlan::dead_branches`: a branch can be dead for
    /// one specialization even when another specialization keeps it live.
    pub dead_branches: HashMap<crate::fz_ir::BlockId, crate::fz_ir::DeadBranch>,
    /// Per-callsite call-edge capability selected for this spec.
    ///
    /// This is the typed handoff codegen should consume. It keeps the selected
    /// target, result-hole demand, and executable return-context plan on one
    /// edge, so future provider-boundary and protocol dispatch facts can extend
    /// the same shape instead of adding side tables.
    pub call_edges: HashMap<crate::fz_ir::CallsiteId, CallEdgePlan>,
    /// Per-spec concrete C marshal classes for extern call arguments.
    ///
    /// Variadic `Auto` args are resolved after this `FnTypes` has inferred
    /// Var types. The map is per spec because the same syntactic call can be
    /// reached under different argument types in different specializations.
    pub extern_marshals: HashMap<crate::fz_ir::ExternMarshalSite, crate::fz_ir::ExternTy>,
}

impl SpecPlan {
    pub fn local_call_target(&self, callsite: &crate::fz_ir::CallsiteId) -> Option<&SpecKey> {
        self.call_edges
            .get(callsite)
            .and_then(CallEdgePlan::local_target)
    }

    pub fn return_use(&self, callsite: &crate::fz_ir::CallsiteId) -> Option<&ReturnDemand> {
        self.call_edges
            .get(callsite)
            .and_then(|edge| edge.return_use.as_ref())
    }

    pub fn return_context_plan(
        &self,
        callsite: &crate::fz_ir::CallsiteId,
    ) -> Option<&ReturnContextPlan> {
        self.call_edges
            .get(callsite)
            .and_then(|edge| edge.return_context.as_ref())
    }

    pub(crate) fn install_call_edges(
        &mut self,
        call_edges: HashMap<crate::fz_ir::CallsiteId, CallEdgePlan>,
    ) {
        self.call_edges = call_edges;
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallEdgePlan {
    pub target: CallEdgeTarget,
    pub return_use: Option<ReturnDemand>,
    pub return_context: Option<ReturnContextPlan>,
}

impl CallEdgePlan {
    pub fn local_target(&self) -> Option<&SpecKey> {
        match &self.target {
            CallEdgeTarget::Local(target) => Some(target),
            CallEdgeTarget::External { .. } => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallEdgeTarget {
    Local(SpecKey),
    External {
        target: crate::modules::identity::ExportKey,
        input: Vec<crate::types::KeySlot>,
        demand: ReturnDemand,
    },
}

/// Per-module type information.
///
/// `specs` is the registered specialization map, keyed by `SpecKey`
/// (`FnId`, input-type tuple, and return demand). Specs are produced by direct
/// calls, closure calls, continuations, receive outcomes, entry seeds, and
/// `MakeClosure` reachability.
#[derive(Debug, Clone)]
pub struct ModulePlan {
    pub specs: HashMap<SpecKey, SpecPlan>,
    /// Kleene LFP of every spec's effective return type. Maintained
    /// incrementally by the worklist: each spec's return is recomputed
    /// after every visit, and changes re-enqueue its `return_readers`.
    /// Continuation slot-0 typing and plan rendering read here instead of
    /// recursing on demand.
    pub effective_returns: HashMap<SpecKey, crate::types::Ty>,
    /// Secondary index from FnId to its all-any key. Populated in
    /// `plan_module` from the final specs map so callers can find any-key
    /// specs without scanning the whole spec map.
    pub any_key_specs: HashMap<FnId, Vec<crate::types::KeySlot>>,
    /// Stable per-family precedence for specialization selection.
    pub spec_precedence: HashMap<SpecKey, u32>,
    /// Per-spec summary of effects that are relevant to return-demand
    /// scheduling. Allocation is tracked separately from externally
    /// observable barriers so demand selection can move allocation only when
    /// no runtime-visible operation can observe the move.
    pub effect_summaries: HashMap<SpecKey, EffectSummary>,
    /// Per-If dead-branch facts under cross-spec consensus.
    /// Populated at the end of `plan_module` by `compute_dead_branches`.
    /// Keyed by `(FnId, BlockId)` where the block ends in a `Term::If`;
    /// value names which branch is provably never taken. Read by the
    /// dead-branch fold and by `collect_diagnostics`. Only covers
    /// registered-spec fns; diagnostics re-run ad-hoc analysis for fns with
    /// no registered spec.
    pub dead_branches: HashMap<(FnId, crate::fz_ir::BlockId), crate::fz_ir::DeadBranch>,
    /// Closure-handle registry used by planner tests. Runtime codegen
    /// resolves closure bodies through the emitted any-key body specs.
    #[cfg(test)]
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

impl From<crate::ir_effects::IrEffects> for EffectSummary {
    fn from(effects: crate::ir_effects::IrEffects) -> Self {
        Self {
            allocates: effects.allocates,
            observable: effects.externally_observable,
            reads_allocation_stats: effects.observes_allocation,
            scheduler_visible: effects.scheduler_boundary,
            halts: effects.halts,
        }
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

impl ModulePlan {
    #[cfg(test)]
    pub fn spec_ty(&self, fn_id: FnId, input_tys: &[crate::types::Ty]) -> Option<&SpecPlan> {
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

    /// Return the any-key spec for `fn_id` if registered. Direct-call-only
    /// fns have no any-key.
    pub fn any_key_spec(&self, fn_id: FnId) -> Option<&SpecPlan> {
        let key = self.any_key_specs.get(&fn_id)?;
        self.specs.get(&SpecKey::value(fn_id, key.clone()))
    }

    /// Return any registered value spec for `fn_id`. Prefers the any-key
    /// spec when available; otherwise uses spec precedence for deterministic
    /// selection.
    pub fn any_spec_for(&self, fn_id: FnId) -> Option<&SpecPlan> {
        if let Some(ft) = self.any_key_spec(fn_id) {
            return Some(ft);
        }
        let mut best: Option<(u32, &SpecPlan)> = None;
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
    specs: &HashMap<SpecKey, SpecPlan>,
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
    specs: &HashMap<SpecKey, SpecPlan>,
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
    pub static PLAN_MODULE_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// Worklist pops in `process_worklist`. Each pop performs one discovery
    /// walk and one return recompute.
    pub static WORKLIST_POPS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// Calls to `type_fn` from the worklist. Since type_fn results are cached
    /// one-per-spec, this equals the number of unique typed specs.
    pub static TYPE_FN_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// Invocations of `walk_spec_for_discovery`.
    pub static WALK_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Unique identity of a place that emits a spec.
///
/// Every spec in `specs` exists because at least one `EmitterSite` currently
/// produces it. When a caller spec re-walks with different state, the driver
/// diffs against `produces[E]`, transitions `holders`, and prunes orphan cycles
/// with a forward BFS from `entry_seeds` through the emits graph.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct EmitterSite {
    pub caller: SpecKey,
    pub ident: crate::fz_ir::CallsiteIdent,
    pub slot: EmitSlot,
}

impl EmitterSite {
    #[cfg(test)]
    /// Project out the spec-aware `EmitterSite` to a spec-agnostic
    /// `CallsiteId` by dropping the caller's input key.
    pub fn callsite_id(&self) -> CallsiteId {
        CallsiteId::new(self.caller.fn_id, &self.ident, self.slot)
    }
}

impl CallsiteId {
    #[cfg(test)]
    /// Re-attach a spec key to recover the full `EmitterSite`. The new
    /// site's FnId must match the `CallsiteId` caller.
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

/// Worklist-internal aliases for repeated index shapes.
pub(crate) type SpecKeySet = std::collections::HashSet<SpecKey>;
pub(crate) type ReturnReaders = HashMap<SpecKey, SpecKeySet>;
pub(crate) type CallsiteFnConsts = HashMap<SpecKey, Vec<Option<FnId>>>;
pub(crate) type EmitterSiteSet = std::collections::HashSet<EmitterSite>;
pub(crate) type HoldersMap = HashMap<SpecKey, EmitterSiteSet>;
pub(crate) type EmitsByCaller = HashMap<SpecKey, EmitterSiteSet>;
pub(crate) type ProducesMap = HashMap<EmitterSite, SpecKey>;

/// Termination tripwire. The proof above (see `plan_module`'s doc) shows the
/// worklist terminates in O(|specs| · H · |edges|) pops. This bound is
/// intentionally loose; a hit indicates a violated monotonicity, equivalence,
/// or recursive-key normalization invariant.
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

pub(crate) fn padded_direct_input_tys<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    mut input_tys: Vec<crate::types::Ty>,
    arity: usize,
) -> Vec<crate::types::Ty> {
    while input_tys.len() < arity {
        input_tys.push(t.any());
    }
    input_tys.truncate(arity);
    input_tys
}

pub(crate) fn recursive_direct_spec_key_for_arity<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    caller: FnId,
    callee: FnId,
    input_tys: Vec<crate::types::Ty>,
    arity: usize,
    demand: Option<ReturnDemand>,
) -> SpecKey {
    let input_tys = padded_direct_input_tys(t, input_tys, arity);
    let mut key = recursive_direct_spec_key(t, module, recursive_fns, caller, callee, input_tys);
    if let Some(demand) = demand {
        key.demand = demand;
    }
    key
}
