use crate::frontend::spec_registry::{BestCoverCandidate, best_covering_candidate};
use crate::fz_ir::{BlockId, CallsiteId, DeadBranch, ExternMarshalSite, ExternTy, FnCategory, FnId, FnIr, Module, Var};
use crate::modules::identity::ExportKey;
use crate::specs::StructuralOccurrence;
use crate::types::{ClosureTypes, KeySlot, Nominals, RenderTypes, Ty, Types, key_slot_var_count, key_slots_to_tys};
use std::cell::Cell;
use std::collections::{BTreeSet, HashMap, HashSet};

#[derive(Debug, Clone, Default)]
pub struct SpecPlan {
    /// Definition-site type for each Var. Block params get the join of their
    /// predecessor args; Let-bound vars get their Prim's type under the env
    /// at that point in the block.
    pub vars: HashMap<Var, Ty>,
    /// Entry env per block, with branch narrowing applied at If terminators.
    pub block_envs: HashMap<BlockId, HashMap<Var, Ty>>,
    /// Vars known to hold callable values, separated by capability instead of
    /// representation. A zero-capture closure is callable as a known fn, while
    /// captured or opaque callables still carry runtime-state/boundary facts for
    /// later consumers.
    pub callable_capabilities: HashMap<Var, CallableCapability>,
    /// Blocks provably reachable from the entry under the inferred types.
    /// If terminators whose condition is a singleton bool prune the dead
    /// branch. Used by `compute_return_for_spec` to ignore returns that
    /// can never execute.
    pub reachable_blocks: HashSet<BlockId>,
    /// Per-spec branch facts used by per-spec codegen folding. These are
    /// stricter than `ModulePlan::dead_branches`: a branch can be dead for
    /// one specialization even when another specialization keeps it live.
    pub dead_branches: HashMap<BlockId, DeadBranch>,
    /// Per-callsite call-edge capability selected for this spec.
    ///
    /// This is the typed handoff codegen should consume. It keeps the selected
    /// target, result-hole demand, and executable return-context plan on one
    /// edge, so future provider-boundary and protocol dispatch facts can extend
    /// the same shape instead of adding side tables.
    pub call_edges: HashMap<CallsiteId, CallEdgePlan>,
    /// Executable closure-entry specs required by surviving `MakeClosure`
    /// statements in this body. These are representation obligations, not
    /// dispatch edges.
    pub callable_entry_targets: HashSet<SpecKey>,
    /// Per-spec concrete C marshal classes for extern call arguments.
    ///
    /// Variadic `Auto` args are resolved after this `SpecPlan` has inferred
    /// Var types. The map is per spec because the same syntactic call can be
    /// reached under different argument types in different specializations.
    pub extern_marshals: HashMap<ExternMarshalSite, ExternTy>,
    /// fz-bsx.3 — the module's brand/opaque inner-type maps, carried here so
    /// codegen's value-equality fold (`lower_eq_binop`) can discharge brand /
    /// opaque tags to their runtime representation. Runtime equality is
    /// brand-blind, so the fold must consult `is_value_disjoint` (which needs
    /// these), never the brand-aware `is_disjoint`. Copied from `Module` at
    /// spec construction; tiny (one entry per declared brand/opaque).
    pub brand_inners: HashMap<String, Ty>,
    pub opaque_inners: HashMap<String, Ty>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecReachabilityRole {
    Entry,
    Activation,
    CallableEntry,
    ProjectionGap,
}

impl SpecReachabilityRole {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Entry => "entry",
            Self::Activation => "activation",
            Self::CallableEntry => "callable_entry",
            Self::ProjectionGap => "projection_gap",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallableCapability {
    KnownFn(FnId),
    KnownClosure {
        fn_id: FnId,
        captures: Vec<Ty>,
        capture_capabilities: Vec<Option<CallableCapability>>,
    },
    OpaqueCallable,
}

impl CallableCapability {
    pub fn known_fn(&self) -> Option<FnId> {
        match self {
            CallableCapability::KnownFn(fid) => Some(*fid),
            CallableCapability::KnownClosure { .. } | CallableCapability::OpaqueCallable => None,
        }
    }
}

impl SpecPlan {
    /// A borrowed view of the brand/opaque inner-type maps copied from the
    /// module, for codegen's brand-blind value-equality fold.
    pub fn nominals(&self) -> Nominals<'_> {
        Nominals::new(&self.brand_inners, &self.opaque_inners)
    }

    pub fn known_fn(&self, var: &Var) -> Option<FnId> {
        self.callable_capabilities
            .get(var)
            .and_then(CallableCapability::known_fn)
    }

    pub fn local_call_target(&self, callsite: &CallsiteId) -> Option<&SpecKey> {
        self.call_edges.get(callsite).and_then(CallEdgePlan::local_target)
    }

    pub fn return_contract(&self, callsite: &CallsiteId) -> Option<&ReturnContract> {
        self.call_edges
            .get(callsite)
            .and_then(|edge| edge.return_contract.as_ref())
    }

    pub fn return_use(&self, callsite: &CallsiteId) -> Option<&ReturnDemand> {
        self.call_edges.get(callsite).and_then(|edge| {
            if let Some(contract) = edge.return_contract.as_ref() {
                return Some(&contract.target.demand);
            }
            match &edge.target {
                CallEdgeTarget::External { demand, .. } => Some(demand),
                CallEdgeTarget::Local(_) => None,
            }
        })
    }

    pub fn return_context_plan(&self, callsite: &CallsiteId) -> Option<&ReturnContextPlan> {
        self.call_edges
            .get(callsite)
            .and_then(|edge| edge.return_contract.as_ref())
            .and_then(|contract| contract.strategy.context_plan())
    }

    pub(crate) fn install_call_edges(&mut self, call_edges: HashMap<CallsiteId, CallEdgePlan>) {
        self.call_edges = call_edges;
    }

    pub(crate) fn install_callable_entry_targets(&mut self, callable_entry_targets: HashSet<SpecKey>) {
        self.callable_entry_targets = callable_entry_targets;
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallEdgePlan {
    pub target: CallEdgeTarget,
    pub return_contract: Option<ReturnContract>,
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
pub struct ReturnContract {
    pub target: SpecKey,
    pub strategy: ReturnStrategy,
}

impl ReturnContract {
    pub fn new(target: SpecKey, strategy: ReturnStrategy) -> Self {
        assert_eq!(
            target.demand,
            strategy.demand(),
            "ReturnContract target demand and strategy demand must agree"
        );
        Self { target, strategy }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReturnStrategy {
    Value,
    TupleFields(usize),
    ForwardedDemand(ReturnDemand),
    ListTail(ReturnContextPlan),
    TupleFieldsListTail { arity: usize, plan: ReturnContextPlan },
}

impl ReturnStrategy {
    pub fn demand(&self) -> ReturnDemand {
        match self {
            ReturnStrategy::Value => ReturnDemand::value(),
            ReturnStrategy::TupleFields(arity) => ReturnDemand::tuple_fields(*arity),
            ReturnStrategy::ForwardedDemand(demand) => demand.clone(),
            ReturnStrategy::ListTail(plan) => {
                let tail_ty = plan
                    .demand()
                    .list_tail_ty()
                    .expect("list-tail strategies require a list-tail context")
                    .clone();
                ReturnDemand::list_tail(tail_ty)
            }
            ReturnStrategy::TupleFieldsListTail { arity, plan } => {
                let tail_ty = plan
                    .demand()
                    .list_tail_ty()
                    .expect("tuple-fields list-tail strategies require a list-tail context")
                    .clone();
                ReturnDemand::tuple_fields_list_tail(*arity, tail_ty)
            }
        }
    }

    pub fn context_plan(&self) -> Option<&ReturnContextPlan> {
        match self {
            ReturnStrategy::Value | ReturnStrategy::TupleFields(_) | ReturnStrategy::ForwardedDemand(_) => None,
            ReturnStrategy::ListTail(plan) | ReturnStrategy::TupleFieldsListTail { plan, .. } => Some(plan),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallEdgeTarget {
    Local(SpecKey),
    External {
        target: ExportKey,
        input: Vec<KeySlot>,
        demand: ReturnDemand,
    },
}

/// Per-module type information.
///
/// `specs` is the registered specialization map, keyed by `SpecKey`
/// (`FnId`, input-type tuple, and return demand). Specs are produced by direct
/// calls, closure calls, continuations, receive outcomes, entry seeds, and
/// callable-boundary reachability.
#[derive(Debug, Clone)]
pub struct ModulePlan {
    pub specs: HashMap<SpecKey, SpecPlan>,
    /// Why each reachable spec remains in the executable plan.
    ///
    /// Entry specs come from whole-program roots such as `main/0`.
    /// Activation specs are justified by solved `type_infer` facts and any
    /// callable-boundary edges that keep closure targets executable.
    /// Projection-gap specs are temporary planner-visible shells whose return
    /// payload is still underconstrained.
    pub spec_roles: HashMap<SpecKey, SpecReachabilityRole>,
    /// Semantic return payloads projected from activation inference onto the
    /// reachable planner specs. `SpecKey::demand` selects ABI/delivery shape;
    /// it does not create a different value payload. During the transplant,
    /// uncovered reachable specs are filled with `any` to keep the map total;
    /// planner telemetry reports those as activation projection gaps.
    pub effective_returns: HashMap<SpecKey, Ty>,
    /// Secondary index from FnId to its all-any key. Populated in
    /// `plan_module` from the final specs map so callers can find any-key
    /// specs without scanning the whole spec map.
    pub any_key_specs: HashMap<FnId, Vec<KeySlot>>,
    /// Stable per-family precedence for specialization selection.
    pub spec_precedence: HashMap<SpecKey, u32>,
    /// Per-FnId summary of effects relevant to return-demand scheduling.
    /// Allocation is tracked separately from externally observable barriers
    /// so demand selection can move allocation only when no runtime-visible
    /// operation can observe the move. Computed once over the static call
    /// graph (a function's effects do not depend on what the caller wants
    /// back), so the destination-planning barrier reads one cached fact
    /// instead of re-walking bodies on demand.
    pub fn_effects: FnEffects,
    /// Per-If dead-branch facts safe to report at the module level.
    /// Populated at the end of `plan_module` by `compute_dead_branches`.
    /// Keyed by `(FnId, BlockId)` where the block ends in a `Term::If`;
    /// value names which branch is provably never taken. Read by the
    /// `collect_diagnostics`. These facts are proven by the fn's all-domain
    /// `any` key; narrower per-spec branch facts live on
    /// `SpecPlan::dead_branches` and are consumed only on planned bodies.
    pub dead_branches: HashMap<(FnId, BlockId), DeadBranch>,
}

/// Capability + effect facts for the pre-plan transforms (closure
/// devirtualization + inlining), produced by `plan_callable_capabilities`.
///
/// Deliberately NOT a `ModulePlan`: it carries only the slice those transforms
/// read — each discovered spec's `callable_capabilities` (tagged by its FnId)
/// and the per-FnId `fn_effects`. The per-spec types, call edges, returns, and
/// the module-level dead-branch/precedence facts are dropped, so this cannot be
/// mistaken for — or used as — a codegen plan.
#[derive(Debug, Clone)]
pub struct CapabilityPlan {
    /// One entry per discovered spec: its FnId and its vars' callable
    /// capabilities. The consumers merge these to a per-fn consensus
    /// (`rewrite`) or scan them for stateful closure targets (`inline`).
    pub spec_capabilities: Vec<(FnId, HashMap<Var, CallableCapability>)>,
    pub fn_effects: FnEffects,
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
    /// Reaches a call through a value whose target is not statically known
    /// (a closure call). Conservatively a barrier: the callee's effects are
    /// invisible, so return-context motion across it is unsafe until the
    /// target is resolved (see fz-w34.2).
    pub calls_opaque: bool,
}

impl EffectSummary {
    pub fn blocks_return_context_motion(self) -> bool {
        self.observable || self.reads_allocation_stats || self.scheduler_visible || self.halts || self.calls_opaque
    }

    pub fn union_with(&mut self, other: EffectSummary) -> bool {
        let before = *self;
        self.allocates |= other.allocates;
        self.observable |= other.observable;
        self.reads_allocation_stats |= other.reads_allocation_stats;
        self.scheduler_visible |= other.scheduler_visible;
        self.halts |= other.halts;
        self.calls_opaque |= other.calls_opaque;
        *self != before
    }
}

#[cfg(test)]
mod tests {
    use super::{
        EffectSummary, ReturnContextPlan, ReturnDemand, ReturnStrategy, SpecKey, forwarded_return_contract_for_target,
        return_contract_for_target,
    };
    use crate::fz_ir::{FnId, Var};
    use crate::types::{ConcreteTypes, Types};

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

    #[test]
    fn return_contract_pairs_non_value_demand_with_matching_strategy() {
        let mut t = ConcreteTypes;
        let tail_ty = t.int();
        let target = SpecKey {
            fn_id: FnId(7),
            input: Vec::new(),
            demand: ReturnDemand::list_tail(tail_ty.clone()),
        };

        assert!(return_contract_for_target(target.clone(), None).is_none());

        let mismatched_plan = ReturnContextPlan::DirectContinuation {
            continuation: FnId(8),
            result_param: Var(0),
            tail_ty: t.any(),
        };
        assert!(return_contract_for_target(target.clone(), Some(mismatched_plan)).is_none());

        let matching_plan = ReturnContextPlan::DirectContinuation {
            continuation: FnId(8),
            result_param: Var(0),
            tail_ty,
        };
        let contract = return_contract_for_target(target.clone(), Some(matching_plan.clone()))
            .expect("matching context plan should produce a return contract");
        assert_eq!(contract.target, target);
        assert_eq!(contract.strategy, ReturnStrategy::ListTail(matching_plan));
    }

    #[test]
    fn non_context_return_contracts_need_no_context_plan() {
        let target = SpecKey::value(FnId(7), Vec::new());
        let contract = return_contract_for_target(target.clone(), None)
            .expect("plain value returns need no executable context plan");
        assert_eq!(contract.target, target);
        assert_eq!(contract.strategy, ReturnStrategy::Value);

        let target = SpecKey {
            fn_id: FnId(7),
            input: Vec::new(),
            demand: ReturnDemand::tuple_fields(2),
        };
        let contract = return_contract_for_target(target.clone(), None)
            .expect("tuple-field returns are executable without a context plan");
        assert_eq!(contract.target, target);
        assert_eq!(contract.strategy, ReturnStrategy::TupleFields(2));
    }

    #[test]
    fn forwarded_return_contract_pairs_tail_call_target_and_strategy() {
        let mut t = ConcreteTypes;
        let any = t.any();
        let target = SpecKey {
            fn_id: FnId(7),
            input: Vec::new(),
            demand: ReturnDemand::list_tail(t.list(any)),
        };
        let contract = forwarded_return_contract_for_target(target.clone());
        assert_eq!(contract.target, target.clone());
        assert_eq!(contract.strategy, ReturnStrategy::ForwardedDemand(target.demand));
    }
}

impl ModulePlan {
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

    pub fn effective_return_for_call_ty<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &T,
        callee: FnId,
        arg_tys: &[Ty],
    ) -> Option<Ty> {
        let candidates: Vec<BestCoverCandidate<'_, &SpecKey>> = self
            .effective_returns
            .keys()
            .filter(|key| key.fn_id == callee && key.demand.is_value())
            .map(|key| BestCoverCandidate {
                id: key,
                key: key.input.as_slice(),
                key_var_count: key_slot_var_count(t, key.input.as_slice()),
                precedence: *self.spec_precedence.get(key).unwrap_or(&u32::MAX),
            })
            .collect();
        let best = best_covering_candidate(t, arg_tys, candidates)?;
        self.effective_returns.get(best).cloned()
    }
}

pub(crate) fn spec_key_for_fn(f: &FnIr, input_tys: Vec<Ty>) -> SpecKey {
    SpecKey::value(f.id, f.semantic_key(input_tys))
}

pub(crate) fn spec_key_for_fn_id(m: &Module, fid: FnId, input_tys: Vec<Ty>) -> SpecKey {
    spec_key_for_fn(m.fn_by_id(fid), input_tys)
}

pub(crate) fn spec_key_input_tys<T: Types<Ty = Ty>>(t: &mut T, key: &SpecKey) -> Vec<Ty> {
    key_slots_to_tys(t, &key.input)
}

pub(crate) fn key_precedence_order(
    specs: &HashMap<SpecKey, SpecPlan>,
    any_key_specs: &HashMap<FnId, Vec<KeySlot>>,
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

pub(crate) fn build_any_key_index<T: Types<Ty = Ty>>(
    t: &mut T,
    m: &Module,
    specs: &HashMap<SpecKey, SpecPlan>,
) -> HashMap<FnId, Vec<KeySlot>> {
    let any = t.any();
    let mut idx: HashMap<FnId, Vec<KeySlot>> = HashMap::new();
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
    /// Worklist pops in `process_worklist`. Each pop performs one discovery
    /// walk and one return recompute.
    pub static WORKLIST_POPS: Cell<usize> = const { Cell::new(0) };
    /// Calls to `type_fn` from the worklist. Since type_fn results are cached
    /// one-per-spec, this equals the number of unique typed specs.
    pub static TYPE_FN_CALLS: Cell<usize> = const { Cell::new(0) };
    /// Invocations of `walk_spec_for_discovery`.
    pub static WALK_CALLS: Cell<usize> = const { Cell::new(0) };
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ReturnDelivery {
    Value,
    TupleFields(usize),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ReturnContext {
    None,
    ListTail(Ty),
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
        result_param: Var,
        tail_ty: Ty,
    },
    ConsThenDirect {
        continuation: FnId,
        pivot: Var,
        tail: Var,
        tail_ty: Ty,
    },
    ContinuationListTailBridge {
        continuation: FnId,
        pivot: Var,
        tail: Var,
        tail_ty: Ty,
    },
    ContinuationEmptyTail {
        continuation: FnId,
        target: SpecKey,
        tail_ty: Ty,
    },
    TailCallDestination {
        callee: FnId,
        source: Var,
        tail: Var,
        tail_ty: Ty,
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

    pub fn list_tail(tail_ty: Ty) -> Self {
        Self {
            delivery: ReturnDelivery::Value,
            context: ReturnContext::ListTail(tail_ty),
        }
    }

    pub fn tuple_fields_list_tail(arity: usize, tail_ty: Ty) -> Self {
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

    pub fn list_tail_ty(&self) -> Option<&Ty> {
        match &self.context {
            ReturnContext::ListTail(ty) => Some(ty),
            ReturnContext::None => None,
        }
    }
}

impl ReturnContextPlan {
    pub fn demand(&self) -> ReturnDemand {
        match self {
            ReturnContextPlan::DirectContinuation { tail_ty, .. }
            | ReturnContextPlan::ConsThenDirect { tail_ty, .. }
            | ReturnContextPlan::ContinuationListTailBridge { tail_ty, .. }
            | ReturnContextPlan::TailCallDestination { tail_ty, .. } => ReturnDemand::list_tail(tail_ty.clone()),
            ReturnContextPlan::ContinuationEmptyTail { target, .. } => target.demand.clone(),
        }
    }
}

pub(crate) fn return_strategy_for_demand(
    demand: ReturnDemand,
    plan: Option<ReturnContextPlan>,
) -> Option<ReturnStrategy> {
    match (&demand.delivery, &demand.context) {
        (ReturnDelivery::Value, ReturnContext::None) => Some(ReturnStrategy::Value),
        (ReturnDelivery::TupleFields(arity), ReturnContext::None) => Some(ReturnStrategy::TupleFields(*arity)),
        (ReturnDelivery::Value, ReturnContext::ListTail(tail_ty)) => {
            let plan = plan?;
            plan_has_list_tail(&plan, tail_ty).then_some(ReturnStrategy::ListTail(plan))
        }
        (ReturnDelivery::TupleFields(arity), ReturnContext::ListTail(tail_ty)) => {
            let plan = plan?;
            plan_has_list_tail(&plan, tail_ty).then_some(ReturnStrategy::TupleFieldsListTail { arity: *arity, plan })
        }
    }
}

fn plan_has_list_tail(plan: &ReturnContextPlan, expected_tail_ty: &Ty) -> bool {
    plan.demand()
        .list_tail_ty()
        .is_some_and(|actual_tail_ty| actual_tail_ty == expected_tail_ty)
}

pub(crate) fn return_contract_for_target(target: SpecKey, plan: Option<ReturnContextPlan>) -> Option<ReturnContract> {
    let strategy = return_strategy_for_demand(target.demand.clone(), plan)?;
    Some(ReturnContract::new(target, strategy))
}

pub(crate) fn forwarded_return_contract_for_target(target: SpecKey) -> ReturnContract {
    ReturnContract::new(target.clone(), ReturnStrategy::ForwardedDemand(target.demand.clone()))
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SpecKey {
    pub fn_id: FnId,
    pub input: Vec<KeySlot>,
    pub demand: ReturnDemand,
}

impl SpecKey {
    pub fn value(fn_id: FnId, input: Vec<KeySlot>) -> Self {
        Self {
            fn_id,
            input,
            demand: ReturnDemand::value(),
        }
    }
}

pub(crate) fn display_return_demand<T: RenderTypes + Types<Ty = Ty>>(t: &T, demand: &ReturnDemand) -> String {
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

pub(crate) fn display_return_context_plan<T: RenderTypes + Types<Ty = Ty>>(t: &T, plan: &ReturnContextPlan) -> String {
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

pub(crate) fn display_return_strategy<T: RenderTypes + Types<Ty = Ty>>(t: &T, strategy: &ReturnStrategy) -> String {
    match strategy {
        ReturnStrategy::Value => "value".to_string(),
        ReturnStrategy::TupleFields(arity) => format!("tuple_fields({})", arity),
        ReturnStrategy::ForwardedDemand(demand) => {
            format!("forwarded({})", display_return_demand(t, demand))
        }
        ReturnStrategy::ListTail(plan) => display_return_context_plan(t, plan),
        ReturnStrategy::TupleFieldsListTail { arity, plan } => {
            format!("tuple_fields({}, {})", arity, display_return_context_plan(t, plan))
        }
    }
}

/// Per-FnId effect facts. Keyed by `FnId` because a function's effects are a
/// property of its body and call graph, independent of any caller's return
/// demand. Consumed by the destination-planning barrier and exposed on
/// `ModulePlan` for downstream passes.
pub type FnEffects = HashMap<FnId, EffectSummary>;

/// Worklist-internal aliases for repeated index shapes.
pub(crate) type SpecKeySet = HashSet<SpecKey>;
pub(crate) type ReturnReaders = HashMap<SpecKey, SpecKeySet>;
pub(crate) type ReturnDepsByCaller = HashMap<SpecKey, SpecKeySet>;
/// Per-target entry-param callable capability facts.
///
/// This is keyed by the selected target `SpecKey`, not by the syntactic
/// caller-site alone, because multiple incoming edges can converge on the
/// same public spec. The vector is indexed by entry param position. Direct
/// calls populate explicit arg slots; continuations also use slot 0 for the
/// returned value that flows into the continuation.
pub(crate) type IncomingParamCallableCapabilities = HashMap<SpecKey, Vec<Option<CallableCapability>>>;

pub(crate) fn result_linked_param_slots(module: &Module, fn_id: FnId) -> BTreeSet<usize> {
    let Some(groups) = module.function_correspondence.get(&fn_id) else {
        return BTreeSet::new();
    };
    let mut params = BTreeSet::new();
    for group in groups {
        if !group
            .occurrences
            .iter()
            .any(|occ| matches!(occ, StructuralOccurrence::Result { .. }))
        {
            continue;
        }
        for occ in &group.occurrences {
            if let StructuralOccurrence::Param { param_index, .. } = occ {
                params.insert(*param_index);
            }
        }
    }
    params
}

/// Termination tripwire. The proof above (see `plan_module`'s doc) shows the
/// worklist terminates in O(|specs| · H · |edges|) pops. This bound is
/// intentionally loose; a hit indicates a violated monotonicity, equivalence,
/// or recursive-key normalization invariant.
pub(crate) const VISIT_HARD_BOUND: usize = 4096;

pub(crate) fn normalize_recursive_direct_key<T: Types<Ty = Ty>>(
    t: &mut T,
    recursive_fns: &HashSet<FnId>,
    k: Vec<Ty>,
    caller: FnId,
    callee: FnId,
    module: &Module,
) -> Vec<Ty> {
    if !recursive_fns.contains(&callee) {
        return k;
    }
    // Matcher fns are pass-through routers. Widening across either side of
    // a matcher edge erases the narrow facts the matcher exists to route.
    let is_matcher = |fid: FnId| -> bool {
        module
            .fn_idx
            .get(&fid)
            .is_some_and(|&j| module.fns[j].category == FnCategory::Matcher)
    };
    if is_matcher(callee) || is_matcher(caller) {
        return k;
    }
    k.into_iter().map(|ty| t.widen_for_recursive_spec_key(&ty)).collect()
}

pub(crate) fn padded_direct_input_tys<T: Types<Ty = Ty>>(t: &mut T, mut input_tys: Vec<Ty>, arity: usize) -> Vec<Ty> {
    while input_tys.len() < arity {
        input_tys.push(t.any());
    }
    input_tys.truncate(arity);
    input_tys
}

pub(crate) fn normalize_result_correspondence_key<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    fn_id: FnId,
    mut key: Vec<Ty>,
) -> Vec<Ty> {
    let recursive_params = result_linked_param_slots(module, fn_id);
    if recursive_params.is_empty() {
        return key;
    }
    if !module.function_correspondence.contains_key(&fn_id) {
        return key;
    }
    for param_index in recursive_params {
        if let Some(slot) = key.get_mut(param_index) {
            *slot = t.widen_for_recursive_spec_key(slot);
        }
    }
    key
}

pub(crate) fn fixed_point_spec_key_for_arity<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    recursive_fns: &HashSet<FnId>,
    caller: FnId,
    callee: FnId,
    input_tys: Vec<Ty>,
    arity: usize,
    demand: Option<ReturnDemand>,
) -> SpecKey {
    let (_, input_tys) = fixed_point_input_tys_for_arity(t, module, recursive_fns, caller, callee, input_tys, arity);
    let mut key = spec_key_for_fn_id(module, callee, input_tys);
    if let Some(demand) = demand {
        key.demand = demand;
    }
    key
}

pub(crate) fn fixed_point_input_tys_for_arity<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    recursive_fns: &HashSet<FnId>,
    caller: FnId,
    callee: FnId,
    input_tys: Vec<Ty>,
    arity: usize,
) -> (Vec<Ty>, Vec<Ty>) {
    let input_tys = padded_direct_input_tys(t, input_tys, arity);
    let input_tys = normalize_recursive_direct_key(t, recursive_fns, input_tys, caller, callee, module);
    let input_tys = normalize_result_correspondence_key(t, module, callee, input_tys);
    let observed = input_tys.clone();
    (observed, input_tys)
}
