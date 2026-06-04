use crate::frontend::spec_registry::{BestCoverCandidate, best_covering_candidate};
use crate::fz_ir::{BlockId, CallsiteId, DeadBranch, ExternMarshalSite, ExternTy, FnCategory, FnId, FnIr, Module, Var};
use crate::modules::identity::ExportKey;
use crate::types::{ClosureTypes, KeySlot, Nominals, RenderTypes, Ty, Types, key_slot_var_count, key_slots_to_tys};
use std::cell::Cell;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, Default)]
pub struct SpecPlan {
    /// Definition-site type for each Var. Block params get the join of their
    /// predecessor args; Let-bound vars get their Prim's type under the env
    /// at that point in the block.
    pub vars: HashMap<Var, Ty>,
    /// Entry env per block, with branch narrowing applied at If terminators.
    pub block_envs: HashMap<BlockId, HashMap<Var, Ty>>,
    /// Vars known to hold callable values, separated by capability instead of
    /// representation. Thin function refs become `KnownFn`; env-carrying
    /// closures and opaque callable joins retain runtime-state/boundary facts
    /// for later consumers.
    pub callable_capabilities: HashMap<Var, CallableCapability>,
    /// Blocks provably reachable from the entry under the inferred types.
    /// If terminators whose condition is a singleton bool prune the dead
    /// branch and materialization to remove unreachable arms.
    pub reachable_blocks: HashSet<BlockId>,
    /// Per-spec branch facts used by per-spec codegen folding. These are
    /// stricter than `ModulePlan::dead_branches`: a branch can be dead for
    /// one specialization even when another specialization keeps it live.
    pub dead_branches: HashMap<BlockId, DeadBranch>,
    /// Per-callsite call-edge capability selected for this spec.
    ///
    /// This is the typed handoff codegen should consume. It keeps the selected
    /// target, result-hole demand, and executable return contract on one
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
}

impl ReturnStrategy {
    pub fn demand(&self) -> ReturnDemand {
        match self {
            ReturnStrategy::Value => ReturnDemand::value(),
            ReturnStrategy::TupleFields(arity) => ReturnDemand::tuple_fields(*arity),
            ReturnStrategy::ForwardedDemand(demand) => demand.clone(),
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
/// (`FnId`, input-type tuple, and return delivery). Specs are produced by
/// direct calls, closure calls, continuations, receive outcomes, entry seeds,
/// and callable-boundary reachability.
#[derive(Debug, Clone)]
pub struct ModulePlan {
    pub specs: HashMap<SpecKey, SpecPlan>,
    /// Closed reachable executable specs selected by the planner worklist.
    ///
    /// `ModulePlan` is the sole semantic reachability authority. Downstream
    /// materialization resolves these keys to stable `SpecId`s; it does not
    /// replay the call graph.
    pub reachable_specs: SpecKeySet,
    /// Why each reachable body remains in the executable plan.
    ///
    /// Entry specs come from whole-program roots such as `main/0`.
    /// Activation specs are justified by solved `type_infer` facts and any
    /// callable-boundary edges that keep closure targets executable.
    /// Projection-gap specs are temporary planner-visible shells whose return
    /// payload is still underconstrained.
    ///
    /// Keyed by `BodyKey`: a role is body-level justification, not an edge ABI.
    /// When reachable demand siblings disagree, the strongest role wins (see
    /// `compute_spec_roles`), so the projection is deterministic.
    pub spec_roles: HashMap<BodyKey, SpecReachabilityRole>,
    /// Semantic return payloads projected from activation inference onto the
    /// reachable planner specs. `SpecKey::demand` selects ABI/delivery shape;
    /// it does not create a different value payload. During the transplant,
    /// uncovered reachable specs are filled with `any` to keep the map total;
    /// planner telemetry reports those as activation projection gaps.
    pub effective_returns: HashMap<BodyKey, Ty>,
    /// Secondary index from FnId to its all-any key. Populated in
    /// `plan_module` from the final specs map so callers can find any-key
    /// specs without scanning the whole spec map.
    pub any_key_specs: HashMap<FnId, Vec<KeySlot>>,
    /// Stable per-family precedence for specialization selection. Keyed by
    /// `BodyKey`: precedence is a property of the `(FnId, input)` family and is
    /// invariant across `ReturnDemand` siblings, so demand never participates.
    pub spec_precedence: HashMap<BodyKey, u32>,
    /// Per-FnId summary of effects relevant to effect-sensitive rewrites.
    /// Allocation is tracked separately from externally observable barriers
    /// so planner-owned transforms can preserve observable behavior. Computed
    /// once over the static call graph, so later consumers read one cached fact
    /// instead of re-walking bodies.
    pub fn_effects: FnEffects,
    /// Per-If dead-branch facts safe to report at the module level.
    /// Populated at the end of `plan_module` by `compute_dead_branches`.
    /// Keyed by `(FnId, BlockId)` where the block ends in a `Term::If`;
    /// value names which branch is provably never taken. Read by the
    /// `collect_diagnostics`. These facts are proven by the fn's all-domain
    /// `any` key; narrower per-spec branch facts live on
    /// `SpecPlan::dead_branches` and are consumed only on planned bodies.
    pub dead_branches: HashMap<(FnId, BlockId), DeadBranch>,
    /// Per-FnId return-shape capabilities, computed once over the static call
    /// graph by `capabilities::compute_return_capabilities`. The return-demand
    /// grant reads these instead of re-walking bodies per call site.
    pub return_capabilities: ReturnCapabilities,
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
    /// Reaches a call through a value whose target is not statically known.
    /// The callee's effects are not visible to the local plan.
    pub calls_opaque: bool,
}

impl EffectSummary {
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

    /// A barrier to relocating an allocation between building a cons cell and
    /// filling its tail. List-tail return delivery moves the moment a cons is
    /// linked relative to whatever sits in the build/fill window, so any
    /// externally observable effect, an allocation-stats read, a scheduler
    /// interaction, a halt, or an opaque call (whose effects are not locally
    /// visible) makes that motion unsafe. Allocation by itself is not a barrier.
    pub fn blocks_return_context_motion(&self) -> bool {
        self.observable || self.reads_allocation_stats || self.scheduler_visible || self.halts || self.calls_opaque
    }
}

#[cfg(test)]
mod tests {
    use super::{
        ReturnDemand, ReturnStrategy, SpecKey, forwarded_return_contract_for_target, return_contract_for_target,
    };
    use crate::fz_ir::FnId;

    #[test]
    fn non_context_return_contracts_need_no_context_plan() {
        let target = SpecKey::value(FnId(7), Vec::new());
        let contract = return_contract_for_target(target.clone());
        assert_eq!(contract.target, target);
        assert_eq!(contract.strategy, ReturnStrategy::Value);

        let target = SpecKey {
            fn_id: FnId(7),
            input: Vec::new(),
            demand: ReturnDemand::tuple_fields(2),
        };
        let contract = return_contract_for_target(target.clone());
        assert_eq!(contract.target, target);
        assert_eq!(contract.strategy, ReturnStrategy::TupleFields(2));
    }

    #[test]
    fn forwarded_return_contract_pairs_tail_call_target_and_strategy() {
        let target = SpecKey {
            fn_id: FnId(7),
            input: Vec::new(),
            demand: ReturnDemand::tuple_fields(2),
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
            let precedence = *self.spec_precedence.get(&key.body_key()).unwrap_or(&u32::MAX);
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
        let candidates: Vec<BestCoverCandidate<'_, &BodyKey>> = self
            .effective_returns
            .keys()
            .filter(|key| key.fn_id == callee)
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

pub(crate) fn body_key_for_fn(f: &FnIr, input_tys: Vec<Ty>) -> BodyKey {
    BodyKey::value(f.id, f.semantic_key(input_tys))
}

pub(crate) fn body_key_for_fn_id(m: &Module, fid: FnId, input_tys: Vec<Ty>) -> BodyKey {
    body_key_for_fn(m.fn_by_id(fid), input_tys)
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
) -> HashMap<BodyKey, u32> {
    let mut keys_by_fn: HashMap<FnId, Vec<BodyKey>> = HashMap::new();
    for key in specs.keys() {
        let body_key = key.body_key();
        let bucket = keys_by_fn.entry(key.fn_id).or_default();
        if !bucket.contains(&body_key) {
            bucket.push(body_key);
        }
    }
    let mut precedence = HashMap::new();
    for (fid, mut keys) in keys_by_fn {
        keys.sort_by(|a, b| {
            let a_is_any = any_key_specs.get(&fid) == Some(&a.input);
            let b_is_any = any_key_specs.get(&fid) == Some(&b.input);
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
    /// walk after ensuring the spec has a typed body.
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
pub struct ReturnDemand {
    pub delivery: ReturnDelivery,
}

impl ReturnDemand {
    pub fn value() -> Self {
        Self {
            delivery: ReturnDelivery::Value,
        }
    }

    pub fn tuple_fields(arity: usize) -> Self {
        Self {
            delivery: ReturnDelivery::TupleFields(arity),
        }
    }

    pub fn is_value(&self) -> bool {
        self.delivery == ReturnDelivery::Value
    }

    pub fn tuple_field_arity(&self) -> Option<usize> {
        match self.delivery {
            ReturnDelivery::TupleFields(arity) => Some(arity),
            ReturnDelivery::Value => None,
        }
    }
}

pub(crate) fn return_strategy_for_demand(demand: ReturnDemand) -> ReturnStrategy {
    match demand.delivery {
        ReturnDelivery::Value => ReturnStrategy::Value,
        ReturnDelivery::TupleFields(arity) => ReturnStrategy::TupleFields(arity),
    }
}

pub(crate) fn return_contract_for_target(target: SpecKey) -> ReturnContract {
    let strategy = return_strategy_for_demand(target.demand.clone());
    ReturnContract::new(target, strategy)
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

    pub fn body_key(&self) -> BodyKey {
        BodyKey {
            fn_id: self.fn_id,
            input: self.input.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BodyKey {
    pub fn_id: FnId,
    pub input: Vec<KeySlot>,
}

impl BodyKey {
    pub fn value(fn_id: FnId, input: Vec<KeySlot>) -> Self {
        Self { fn_id, input }
    }
}

impl From<&SpecKey> for BodyKey {
    fn from(value: &SpecKey) -> Self {
        value.body_key()
    }
}

pub(crate) fn display_return_demand<T: RenderTypes + Types<Ty = Ty>>(_t: &T, demand: &ReturnDemand) -> String {
    match &demand.delivery {
        ReturnDelivery::Value => "value".to_string(),
        ReturnDelivery::TupleFields(n) => format!("tuple_fields({})", n),
    }
}

pub(crate) fn display_return_strategy<T: RenderTypes + Types<Ty = Ty>>(t: &T, strategy: &ReturnStrategy) -> String {
    match strategy {
        ReturnStrategy::Value => "value".to_string(),
        ReturnStrategy::TupleFields(arity) => format!("tuple_fields({})", arity),
        ReturnStrategy::ForwardedDemand(demand) => {
            format!("forwarded({})", display_return_demand(t, demand))
        }
    }
}

/// Per-FnId effect facts. Keyed by `FnId` because a function's effects are a
/// property of its body and call graph, independent of any caller's return
/// demand. Consumed by the destination-planning barrier and exposed on
/// `ModulePlan` for downstream passes.
pub type FnEffects = HashMap<FnId, EffectSummary>;

/// Per-FnId return-shape capabilities: cached structural facts that the
/// return-demand grant reads in O(1) instead of re-walking bodies per call
/// site. Computed once over the static call graph by
/// `capabilities::compute_return_capabilities` and stored on `ModulePlan`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ReturnCapability {
    /// `Some(n)` when every return delivers an `n`-tuple construction (across
    /// the fn's `Return`s and tail-call targets), so a destructuring caller may
    /// demand the fields directly and skip the struct box.
    pub returns_tuple_of_arity: Option<usize>,
    /// The fn (or its call graph) reaches an observable barrier, so relocating
    /// an allocation across it is unsafe; list-tail motion is refused here.
    /// Cached from the fn's `EffectSummary::blocks_return_context_motion`.
    pub blocks_motion: bool,
    /// `Some(n)` when this fn is a continuation that consumes its slot-0 input
    /// purely by projecting all `n` fields of an `n`-tuple — never using the
    /// tuple whole — so the producing call may deliver the fields directly
    /// instead of a materialized struct. `None` for any material use.
    pub destructures_slot0_into_arity: Option<usize>,
}

/// Per-FnId return capabilities, keyed like `FnEffects`.
pub type ReturnCapabilities = HashMap<FnId, ReturnCapability>;

/// Worklist-internal aliases for repeated index shapes.
pub(crate) type SpecKeySet = HashSet<SpecKey>;
/// Per-target entry-param callable capability facts.
///
/// This is keyed by the selected target `SpecKey`, not by the syntactic
/// caller-site alone, because multiple incoming edges can converge on the
/// same public spec. The vector is indexed by entry param position. Direct
/// calls populate explicit arg slots; continuations also use slot 0 for the
/// returned value that flows into the continuation.
pub(crate) type IncomingParamCallableCapabilities = HashMap<BodyKey, Vec<Option<CallableCapability>>>;

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
    let observed = input_tys.clone();
    (observed, input_tys)
}
