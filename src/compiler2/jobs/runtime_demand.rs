use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use super::super::body::{
    CallArg, CallInputMode, CallSiteId, ControlDestination, ControlEntryId, DeliveredValueSource, LoweredBody,
    LoweredEntry, LoweredStep, LoweredTail, ValueId, callsite_call_args, callsite_input_modes,
};
use super::super::callsite_dispatch::dispatch_stress;
use super::super::drive::FactKey;
use super::super::executable_facts::{
    ExecutableFacts, LocalCallableProducer, RuntimeDemandFacts, prepare_type_projection,
};
#[cfg(test)]
use super::super::executable_facts::{TransportOrigin, collect_callsite_return_origins, collect_value_origins};
use super::super::facts::FactUse;
use super::super::identity::{ExecutableKey, ExecutableNeed, FunctionId};
#[cfg(test)]
use super::super::pull::ProductReadObservation;
use super::super::pull::{
    CallableResolutionKey, IncomingInputRole, IncomingInputSource, InputSlot, ProductKey, ProductReadContext,
    ProductValue, PullOutcome, PullWait,
};
use super::super::semantic::{
    CallSiteSummary, CallableActivationInput, CallableDemand, CallableFlowEdge, CallableFlowFact, CallableSurface,
    CallableTarget, ExecutableRuntimeDemand, RuntimeDemand, RuntimeDemandTypeInputs, ShapeDemand,
    ground_dispatch_surfaces,
};
use super::super::types::{Ty, Types};
use super::super::world::World;
use crate::telemetry::{Telemetry, TelemetryExt as _};

#[cfg(test)]
thread_local! {
    static DEMAND_FORMULA_HARNESS: std::cell::RefCell<Option<DemandFormulaHarness>> = const {
        std::cell::RefCell::new(None)
    };
}

#[cfg(test)]
#[derive(Clone, Copy)]
pub(crate) enum DemandFormulaOrder {
    Forward,
    Reverse,
    Seeded(u64),
}

#[cfg(test)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum DemandFormulaCapture {
    All,
    Latest,
    None,
}

#[cfg(test)]
pub(crate) struct DemandFormulaOrdered;

#[cfg(test)]
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct DemandFormulaEvaluation {
    pub(crate) member: ExecutableKey,
    pub(crate) facts: Rc<ExecutableFacts>,
    pub(crate) current: RuntimeDemandFormulaSnapshot,
    pub(crate) product_answers: Vec<RuntimeDemandProductInput>,
    pub(crate) demand: ExecutableRuntimeDemand,
    pub(crate) contributions: HashMap<ExecutableKey, TargetDemandContribution>,
    pub(crate) product_reads: Vec<ProductReadObservation>,
}

/// The exact fields this formula reads from its own demand cell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RuntimeDemandOwnInput {
    pub(crate) return_demand: RuntimeDemand,
    pub(crate) input_demands: Vec<RuntimeDemand>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RuntimeDemandCallableInput {
    pub(crate) callable_activation_inputs: Vec<CallableActivationInput>,
    pub(crate) input_demands: Vec<RuntimeDemand>,
}

/// Role-specific peer reads; unrelated demand fields are not representable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RuntimeDemandFormulaSnapshot {
    pub(crate) own: RuntimeDemandOwnInput,
    pub(crate) target_inputs: HashMap<ExecutableKey, Vec<RuntimeDemand>>,
    pub(crate) callable_inputs: HashMap<ExecutableKey, RuntimeDemandCallableInput>,
}

/// Complete production boundary for one RuntimeDemand formula; `Types` is the
/// other explicit input and no `World` crosses this boundary.
struct RuntimeDemandFormulaInput<'a> {
    member: &'a ExecutableKey,
    facts: RuntimeDemandFacts<'a>,
    current: RuntimeDemandFormulaSnapshot,
    product_answers: Vec<RuntimeDemandProductInput>,
}

/// One exact product answer supplied to formula finalization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RuntimeDemandProductInput {
    pub(crate) key: CallableResolutionKey,
    pub(crate) answer: Option<CallableFlowEdge>,
}

#[cfg(test)]
struct DemandFormulaHarness {
    order: DemandFormulaOrder,
    capture: DemandFormulaCapture,
    evaluations: Vec<DemandFormulaEvaluation>,
}

#[cfg(test)]
impl DemandFormulaOrdered {
    pub(crate) fn install(order: DemandFormulaOrder) -> Self {
        Self::configure(order, DemandFormulaCapture::All)
    }

    pub(crate) fn latest(order: DemandFormulaOrder) -> Self {
        Self::configure(order, DemandFormulaCapture::Latest)
    }

    pub(crate) fn shuffle(order: DemandFormulaOrder) -> Self {
        Self::configure(order, DemandFormulaCapture::None)
    }

    fn configure(order: DemandFormulaOrder, capture: DemandFormulaCapture) -> Self {
        DEMAND_FORMULA_HARNESS.with(|harness| {
            assert!(harness.borrow().is_none(), "demand formula order already installed");
            *harness.borrow_mut() = Some(DemandFormulaHarness {
                order,
                capture,
                evaluations: Vec::new(),
            });
        });
        Self
    }

    pub(crate) fn evaluations(&self) -> Vec<DemandFormulaEvaluation> {
        DEMAND_FORMULA_HARNESS.with(|harness| {
            let harness = harness.borrow();
            let harness = harness.as_ref().unwrap();
            assert!(
                harness.capture != DemandFormulaCapture::None,
                "formula capture was not enabled"
            );
            harness.evaluations.clone()
        })
    }
}

#[cfg(test)]
impl Drop for DemandFormulaOrdered {
    fn drop(&mut self) {
        DEMAND_FORMULA_HARNESS.with(|harness| *harness.borrow_mut() = None);
    }
}

struct DerivedExecutableDemand {
    demand: ExecutableRuntimeDemand,
    call_return_demands: HashMap<CallSiteId, RuntimeDemand>,
    callable_flows: CallableFlowBuilder,
}

struct CallableFlowPlan {
    value: ValueId,
    producer: LocalCallableProducer,
    direct_surfaces: BTreeSet<CallableSurface>,
    direct_edges: Vec<CallableFlowEdge>,
    first_class_surfaces: BTreeSet<CallableSurface>,
    resolution_keys: Vec<CallableResolutionKey>,
    opaque: bool,
    escape: bool,
}

fn trivial_value_clause_ids(body: &LoweredBody, reachable: &[u32]) -> Vec<u32> {
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return Vec::new();
    };
    (0..clauses.len() as u32)
        .filter(|clause_id| !reachable.contains(clause_id))
        .filter(|clause_id| {
            let clause = &clauses[*clause_id as usize];
            let entry = &entries[clause.entry.as_u32() as usize];
            entry.steps.is_empty() && matches!(entry.tail, LoweredTail::Value { .. })
        })
        .collect()
}

#[derive(Debug, Clone, Default)]
struct CallableFlowBuilder {
    direct_surfaces: HashMap<ValueId, BTreeSet<CallableSurface>>,
    direct_targets: HashMap<ValueId, BTreeSet<CallableTarget>>,
    first_class_surfaces: HashMap<ValueId, BTreeSet<CallableSurface>>,
}

impl CallableFlowBuilder {
    fn new() -> Self {
        Self::default()
    }

    fn direct_surfaces(&self, value: ValueId) -> BTreeSet<CallableSurface> {
        self.direct_surfaces.get(&value).cloned().unwrap_or_default()
    }

    fn first_class_surfaces(&self, value: ValueId) -> BTreeSet<CallableSurface> {
        self.first_class_surfaces.get(&value).cloned().unwrap_or_default()
    }

    fn direct_targets(&self, value: ValueId) -> BTreeSet<CallableTarget> {
        self.direct_targets.get(&value).cloned().unwrap_or_default()
    }

    fn record_direct_demand(&mut self, facts: &RuntimeDemandFacts<'_>, value: ValueId, demand: &RuntimeDemand) {
        self.record_direct_surfaces(facts, value, &demand.callable.resolved);
        let targets = &demand.callable.targets;
        if !targets.is_empty() {
            let mut seen = HashSet::new();
            self.record_direct_targets_for_value(facts, value, targets, &mut seen);
        }
    }

    fn record_direct_surfaces(
        &mut self,
        facts: &RuntimeDemandFacts<'_>,
        value: ValueId,
        surfaces: &BTreeSet<CallableSurface>,
    ) {
        if surfaces.is_empty() {
            return;
        }
        let mut seen = HashSet::new();
        self.record_direct_surfaces_for_value(facts, value, surfaces, &mut seen);
    }

    fn record_first_class_demand(&mut self, facts: &RuntimeDemandFacts<'_>, value: ValueId, demand: &RuntimeDemand) {
        if demand.callable.is_first_class() {
            self.record_first_class_surfaces(facts, value, &demand.callable.resolved);
        }
    }

    fn record_first_class_surfaces(
        &mut self,
        facts: &RuntimeDemandFacts<'_>,
        value: ValueId,
        surfaces: &BTreeSet<CallableSurface>,
    ) {
        if surfaces.is_empty() {
            return;
        }
        let mut seen = HashSet::new();
        self.record_first_class_surfaces_for_value(facts, value, surfaces, &mut seen);
    }

    fn record_direct_surfaces_for_value(
        &mut self,
        facts: &RuntimeDemandFacts<'_>,
        value: ValueId,
        surfaces: &BTreeSet<CallableSurface>,
        seen: &mut HashSet<ValueId>,
    ) {
        if !seen.insert(value) {
            return;
        }
        if facts.callable_origin(value).is_some() {
            self.direct_surfaces
                .entry(value)
                .or_default()
                .extend(surfaces.iter().cloned());
        }
        for join in facts.delivered_value_joins.values().filter(|join| join.value == value) {
            for source in &join.sources {
                let DeliveredValueSource::LocalValue(source) = source else {
                    continue;
                };
                self.record_direct_surfaces_for_value(facts, *source, surfaces, seen);
            }
        }
    }

    fn record_first_class_surfaces_for_value(
        &mut self,
        facts: &RuntimeDemandFacts<'_>,
        value: ValueId,
        surfaces: &BTreeSet<CallableSurface>,
        seen: &mut HashSet<ValueId>,
    ) {
        if !seen.insert(value) {
            return;
        }
        if facts.callable_origin(value).is_some() {
            self.first_class_surfaces
                .entry(value)
                .or_default()
                .extend(surfaces.iter().cloned());
        }
        for join in facts.delivered_value_joins.values().filter(|join| join.value == value) {
            for source in &join.sources {
                let DeliveredValueSource::LocalValue(source) = source else {
                    continue;
                };
                self.record_first_class_surfaces_for_value(facts, *source, surfaces, seen);
            }
        }
    }

    fn record_direct_targets_for_value(
        &mut self,
        facts: &RuntimeDemandFacts<'_>,
        value: ValueId,
        targets: &BTreeSet<CallableTarget>,
        seen: &mut HashSet<ValueId>,
    ) {
        if !seen.insert(value) {
            return;
        }
        if facts.callable_origin(value).is_some() {
            self.direct_targets
                .entry(value)
                .or_default()
                .extend(targets.iter().cloned());
        }
        for join in facts.delivered_value_joins.values().filter(|join| join.value == value) {
            for source in &join.sources {
                let DeliveredValueSource::LocalValue(source) = source else {
                    continue;
                };
                self.record_direct_targets_for_value(facts, *source, targets, seen);
            }
        }
    }
}

/// Settle the demand SCC containing `executable` as one monotone fixpoint — the
/// ExecutableEffects pattern generalized to the richer demand lattice.
///
/// Demand dependencies run BOTH ways along every call edge (a caller reads its
/// callees' input demands; a callee's return demand joins its callers'
/// contributions), so the demand dependency graph is symmetric and the SCC
/// containing the anchor is exactly the anchor's call cone (stopping at
/// executables whose demand is already settled — those are external inputs,
/// like effects treats already-settled callee effects). The cone starts from
/// `CallSiteSummary` direct targets and previously materialized call edges. A
/// settled ascent then closes it over the callable-flow edges that demand
/// actually derived before any result is published.
///
/// The whole cone is then solved by a bottom-start Kleene ascent inside this
/// one producer: per round every member's demand is re-derived from the
/// previous round's iterates (input demands down edges, return-demand
/// contributions up edges, `ShapeDemand::join`), until nothing changes. Members
/// with no contributor at the fixpoint (the entry, escaped closure bodies) get
/// the whole-by-need bootstrap — absence is a distinct settled cell — and the
/// ascent continues monotonically. Only the settled fixpoint is ever published:
/// every member is memoized, so no other product can observe a mid-ascent
/// value. There is no active-SCC seed (the SCC is solved together and never
/// re-entered) and no consumed-return floor: at the fixpoint the callee's real
/// input demand is present, so the demand is derived. A statically consumed
/// return may honestly settle at `ignore` — static consumption over-reports
/// liveness when the consuming position is itself undemanded (e.g. an argument
/// the settled callee ignores); transport's resume gate owns that value's
/// physical soundness from the static body fact, independent of demand.
///
/// Publication closes the stale-caller window: when a member's settled
/// contribution GROWS the joined return demand of an executable settled
/// earlier OUTSIDE this cone, that external's memo (and its dependents') is
/// displaced — but the members were derived reading the external's PRE-growth
/// input demands, and nothing downstream re-derives a caller of a re-settled
/// callee. So the producer refuses to memoize a cone that displaced one of its
/// own external inputs: it re-collects (the displaced external has no memo and
/// is reachable through the very edge that carried the contribution, so it is
/// absorbed as a member) and re-settles the grown cone together. Each re-cycle
/// strictly grows the member set — memos are only recorded once publication is
/// quiescent, members never leave the cone, and at least the moved external
/// joins — so the loop terminates within the finite demanded universe.
/// What one demand-cone settlement cost, in the terms that drive it.
///
/// A cone is collected transitively from its anchor and stops only at
/// executables whose demand has already settled, so `members` -- not the single
/// executable the product key names -- is the real unit of work behind a
/// `RuntimeDemand(E)` answer. `rounds` is the height the Jacobi ascent climbed
/// and `derivations` is how many member re-derivations it actually ran, which
/// is well below `members * rounds` because a member whose reads did not move
/// is skipped. Together they separate the three ways this product can get
/// expensive -- a cone that is too big, an ascent that climbs too far, or
/// members that re-derive too often -- which a wall-clock number cannot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DemandConeSettlement {
    pub members: u64,
    pub external_members: u64,
    pub rounds: u64,
    pub derivations: u64,
}

pub(crate) fn produce_runtime_demand_product<T: Telemetry>(
    world: &mut World,
    tel: &T,
    context: &mut ProductReadContext<'_>,
    executable: &ExecutableKey,
) -> PullOutcome {
    let mut actual_flow_edges: HashMap<ExecutableKey, HashSet<ExecutableKey>> = HashMap::new();
    let mut retry_guard = None;
    loop {
        let graph = match collect_demand_cone(world, tel, context, executable, &actual_flow_edges) {
            Ok(graph) => graph,
            Err(waits) => return product_waits(waits),
        };
        let members: HashSet<ExecutableKey> = graph.facts.keys().cloned().collect();
        let edge_count = graph.edges.values().map(HashSet::len).sum();
        match retry_guard.take() {
            Some(DemandConeRetryGuard::ActualFlowEdges {
                member_count,
                edge_count: previous_edge_count,
            }) => assert!(
                members.len() > member_count || edge_count > previous_edge_count,
                "re-collecting the demand cone for {executable:?} after actual flow-edge growth \
                 must grow its members or owner edges"
            ),
            Some(DemandConeRetryGuard::DisplacedExternal { member_count }) => assert!(
                members.len() > member_count,
                "re-collecting the demand cone for {executable:?} must absorb the displaced external \
                 it re-settles for; the cone stalled at {} members",
                members.len()
            ),
            None => {}
        }
        let settled = match settle_demand_cone(world, tel, context, &graph) {
            Ok(settled) => settled,
            Err(waits) => return product_waits(waits),
        };
        let mut grew_actual_flow_edges = false;
        for (member, demand) in &settled.demands {
            let graph_edges = graph.edges.get(member);
            let member_flow_edges = actual_flow_edges.entry(member.clone()).or_default();
            for target in demand
                .callable_flows
                .values()
                .flat_map(|flow| flow.direct_edges.iter().chain(&flow.first_class_edges))
                .map(|edge| edge.resolution.clone())
            {
                if !graph_edges.is_some_and(|edges| edges.contains(&target)) {
                    grew_actual_flow_edges = true;
                }
                member_flow_edges.insert(target);
            }
        }
        if grew_actual_flow_edges {
            retry_guard = Some(DemandConeRetryGuard::ActualFlowEdges {
                member_count: members.len(),
                edge_count,
            });
            continue;
        }
        // Persist the settled evidence FIRST: the per-caller contribution store is
        // the cross-settle channel (a later cone anchored elsewhere reads these as
        // external caller evidence) and the change-driven retraction wavefront in
        // `recompute_return_demand` fires only for NON-member targets — within this
        // settlement the joins are quiescent by construction, so recording the
        // members' memos afterwards cannot be wiped by their own contributions.
        let mut displaced: HashSet<ExecutableKey> = HashSet::new();
        for (member, contributions) in settled.contributions {
            // A callable-flow resolution can already be
            // memoized from an earlier, separate pull (its own cone anchored
            // elsewhere ran first) -- then it is `graph.external`, not a member,
            // and this settlement's pin must cross the cone boundary exactly
            // like a return-demand contribution does. Both halves persist
            // through the same per-caller replace-and-recompute channel.
            let mut return_demand_contributions: HashMap<ExecutableKey, RuntimeDemand> = HashMap::new();
            let mut input_demand_contributions: HashMap<ExecutableKey, HashMap<usize, RuntimeDemand>> = HashMap::new();
            for (target, contribution) in contributions {
                if let Some(demand) = contribution.return_demand {
                    return_demand_contributions.insert(target.clone(), demand);
                }
                if !contribution.input_demands.is_empty() {
                    input_demand_contributions.insert(target, contribution.input_demands);
                }
            }
            displaced.extend(context.session_mut().replace_settled_return_demand_contributions(
                tel,
                member.clone(),
                return_demand_contributions,
                &members,
            ));
            displaced.extend(context.session_mut().replace_settled_input_demand_contributions(
                tel,
                member,
                input_demand_contributions,
                &members,
            ));
        }
        // The stale-caller window: this settlement read the external's settled
        // demand as an input AND its publication moved that external's join, so
        // every member was derived against a displaced value. Do not memoize —
        // re-collect and settle the grown cone (the displaced external is now
        // memo-less and joins as a member). The exact predicate is membership
        // in `graph.external` — the set of demand values this settlement READ.
        // A displaced executable outside it (a pure downstream dependent, or a
        // withdrawn-contribution target the cone never read) cannot have staled
        // the members; it re-settles on its own next pull, exactly like any
        // cross-settle displacement. A withdrawn target that IS a read external
        // conservatively re-collects too — terminating by the same strict-growth
        // argument, and honest: its retraction changed an input we consumed.
        if displaced.iter().any(|key| graph.external.contains_key(key)) {
            retry_guard = Some(DemandConeRetryGuard::DisplacedExternal {
                member_count: members.len(),
            });
            continue;
        }
        context.remove_product_dependencies(members.iter().cloned().map(ProductKey::RuntimeDemand));
        for (member, edges) in &graph.edges {
            context
                .session_mut()
                .record_settled_demand_callees(member.clone(), edges.clone());
            for target in edges {
                if !actual_flow_edges
                    .get(member)
                    .is_some_and(|flow_edges| flow_edges.contains(target))
                {
                    context
                        .session_mut()
                        .record_runtime_demand_dependency(target.clone(), member.clone());
                }
            }
        }
        for (member, edges) in &actual_flow_edges {
            for target in edges {
                context
                    .session_mut()
                    .record_demand_flow_dependency(target.clone(), member.clone());
            }
        }
        let demand = settled
            .demands
            .get(executable)
            .cloned()
            .expect("requested executable should belong to its demand cone");
        for (member, member_demand) in settled.demands {
            if member == *executable {
                continue;
            }
            context.publish_product(
                tel,
                ProductKey::RuntimeDemand(member.clone()),
                ProductValue::RuntimeDemand(Box::new(member_demand.clone())),
            );
        }
        return PullOutcome::Produced(ProductValue::RuntimeDemand(Box::new(demand)));
    }
}

enum DemandConeRetryGuard {
    ActualFlowEdges { member_count: usize, edge_count: usize },
    DisplacedExternal { member_count: usize },
}

/// The demand cone: per-member settled facts, the demand-relevant edge set per
/// member, and the settled demands of callees outside the cone.
struct DemandGraph {
    facts: HashMap<ExecutableKey, Rc<ExecutableFacts>>,
    edges: HashMap<ExecutableKey, HashSet<ExecutableKey>>,
    external: HashMap<ExecutableKey, ExecutableRuntimeDemand>,
}

struct SettledDemandCone {
    demands: HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    contributions: HashMap<ExecutableKey, HashMap<ExecutableKey, TargetDemandContribution>>,
}

/// One caller's contribution to a single target: its joined return-demand
/// pin (the existing channel) plus any boundary-pinned INPUT positions —
/// e.g. a boundary-published callable's argument, which a contract can
/// demand even when the body itself elides it. Both halves join
/// independently onto the target's `ExecutableRuntimeDemand`.
#[derive(Debug, Clone, Default, PartialEq)]
pub(crate) struct TargetDemandContribution {
    pub(crate) return_demand: Option<RuntimeDemand>,
    pub(crate) input_demands: HashMap<usize, RuntimeDemand>,
}

fn collect_demand_cone(
    world: &World,
    tel: &impl Telemetry,
    context: &mut ProductReadContext<'_>,
    anchor: &ExecutableKey,
    actual_flow_edges: &HashMap<ExecutableKey, HashSet<ExecutableKey>>,
) -> Result<DemandGraph, HashSet<PullWait>> {
    let mut facts: HashMap<ExecutableKey, Rc<ExecutableFacts>> = HashMap::new();
    let mut edges: HashMap<ExecutableKey, HashSet<ExecutableKey>> = HashMap::new();
    let mut external = HashMap::new();
    let mut waits = HashSet::new();
    let mut stack = vec![anchor.clone()];
    let mut seen = HashSet::new();
    while let Some(current) = stack.pop() {
        if !seen.insert(current.clone()) {
            continue;
        }
        if current != *anchor
            && let Some(demand) = context.read_runtime_demand(tel, &current)
        {
            external.insert(current, demand.clone());
            continue;
        }
        let Some(current_facts) = context.read_executable_facts(world, &current) else {
            waits.insert(PullWait::Fact(FactUse::settled(FactKey::ExecutableFacts(current))));
            continue;
        };
        let mut targets = direct_local_targets(&current_facts);
        if let Some(callees) = context.session().settled_demand_callees(&current) {
            targets.extend(callees.iter().cloned());
        }
        if let Some(callees) = actual_flow_edges.get(&current) {
            targets.extend(callees.iter().cloned());
        }
        stack.extend(targets.iter().cloned());
        edges.insert(current.clone(), targets);
        facts.insert(current, current_facts);
    }
    if waits.is_empty() {
        Ok(DemandGraph { facts, edges, external })
    } else {
        Err(waits)
    }
}

fn settle_demand_cone<T: Telemetry>(
    world: &mut World,
    tel: &T,
    context: &mut ProductReadContext<'_>,
    graph: &DemandGraph,
) -> Result<SettledDemandCone, HashSet<PullWait>> {
    // Each Jacobi round reads one frozen previous-round snapshot. Member order
    // is therefore schedule only: formulas are read-only and joins commute, so
    // the native HashMap order is deliberately left unconstrained.
    let members: Vec<ExecutableKey> = graph.facts.keys().cloned().collect();
    #[cfg(test)]
    let mut members = members;
    #[cfg(test)]
    DEMAND_FORMULA_HARNESS.with(|configured| {
        use super::super::semantic::StableSortKey as _;
        let Some(order) = configured.borrow().as_ref().map(|harness| harness.order) else {
            return;
        };
        members.sort_by_cached_key(|member| member.stable_sort_key(world.types()));
        match order {
            DemandFormulaOrder::Forward => {}
            DemandFormulaOrder::Reverse => members.reverse(),
            DemandFormulaOrder::Seeded(mut seed) => {
                for index in (1..members.len()).rev() {
                    seed ^= seed << 13;
                    seed ^= seed >> 7;
                    seed ^= seed << 17;
                    members.swap(index, seed as usize % (index + 1));
                }
            }
        }
    });
    let member_set: HashSet<ExecutableKey> = members.iter().cloned().collect();
    // The external caller evidence is settled session state the ascent never
    // mutates: join it once, not per member per round.
    let external_return_demands: HashMap<ExecutableKey, RuntimeDemand> = members
        .iter()
        .filter_map(|member| {
            context
                .session()
                .external_return_demand(member, &member_set)
                .map(|demand| (member.clone(), demand))
        })
        .collect();
    // The INPUT-side sibling: boundary-pinned argument positions a settled
    // contributor OUTSIDE this cone joined onto a member the cone treats as
    // an anchor (a resolution settled on an earlier, separate pull before its
    // producer's cone was collected).
    let external_input_demands: HashMap<ExecutableKey, HashMap<usize, RuntimeDemand>> = members
        .iter()
        .filter_map(|member| {
            let demands = context.session().external_input_demand(member, &member_set);
            (!demands.is_empty()).then_some((member.clone(), demands))
        })
        .collect();
    // A member's derivation reads exactly three things out of the round's
    // iterates: its own joined return demand, its call-edge targets' demands
    // (`local_target_input_demands` over the same targets the cone's edges
    // carry), and — for a member producing a lambda — the input demands of
    // every executable of the produced function (the capture-prefix scan in
    // `propagate_lambda_capture_demands`). These two reverse indexes name the
    // readers a moved member must re-dirty; anything else re-derives
    // identically and is skipped.
    let mut edge_readers: HashMap<&ExecutableKey, Vec<&ExecutableKey>> = HashMap::new();
    for (reader, targets) in &graph.edges {
        for target in targets {
            edge_readers.entry(target).or_default().push(reader);
        }
    }
    let mut produced_function_readers: HashMap<FunctionId, Vec<&ExecutableKey>> = HashMap::new();
    for member in &members {
        let facts = graph.facts.get(member).expect("every cone member has facts");
        for (_, producer) in facts.callable_origins() {
            produced_function_readers
                .entry(producer.function)
                .or_default()
                .push(member);
        }
    }
    // `reads` is the Jacobi input view: the externals' settled demands plus
    // every member's previous-round iterate, its `return_demand` overwritten
    // with the round's joined value. It is maintained incrementally — the
    // externals are cloned in once, and only members whose iterate moved are
    // rewritten between rounds.
    let mut reads: HashMap<ExecutableKey, ExecutableRuntimeDemand> = graph.external.clone();
    let mut iterates: HashMap<ExecutableKey, ExecutableRuntimeDemand> = HashMap::new();
    for member in &members {
        let facts = graph.facts.get(member).expect("every cone member has facts");
        let bottom = empty_runtime_demand(member, facts, world.types());
        reads.insert(member.clone(), bottom.clone());
        iterates.insert(member.clone(), bottom);
    }
    let mut contributions: HashMap<ExecutableKey, HashMap<ExecutableKey, TargetDemandContribution>> = HashMap::new();
    let mut bootstrapped: HashSet<ExecutableKey> = HashSet::new();
    let mut dirty: HashSet<&ExecutableKey> = members.iter().collect();
    let mut rounds = 0_u32;
    let mut derivations = 0_u64;
    loop {
        rounds += 1;
        // Invert the per-caller contribution store once per round: each
        // member's joined return demand (and boundary-pinned input demand
        // positions) is then a single lookup instead of a scan over every
        // member's contributions (quadratic in cone size).
        let mut joined_contributions: HashMap<ExecutableKey, RuntimeDemand> = HashMap::new();
        let mut joined_input_contributions: HashMap<ExecutableKey, HashMap<usize, RuntimeDemand>> = HashMap::new();
        for member_contributions in contributions.values() {
            for (target, contribution) in member_contributions {
                if let Some(demand) = &contribution.return_demand {
                    joined_contributions
                        .entry(target.clone())
                        .and_modify(|joined| joined.join_assign(demand))
                        .or_insert_with(|| demand.clone());
                }
                if !contribution.input_demands.is_empty() {
                    let slots = joined_input_contributions.entry(target.clone()).or_default();
                    for (index, demand) in &contribution.input_demands {
                        slots
                            .entry(*index)
                            .and_modify(|joined| joined.join_assign(demand))
                            .or_insert_with(|| demand.clone());
                    }
                }
            }
        }
        for member in &members {
            let mut joined = external_return_demands
                .get(member)
                .cloned()
                .unwrap_or_else(RuntimeDemand::ignore);
            if let Some(demand) = joined_contributions.get(member) {
                joined.join_assign(demand);
            }
            if bootstrapped.contains(member) {
                joined.join_assign(&runtime_demand_for_executable_need(member.need));
            }
            let cell = reads.get_mut(member).expect("every cone member has a read cell");
            let mut moved_cell = false;
            if cell.return_demand != joined {
                cell.return_demand = joined;
                moved_cell = true;
            }
            let local_positions = joined_input_contributions.get(member).into_iter().flatten();
            let external_positions = external_input_demands.get(member).into_iter().flatten();
            for (&index, demand) in local_positions.chain(external_positions) {
                if let Some(slot) = cell.input_demands.get_mut(index) {
                    let mut merged = slot.clone();
                    merged.join_assign(demand);
                    if merged != *slot {
                        *slot = merged;
                        moved_cell = true;
                    }
                }
            }
            if moved_cell {
                dirty.insert(member);
            }
        }
        // Re-derive the dirty members against the previous round's view; a
        // member none of whose reads moved derives the identical value and is
        // skipped. The Jacobi round structure is unchanged: derived values
        // land in the shared view only after the whole round.
        let mut waits = HashSet::new();
        let mut moved: Vec<&ExecutableKey> = Vec::new();
        let mut demand_moved: Vec<&ExecutableKey> = Vec::new();
        let mut read_updates: Vec<(&ExecutableKey, ExecutableRuntimeDemand)> = Vec::new();
        for member in &members {
            if !dirty.contains(member) {
                continue;
            }
            let facts = graph.facts.get(member).expect("every cone member has facts");
            derivations += 1;
            let (demand, member_contributions) =
                derive_member_demand(world.types(), tel, context, member, facts, &reads, &mut waits);
            let demand_changed = iterates.get(member) != Some(&demand);
            if demand_changed {
                demand_moved.push(member);
                read_updates.push((member, demand.clone()));
                iterates.insert(member.clone(), demand);
            }
            if demand_changed || contributions.get(member) != Some(&member_contributions) {
                contributions.insert(member.clone(), member_contributions);
                moved.push(member);
            }
        }
        if !waits.is_empty() {
            return Err(waits);
        }
        dirty.clear();
        for (member, demand) in read_updates {
            reads.insert(member.clone(), demand);
        }
        for member in &demand_moved {
            if let Some(readers) = edge_readers.get(*member) {
                dirty.extend(readers.iter().copied());
            }
            if let Some(readers) = produced_function_readers.get(&member.activation.function) {
                dirty.extend(readers.iter().copied());
            }
        }
        if moved.is_empty() {
            // A member standing behind a construction wrapper is reached
            // through the boxed apply seam, and the callsite that reaches it
            // there names none of the wrapper's members -- a mailbox callable
            // names no target at all. So the contributions this cone CAN see
            // are, exactly like an unnamed member's, not the whole story: a
            // grounded sibling callsite's discarded result must not be allowed
            // to settle the member at zero lanes while the wrapper it also
            // sits behind still hands a value back (fz-kdt.155).
            //
            // Only the bottom is at stake. A visible contributor asking for
            // anything at all already keeps the member's return non-empty,
            // which is all the wrapper needs -- its adapter boxes however many
            // lanes the member returns into the one public word -- so a
            // destination-passing member keeps its field lanes.
            let seam_members: HashSet<&ExecutableKey> = reads
                .values()
                .flat_map(|demand| demand.callable_flows.values())
                .flat_map(|flow| &flow.first_class_edges)
                .map(|edge| &edge.resolution)
                .collect();
            // At the fixpoint the round's inverted join names exactly the
            // members some contributor names in the settled contribution
            // store.
            let unnamed: Vec<ExecutableKey> = members
                .iter()
                .filter(|member| {
                    !bootstrapped.contains(*member)
                        && !external_return_demands.contains_key(*member)
                        && joined_contributions.get(*member).is_none_or(RuntimeDemand::is_ignore)
                        && (!joined_contributions.contains_key(*member) || seam_members.contains(*member))
                })
                .cloned()
                .collect();
            if unnamed.is_empty() {
                tel.raw_event1(
                    &["fz", "compiler2", "demand", "cone", "settled"],
                    &DemandConeSettlement {
                        members: members.len() as u64,
                        external_members: graph.external.len() as u64,
                        rounds: u64::from(rounds),
                        derivations,
                    },
                );
                return Ok(SettledDemandCone {
                    demands: iterates,
                    contributions,
                });
            }
            // Nothing this cone can see asks these members for anything, and
            // something outside it reaches them: the entry, delivery-reached
            // continuations, escaped closure bodies, or a construction
            // wrapper. A settled bottom is a distinct cell from a settled
            // narrowing — the whole-by-need bootstrap applies AT the fixpoint,
            // where every contribution has arrived so the decision cannot
            // depend on the schedule, and sticks: it only ever raises, so the
            // ascent stays monotone.
            bootstrapped.extend(unnamed);
        }
        // A hard budget in every build: the ascent is monotone over a
        // finite-height lattice, so exceeding the probe-measured bound means a
        // non-monotone regression — fail loudly instead of hanging in release.
        if rounds >= DEMAND_ASCENT_ROUND_BUDGET {
            panic!(
                "demand ascent exceeded its round budget ({DEMAND_ASCENT_ROUND_BUDGET}) settling a \
                 {}-member cone: the demand lattice has an ascent hole; still-moving members: {moved:?}",
                members.len()
            );
        }
    }
}

const DEMAND_ASCENT_ROUND_BUDGET: u32 = 32;

fn derive_member_demand<T: Telemetry>(
    types: &Types,
    tel: &T,
    context: &mut ProductReadContext<'_>,
    member: &ExecutableKey,
    facts: &Rc<ExecutableFacts>,
    reads: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    waits: &mut HashSet<PullWait>,
) -> (
    ExecutableRuntimeDemand,
    HashMap<ExecutableKey, TargetDemandContribution>,
) {
    #[cfg(test)]
    let identity_inventory = types.identity_inventory();
    #[cfg(test)]
    let read_checkpoint = context.product_read_checkpoint();
    let mut input = RuntimeDemandFormulaInput::new(member, facts, reads);
    let mut derived = derive_executable_runtime_demand(types, &input);
    let return_demand_contributions = call_return_demand_contributions(&input.facts, derived.call_return_demands);
    let flow_plans = plan_callable_flows(types, &input, &derived.callable_flows, &derived.demand);
    input.product_answers = read_runtime_demand_products(tel, context, &flow_plans, waits);
    finish_callable_flows(&input, flow_plans, &mut derived.demand);
    let boundary_input_demands = callable_boundary_input_demand_contributions_product(&derived.demand);
    let mut contributions = HashMap::<ExecutableKey, TargetDemandContribution>::new();
    for (target, demand) in return_demand_contributions {
        let entry = contributions.entry(target).or_default();
        match &mut entry.return_demand {
            Some(current) => current.join_assign(&demand),
            None => entry.return_demand = Some(demand),
        }
    }
    for (target, index, demand) in boundary_input_demands {
        let entry = contributions.entry(target).or_default();
        entry
            .input_demands
            .entry(index)
            .and_modify(|current| current.join_assign(&demand))
            .or_insert(demand);
    }
    derived.demand.ground_callable_surfaces(types);
    #[cfg(test)]
    assert_eq!(
        types.identity_inventory(),
        identity_inventory,
        "one RuntimeDemand formula evaluation must not mint types or structural addresses"
    );
    #[cfg(test)]
    DEMAND_FORMULA_HARNESS.with(|harness| {
        if let Some(harness) = harness.borrow_mut().as_mut() {
            if harness.capture == DemandFormulaCapture::None {
                return;
            }
            let evaluation = DemandFormulaEvaluation {
                member: member.clone(),
                facts: Rc::clone(facts),
                current: input.current.clone(),
                product_answers: input.product_answers.clone(),
                demand: derived.demand.clone(),
                contributions: contributions.clone(),
                product_reads: context.product_reads_since(read_checkpoint),
            };
            if harness.capture == DemandFormulaCapture::Latest
                && let Some(previous) = harness
                    .evaluations
                    .iter_mut()
                    .find(|previous| previous.member == evaluation.member)
            {
                *previous = evaluation;
            } else {
                harness.evaluations.push(evaluation);
            }
        }
    });
    (derived.demand, contributions)
}

impl<'a> RuntimeDemandFormulaInput<'a> {
    fn new(
        member: &'a ExecutableKey,
        facts: &'a ExecutableFacts,
        reads: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    ) -> Self {
        Self {
            current: RuntimeDemandFormulaSnapshot::new(member, facts, reads),
            member,
            facts: facts.runtime_demand_facts(),
            product_answers: Vec::new(),
        }
    }
}

impl RuntimeDemandFormulaSnapshot {
    fn new(
        member: &ExecutableKey,
        facts: &ExecutableFacts,
        reads: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    ) -> Self {
        let own = reads.get(member).expect("formula member must have a current demand");
        let target_inputs = direct_local_targets(facts)
            .into_iter()
            .filter_map(|key| reads.get(&key).map(|demand| (key, demand.input_demands.clone())))
            .collect();
        let mut callable_inputs = HashMap::new();
        for (_, producer) in facts.callable_origins() {
            for (key, demand) in reads.iter().filter(|(key, _)| {
                key.activation.root == member.activation.root && key.activation.function == producer.function
            }) {
                callable_inputs.insert(
                    key.clone(),
                    RuntimeDemandCallableInput {
                        callable_activation_inputs: demand.callable_activation_inputs.clone(),
                        input_demands: demand.input_demands.clone(),
                    },
                );
            }
        }
        Self {
            own: RuntimeDemandOwnInput {
                return_demand: own.return_demand.clone(),
                input_demands: own.input_demands.clone(),
            },
            target_inputs,
            callable_inputs,
        }
    }
}

pub(crate) fn produce_outgoing_input_edges_product<T: Telemetry>(
    world: &mut World,
    tel: &T,
    context: &mut ProductReadContext<'_>,
    executable: &ExecutableKey,
) -> PullOutcome {
    let mut waits = HashSet::new();
    let Some(facts) = context.read_executable_facts(world, executable) else {
        waits.insert(PullWait::Fact(FactUse::settled(FactKey::ExecutableFacts(
            executable.clone(),
        ))));
        return product_waits(waits);
    };
    let Some(runtime_demand) = context.read_runtime_demand(tel, executable) else {
        waits.insert(PullWait::Product(ProductKey::RuntimeDemand(executable.clone())));
        return product_waits(waits);
    };

    let mut contribution = HashMap::new();
    collect_callsite_input_sources(world, executable, &facts, &mut contribution);
    collect_callable_capture_input_sources(executable, &runtime_demand, &mut contribution);
    PullOutcome::Produced(ProductValue::OutgoingInputEdges(Rc::new(contribution)))
}

fn product_waits(waits: HashSet<PullWait>) -> PullOutcome {
    PullOutcome::Waiting(waits.into_iter().collect())
}

pub(crate) fn produce_callable_resolution_product<T: Telemetry>(
    world: &mut World,
    _tel: &T,
    context: &mut ProductReadContext<'_>,
    key: &CallableResolutionKey,
) -> PullOutcome {
    let Some(facts) = context.read_executable_facts(world, &key.executable) else {
        return PullOutcome::wait_on_fact(FactUse::settled(FactKey::ExecutableFacts(key.executable.clone())));
    };
    let Some(producer) = facts.callable_origin(key.value) else {
        panic!("callable resolution key names no local producer: {key:?}");
    };
    let mut waits = HashSet::new();
    if !require_activation_key_facts_product(world, context, producer.function, &mut waits) {
        return product_waits(waits);
    }
    let Some(capture_tys) = producer
        .captures
        .iter()
        .map(|capture| facts.analysis.value_types.get(capture).copied())
        .collect::<Option<Vec<_>>>()
    else {
        panic!("settled callable producer has no capture types: {producer:?}");
    };
    let mut inputs = capture_tys.clone();
    inputs.extend(key.surface.inputs.iter().copied());
    let any = world.types_mut().any();
    let mut boundary_types = RuntimeDemandTypeInputs::new(any);
    for &ty in &key.surface.inputs {
        prepare_type_projection(world, &mut boundary_types, ty);
    }
    PullOutcome::Produced(ProductValue::CallableResolution(CallableFlowEdge {
        surface: key.surface.clone(),
        resolution: ExecutableKey {
            activation: world.activation_key(key.executable.activation.root, producer.function, &inputs),
            need: ExecutableNeed::Value,
        },
        capture_semantic_inputs: (0..capture_tys.len()).collect(),
        surface_semantic_inputs: (capture_tys.len()..inputs.len()).collect(),
        boundary_input_demands: key
            .surface
            .inputs
            .iter()
            .map(|&ty| informative_boundary_demand_from_types(world, &boundary_types, ty))
            .collect(),
    }))
}

fn collect_callsite_input_sources(
    world: &World,
    executable: &ExecutableKey,
    facts: &ExecutableFacts,
    contribution: &mut HashMap<InputSlot, HashSet<IncomingInputSource>>,
) {
    let call_args = callsite_call_args(&facts.body);
    let call_modes = callsite_input_modes(&facts.body);
    for (callsite, summary) in &facts.callsites {
        let Some(args) = call_args.get(callsite) else {
            continue;
        };
        let Some(mode) = call_modes.get(callsite).copied() else {
            continue;
        };
        let need = facts
            .callsite_needs
            .get(callsite)
            .copied()
            .unwrap_or(ExecutableNeed::Value);
        for target in &summary.targets {
            let Some(callee) = target.runtime_executable(need) else {
                continue;
            };
            for (index, arg) in args.iter().enumerate() {
                let Some(semantic_index) =
                    mode.semantic_index(callee.activation.input_len(world.types()), args.len(), index)
                else {
                    continue;
                };
                contribution
                    .entry(InputSlot {
                        executable: callee.clone(),
                        semantic_index,
                    })
                    .or_default()
                    .insert(IncomingInputSource {
                        producer: executable.clone(),
                        value: arg.value,
                        role: IncomingInputRole::CallArgument,
                    });
            }
        }
    }
}

fn collect_callable_capture_input_sources(
    executable: &ExecutableKey,
    demand: &ExecutableRuntimeDemand,
    contribution: &mut HashMap<InputSlot, HashSet<IncomingInputSource>>,
) {
    for (&flow_value, flow) in &demand.callable_flows {
        for edge in flow.direct_edges.iter().chain(&flow.first_class_edges) {
            for (capture_index, (&semantic_index, value)) in edge
                .capture_semantic_inputs
                .iter()
                .zip(flow.captures.iter().copied())
                .enumerate()
            {
                contribution
                    .entry(InputSlot {
                        executable: edge.resolution.clone(),
                        semantic_index,
                    })
                    .or_default()
                    .insert(IncomingInputSource {
                        producer: executable.clone(),
                        value,
                        role: IncomingInputRole::CallableCapture {
                            construction: flow_value,
                            capture_index,
                        },
                    });
            }
        }
    }
}

fn empty_runtime_demand(executable: &ExecutableKey, facts: &ExecutableFacts, types: &Types) -> ExecutableRuntimeDemand {
    ExecutableRuntimeDemand {
        callable_activation_inputs: facts.callable_activation_inputs.clone(),
        input_demands: vec![RuntimeDemand::ignore(); executable.activation.input_len(types)],
        ..ExecutableRuntimeDemand::default()
    }
}

fn direct_local_targets(facts: &ExecutableFacts) -> HashSet<ExecutableKey> {
    let mut targets = HashSet::new();
    for (callsite, summary) in &facts.callsites {
        let need = facts
            .callsite_needs
            .get(callsite)
            .copied()
            .unwrap_or(ExecutableNeed::Value);
        targets.extend(local_call_targets(summary, need));
    }
    targets
}

fn call_return_demand_contributions(
    facts: &RuntimeDemandFacts<'_>,
    observed_returns: HashMap<CallSiteId, RuntimeDemand>,
) -> Vec<(ExecutableKey, RuntimeDemand)> {
    // A caller's contribution names EVERY local callee it calls, including the
    // ones whose return it discards -- so the iteration is over the static call
    // graph (`facts.callsites`), not the lossy `observed_returns` (which omits a
    // callsite entirely once its demand collapses to `ignore`). A discarded
    // callee contributes the bottom `ignore` demand: a distinct cell from "no
    // caller has named this callee at all" -- an observed-but-discarded callee
    // collapses its return at the settled fixpoint, whereas a member no
    // contributor ever names gets the whole-by-need bootstrap at settle time
    // (see `settle_demand_cone`).
    let mut out = Vec::new();
    for (callsite, summary) in facts.callsites {
        let need = facts
            .callsite_needs
            .get(callsite)
            .copied()
            .unwrap_or(ExecutableNeed::Value);
        let observed = observed_returns
            .get(callsite)
            .cloned()
            .unwrap_or_else(RuntimeDemand::ignore);
        let delivered = match need {
            // Destination-passing delivery writes fields into the caller frame,
            // so its slots are retained even when a field is ignored.
            ExecutableNeed::TupleFields(_) => tuple_return_demand_for_observed_need(need, observed),
            ExecutableNeed::Value => observed,
        };
        for target in local_call_targets(summary, need) {
            out.push((target, delivered.clone()));
        }
    }
    out
}

fn tuple_return_demand_for_observed_need(need: ExecutableNeed, observed: RuntimeDemand) -> RuntimeDemand {
    let mut delivered = runtime_demand_for_executable_need(need);
    if let (ShapeDemand::TupleFields(delivered_fields), ShapeDemand::TupleFields(observed_fields)) =
        (&mut delivered.shape, observed.shape)
    {
        for (delivered_field, observed_field) in delivered_fields.iter_mut().zip(observed_fields) {
            delivered_field.join_assign(&observed_field);
        }
    }
    delivered.callable.join_assign(&observed.callable);
    delivered
}

fn plan_callable_flows(
    types: &Types,
    input: &RuntimeDemandFormulaInput,
    callable_flows: &CallableFlowBuilder,
    demand: &ExecutableRuntimeDemand,
) -> Vec<CallableFlowPlan> {
    let executable = input.member;
    let facts = &input.facts;
    let mut plans = Vec::new();
    for (&value, producer) in facts.callable_origins() {
        let Some(value_demand) = demand.value_demands.get(&value) else {
            continue;
        };
        if !value_demand.is_callable() {
            continue;
        }
        let direct_surfaces = callable_flows.direct_surfaces(value);
        let direct_targets = callable_flows.direct_targets(value);
        let producer_surfaces = callable_value_type_demand(facts, value)
            .map(|demand| demand.callable.resolved)
            .unwrap_or_default();
        let direct_edges = callable_flow_edges_for_targets(types, executable, facts, producer, &direct_targets);
        let mut ground_source = producer_surfaces;
        ground_source.extend(direct_surfaces.iter().cloned());
        let first_class_surfaces =
            ground_dispatch_surfaces(types, &callable_flows.first_class_surfaces(value), &ground_source);
        let mut ordered = first_class_surfaces.iter().cloned().collect::<Vec<_>>();
        ordered.sort_by(|a, b| types.cmp_tys(&a.inputs, &b.inputs));
        plans.push(CallableFlowPlan {
            value,
            producer: producer.clone(),
            direct_surfaces,
            direct_edges,
            first_class_surfaces,
            resolution_keys: ordered
                .into_iter()
                .map(|surface| CallableResolutionKey {
                    executable: (*executable).clone(),
                    value,
                    surface,
                })
                .collect(),
            opaque: value_demand.callable.opaque,
            escape: value_demand.callable.escape,
        });
    }
    plans
}

fn callable_flow_edges_for_targets(
    types: &Types,
    executable: &ExecutableKey,
    facts: &RuntimeDemandFacts<'_>,
    producer: &LocalCallableProducer,
    targets: &BTreeSet<CallableTarget>,
) -> Vec<CallableFlowEdge> {
    if targets.is_empty() {
        return Vec::new();
    }
    let Some(capture_tys) = producer
        .captures
        .iter()
        .map(|capture| facts.value_types.get(capture).copied())
        .collect::<Option<Vec<_>>>()
    else {
        return Vec::new();
    };
    let captures_len = capture_tys.len();
    let mut edges = targets
        .iter()
        .filter(|target| {
            target.activation.root == executable.activation.root && target.activation.function == producer.function
        })
        .filter(|target| {
            target.activation_inputs.len() == captures_len + target.surface.inputs.len()
                && target
                    .activation_inputs
                    .iter()
                    .zip(&capture_tys)
                    .all(|(target, capture)| types.is_equivalent(target, capture))
        })
        .map(|target| CallableFlowEdge {
            surface: target.surface.clone(),
            resolution: ExecutableKey {
                activation: target.activation.clone(),
                need: target.need,
            },
            capture_semantic_inputs: (0..captures_len).collect(),
            surface_semantic_inputs: (captures_len..captures_len + target.surface.inputs.len()).collect(),
            boundary_input_demands: Box::new([]),
        })
        .collect::<Vec<_>>();
    // `targets` is a `BTreeSet<CallableTarget>` ordered by interned-`Ty` id, so
    // walking it leaks the interner's mint order (the agenda's) into this
    // executable's stored `direct_edges` and every artifact rendered from them.
    // Order by what each surface SAYS, the same `cmp_tys` key the first-class
    // edges use, so the direct half is canonical for the same reason and by the
    // same authority (fz-kdt.108).
    edges.sort_by(|a, b| types.cmp_tys(&a.surface.inputs, &b.surface.inputs));
    edges
}

fn informative_boundary_demand_from_types(
    world: &World,
    demand_types: &RuntimeDemandTypeInputs,
    ty: Ty,
) -> Option<RuntimeDemand> {
    if world.types().is_empty(&ty) {
        return None;
    }
    let any = demand_types.any;
    if ty == any {
        return None;
    }
    let demand = demand_types.boundary_demand(ty);
    if !matches!(demand.shape, ShapeDemand::Whole) || !demand.callable.is_empty() {
        return Some(demand);
    }
    (world.types().is_integer(&ty)
        || world.types().is_floating(&ty)
        || world.types().is_nil(&ty)
        || world.types().is_atom_type(&ty))
    .then_some(demand)
}

fn callable_boundary_input_demand_contributions_product(
    demand: &ExecutableRuntimeDemand,
) -> Vec<(ExecutableKey, usize, RuntimeDemand)> {
    let mut required = Vec::new();
    for flow in demand.callable_flows.values() {
        for edge in flow.direct_edges.iter().chain(&flow.first_class_edges) {
            for (&semantic_index, capture) in edge.capture_semantic_inputs.iter().zip(flow.captures.iter()) {
                let Some(capture_demand) = demand.value_demands.get(capture) else {
                    continue;
                };
                required.push((edge.resolution.clone(), semantic_index, capture_demand.clone()));
            }
        }
        if flow.first_class_surfaces.is_empty() {
            continue;
        }
        for edge in &flow.first_class_edges {
            for (offset, arg_demand) in edge.boundary_input_demands.iter().enumerate() {
                let Some(arg_demand) = arg_demand else {
                    continue;
                };
                required.push((
                    edge.resolution.clone(),
                    edge.capture_semantic_inputs.len() + offset,
                    arg_demand.clone(),
                ));
            }
        }
    }
    required
}

fn local_call_targets(summary: &CallSiteSummary, need: ExecutableNeed) -> Vec<ExecutableKey> {
    summary
        .targets
        .iter()
        .filter_map(|target| target.runtime_executable(need))
        .collect()
}

/// Join a carried-forward `input_demands` iterate (round-to-round evidence,
/// including boundary-pinned positions a contributor joined onto this
/// executable) onto a freshly rebuilt `input_demands`. Positions the fresh
/// walk did not touch keep the carried demand; this is the input-side
/// counterpart of seeding `return_demand` from the previous round's value.
fn join_previous_input_demands(input_demands: &mut [RuntimeDemand], previous: Option<&[RuntimeDemand]>) {
    let Some(previous) = previous else { return };
    for (slot, prev) in input_demands.iter_mut().zip(previous) {
        slot.join_assign(prev);
    }
}

fn derive_executable_runtime_demand(types: &Types, input: &RuntimeDemandFormulaInput) -> DerivedExecutableDemand {
    let executable = &input.member;
    let facts = &input.facts;
    let demands = &input.current;
    let mut callable_flows = CallableFlowBuilder::new();
    // The previous round's iterate for THIS executable, if any: it carries
    // boundary-pinned input-demand contributions other members joined onto
    // this executable's `input_demands` (mirrors how `return_demand` below
    // seeds from the same round-carried value). Unlike `return_demand`, the
    // body walk below fully rebuilds `input_demands` from scratch, so the
    // carried positions are joined back in at every return point instead of
    // seeded up front.
    let previous_input_demands = Some(demands.own.input_demands.clone());
    let mut out = ExecutableRuntimeDemand {
        callable_activation_inputs: facts.callable_activation_inputs.to_vec(),
        return_demand: demands.own.return_demand.clone(),
        input_demands: vec![RuntimeDemand::ignore(); executable.activation.input_len(types)],
        ..ExecutableRuntimeDemand::default()
    };
    let mut call_return_demands = HashMap::new();

    let LoweredBody::Clauses { clauses, entries, .. } = &facts.body else {
        out.input_demands = match &facts.body {
            LoweredBody::Extern { signature } => executable
                .activation
                .inputs(types)
                .iter()
                .enumerate()
                .map(|(index, ty)| {
                    signature
                        .params
                        .get(index)
                        .map(|_| RuntimeDemand::whole())
                        .unwrap_or_else(|| facts.demand_types.boundary_demand(*ty))
                })
                .collect(),
            LoweredBody::Clauses { .. } => unreachable!(),
        };
        join_previous_input_demands(&mut out.input_demands, previous_input_demands.as_deref());
        return DerivedExecutableDemand {
            demand: out,
            call_return_demands,
            callable_flows: CallableFlowBuilder::new(),
        };
    };

    // Live-demand propagation is the authoritative "what must be
    // materialized" pass that native codegen relies on (`env_runtime_var`).
    // Codegen lowers every structural clause regardless of
    // the settled entry reachability, so a clause the type-level reachability
    // analysis under-approximates as dead (e.g. a recursive base case whose
    // list slot is over-narrowed) can still reach native lowering and crash
    // when its return value was never marked live. Widen the walked clause
    // set by the trivial delta `trivial_value_clause_ids` identifies.
    let mut walked_clauses = facts.reachable_clauses.to_vec();
    walked_clauses.extend(trivial_value_clause_ids(facts.body, facts.reachable_clauses));
    for clause_id in walked_clauses {
        let clause = &clauses[clause_id as usize];
        let mut live = collect_entry_live_demands(
            types,
            executable,
            entries.as_slice(),
            clause.entry,
            out.return_demand.clone(),
            facts,
            demands,
            &mut out,
            &mut call_return_demands,
            &mut callable_flows,
        );
        propagate_steps_reverse(
            executable,
            clause.projections.as_slice(),
            &mut live,
            facts,
            demands,
            &mut out,
            &mut callable_flows,
        );
        note_clause_matcher_demands(facts, clause.projections.as_slice(), &mut live, &mut out);
        for (index, param) in clause.params.iter().enumerate() {
            if let Some(demand) = live.remove(param) {
                out.input_demands[index].join_assign(&demand);
            }
        }
    }

    let activation_inputs = executable.activation.inputs(types);
    for &semantic_index in facts.entry_dispatch_inputs {
        let Some(&ty) = activation_inputs.get(semantic_index) else {
            continue;
        };
        let demand = facts.demand_types.dispatch_demand(ty);
        out.input_demands[semantic_index].join_assign(&demand);
    }

    join_previous_input_demands(&mut out.input_demands, previous_input_demands.as_deref());
    widen_boxed_closure_call_results(facts, &mut out, &mut call_return_demands);

    DerivedExecutableDemand {
        demand: out,
        call_return_demands,
        callable_flows,
    }
}

/// The consumer half of the boxed apply seam's one return convention
/// (fz-kdt.155). Its producer half is the seam clause of the whole-by-need
/// bootstrap in [`settle_demand_cone`], which keeps a wrapper's members from
/// settling at zero lanes; here every callsite that reaches a wrapper is made
/// to expect the lane the wrapper hands back.
///
/// The question "does this call go through the seam?" is a property of the
/// CALLEE VALUE, not of the callsite: `materialize_closure_call_edge` lowers a
/// direct edge to a named target only while the callee travels in its exact
/// carrier, and that carrier is `ValueRef` the moment the value's own joined
/// demand is first-class -- which a use somewhere else in this body can decide
/// on its own. A callsite that names an exact target is still a boxed call if
/// the lambda it calls is also handed out of the function two lines later. So
/// this runs once the whole body is walked and asks the joined value demand,
/// the same authority transport asks.
///
/// A callsite past the seam names none of the members behind the wrapper -- a
/// mailbox callable names none at all -- so its `ignore` never reaches them and
/// the value arrives whatever the caller wanted. Publishing zero lanes for it
/// left the two halves of one calling convention on different lane counts: the
/// wrapper wrote the delivered value into the continuation's first slot, which
/// the continuation reads as its own closure pointer, and the run aborted in
/// `fz_closure_get_capture_atom`. Every RICHER demand already crosses the seam
/// as that one boxed lane, so only the zero widens.
///
/// A callee that stays in its exact carrier is untouched: its result aliases
/// the named target executable's own return fact
/// (`TransportRecipe::ClosureCallReturn`'s grounded arm), so caller and callee
/// read one shape whatever it settles to -- zero when no seam boxes the
/// callable (fz-f98.14.11), non-empty when a seam does and the bootstrap kept
/// the member off the bottom.
fn widen_boxed_closure_call_results(
    facts: &RuntimeDemandFacts<'_>,
    out: &mut ExecutableRuntimeDemand,
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
) {
    let LoweredBody::Clauses { entries, .. } = &facts.body else {
        return;
    };
    for entry in entries {
        let LoweredTail::ClosureCall {
            value,
            callsite,
            callee,
            ..
        } = &entry.tail
        else {
            continue;
        };
        if !out
            .value_demands
            .get(callee)
            .is_some_and(|demand| demand.callable.is_first_class())
        {
            continue;
        }
        // Only the ZERO widens, and it widens on BOTH halves together: the
        // delivered value's own demand (which the payload layout is derived
        // from) and the callsite's contribution to whatever targets it does
        // name. A richer demand already crosses the seam as at least one lane,
        // and coarsening it here would cost a member its destination-passing
        // return for nothing.
        if !out.value_demands.get(value).is_none_or(RuntimeDemand::is_ignore) {
            continue;
        }
        join_map_demand(&mut out.value_demands, *value, RuntimeDemand::whole());
        record_call_return_demand(call_return_demands, *callsite, RuntimeDemand::whole());
    }
}

fn collect_entry_external_demands(
    types: &Types,
    executable: &ExecutableKey,
    entries: &[LoweredEntry],
    entry_id: ControlEntryId,
    outgoing_demand: RuntimeDemand,
    facts: &RuntimeDemandFacts<'_>,
    demands: &RuntimeDemandFormulaSnapshot,
    out: &mut ExecutableRuntimeDemand,
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
    callable_flows: &mut CallableFlowBuilder,
) -> HashMap<ValueId, RuntimeDemand> {
    let entry = &entries[entry_id.as_u32() as usize];
    let mut live = collect_entry_live_demands(
        types,
        executable,
        entries,
        entry_id,
        outgoing_demand,
        facts,
        demands,
        out,
        call_return_demands,
        callable_flows,
    );
    let mut external = HashMap::new();
    if let Some(value) = entry.origin.input_value()
        && let Some(demand) = live.remove(&value)
    {
        let demand = upgrade_joined_delivered_callable_value_demand(facts, callable_flows, entry_id, value, demand);
        record_delivered_call_return_demands(facts, call_return_demands, entry_id, value, &demand);
        join_map_demand(&mut out.value_demands, value, demand.clone());
        external.insert(value, demand);
    }
    let capture_demands = entry
        .captures
        .iter()
        .map(|capture| {
            let demand = live.remove(capture).unwrap_or(RuntimeDemand::ignore());
            continuation_capture_demand(facts, callable_flows, *capture, demand)
        })
        .collect::<Vec<_>>();
    record_entry_capture_demands(out, entry_id, &capture_demands);
    for (capture, demand) in entry.captures.iter().zip(capture_demands) {
        if !demand.is_ignore() {
            join_map_demand(&mut external, *capture, demand);
        }
    }
    for param in &entry.params {
        live.remove(param);
    }
    merge_live_demands(&mut external, live);
    external
}

fn collect_entry_live_demands(
    types: &Types,
    executable: &ExecutableKey,
    entries: &[LoweredEntry],
    entry_id: ControlEntryId,
    outgoing_demand: RuntimeDemand,
    facts: &RuntimeDemandFacts<'_>,
    demands: &RuntimeDemandFormulaSnapshot,
    out: &mut ExecutableRuntimeDemand,
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
    callable_flows: &mut CallableFlowBuilder,
) -> HashMap<ValueId, RuntimeDemand> {
    let entry = &entries[entry_id.as_u32() as usize];
    let mut live = HashMap::new();
    let mut tail_call_return = None;
    match &entry.tail {
        LoweredTail::Value { value, dest } => {
            let (boundary_demand, external_demands) = destination_demands(
                types,
                executable,
                entries,
                dest,
                outgoing_demand,
                facts,
                demands,
                out,
                call_return_demands,
                callable_flows,
            );
            let demand = boundary_value_flow_demand(facts, callable_flows, *value, boundary_demand);
            note_live_demand(out, &mut live, *value, demand);
            merge_live_demands(&mut live, external_demands);
        }
        LoweredTail::DirectCall {
            value,
            callsite,
            args,
            dest,
            ..
        } => {
            let (boundary_demand, external_demands) = destination_demands(
                types,
                executable,
                entries,
                dest,
                outgoing_demand,
                facts,
                demands,
                out,
                call_return_demands,
                callable_flows,
            );
            let demand = boundary_value_flow_demand(facts, callable_flows, *value, boundary_demand);
            note_live_demand(out, &mut live, *value, demand.clone());
            record_call_return_demand(call_return_demands, *callsite, demand);
            tail_call_return = Some((*callsite, *value));
            merge_live_demands(&mut live, external_demands);
            let arg_demands = direct_call_arg_demands(
                types,
                executable,
                *callsite,
                args.as_slice(),
                facts,
                demands,
                callable_flows,
            );
            record_call_arg_demands(out, *callsite, arg_demands.as_slice());
            for (arg, demand) in args.iter().zip(arg_demands) {
                note_live_demand(out, &mut live, arg.value, demand);
            }
        }
        LoweredTail::ClosureCall {
            value,
            callsite,
            callee,
            args,
            dest,
            ..
        } => {
            let (boundary_demand, external_demands) = destination_demands(
                types,
                executable,
                entries,
                dest,
                outgoing_demand,
                facts,
                demands,
                out,
                call_return_demands,
                callable_flows,
            );
            let demand = boundary_value_flow_demand(facts, callable_flows, *value, boundary_demand);
            note_live_demand(out, &mut live, *value, demand.clone());
            record_call_return_demand(call_return_demands, *callsite, demand);
            tail_call_return = Some((*callsite, *value));
            merge_live_demands(&mut live, external_demands);
            let callee_callable = closure_callee_demand(
                facts,
                args.as_slice(),
                facts.callsites.get(callsite),
                facts
                    .callsite_needs
                    .get(callsite)
                    .copied()
                    .unwrap_or(ExecutableNeed::Value),
            );
            let callee_demand = RuntimeDemand::callable(callee_callable);
            callable_flows.record_direct_demand(facts, *callee, &callee_demand);
            note_live_demand(out, &mut live, *callee, callee_demand);
            let arg_demands = closure_call_arg_demands(
                types,
                executable,
                *callsite,
                args.as_slice(),
                facts,
                demands,
                callable_flows,
            );
            record_call_arg_demands(out, *callsite, arg_demands.as_slice());
            for (arg, demand) in args.iter().zip(arg_demands) {
                note_live_demand(out, &mut live, arg.value, demand);
            }
        }
        LoweredTail::If {
            cond,
            then_entry,
            else_entry,
        } => {
            note_live_demand(out, &mut live, *cond, RuntimeDemand::whole());
            merge_live_demands(
                &mut live,
                collect_entry_external_demands(
                    types,
                    executable,
                    entries,
                    *then_entry,
                    outgoing_demand.clone(),
                    facts,
                    demands,
                    out,
                    call_return_demands,
                    callable_flows,
                ),
            );
            merge_live_demands(
                &mut live,
                collect_entry_external_demands(
                    types,
                    executable,
                    entries,
                    *else_entry,
                    outgoing_demand,
                    facts,
                    demands,
                    out,
                    call_return_demands,
                    callable_flows,
                ),
            );
        }
        LoweredTail::Dispatch {
            inputs,
            bindings,
            dispatch,
        } => {
            for input in inputs {
                note_live_demand(out, &mut live, *input, RuntimeDemand::whole());
            }
            for value in bindings.pinned.iter().chain(bindings.prepared.iter()) {
                note_live_demand(out, &mut live, *value, RuntimeDemand::whole());
            }
            for arm_entry in &dispatch.arm_entries {
                merge_live_demands(
                    &mut live,
                    collect_entry_external_demands(
                        types,
                        executable,
                        entries,
                        *arm_entry,
                        outgoing_demand.clone(),
                        facts,
                        demands,
                        out,
                        call_return_demands,
                        callable_flows,
                    ),
                );
            }
            merge_live_demands(
                &mut live,
                collect_entry_external_demands(
                    types,
                    executable,
                    entries,
                    dispatch.miss_entry,
                    outgoing_demand,
                    facts,
                    demands,
                    out,
                    call_return_demands,
                    callable_flows,
                ),
            );
        }
        LoweredTail::Receive(receive) => {
            for value in receive.bindings.pinned.iter().chain(receive.bindings.prepared.iter()) {
                note_live_demand(out, &mut live, *value, RuntimeDemand::whole());
            }
            for clause in &receive.clauses {
                merge_live_demands(
                    &mut live,
                    collect_entry_external_demands(
                        types,
                        executable,
                        entries,
                        clause.entry,
                        outgoing_demand.clone(),
                        facts,
                        demands,
                        out,
                        call_return_demands,
                        callable_flows,
                    ),
                );
            }
            if let Some(after) = &receive.after {
                note_live_demand(out, &mut live, after.timeout, RuntimeDemand::whole());
                merge_live_demands(
                    &mut live,
                    collect_entry_external_demands(
                        types,
                        executable,
                        entries,
                        after.entry,
                        outgoing_demand,
                        facts,
                        demands,
                        out,
                        call_return_demands,
                        callable_flows,
                    ),
                );
            }
        }
        LoweredTail::Halt { .. } => {}
    }

    propagate_steps_reverse(
        executable,
        entry.steps.as_slice(),
        &mut live,
        facts,
        demands,
        out,
        callable_flows,
    );
    if let Some((callsite, value)) = tail_call_return
        && let Some(demand) = out.value_demands.get(&value).cloned()
    {
        record_call_return_demand(call_return_demands, callsite, demand);
    }
    live
}

fn destination_demands(
    types: &Types,
    executable: &ExecutableKey,
    entries: &[LoweredEntry],
    dest: &ControlDestination,
    outgoing_demand: RuntimeDemand,
    facts: &RuntimeDemandFacts<'_>,
    demands: &RuntimeDemandFormulaSnapshot,
    out: &mut ExecutableRuntimeDemand,
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
    callable_flows: &mut CallableFlowBuilder,
) -> (RuntimeDemand, HashMap<ValueId, RuntimeDemand>) {
    match dest {
        ControlDestination::Return => (outgoing_demand, HashMap::new()),
        ControlDestination::Deliver(entry_id) => {
            let delivered = entries[entry_id.as_u32() as usize]
                .origin
                .input_value()
                .expect("delivered control edges should target a resume entry");
            let mut external_demands = collect_entry_external_demands(
                types,
                executable,
                entries,
                *entry_id,
                outgoing_demand,
                facts,
                demands,
                out,
                call_return_demands,
                callable_flows,
            );
            let delivered_demand = external_demands.remove(&delivered).unwrap_or(RuntimeDemand::ignore());
            (delivered_demand, external_demands)
        }
    }
}

fn upgrade_joined_delivered_callable_value_demand(
    facts: &RuntimeDemandFacts<'_>,
    callable_flows: &mut CallableFlowBuilder,
    entry: ControlEntryId,
    value: ValueId,
    mut demand: RuntimeDemand,
) -> RuntimeDemand {
    if demand.is_callable() && delivered_join_has_distinct_callable_producers(facts, entry, value) {
        callable_flows.record_direct_demand(facts, value, &demand);
        demand.callable.escape = true;
    }
    demand
}

fn continuation_capture_demand(
    facts: &RuntimeDemandFacts<'_>,
    callable_flows: &mut CallableFlowBuilder,
    capture: ValueId,
    mut demand: RuntimeDemand,
) -> RuntimeDemand {
    if demand.is_callable()
        && facts.callable_origin(capture).is_none()
        && value_is_callable(facts, capture)
        && value_depends_on_callsite_return(facts, capture)
        && value_is_closure_callee(facts.body, capture)
    {
        demand.callable.escape = true;
    }
    record_first_class_boundary_demand(facts, callable_flows, capture, demand, None)
}

fn value_is_closure_callee(body: &LoweredBody, value: ValueId) -> bool {
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return false;
    };
    clauses
        .iter()
        .any(|clause| tail_closure_callee(&clause.entry, entries, value))
        || entries
            .iter()
            .any(|entry| matches!(&entry.tail, LoweredTail::ClosureCall { callee, .. } if *callee == value))
}

fn tail_closure_callee(entry_id: &ControlEntryId, entries: &[LoweredEntry], value: ValueId) -> bool {
    entries
        .get(entry_id.as_u32() as usize)
        .is_some_and(|entry| matches!(&entry.tail, LoweredTail::ClosureCall { callee, .. } if *callee == value))
}

fn value_depends_on_callsite_return(facts: &RuntimeDemandFacts<'_>, value: ValueId) -> bool {
    let mut seen = HashSet::new();
    value_depends_on_callsite_return_inner(facts, value, &mut seen)
}

fn value_depends_on_callsite_return_inner(
    facts: &RuntimeDemandFacts<'_>,
    value: ValueId,
    seen: &mut HashSet<ValueId>,
) -> bool {
    if !seen.insert(value) {
        return false;
    }
    for join in facts.delivered_value_joins.values().filter(|join| join.value == value) {
        for source in &join.sources {
            match source {
                DeliveredValueSource::CallsiteReturn(_) => return true,
                DeliveredValueSource::LocalValue(source) => {
                    if value_depends_on_callsite_return_inner(facts, *source, seen) {
                        return true;
                    }
                }
            }
        }
    }
    let LoweredBody::Clauses { entries, .. } = &facts.body else {
        return false;
    };
    entries
        .iter()
        .flat_map(|entry| entry.steps.iter())
        .any(|step| step_value_depends_on_callsite_return(facts, step, value, seen))
}

fn step_value_depends_on_callsite_return(
    facts: &RuntimeDemandFacts<'_>,
    step: &LoweredStep,
    value: ValueId,
    seen: &mut HashSet<ValueId>,
) -> bool {
    let mut depends = |source| value_depends_on_callsite_return_inner(facts, source, seen);
    match step {
        LoweredStep::Tuple { value: defined, items } if *defined == value => items.iter().copied().any(depends),
        LoweredStep::List {
            value: defined,
            items,
            tail,
        } if *defined == value => items.iter().copied().any(&mut depends) || tail.is_some_and(depends),
        LoweredStep::Map {
            value: defined,
            entries,
        } if *defined == value => entries.iter().any(|(key, field)| depends(key.value) || depends(*field)),
        LoweredStep::MapUpdate {
            value: defined,
            base,
            entries,
        } if *defined == value => {
            depends(*base) || entries.iter().any(|(key, field)| depends(key.value) || depends(*field))
        }
        LoweredStep::Struct {
            value: defined, fields, ..
        } if *defined == value => fields.iter().any(|(_, field)| depends(*field)),
        LoweredStep::Bitstring { value: defined, fields } if *defined == value => fields.iter().any(|field| {
            depends(field.value)
                || matches!(
                    field.spec.size,
                    Some(super::super::body::LoweredBitSize::Value(size)) if depends(size)
                )
        }),
        LoweredStep::BinaryOp {
            value: defined,
            left,
            right,
            ..
        } if *defined == value => depends(*left) || depends(*right),
        LoweredStep::UnaryOp {
            value: defined, input, ..
        } if *defined == value => depends(*input),
        LoweredStep::MapIndex {
            value: defined,
            base,
            key,
        } if *defined == value => depends(*base) || depends(key.value),
        LoweredStep::FieldAccess {
            value: defined, base, ..
        } if *defined == value => depends(*base),
        LoweredStep::RequireMapValue {
            value: defined, source, ..
        } if *defined == value => depends(*source),
        LoweredStep::TupleField {
            value: defined, source, ..
        } if *defined == value => depends(*source),
        LoweredStep::SplitList { source, head, tail } if *head == value || *tail == value => depends(*source),
        LoweredStep::BitstringInit { reader, source } if *reader == value => depends(*source),
        LoweredStep::BitstringRead {
            ok,
            value: read_value,
            next_reader,
            reader,
            spec,
            ..
        } if *ok == value || *read_value == value || *next_reader == value => {
            depends(*reader)
                || matches!(
                    spec.size,
                    Some(super::super::body::LoweredBitSize::Value(size)) if depends(size)
                )
        }
        LoweredStep::Const { .. }
        | LoweredStep::FunctionRef { .. }
        | LoweredStep::Lambda { .. }
        | LoweredStep::AssertLiteral { .. }
        | LoweredStep::AssertStruct { .. }
        | LoweredStep::AssertTuple { .. }
        | LoweredStep::AssertEmptyList { .. }
        | LoweredStep::AssertSame { .. }
        | LoweredStep::AssertBitstringDone { .. }
        | LoweredStep::Tuple { .. }
        | LoweredStep::List { .. }
        | LoweredStep::Map { .. }
        | LoweredStep::MapUpdate { .. }
        | LoweredStep::Struct { .. }
        | LoweredStep::Bitstring { .. }
        | LoweredStep::BinaryOp { .. }
        | LoweredStep::UnaryOp { .. }
        | LoweredStep::MapIndex { .. }
        | LoweredStep::FieldAccess { .. }
        | LoweredStep::RequireMapValue { .. }
        | LoweredStep::TupleField { .. }
        | LoweredStep::SplitList { .. }
        | LoweredStep::BitstringInit { .. }
        | LoweredStep::BitstringRead { .. } => false,
    }
}

fn record_delivered_call_return_demands(
    facts: &RuntimeDemandFacts<'_>,
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
    entry: ControlEntryId,
    value: ValueId,
    demand: &RuntimeDemand,
) {
    let Some(join) = facts.delivered_value_joins.get(&entry) else {
        return;
    };
    if join.value != value {
        return;
    }
    for source in &join.sources {
        let DeliveredValueSource::CallsiteReturn(callsite) = source else {
            continue;
        };
        record_call_return_demand(call_return_demands, *callsite, demand.clone());
    }
}

fn delivered_join_has_distinct_callable_producers(
    facts: &RuntimeDemandFacts<'_>,
    entry: ControlEntryId,
    delivered: ValueId,
) -> bool {
    let Some(join) = facts.delivered_value_joins.get(&entry) else {
        return false;
    };
    if join.value != delivered {
        return false;
    }
    let producers = join
        .sources
        .iter()
        .filter_map(|join_source| match join_source {
            DeliveredValueSource::LocalValue(value) => facts.callable_origin(*value),
            DeliveredValueSource::CallsiteReturn(_) => None,
        })
        .collect::<HashSet<_>>();
    producers.len() > 1
}

fn propagate_steps_reverse(
    executable: &ExecutableKey,
    steps: &[LoweredStep],
    live: &mut HashMap<ValueId, RuntimeDemand>,
    facts: &RuntimeDemandFacts<'_>,
    demands: &RuntimeDemandFormulaSnapshot,
    out: &mut ExecutableRuntimeDemand,
    callable_flows: &mut CallableFlowBuilder,
) {
    let asserted_tuple_arities = step_asserted_tuple_arities(steps);
    for step in steps.iter().rev() {
        match step {
            LoweredStep::Const { .. } => {}
            LoweredStep::FunctionRef { value, .. } => {
                if let Some(demand) = live.get(value) {
                    callable_flows.record_direct_demand(facts, *value, demand);
                }
            }
            LoweredStep::Tuple { value, items } => {
                let demand = take_live_demand(live, *value);
                if !demand.is_callable() {
                    match demand.shape {
                        ShapeDemand::Ignore => {}
                        ShapeDemand::TupleFields(fields) if fields.len() == items.len() => {
                            for (item, demand) in items.iter().zip(fields) {
                                let demand = boundary_value_flow_demand(facts, callable_flows, *item, demand);
                                note_live_demand(out, live, *item, demand);
                            }
                        }
                        _ => {
                            for item in items {
                                let demand =
                                    boundary_value_flow_demand(facts, callable_flows, *item, RuntimeDemand::whole());
                                note_live_demand(out, live, *item, demand);
                            }
                        }
                    }
                } else {
                    for item in items {
                        let demand = boundary_value_flow_demand(facts, callable_flows, *item, RuntimeDemand::whole());
                        note_live_demand(out, live, *item, demand);
                    }
                }
            }
            LoweredStep::List { value, items, tail } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for item in items {
                        let demand = boundary_value_flow_demand(facts, callable_flows, *item, RuntimeDemand::whole());
                        note_live_demand(out, live, *item, demand);
                    }
                    if let Some(tail) = tail {
                        let demand = boundary_value_flow_demand(facts, callable_flows, *tail, RuntimeDemand::whole());
                        note_live_demand(out, live, *tail, demand);
                    }
                }
            }
            LoweredStep::Map { value, entries } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for (key, field) in entries {
                        let key_demand =
                            boundary_value_flow_demand(facts, callable_flows, key.value, RuntimeDemand::whole());
                        let field_demand =
                            boundary_value_flow_demand(facts, callable_flows, *field, RuntimeDemand::whole());
                        note_live_demand(out, live, key.value, key_demand);
                        note_live_demand(out, live, *field, field_demand);
                    }
                }
            }
            LoweredStep::MapUpdate { value, base, entries } => {
                if !take_live_demand(live, *value).is_ignore() {
                    let base_demand = boundary_value_flow_demand(facts, callable_flows, *base, RuntimeDemand::whole());
                    note_live_demand(out, live, *base, base_demand);
                    for (key, field) in entries {
                        let key_demand =
                            boundary_value_flow_demand(facts, callable_flows, key.value, RuntimeDemand::whole());
                        let field_demand =
                            boundary_value_flow_demand(facts, callable_flows, *field, RuntimeDemand::whole());
                        note_live_demand(out, live, key.value, key_demand);
                        note_live_demand(out, live, *field, field_demand);
                    }
                }
            }
            LoweredStep::Struct { value, fields, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for (_, field) in fields {
                        let demand = boundary_value_flow_demand(facts, callable_flows, *field, RuntimeDemand::whole());
                        note_live_demand(out, live, *field, demand);
                    }
                }
            }
            LoweredStep::Bitstring { value, fields } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for field in fields {
                        note_live_demand(out, live, field.value, RuntimeDemand::whole());
                        if let Some(super::super::body::LoweredBitSize::Value(size)) = &field.spec.size {
                            note_live_demand(out, live, *size, RuntimeDemand::whole());
                        }
                    }
                }
            }
            LoweredStep::Lambda {
                value,
                function,
                captures,
            } => {
                let demand = take_live_demand(live, *value);
                callable_flows.record_direct_demand(facts, *value, &demand);
                if !demand.is_ignore() {
                    propagate_lambda_capture_demands(
                        executable,
                        *function,
                        captures.as_slice(),
                        demand,
                        facts,
                        demands,
                        live,
                        out,
                        callable_flows,
                    );
                }
            }
            LoweredStep::BinaryOp { value, left, right, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(out, live, *left, RuntimeDemand::whole());
                    note_live_demand(out, live, *right, RuntimeDemand::whole());
                }
            }
            LoweredStep::UnaryOp { value, input, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(out, live, *input, RuntimeDemand::whole());
                }
            }
            LoweredStep::MapIndex { value, base, key } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(out, live, *base, RuntimeDemand::whole());
                    note_live_demand(out, live, key.value, RuntimeDemand::whole());
                }
            }
            LoweredStep::FieldAccess { value, base, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(out, live, *base, RuntimeDemand::whole());
                }
            }
            LoweredStep::AssertLiteral { source, .. } => {
                note_live_demand(out, live, *source, RuntimeDemand::whole());
            }
            LoweredStep::AssertStruct { source, .. } => {
                note_live_demand(out, live, *source, RuntimeDemand::whole());
            }
            LoweredStep::RequireMapValue { value, source, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(out, live, *source, RuntimeDemand::whole());
                }
            }
            LoweredStep::AssertTuple { source, arity } => {
                if !live.contains_key(source) || asserted_tuple_arities.get(source).copied() != Some(*arity) {
                    note_live_demand(out, live, *source, RuntimeDemand::whole());
                }
            }
            LoweredStep::TupleField { value, source, index } => {
                let demand = take_live_demand(live, *value);
                if !demand.is_ignore() {
                    let arity = asserted_tuple_arities.get(source).copied().unwrap_or(index + 1);
                    let mut fields = vec![RuntimeDemand::ignore(); arity];
                    fields[*index] = demand;
                    note_live_demand(out, live, *source, RuntimeDemand::tuple_fields(fields));
                }
            }
            LoweredStep::AssertEmptyList { source } => {
                note_live_demand(out, live, *source, RuntimeDemand::whole());
            }
            LoweredStep::AssertSame { source, value } => {
                note_live_demand(out, live, *source, RuntimeDemand::whole());
                note_live_demand(out, live, *value, RuntimeDemand::whole());
            }
            LoweredStep::SplitList { source, head, tail } => {
                let head_demand = take_live_demand(live, *head);
                let tail_demand = take_live_demand(live, *tail);
                if !head_demand.is_ignore() || !tail_demand.is_ignore() {
                    note_live_demand(out, live, *source, RuntimeDemand::whole());
                }
            }
            LoweredStep::BitstringInit { reader, source } => {
                if !take_live_demand(live, *reader).is_ignore() {
                    note_live_demand(out, live, *source, RuntimeDemand::whole());
                }
            }
            LoweredStep::BitstringRead {
                ok,
                value,
                next_reader,
                reader,
                spec,
                ..
            } => {
                let ok_demand = take_live_demand(live, *ok);
                let value_demand = take_live_demand(live, *value);
                let next_reader_demand = take_live_demand(live, *next_reader);
                if !ok_demand.is_ignore() || !value_demand.is_ignore() || !next_reader_demand.is_ignore() {
                    note_live_demand(out, live, *reader, RuntimeDemand::whole());
                    if let Some(super::super::body::LoweredBitSize::Value(size)) = &spec.size {
                        note_live_demand(out, live, *size, RuntimeDemand::whole());
                    }
                }
            }
            LoweredStep::AssertBitstringDone { reader } => {
                note_live_demand(out, live, *reader, RuntimeDemand::whole());
            }
        }
    }
    // `jobs/backend.rs::lower_step` packages a `TupleField` step into a real
    // `BackendStep::TupleField` unconditionally — unlike the fresh-construction
    // steps (`construction_step_or_omitted`), it
    // has no `Omitted` fallback for a provably-unread projection. Native
    // codegen therefore always reads `source` to extract the field, even
    // when every field ever projected from it goes unused downstream (e.g.
    // a guard-passed match arm that destructures `{:ok, s}` but returns a
    // literal without touching `s`). The per-step handling above already
    // keeps `source` live whenever ANY projected field carries real demand
    // (the ordinary, common case — no change needed there), but when EVERY
    // field projected from a given `source` is ignored, `source` never
    // enters `live` at all and its transport lane starves — the fz-xvq
    // "materialize absent value" crash. This closing sweep is the exact,
    // minimal net for only that starved case: for any `source` this steps
    // slice projects a `TupleField` from that isn't already live by any
    // other means, float it to a per-field `Whole` (`tuple_fields`, not a
    // bare `whole()`) so the transport layer keeps the same field-split
    // freedom an already-demanded source has — a bare `whole()` would
    // instead assert the *opaque box* is needed, forcing a single boxed
    // lane and coarsening an otherwise-splittable tuple (e.g. a `{:cont,
    // acc}` HOF continuation whose split raw lanes another clause of the
    // same shared body legitimately demands). Sources that already carry
    // demand from a live field are untouched, so this cannot regress the
    // split-lane shape of an already-working case.
    let mut floored = HashSet::new();
    for step in steps {
        if let LoweredStep::TupleField { source, .. } = step
            && !live.contains_key(source)
            && floored.insert(*source)
        {
            let arity = asserted_tuple_arities.get(source).copied().unwrap_or_else(|| {
                steps
                    .iter()
                    .filter_map(|step| match step {
                        LoweredStep::TupleField {
                            source: candidate,
                            index,
                            ..
                        } if candidate == source => Some(*index + 1),
                        _ => None,
                    })
                    .max()
                    .unwrap_or(1)
            });
            note_live_demand(
                out,
                live,
                *source,
                RuntimeDemand::tuple_fields(vec![RuntimeDemand::whole(); arity]),
            );
        }
    }
}

fn step_asserted_tuple_arities(steps: &[LoweredStep]) -> HashMap<ValueId, usize> {
    let mut arities = HashMap::new();
    for step in steps {
        if let LoweredStep::AssertTuple { source, arity } = step {
            arities.insert(*source, *arity);
        }
    }
    arities
}

fn note_clause_matcher_demands(
    facts: &RuntimeDemandFacts<'_>,
    steps: &[LoweredStep],
    live: &mut HashMap<ValueId, RuntimeDemand>,
    out: &mut ExecutableRuntimeDemand,
) {
    for step in steps {
        match step {
            LoweredStep::AssertLiteral { source, .. }
            | LoweredStep::AssertStruct { source, .. }
            | LoweredStep::AssertTuple { source, .. }
            | LoweredStep::AssertEmptyList { source }
            | LoweredStep::BitstringInit { source, .. } => {
                let demand = boundary_value_demand(facts, *source, RuntimeDemand::whole());
                note_live_demand(out, live, *source, demand);
            }
            LoweredStep::RequireMapValue { source, .. } => {
                let source_demand = boundary_value_demand(facts, *source, RuntimeDemand::whole());
                note_live_demand(out, live, *source, source_demand);
            }
            LoweredStep::AssertSame { source, value } => {
                let source_demand = boundary_value_demand(facts, *source, RuntimeDemand::whole());
                note_live_demand(out, live, *source, source_demand);
                let value_demand = boundary_value_demand(facts, *value, RuntimeDemand::whole());
                note_live_demand(out, live, *value, value_demand);
            }
            LoweredStep::SplitList { source, .. } => {
                let demand = boundary_value_demand(facts, *source, RuntimeDemand::whole());
                note_live_demand(out, live, *source, demand);
            }
            LoweredStep::BitstringRead { reader, spec, .. } => {
                let demand = boundary_value_demand(facts, *reader, RuntimeDemand::whole());
                note_live_demand(out, live, *reader, demand);
                if let Some(super::super::body::LoweredBitSize::Value(size)) = &spec.size {
                    note_live_demand(out, live, *size, RuntimeDemand::whole());
                }
            }
            LoweredStep::AssertBitstringDone { reader } => {
                let demand = boundary_value_demand(facts, *reader, RuntimeDemand::whole());
                note_live_demand(out, live, *reader, demand);
            }
            LoweredStep::Const { .. }
            | LoweredStep::Tuple { .. }
            | LoweredStep::List { .. }
            | LoweredStep::Map { .. }
            | LoweredStep::MapUpdate { .. }
            | LoweredStep::Struct { .. }
            | LoweredStep::Bitstring { .. }
            | LoweredStep::FunctionRef { .. }
            | LoweredStep::Lambda { .. }
            | LoweredStep::BinaryOp { .. }
            | LoweredStep::UnaryOp { .. }
            | LoweredStep::MapIndex { .. }
            | LoweredStep::FieldAccess { .. }
            | LoweredStep::TupleField { .. } => {}
        }
    }
}

fn propagate_lambda_capture_demands(
    executable: &ExecutableKey,
    function: FunctionId,
    captures: &[ValueId],
    demand: RuntimeDemand,
    facts: &RuntimeDemandFacts<'_>,
    all_demands: &RuntimeDemandFormulaSnapshot,
    live: &mut HashMap<ValueId, RuntimeDemand>,
    out: &mut ExecutableRuntimeDemand,
    callable_flows: &mut CallableFlowBuilder,
) {
    if !demand.is_callable() {
        for capture in captures {
            note_live_demand(out, live, *capture, RuntimeDemand::whole());
        }
        return;
    }
    let callable = demand.callable;
    let capture_types = captures
        .iter()
        .map(|capture| facts.value_types.get(capture).copied())
        .collect::<Option<Vec<_>>>();
    let Some(capture_types) = capture_types else {
        for capture in captures {
            let demand =
                closure_capture_boundary_demand(facts, callable_flows, *capture, RuntimeDemand::whole(), &callable);
            note_live_demand(out, live, *capture, demand);
        }
        return;
    };
    // The captured values' demands live in the producer's own executable, in the
    // input-demand prefix that precedes its parameters. The closure's call
    // surfaces only select *which* specialization to read: a directly-called
    // closure restricts to the invoked surfaces, but an escaped closure — one
    // returned or stored rather than called here — carries no direct surface
    // (`resolved` is empty) even though its body still proves how it invokes each
    // capture (e.g. a returned `fn () -> f.(1) end` calls `f` at `(int)`). Reading
    // the producer executable by capture-type prefix recovers that proven surface;
    // gating on a non-empty `resolved` would discard it and let `f` reach
    // transport as a surface-less first-class demand.
    // A callee activation key is the whole-scope addressed arrow of
    // `capture_tys ++ own_surface`. Match in that addressed frame (fz-hwn.27.6,
    // A): by the left-to-right property the addressed capture prefix is just the
    // captures addressed alone, and re-addressing the own-surface suffix
    // standalone yields the same canonical surface the resolved set carries.
    let addressed_captures = facts.demand_types.addressed_inputs(&capture_types);
    let mut matched = false;
    for (callee, callee_demand) in &all_demands.callable_inputs {
        if callee.activation.root != executable.activation.root || callee.activation.function != function {
            continue;
        }
        // Captures and surface are one correlated authoritative row. They were
        // addressed when ExecutableFacts captured the settled activation
        // evidence, so this formula only compares canonical identities.
        for frame in &callee_demand.callable_activation_inputs {
            if frame.captures != addressed_captures {
                continue;
            }
            let own_params = &frame.surface.inputs;
            if !callable.resolved.is_empty() && !callable.resolved.iter().any(|surface| surface.inputs == *own_params) {
                continue;
            }
            matched = true;
            for (capture_index, (capture, demand)) in
                captures.iter().zip(callee_demand.input_demands.iter()).enumerate()
            {
                let mut capture_surfaces = demand.callable.resolved.clone();
                if frame
                    .capture_called_with_own_surface
                    .get(capture_index)
                    .copied()
                    .unwrap_or(false)
                {
                    capture_surfaces.insert(CallableSurface {
                        inputs: own_params.clone(),
                    });
                }
                callable_flows.record_direct_surfaces(facts, *capture, &capture_surfaces);
                let mut demand = demand.clone();
                demand.callable.resolved.extend(capture_surfaces);
                let demand = closure_capture_boundary_demand(facts, callable_flows, *capture, demand, &callable);
                note_live_demand(out, live, *capture, demand);
            }
        }
    }
    if !matched {
        for capture in captures {
            let demand =
                closure_capture_boundary_demand(facts, callable_flows, *capture, RuntimeDemand::whole(), &callable);
            note_live_demand(out, live, *capture, demand);
        }
    }
}

fn closure_capture_boundary_demand(
    facts: &RuntimeDemandFacts<'_>,
    callable_flows: &mut CallableFlowBuilder,
    capture: ValueId,
    demand: RuntimeDemand,
    closure: &CallableDemand,
) -> RuntimeDemand {
    if demand.shape == ShapeDemand::Whole
        && !demand.is_callable()
        && value_is_callable(facts, capture)
        && let Some(direct) = direct_only_capture_callable_demand(facts, capture, closure)
    {
        callable_flows.record_direct_demand(facts, capture, &direct);
        return direct;
    }
    let mut upgraded = boundary_value_demand(facts, capture, demand);
    if upgraded.is_callable() {
        upgraded.callable.opaque |= closure.opaque;
        upgraded.callable.escape |= closure.escape;
        record_first_class_boundary_demand(facts, callable_flows, capture, upgraded.clone(), None);
    }
    upgraded
}

fn callable_value_type_demand(facts: &RuntimeDemandFacts<'_>, value: ValueId) -> Option<RuntimeDemand> {
    let ty = facts.value_types.get(&value).copied()?;
    facts.demand_types.callable_value_demand(ty)
}

fn direct_only_capture_callable_demand(
    facts: &RuntimeDemandFacts<'_>,
    value: ValueId,
    closure: &CallableDemand,
) -> Option<RuntimeDemand> {
    let type_demand = callable_value_type_demand(facts, value)?;
    let arities = type_demand
        .callable
        .resolved
        .iter()
        .map(|surface| surface.inputs.len())
        .collect::<HashSet<_>>();
    let closure_surfaces = closure
        .resolved
        .iter()
        .filter(|surface| arities.contains(&surface.inputs.len()))
        .cloned()
        .collect::<BTreeSet<_>>();
    if closure_surfaces.is_empty() {
        return Some(type_demand);
    }
    Some(RuntimeDemand::callable(CallableDemand {
        resolved: closure_surfaces,
        targets: closure
            .targets
            .iter()
            .filter(|target| arities.contains(&target.surface.inputs.len()))
            .cloned()
            .collect(),
        opaque: false,
        escape: false,
    }))
}

fn direct_call_arg_demands(
    types: &Types,
    executable: &ExecutableKey,
    callsite: CallSiteId,
    args: &[CallArg],
    facts: &RuntimeDemandFacts<'_>,
    demands: &RuntimeDemandFormulaSnapshot,
    callable_flows: &mut CallableFlowBuilder,
) -> Vec<RuntimeDemand> {
    arg_demands_for_summary(
        types,
        executable,
        callsite,
        args,
        CallInputMode::Direct,
        facts,
        demands,
        callable_flows,
    )
}

fn closure_call_arg_demands(
    types: &Types,
    executable: &ExecutableKey,
    callsite: CallSiteId,
    args: &[CallArg],
    facts: &RuntimeDemandFacts<'_>,
    demands: &RuntimeDemandFormulaSnapshot,
    callable_flows: &mut CallableFlowBuilder,
) -> Vec<RuntimeDemand> {
    arg_demands_for_summary(
        types,
        executable,
        callsite,
        args,
        CallInputMode::Closure,
        facts,
        demands,
        callable_flows,
    )
}

fn arg_demands_for_summary(
    types: &Types,
    _executable: &ExecutableKey,
    callsite: CallSiteId,
    args: &[CallArg],
    input_mode: CallInputMode,
    facts: &RuntimeDemandFacts<'_>,
    demands: &RuntimeDemandFormulaSnapshot,
    callable_flows: &mut CallableFlowBuilder,
) -> Vec<RuntimeDemand> {
    let arity = args.len();
    let mut out = vec![RuntimeDemand::ignore(); arity];
    let Some(summary) = facts.callsites.get(&callsite) else {
        return args
            .iter()
            .map(|arg| boundary_value_flow_demand(facts, callable_flows, arg.value, RuntimeDemand::whole()))
            .collect();
    };
    let need = facts
        .callsite_needs
        .get(&callsite)
        .copied()
        .unwrap_or(ExecutableNeed::Value);
    if summary.targets.len() > 1
        && let Some(arg) = args.first()
    {
        for fallback_ty in multi_target_receiver_fallbacks(summary, facts.demand_types.any) {
            let receiver_demand =
                boundary_value_flow_demand_at(facts, callable_flows, arg.value, RuntimeDemand::whole(), fallback_ty);
            out[0].join_assign(&receiver_demand);
        }
    }
    for target in &summary.targets {
        let records_direct_arg_surfaces = matches!(target.callee, super::super::semantic::SelectedCallee::Function(_))
            && target.activation.is_some()
            && target.extern_params.is_none();
        let target_demands = local_target_input_demands(types, facts, target, need, demands);
        for (index, (arg, slot)) in args.iter().zip(out.iter_mut()).enumerate().take(arity) {
            let fallback_ty = target
                .surface_inputs
                .get(index)
                .copied()
                .unwrap_or(facts.demand_types.any);
            // A malformed callsite (more closure args than the callee has
            // inputs, or a direct arg past the callee's arity) falls back to
            // the raw `index` -- the same offset the checked computation
            // would have produced anyway for `Direct` (it returns `arg_index`
            // verbatim when in range), and the same offset the old unchecked
            // `Closure` arithmetic produced once its `saturating_sub`
            // underflow-clip landed on zero. `target_demands.get(offset)`
            // below treats an out-of-range offset as a miss regardless, so
            // this is not a behavior change.
            let offset = target
                .activation
                .as_ref()
                .and_then(|activation| input_mode.semantic_index(activation.input_len(types), args.len(), index))
                .unwrap_or(index);
            let observed = target_demands
                .get(offset)
                .cloned()
                .unwrap_or_else(|| facts.demand_types.boundary_demand(fallback_ty));
            if records_direct_arg_surfaces {
                let direct_surfaces = facts
                    .demand_types
                    .callable_surfaces(fallback_ty)
                    .cloned()
                    .unwrap_or_else(|| observed.callable.resolved.clone());
                callable_flows.record_direct_surfaces(facts, arg.value, &direct_surfaces);
            }
            let mut observed = boundary_value_flow_demand_at(facts, callable_flows, arg.value, observed, fallback_ty);
            if !records_direct_arg_surfaces {
                ground_first_class_callable_surface(facts, &mut observed, fallback_ty);
            }
            slot.join_assign(&observed);
        }
    }
    // The boxed-apply ABI for a *closure* callsite (`CallEdge::Indirect` /
    // `generic_callable_shape`) transmits a real value in every argument
    // lane regardless of what any one resolved callee does with it, and
    // regardless of how many targets `summary.targets` resolved to. Whether
    // native codegen ends up on the direct-call fast path (which *can* skip
    // a truly-unused arg lane, because there the caller and the one callee
    // share a co-designed, per-instantiation ABI —
    // `direct_closure_capture_lanes`/`closure_fast_path_arg_is_structural`
    // in `native.rs`) or falls back to the generic indirect closure-call
    // path (which always lowers every positional arg via `env_runtime_vars`,
    // with no callee-demand check at all) is a native-codegen-time
    // structural decision this pass cannot predict — so it must assume the
    // worst case even for an unambiguous single-target callsite. Joining
    // demands *per target* (as the loop above does) lets an argument some
    // targets ignore -- e.g. a shared HOF body's `_acc` parameter that one
    // target discards, or a closure whose sole target never reads its own
    // parameter (an Enumerable slice continuation's unused `_map`) -- join
    // down to `Ignore`, starving that argument's materialization even
    // though the ABI still carries it once codegen picks the generic path.
    // Floor every argument to `Whole` for every closure callsite,
    // generalizing the index-0-only receiver floor above (which covers the
    // direct/receiver protocol-dispatch case) to every argument position.
    if matches!(input_mode, CallInputMode::Closure) {
        for slot in out.iter_mut() {
            slot.join_assign(&RuntimeDemand::whole());
        }
    }
    out
}

fn multi_target_receiver_fallbacks(summary: &CallSiteSummary, any: Ty) -> BTreeSet<Ty> {
    let mut fallbacks = summary
        .targets
        .iter()
        .filter_map(|target| target.surface_inputs.first().copied())
        .collect::<BTreeSet<_>>();
    if fallbacks.is_empty() {
        fallbacks.insert(any);
    }
    fallbacks
}

/// Seed an escaping callable argument's surface from the boundary it crosses.
///
/// `boundary_value_demand` raises first-class `escape` on the callable axis but
/// records no `resolved` surface — the axis is type-blind by construction. The
/// surface the callee actually invokes the argument at is the boundary's settled
/// parameter type (`boundary_ty`), which pins free callable type variables to
/// their grounded instantiation. Unioning that surface onto an escaping callable
/// keys the escaping body at the grounded lane instead of its own polymorphic
/// template.
///
/// This is a *type seed*, not a re-grounding: it only ever adds a surface
/// derived from the static boundary type, gated solely on the monotone `escape`
/// bit. It never inspects (and so never depends on) the evolving callable axis,
/// so the union is unconditional — a callable that is both directly called and
/// escapes keeps both its call surface and its escape surface, and the demand
/// can only ascend across fixpoint rounds.
fn ground_first_class_callable_surface(facts: &RuntimeDemandFacts<'_>, demand: &mut RuntimeDemand, boundary_ty: Ty) {
    if !demand.callable.is_first_class() {
        return;
    }
    let Some(surfaces) = facts.demand_types.callable_surfaces(boundary_ty) else {
        return;
    };
    demand.callable.resolved.extend(surfaces.iter().cloned());
}

fn local_target_input_demands(
    types: &Types,
    facts: &RuntimeDemandFacts<'_>,
    target: &super::super::semantic::CallTargetSummary,
    need: ExecutableNeed,
    demands: &RuntimeDemandFormulaSnapshot,
) -> Vec<RuntimeDemand> {
    match target.callee {
        super::super::semantic::SelectedCallee::ProviderBoundary(_function) => {
            // A provider boundary is interface-only by construction: it has no
            // defined function and no module body (`function_is_provider_boundary`),
            // so there is no lowered body to consult. Every argument crosses the
            // seam at its boundary demand; marshalling is the boundary fact's job.
            target
                .surface_inputs
                .iter()
                .copied()
                .map(|ty| facts.demand_types.boundary_demand(ty))
                .collect()
        }
        super::super::semantic::SelectedCallee::Function(_) => {
            if let Some(extern_params) = target.extern_params {
                return target
                    .surface_inputs
                    .iter()
                    .enumerate()
                    .map(|(index, ty)| {
                        if index < extern_params {
                            RuntimeDemand::whole()
                        } else {
                            facts.demand_types.boundary_demand(*ty)
                        }
                    })
                    .collect();
            }
            let Some(activation) = target.activation.clone() else {
                return target
                    .surface_inputs
                    .iter()
                    .copied()
                    .map(|ty| facts.demand_types.boundary_demand(ty))
                    .collect();
            };
            demands
                .target_inputs
                .get(&ExecutableKey { activation, need })
                .cloned()
                .unwrap_or_else(|| {
                    vec![RuntimeDemand::ignore(); target.activation.as_ref().map_or(0, |a| a.input_len(types))]
                })
        }
    }
}

fn value_is_callable(facts: &RuntimeDemandFacts<'_>, value: ValueId) -> bool {
    facts
        .value_types
        .get(&value)
        .copied()
        .is_some_and(|ty| facts.demand_types.callable_surfaces(ty).is_some())
}

/// The runtime demand on `value` given the representation demand a consumer
/// places on it — the single chokepoint for first-class callable escape.
///
/// A callable consumed for its whole representation, with no resolved call
/// contract, escapes first-class. That is recorded by joining `escape` onto the
/// value's callable axis: a monotone raise that preserves the shape axis,
/// preserves any accumulated `resolved` surfaces, and never clears `opaque`.
/// Non-callable values, and callables that already carry a call contract, pass
/// through unchanged. There is no re-grounding from the value's type: the
/// callable axis is never erased by a shape join, so nothing needs recovering.
fn boundary_value_demand(facts: &RuntimeDemandFacts<'_>, value: ValueId, mut demand: RuntimeDemand) -> RuntimeDemand {
    if demand.shape == ShapeDemand::Whole && !demand.is_callable() && value_is_callable(facts, value) {
        demand.callable.join_assign(&CallableDemand::escaped());
    }
    demand
}

fn boundary_value_flow_demand(
    facts: &RuntimeDemandFacts<'_>,
    callable_flows: &mut CallableFlowBuilder,
    value: ValueId,
    demand: RuntimeDemand,
) -> RuntimeDemand {
    let demand = boundary_value_demand(facts, value, demand);
    record_first_class_boundary_demand(facts, callable_flows, value, demand, None)
}

fn boundary_value_flow_demand_at(
    facts: &RuntimeDemandFacts<'_>,
    callable_flows: &mut CallableFlowBuilder,
    value: ValueId,
    demand: RuntimeDemand,
    boundary_ty: Ty,
) -> RuntimeDemand {
    let demand = boundary_value_demand(facts, value, demand);
    record_first_class_boundary_demand(facts, callable_flows, value, demand, Some(boundary_ty))
}

fn record_first_class_boundary_demand(
    facts: &RuntimeDemandFacts<'_>,
    callable_flows: &mut CallableFlowBuilder,
    value: ValueId,
    demand: RuntimeDemand,
    boundary_ty: Option<Ty>,
) -> RuntimeDemand {
    if demand.callable.is_first_class() {
        let mut recorded = RuntimeDemand::callable(CallableDemand {
            resolved: BTreeSet::new(),
            targets: BTreeSet::new(),
            opaque: demand.callable.opaque,
            escape: demand.callable.escape,
        });
        let may_seed_from_value_type = demand.callable.resolved.is_empty() || facts.callable_origin(value).is_some();
        let type_seed = boundary_ty.or_else(|| {
            may_seed_from_value_type
                .then(|| facts.value_types.get(&value).copied())
                .flatten()
        });
        if let Some(ty) = type_seed {
            ground_first_class_callable_surface(facts, &mut recorded, ty);
        }
        if boundary_ty.is_none() {
            // No boundary type to ground against: seed the escaping surfaces from
            // the value's concrete call shapes. The publication surfaces are
            // grounded once, downstream, in `ground_dispatch_surfaces`.
            recorded.callable.resolved.extend(demand.callable.resolved.clone());
            recorded.callable.resolved.extend(callable_flows.direct_surfaces(value));
        }
        callable_flows.record_first_class_demand(facts, value, &recorded);
    }
    demand
}

fn closure_callee_demand(
    facts: &RuntimeDemandFacts<'_>,
    args: &[CallArg],
    summary: Option<&CallSiteSummary>,
    need: ExecutableNeed,
) -> CallableDemand {
    let actual_inputs: Vec<Ty> = args
        .iter()
        .map(|arg| {
            facts
                .value_types
                .get(&arg.value)
                .copied()
                .unwrap_or(facts.demand_types.any)
        })
        .collect();
    let Some(summary) = summary else {
        let mut demand = CallableDemand {
            resolved: Default::default(),
            targets: BTreeSet::new(),
            opaque: true,
            escape: false,
        };
        demand.resolved.insert(facts.demand_types.surface(&actual_inputs));
        return demand;
    };
    let mut demand = CallableDemand::default();
    demand.resolved.insert(facts.demand_types.surface(&actual_inputs));
    for target in &summary.targets {
        let surface = facts.demand_types.surface(&target.surface_inputs);
        demand.resolved.insert(surface.clone());
        if let (Some(activation), Some(activation_inputs)) = (&target.activation, &target.activation_inputs) {
            demand.targets.insert(CallableTarget {
                surface,
                activation: activation.clone(),
                activation_inputs: activation_inputs.clone(),
                need,
            });
        }
    }
    let exact_local_target = matches!(
        summary.targets.as_slice(),
        [target]
            if matches!(target.callee, super::super::semantic::SelectedCallee::Function(_))
                && target.activation.is_some()
                && target.activation_inputs.is_some()
    );
    if !exact_local_target {
        demand.opaque = true;
    }
    demand
}

fn runtime_demand_for_executable_need(need: ExecutableNeed) -> RuntimeDemand {
    match need {
        ExecutableNeed::Value => RuntimeDemand::whole(),
        ExecutableNeed::TupleFields(arity) => RuntimeDemand::tuple_fields(vec![RuntimeDemand::whole(); arity]),
    }
}

fn read_runtime_demand_products<T: Telemetry>(
    tel: &T,
    context: &mut ProductReadContext<'_>,
    plans: &[CallableFlowPlan],
    waits: &mut HashSet<PullWait>,
) -> Vec<RuntimeDemandProductInput> {
    plans
        .iter()
        .flat_map(|plan| &plan.resolution_keys)
        .map(|resolution_key| {
            let key = ProductKey::CallableResolution(resolution_key.clone());
            let answer = match context.read_product(tel, key.clone()) {
                Some(ProductValue::CallableResolution(edge)) => Some(edge.clone()),
                Some(other) => panic!("callable resolution produced unexpected value {other:?}"),
                None => {
                    waits.insert(PullWait::Product(key));
                    None
                }
            };
            RuntimeDemandProductInput {
                key: resolution_key.clone(),
                answer,
            }
        })
        .collect()
}

fn finish_callable_flows(
    input: &RuntimeDemandFormulaInput<'_>,
    plans: Vec<CallableFlowPlan>,
    demand: &mut ExecutableRuntimeDemand,
) {
    demand.callable_flows.clear();
    let answers = input
        .product_answers
        .iter()
        .filter_map(|input| input.answer.as_ref().map(|answer| (&input.key, answer)))
        .collect::<HashMap<_, _>>();
    for plan in plans {
        let first_class_edges = dispatch_stress::perturbed_construction_edges(
            plan.resolution_keys
                .iter()
                .filter_map(|key| answers.get(key).map(|answer| (*answer).clone()))
                .collect(),
        );
        let mut resolutions = Vec::new();
        extend_unique(
            &mut resolutions,
            plan.direct_edges
                .iter()
                .chain(&first_class_edges)
                .map(|edge| edge.resolution.clone())
                .collect(),
        );
        demand.callable_flows.insert(
            plan.value,
            CallableFlowFact {
                function: plan.producer.function,
                captures: plan.producer.captures,
                direct_surfaces: plan.direct_surfaces,
                first_class_surfaces: plan.first_class_surfaces,
                direct_edges: plan.direct_edges,
                first_class_edges,
                opaque: plan.opaque,
                escape: plan.escape,
                resolutions,
            },
        );
    }
}

fn require_activation_key_facts_product(
    world: &World,
    context: &mut ProductReadContext<'_>,
    function: FunctionId,
    waits: &mut HashSet<PullWait>,
) -> bool {
    let recursive = FactKey::Recursive(function);
    let recursive_ready = context.read_fact(world, FactUse::current(recursive.clone()));
    if !recursive_ready {
        waits.insert(PullWait::Fact(FactUse::current(recursive)));
    }

    let input_demand = FactKey::InputDemand(function);
    let input_demand_ready = context.read_fact(world, FactUse::current(input_demand.clone()));
    if !input_demand_ready {
        waits.insert(PullWait::Fact(FactUse::current(input_demand)));
    }

    recursive_ready && input_demand_ready
}

fn extend_unique<T: PartialEq>(target: &mut Vec<T>, values: Vec<T>) {
    for value in values {
        if !target.contains(&value) {
            target.push(value);
        }
    }
}

fn note_live_demand(
    out: &mut ExecutableRuntimeDemand,
    live: &mut HashMap<ValueId, RuntimeDemand>,
    value: ValueId,
    demand: RuntimeDemand,
) {
    if demand.is_ignore() {
        return;
    }
    join_map_demand(live, value, demand.clone());
    join_map_demand(&mut out.value_demands, value, demand);
}

fn merge_live_demands(target: &mut HashMap<ValueId, RuntimeDemand>, observed: HashMap<ValueId, RuntimeDemand>) {
    for (value, demand) in observed {
        join_map_demand(target, value, demand);
    }
}

fn join_map_demand(target: &mut HashMap<ValueId, RuntimeDemand>, value: ValueId, demand: RuntimeDemand) {
    target
        .entry(value)
        .and_modify(|existing| existing.join_assign(&demand))
        .or_insert(demand);
}

fn record_call_arg_demands(out: &mut ExecutableRuntimeDemand, callsite: CallSiteId, observed: &[RuntimeDemand]) {
    let slot = out
        .call_arg_demands
        .entry(callsite)
        .or_insert_with(|| vec![RuntimeDemand::ignore(); observed.len()]);
    if slot.len() < observed.len() {
        slot.resize(observed.len(), RuntimeDemand::ignore());
    }
    for (existing, observed) in slot.iter_mut().zip(observed.iter()) {
        existing.join_assign(observed);
    }
}

fn record_entry_capture_demands(
    out: &mut ExecutableRuntimeDemand,
    entry_id: ControlEntryId,
    observed: &[RuntimeDemand],
) {
    let slot = out
        .entry_capture_demands
        .entry(entry_id)
        .or_insert_with(|| vec![RuntimeDemand::ignore(); observed.len()]);
    if slot.len() < observed.len() {
        slot.resize(observed.len(), RuntimeDemand::ignore());
    }
    for (existing, observed) in slot.iter_mut().zip(observed.iter()) {
        existing.join_assign(observed);
    }
}

fn record_call_return_demand(
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
    callsite: CallSiteId,
    observed: RuntimeDemand,
) {
    if observed.is_ignore() {
        return;
    }
    call_return_demands
        .entry(callsite)
        .and_modify(|existing| existing.join_assign(&observed))
        .or_insert(observed);
}

fn take_live_demand(live: &mut HashMap<ValueId, RuntimeDemand>, value: ValueId) -> RuntimeDemand {
    live.remove(&value).unwrap_or(RuntimeDemand::ignore())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler2::body::ControlEntryOrigin;
    use crate::compiler2::semantic::{CallTargetSummary, SelectedCallee};
    use crate::compiler2::types::Types;
    use crate::source::Span;

    #[test]
    fn lowered_call_kind_is_preserved_in_transport_origins() {
        let direct_callsite = CallSiteId::from_u32(0);
        let closure_callsite = CallSiteId::from_u32(1);
        let direct_value = ValueId::from_u32(0);
        let closure_value = ValueId::from_u32(1);
        let entry = |tail| LoweredEntry {
            span: Span::DUMMY,
            origin: ControlEntryOrigin::Clause,
            params: Vec::new(),
            captures: Vec::new(),
            reusable_cons_captures: Vec::new(),
            steps: Vec::new(),
            tail,
        };
        let body = LoweredBody::Clauses {
            clauses: Vec::new(),
            entries: vec![
                entry(LoweredTail::DirectCall {
                    value: direct_value,
                    callsite: direct_callsite,
                    callee: FunctionId::for_test(0),
                    args: Vec::new(),
                    dest: ControlDestination::Return,
                }),
                entry(LoweredTail::ClosureCall {
                    value: closure_value,
                    callsite: closure_callsite,
                    callee: ValueId::from_u32(2),
                    args: Vec::new(),
                    dest: ControlDestination::Return,
                }),
            ],
            generated: Vec::new(),
        };

        let callsite_origins = collect_callsite_return_origins(&body);
        let value_origins = collect_value_origins(&body, &callsite_origins);

        assert_eq!(
            value_origins.get(&direct_value),
            Some(&TransportOrigin::CallsiteReturn(direct_callsite))
        );
        assert_eq!(
            value_origins.get(&closure_value),
            Some(&TransportOrigin::ClosureCallReturn {
                callsite: closure_callsite,
                callee: ValueId::from_u32(2),
            })
        );
    }

    #[test]
    fn multi_target_receiver_fallback_joins_exact_surfaces_independent_of_target_order() {
        let mut types = Types::new();
        let (any, int, atom) = (types.any(), types.int(), types.atom());
        let target = |ty: Option<Ty>| CallTargetSummary {
            callee: SelectedCallee::Function(FunctionId::for_test(0)),
            surface_inputs: ty.into_iter().collect(),
            activation: None,
            activation_inputs: None,
            extern_params: None,
            return_ty: None,
        };
        let summary = |targets| CallSiteSummary {
            targets,
            return_ty: None,
        };
        let expected = BTreeSet::from([int, atom]);

        assert_eq!(
            multi_target_receiver_fallbacks(&summary(vec![target(Some(int)), target(Some(atom))]), any),
            expected
        );
        assert_eq!(
            multi_target_receiver_fallbacks(&summary(vec![target(Some(atom)), target(Some(int))]), any),
            expected
        );
        assert_eq!(
            multi_target_receiver_fallbacks(&summary(vec![target(None), target(Some(atom))]), any),
            BTreeSet::from([atom]),
            "an absent surface must not widen a receiver when another target supplies its exact surface"
        );
        assert_eq!(
            multi_target_receiver_fallbacks(&summary(vec![target(None), target(None)]), any),
            BTreeSet::from([any]),
            "only an entirely unknown target set needs the any fallback"
        );
    }
}
