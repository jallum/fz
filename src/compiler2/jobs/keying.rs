//! Jobs that derive the stable facts used for activation keying.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardExpr};
use crate::dispatch_matrix::{ListRegion, ProjectionKind, Region, RegionPredicate, Subject, SubjectId, SubjectSource};

use super::super::body::{CallSiteId, LoweredBody, LoweredStep, LoweredTail};
use super::super::drive::{FactKey, JobEffects, current_uses};
use super::super::identity::FunctionId;
use super::super::keying::{
    BodyKeying, DispatchDemand, InputDemand, InputFlow, InputFlowOrigin, InputFlowRelation, InputFlowSink, InputMapKey,
    InputPathStep, InputPosition, InputPullback, MapSelector,
};
use super::super::protocol::ProtocolDispatch;
use super::super::scheduler::FatalError;
use super::super::types::Ty;
use super::super::world::World;
use crate::telemetry::TelemetryExt as _;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StaticEdge {
    Direct(FunctionId),
    Lambda(FunctionId),
}

impl StaticEdge {
    fn function(self) -> FunctionId {
        match self {
            StaticEdge::Direct(function) | StaticEdge::Lambda(function) => function,
        }
    }
}

/// Derives the static call edges leaving one function: the callees its
/// lowered body names, ascending by function id, deduplicated.
///
/// This is the call graph's edge fact, one body's worth per publication.
/// Reachability questions -- `derive_recursive` today, component membership
/// next -- walk these facts instead of re-extracting edges from every body
/// they can reach, so discovering one more layer of the graph costs one fact
/// read per node rather than one body scan per node per layer (fz-kdt.56).
pub(super) fn derive_static_callees(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
) -> Result<JobEffects, FatalError> {
    let mut reads = Vec::new();
    if world.function_is_provider_boundary(function, &mut reads) {
        // A provider boundary has an interface but no body in this program:
        // no edges. The boundary test is not monotone -- a definition landing
        // later dissolves it -- so the conclusion subscribes to the facts it
        // consulted rather than freezing the filter's answer.
        return Ok(publish_static_callees(world, function, Vec::new(), reads));
    }
    if world.function_defined_revision(function).is_none() && world.protocol_callback(function).is_some() {
        // A protocol callback is dispatched through, never lowered: it is
        // a leaf of the static graph, not a wait that would never resolve.
        let defined = FactKey::FunctionDefined(function);
        if !reads.contains(&defined) {
            reads.push(defined);
        }
        return Ok(publish_static_callees(world, function, Vec::new(), reads));
    }
    if let Some(wait) = wait_for_undefined_function_module(world, tel, function) {
        return Ok(wait_after_reads(wait, reads));
    }

    let lowered = FactKey::LoweredBody(function);
    if !world.has_fact(&lowered) {
        // One wait, for the one fact this derivation reads. `LoweredBody`'s
        // sole producer arm is `Job::LowerFunction`, and the chain behind it
        // (`DefineFunction` -> `PublishFunctionSource` -> `demand_function_scope`)
        // is what scopes the code the body comes from. Waiting on
        // `FunctionDefined` first, as a separate rung, would buy nothing but
        // one more blocked evaluation per function.
        return Ok(wait_after_reads(JobEffects::wait_on_current(lowered), reads));
    }
    reads.extend([FactKey::FunctionDefined(function), lowered]);
    let callees = body_static_callees(world, function, &mut reads);
    Ok(publish_static_callees(world, function, callees, reads))
}

/// Demands the module scope shared by every body-derived function fact.
///
/// Provider and protocol boundaries are semantic exceptions handled by their
/// callers. For an ordinary undefined non-global function, `ModuleDefined` is
/// the first real prerequisite: ensuring its runtime module mints the code
/// whose definition/lowering chain will eventually publish the body.
fn wait_for_undefined_function_module(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
) -> Option<JobEffects> {
    if world.function_defined_revision(function).is_some() {
        return None;
    }
    let module = world.function_module(function);
    if module.is_global() || world.module_defined_revision(module).is_some() {
        return None;
    }
    super::super::drive::ExecutionContext::new(world, tel).ensure_runtime_module(module);
    Some(JobEffects::wait_on_current(FactKey::ModuleDefined(module)))
}

fn wait_after_reads(mut wait: JobEffects, reads: Vec<FactKey>) -> JobEffects {
    wait.reads = current_uses(reads);
    wait
}

/// The callees one lowered body names, in the order `static_edges` yields
/// them -- ascending by function id, so the published `Vec` is deterministic
/// by construction and adjacent duplicates (a function both called directly
/// and captured as a lambda) collapse without a second sort.
fn body_static_callees(world: &World, function: FunctionId, reads: &mut Vec<FactKey>) -> Vec<FunctionId> {
    let mut callees: Vec<FunctionId> = Vec::new();
    for edge in static_edges(&world.lowered_body(function)) {
        let target = edge.function();
        if world.function_is_provider_boundary(target, reads) {
            // The boundary test consults the target's definedness, and it is
            // not monotone: a module or function defined later dissolves the
            // boundary. Record the read so that definition grows this edge
            // set instead of leaving the filter frozen in a fact.
            continue;
        }
        if matches!(edge, StaticEdge::Lambda(_)) {
            // A lambda target is an edge only once its generated function
            // exists. The conclusion consulted that fact, so it is read
            // whether or not it was there -- a definition that lands later
            // must be able to grow this edge set.
            let defined = FactKey::FunctionDefined(target);
            if !reads.contains(&defined) {
                reads.push(defined);
            }
            if world.function_defined_revision(target).is_none() {
                continue;
            }
        }
        if callees.last() != Some(&target) {
            callees.push(target);
        }
    }
    callees
}

fn publish_static_callees(
    world: &mut World,
    function: FunctionId,
    callees: Vec<FunctionId>,
    reads: Vec<FactKey>,
) -> JobEffects {
    let changed = world.define_static_callees(function, callees);
    JobEffects {
        reads: current_uses(reads),
        outputs: vec![FactKey::StaticCallees(function)],
        changed: changed
            .then_some(FactKey::StaticCallees(function))
            .into_iter()
            .collect(),
        ..JobEffects::default()
    }
}

/// Derives where one function sits in the static call graph: the canonical
/// member of its strong component, and the recursion answer that component
/// decides.
///
/// One walk, two facts. `CallGraphComponent(f)` is the smallest `FunctionId`
/// mutually reachable with `f`, so "are these two functions mutually
/// reachable" becomes an equality between two fact reads instead of a
/// traversal at every asking site (fz-kdt.13). Recursion is a projection of
/// the same answer -- `f` reaches itself exactly when its component has more
/// than one member or its own edge set names it -- so the pyramid that used
/// to walk the graph for recursion alone no longer exists as separate work.
/// Identity consumption is a body-local property with no call-graph content,
/// but it has always ridden `FactKey::Recursive`'s one value and still does.
///
/// Lambda creation is a static edge from the owner to the generated function,
/// so recursion through generated closures is handled the same way as direct
/// or mutual recursion.
pub(super) fn derive_call_graph_component(world: &mut World, function: FunctionId) -> Result<JobEffects, FatalError> {
    let mut reads = Vec::new();
    if world.function_is_provider_boundary(function, &mut reads) {
        // No body in this program: no edges, so the component is the function
        // alone and nothing it does can reach back to it.
        return Ok(publish_call_graph_node(
            world,
            function,
            function,
            BodyKeying {
                recursive: false,
                consumes_callable_identity: false,
            },
            reads,
        ));
    }

    let mut waits = HashSet::new();
    let mut graph = HashMap::new();
    let mut seen = HashSet::new();
    collect_static_graph(world, function, &mut reads, &mut waits, &mut graph, &mut seen);
    // Identity consumption is a property of this body alone, so it rides the
    // same conclusion rather than the graph walk -- but it needs the body,
    // which a `StaticCallees` fact published for an undefined protocol
    // callback does not imply.
    let lowered = FactKey::LoweredBody(function);
    if !world.has_fact(&lowered) {
        waits.insert(lowered);
    } else {
        reads.push(lowered);
    }
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads: current_uses(reads),
            waits: current_uses(waits),
            ..JobEffects::default()
        });
    }

    let component = strong_component(function, &graph);
    let keying = BodyKeying {
        recursive: component.len() > 1 || graph.get(&function).is_some_and(|edges| edges.contains(&function)),
        consumes_callable_identity: body_consumes_callable_identity(world, function),
    };
    let canonical = component
        .into_iter()
        .min()
        .expect("a function is always a member of its own strong component");
    Ok(publish_call_graph_node(world, function, canonical, keying, reads))
}

/// Publishes both answers one walk produced. Two facts, not one value: a
/// component id and a body's keying move for different reasons and wake
/// different readers, so fusing them would wake activation keying every time
/// the graph merged two components.
fn publish_call_graph_node(
    world: &mut World,
    function: FunctionId,
    component: FunctionId,
    keying: BodyKeying,
    reads: Vec<FactKey>,
) -> JobEffects {
    let component_fact = FactKey::CallGraphComponent(function);
    let keying_fact = FactKey::Recursive(function);
    let component_changed = world.define_call_graph_component(function, component);
    // One fact, one value: a body edit can flip identity-consumption without
    // touching recursion, and keying dependents re-derive off this fact --
    // publishing both answers as one struct makes a half-defined or
    // half-signalled state unrepresentable.
    let keying_changed = world.define_body_keying(function, keying);
    JobEffects {
        reads: current_uses(reads),
        outputs: vec![component_fact.clone(), keying_fact.clone()],
        changed: component_changed
            .then_some(component_fact)
            .into_iter()
            .chain(keying_changed.then_some(keying_fact))
            .collect(),
        ..JobEffects::default()
    }
}

/// Does this function's body CONSUME callable identity -- call through a
/// callable value, or capture values into a lambda it constructs? A call
/// consumes identity directly (the specialization buys direct dispatch); a
/// construction bakes the captured value's identity into a new closure whose
/// downstream consumers depend on the correlation, so the constructor must
/// stay split per identity too. A body that does neither only transports
/// callables, and brands are freight to it. `ClosureCall` only occurs as an
/// entry tail and `Lambda` only as a step, so scanning the flat entry list
/// covers every dispatch arm, branch, and receive clause.
fn body_consumes_callable_identity(world: &World, function: FunctionId) -> bool {
    // A closure's captures ARE identity: whatever a capturing lambda does with
    // a capture -- call it, or pass it to something that does -- its consumers
    // depend on the correlation between the construction site and the captured
    // values, and that correlation is transitive through any chain of
    // capture-holding lambdas. So a function with capture params is
    // identity-laden by definition, without needing a flow analysis to prove
    // where the captures end up.
    if world
        .function_source(function)
        .is_some_and(|source| !source.capture_params.is_empty())
    {
        return true;
    }
    match world.lowered_body(function) {
        LoweredBody::Extern { .. } => false,
        LoweredBody::Clauses { clauses, entries, .. } => {
            let step_constructs = |step: &LoweredStep| matches!(step, LoweredStep::Lambda { .. });
            entries.iter().any(|entry| {
                matches!(entry.tail, LoweredTail::ClosureCall { .. }) || entry.steps.iter().any(step_constructs)
            }) || clauses
                .iter()
                .any(|clause| clause.projections.iter().any(step_constructs))
        }
    }
}

/// One node of the still-private InputDemand solver. fz-kdt.213 deletes this
/// graph; its edges are projections of the independently retained
/// [`InputFlowRelation`] rather than another body scan.
#[derive(Debug, Clone)]
struct DemandNode<'a> {
    relation: &'a InputFlowRelation,
}

/// Extracts the one immutable path relation for a function. This job performs
/// no inter-function solving: body/dispatch or protocol facts go in, one local
/// relation comes out, and equality at the World boundary suppresses wakes.
pub(super) fn derive_input_flow(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
) -> Result<JobEffects, FatalError> {
    let mut reads = Vec::new();

    let relation = if let Some(callback) = world.protocol_callback(function) {
        let module = FactKey::ModuleDefined(callback.protocol);
        if world.module_defined_revision(callback.protocol).is_none() {
            return Ok(JobEffects::wait_on_current(module));
        }
        reads.push(module);
        let dispatch_fact = FactKey::ProtocolDispatch(callback.protocol);
        let Some(dispatch) = world.protocol_dispatch(callback.protocol) else {
            return Ok(wait_after_reads(JobEffects::wait_on_current(dispatch_fact), reads));
        };
        reads.push(dispatch_fact);
        protocol_input_flow_relation(world, function, dispatch)
    } else {
        let provider_boundary = world.function_is_provider_boundary(function, &mut reads);
        if !provider_boundary && let Some(wait) = wait_for_undefined_function_module(world, tel, function) {
            return Ok(wait_after_reads(wait, reads));
        }
        let lowered = FactKey::LoweredBody(function);
        if provider_boundary {
            InputFlowRelation {
                local_dispatch: vec![DispatchDemand::Ignore; world.function_arity(function)].into_boxed_slice(),
                ..InputFlowRelation::default()
            }
        } else if !world.has_fact(&lowered) {
            return Ok(wait_after_reads(JobEffects::wait_on_current(lowered), reads));
        } else {
            reads.push(lowered);
            let dispatch = FactKey::EntryDispatch(function);
            if !world.has_fact(&dispatch) {
                return Ok(wait_after_reads(JobEffects::wait_on_current(dispatch), reads));
            }
            reads.push(dispatch);
            super::super::input_flow::extract_input_flow_relation(
                world,
                function,
                local_dispatch_mask(world.entry_dispatch_ref(function)).into_boxed_slice(),
            )
        }
    };

    let changed = world.define_input_flow(function, relation);
    Ok(JobEffects {
        reads: current_uses(reads),
        outputs: vec![FactKey::InputFlow(function)],
        changed: changed.then_some(FactKey::InputFlow(function)).into_iter().collect(),
        ..JobEffects::default()
    })
}

/// Projects activation-key demand from the retained typed flow relations.
///
/// Dispatch queries seed local entry questions and visit every callsite;
/// returned queries seed the requested return path and visit only results that
/// flow to it. Child answers are routed back through the exact `CallSiteId`, so
/// equal callee questions may share computation without cross-connecting two
/// calls. Acyclic composition is exact. Recursive SCC query states alone use a
/// deterministic, sound structural over-approximation until fz-kdt.200 replaces
/// the coarse `DispatchDemand` domain; fz-kdt.213 deletes this private solver.
pub(super) fn derive_input_demand(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
) -> Result<JobEffects, FatalError> {
    let mut reads = Vec::new();
    let mut waits = HashSet::new();
    let mut graph = BTreeMap::new();
    collect_input_forwarding_graph(world, function, &mut reads, &mut waits, &mut graph);
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads: current_uses(reads),
            waits: current_uses(waits),
            ..JobEffects::default()
        });
    }

    let recursion = demand_recursion_plan(&graph, function);
    let demand = InputDemand {
        local_dispatch: graph
            .get(&function)
            .map(|node| node.relation.local_dispatch.to_vec())
            .unwrap_or_default(),
        forwarded_dispatch: solve_demand_query_graph_with_plan(
            &graph,
            function,
            DemandMode::Dispatch,
            DispatchDemand::Ignore,
            &recursion,
        ),
        returned: solve_demand_query_graph_with_plan(
            &graph,
            function,
            DemandMode::Returned,
            DispatchDemand::Whole,
            &recursion,
        ),
    };
    emit_input_demand_derived(tel, &function, &demand);
    let changed = world.define_input_demand(function, demand);
    Ok(JobEffects {
        reads: current_uses(reads),
        outputs: vec![FactKey::InputDemand(function)],
        changed: changed.then_some(FactKey::InputDemand(function)).into_iter().collect(),
        ..JobEffects::default()
    })
}

/// Walks the callees named by retained direct/protocol input-flow sinks.
///
/// This discovers the relations the query may compose without rescanning a
/// lowered body. The graph borrows World-owned relations, so deriving demand
/// neither copies nor republishes their normalized edge sets.
fn collect_input_forwarding_graph<'a>(
    world: &'a World,
    function: FunctionId,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    graph: &mut BTreeMap<FunctionId, DemandNode<'a>>,
) {
    if graph.contains_key(&function) {
        return;
    }
    let flow_fact = FactKey::InputFlow(function);
    if !world.has_fact(&flow_fact) {
        waits.insert(flow_fact);
        return;
    }
    reads.push(flow_fact);
    let relation = world.input_flow(function).expect("present InputFlow fact");
    let next = relation
        .direct_calls
        .values()
        .map(|call| call.callee)
        .chain(relation.flows.iter().filter_map(|flow| match &flow.sink {
            InputFlowSink::ProtocolInput { callee, .. } => Some(*callee),
            _ => None,
        }))
        .collect::<BTreeSet<_>>();
    graph.insert(function, DemandNode { relation });
    for callee in next {
        collect_input_forwarding_graph(world, callee, reads, waits, graph);
    }
}

fn protocol_input_flow_relation(world: &World, function: FunctionId, dispatch: &ProtocolDispatch) -> InputFlowRelation {
    let arity = world.function_arity(function);
    let mut flows = BTreeSet::new();
    for arm in &dispatch.arms {
        let Some(callee) = arm.callbacks.get(&function).map(|target| target.function) else {
            continue;
        };
        for input in 0..arity.min(world.function_arity(callee)) {
            flows.insert(InputFlow {
                origin: InputFlowOrigin::Input(InputPosition::root(input)),
                sink: InputFlowSink::ProtocolInput {
                    callee,
                    input: InputPosition::root(input),
                },
                pullback: InputPullback::Structural,
            });
        }
    }
    InputFlowRelation {
        local_dispatch: vec![DispatchDemand::Ignore; arity].into_boxed_slice(),
        flows,
        ..InputFlowRelation::default()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum DemandPort {
    Return,
    Input(usize),
    CallResult(CallSiteId),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct DemandQuery {
    mode: DemandMode,
    function: FunctionId,
    result: DispatchDemand,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum DemandMode {
    Dispatch,
    Returned,
}

#[cfg(test)]
fn solve_demand_query_graph(
    graph: &BTreeMap<FunctionId, DemandNode<'_>>,
    function: FunctionId,
    mode: DemandMode,
    result: DispatchDemand,
) -> Vec<DispatchDemand> {
    let recursion = demand_recursion_plan(graph, function);
    solve_demand_query_graph_with_plan(graph, function, mode, result, &recursion)
}

fn solve_demand_query_graph_with_plan(
    graph: &BTreeMap<FunctionId, DemandNode<'_>>,
    function: FunctionId,
    mode: DemandMode,
    result: DispatchDemand,
    recursion: &DemandRecursionPlan,
) -> Vec<DispatchDemand> {
    let recursive = &recursion.functions;
    let depth_bound = recursion.depth_bound;
    let root = DemandQuery { mode, function, result };
    let mut answers = BTreeMap::from([(
        root.clone(),
        vec![
            DispatchDemand::Ignore;
            graph
                .get(&function)
                .map_or(0, |node| node.relation.local_dispatch.len())
        ],
    )]);
    loop {
        let queries = answers.keys().cloned().collect::<Vec<_>>();
        let mut requested = BTreeSet::new();
        let mut changed = false;
        for query in &queries {
            let next = evaluate_demand_query(graph, query, &answers, &mut requested, recursion);
            let answer = answers
                .get_mut(query)
                .expect("every evaluated return query has a result slot");
            for (slot, next) in answer.iter_mut().zip(next) {
                let before = slot.clone();
                slot.join_assign(next);
                if recursive.contains(&query.function) {
                    *slot = normalize_demand(slot.clone(), depth_bound);
                }
                changed |= *slot != before;
            }
        }
        for query in requested {
            if let std::collections::btree_map::Entry::Vacant(slot) = answers.entry(query) {
                let inputs = graph
                    .get(&slot.key().function)
                    .map_or(0, |node| node.relation.local_dispatch.len());
                slot.insert(vec![DispatchDemand::Ignore; inputs]);
                changed = true;
            }
        }
        if !changed {
            return answers.remove(&root).unwrap_or_default();
        }
    }
}

fn evaluate_demand_query(
    graph: &BTreeMap<FunctionId, DemandNode<'_>>,
    query: &DemandQuery,
    answers: &BTreeMap<DemandQuery, Vec<DispatchDemand>>,
    requested: &mut BTreeSet<DemandQuery>,
    recursion: &DemandRecursionPlan,
) -> Vec<DispatchDemand> {
    let Some(node) = graph.get(&query.function) else {
        return Vec::new();
    };
    let recursive = &recursion.functions;
    let depth_bound = recursion.depth_bound;
    let mut demands = BTreeMap::new();
    if query.result != DispatchDemand::Ignore {
        demands.insert(DemandPort::Return, query.result.clone());
    }
    if query.mode == DemandMode::Dispatch {
        for (input, demand) in node.relation.local_dispatch.iter().cloned().enumerate() {
            demands.insert(DemandPort::Input(input), demand);
        }
    }
    loop {
        let snapshot = demands.clone();
        let mut changed = false;
        for flow in &node.relation.flows {
            let sink_demand = match &flow.sink {
                InputFlowSink::FunctionReturn(path) => snapshot
                    .get(&DemandPort::Return)
                    .cloned()
                    .map(|demand| demand_below_path(demand, path)),
                InputFlowSink::ProtocolInput { callee, input } => {
                    let result = snapshot.get(&DemandPort::Return).cloned().unwrap_or_default();
                    if query.mode == DemandMode::Returned && result == DispatchDemand::Ignore {
                        continue;
                    }
                    let child = DemandQuery {
                        mode: query.mode,
                        function: *callee,
                        result: normalize_query_demand(*callee, result, depth_bound, recursive),
                    };
                    requested.insert(child.clone());
                    answers
                        .get(&child)
                        .and_then(|inputs| inputs.get(input.input))
                        .cloned()
                        .map(|demand| demand_below_path(demand, &input.path))
                }
                InputFlowSink::CallableUse { .. } => None,
            };
            let Some(sink_demand) = sink_demand else {
                continue;
            };
            changed |= join_origin_demand(
                &mut demands,
                &flow.origin,
                sink_demand,
                flow.pullback,
                recursive.contains(&query.function),
                depth_bound,
            );
        }
        for (callsite, call) in &node.relation.direct_calls {
            let result = snapshot
                .get(&DemandPort::CallResult(*callsite))
                .cloned()
                .unwrap_or_default();
            if query.mode == DemandMode::Returned && result == DispatchDemand::Ignore {
                continue;
            }
            let child = DemandQuery {
                mode: query.mode,
                function: call.callee,
                result: normalize_query_demand(call.callee, result, depth_bound, recursive),
            };
            requested.insert(child.clone());
            let Some(child_inputs) = answers.get(&child) else {
                continue;
            };
            for (input, bindings) in call.inputs.iter().enumerate() {
                let Some(input_demand) = child_inputs.get(input).cloned() else {
                    continue;
                };
                for binding in bindings {
                    changed |= join_origin_demand(
                        &mut demands,
                        &binding.origin,
                        demand_below_path(input_demand.clone(), &binding.path),
                        binding.pullback,
                        recursive.contains(&query.function),
                        depth_bound,
                    );
                }
            }
        }
        if !changed {
            break;
        }
    }
    (0..node.relation.local_dispatch.len())
        .map(|input| demands.remove(&DemandPort::Input(input)).unwrap_or_default())
        .collect()
}

fn join_origin_demand(
    demands: &mut BTreeMap<DemandPort, DispatchDemand>,
    origin: &InputFlowOrigin,
    sink_demand: DispatchDemand,
    pullback: InputPullback,
    normalize: bool,
    depth_bound: usize,
) -> bool {
    let (port, path) = match origin {
        InputFlowOrigin::Input(input) => (DemandPort::Input(input.input), input.path.as_ref()),
        InputFlowOrigin::CallResult { callsite, path } => (DemandPort::CallResult(*callsite), path.as_ref()),
    };
    let slot = demands.entry(port).or_default();
    let before = slot.clone();
    let origin_demand = match pullback {
        InputPullback::Structural => demand_at_path(path, sink_demand),
        InputPullback::WholeOrigin if sink_demand == DispatchDemand::Ignore => DispatchDemand::Ignore,
        InputPullback::WholeOrigin => demand_at_path(path, DispatchDemand::Whole),
    };
    slot.join_assign(origin_demand);
    if normalize {
        *slot = normalize_demand(slot.clone(), depth_bound);
    }
    *slot != before
}

fn normalize_query_demand(
    function: FunctionId,
    demand: DispatchDemand,
    depth_bound: usize,
    recursive: &BTreeSet<FunctionId>,
) -> DispatchDemand {
    if recursive.contains(&function) {
        normalize_demand(demand, depth_bound)
    } else {
        demand
    }
}

fn normalize_demand(demand: DispatchDemand, depth: usize) -> DispatchDemand {
    if demand == DispatchDemand::Ignore {
        return DispatchDemand::Ignore;
    }
    if depth == 0 {
        return DispatchDemand::Whole;
    }
    match demand {
        DispatchDemand::Ignore | DispatchDemand::Whole => demand,
        DispatchDemand::ListShape(element) => {
            DispatchDemand::ListShape(Box::new(normalize_demand(*element, depth - 1)))
        }
        DispatchDemand::TupleFields(fields) => DispatchDemand::TupleFields(
            fields
                .into_iter()
                .map(|(field, demand)| (field, normalize_demand(demand, depth - 1)))
                .filter(|(_, demand)| *demand != DispatchDemand::Ignore)
                .collect(),
        ),
    }
}

#[derive(Debug)]
struct DemandRecursionPlan {
    functions: BTreeSet<FunctionId>,
    depth_bound: usize,
}

fn demand_recursion_plan(graph: &BTreeMap<FunctionId, DemandNode<'_>>, root: FunctionId) -> DemandRecursionPlan {
    fn visit(
        function: FunctionId,
        edges: &BTreeMap<FunctionId, BTreeSet<FunctionId>>,
        seen: &mut BTreeSet<FunctionId>,
        order: &mut Vec<FunctionId>,
    ) {
        if !seen.insert(function) {
            return;
        }
        for callee in edges.get(&function).into_iter().flatten() {
            visit(*callee, edges, seen, order);
        }
        order.push(function);
    }

    fn component_bound(
        component: usize,
        weights: &[usize],
        successors: &[BTreeSet<usize>],
        memo: &mut [Option<usize>],
    ) -> usize {
        if let Some(bound) = memo[component] {
            return bound;
        }
        let downstream = successors[component]
            .iter()
            .map(|next| component_bound(*next, weights, successors, memo))
            .max()
            .unwrap_or(0);
        let bound = weights[component].saturating_add(downstream);
        memo[component] = Some(bound);
        bound
    }

    let edges: BTreeMap<FunctionId, BTreeSet<FunctionId>> = graph
        .iter()
        .map(|(function, node)| {
            (
                *function,
                demand_callees(node)
                    .into_iter()
                    .filter(|callee| graph.contains_key(callee))
                    .collect(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut reverse = graph
        .keys()
        .copied()
        .map(|function| (function, BTreeSet::new()))
        .collect::<BTreeMap<_, _>>();
    for (caller, callees) in &edges {
        for callee in callees {
            reverse.entry(*callee).or_default().insert(*caller);
        }
    }

    let mut order = Vec::new();
    let mut seen = BTreeSet::new();
    for function in graph.keys().copied() {
        visit(function, &edges, &mut seen, &mut order);
    }
    let mut components = Vec::<BTreeSet<FunctionId>>::new();
    let mut assigned = BTreeSet::new();
    for function in order.into_iter().rev() {
        if assigned.contains(&function) {
            continue;
        }
        let mut members = Vec::new();
        visit(function, &reverse, &mut assigned, &mut members);
        components.push(members.into_iter().collect());
    }
    let component_of = components
        .iter()
        .enumerate()
        .flat_map(|(component, members)| members.iter().map(move |member| (*member, component)))
        .collect::<BTreeMap<_, _>>();
    let functions: BTreeSet<_> = components
        .iter()
        .filter(|members| {
            members.len() > 1
                || members
                    .first()
                    .is_some_and(|member| edges.get(member).is_some_and(|callees| callees.contains(member)))
        })
        .flat_map(|members| members.iter().copied())
        .collect();
    let mut weights = vec![0usize; components.len()];
    let mut successors = vec![BTreeSet::new(); components.len()];
    for (function, node) in graph {
        let component = component_of[function];
        weights[component] = weights[component].saturating_add(demand_local_cost(node));
        for callee in &edges[function] {
            let target = component_of[callee];
            if target != component {
                successors[component].insert(target);
            }
        }
    }
    let root_component = component_of.get(&root).copied();
    let depth_bound = root_component
        .map(|component| {
            component_bound(component, &weights, &successors, &mut vec![None; components.len()]).saturating_add(1)
        })
        .unwrap_or(1);
    DemandRecursionPlan { functions, depth_bound }
}

fn demand_local_cost(node: &DemandNode<'_>) -> usize {
    let local_depth = node.relation.local_dispatch.iter().map(demand_depth).max().unwrap_or(0);
    let flow_cost = node.relation.flows.iter().fold(local_depth, |cost, flow| {
        cost.saturating_add(origin_path(&flow.origin).len())
            .saturating_add(sink_path(&flow.sink).len())
            .saturating_add(1)
    });
    node.relation
        .direct_calls
        .values()
        .flat_map(|call| call.inputs.iter().flatten())
        .fold(flow_cost, |cost, binding| {
            cost.saturating_add(origin_path(&binding.origin).len())
                .saturating_add(binding.path.len())
                .saturating_add(1)
        })
}

fn demand_callees(node: &DemandNode<'_>) -> BTreeSet<FunctionId> {
    demand_call_targets(node)
        .into_iter()
        .map(|(_, callee)| callee)
        .collect()
}

fn demand_call_targets(node: &DemandNode<'_>) -> BTreeSet<(Option<CallSiteId>, FunctionId)> {
    node.relation
        .direct_calls
        .iter()
        .map(|(callsite, call)| (Some(*callsite), call.callee))
        .chain(node.relation.flows.iter().filter_map(|flow| match &flow.sink {
            InputFlowSink::ProtocolInput { callee, .. } => Some((None, *callee)),
            _ => None,
        }))
        .collect()
}

fn origin_path(origin: &InputFlowOrigin) -> &[InputPathStep] {
    match origin {
        InputFlowOrigin::Input(input) => &input.path,
        InputFlowOrigin::CallResult { path, .. } => path,
    }
}

fn sink_path(sink: &InputFlowSink) -> &[InputPathStep] {
    match sink {
        InputFlowSink::FunctionReturn(path) | InputFlowSink::CallableUse { path, .. } => path,
        InputFlowSink::ProtocolInput { input, .. } => &input.path,
    }
}

fn demand_depth(demand: &DispatchDemand) -> usize {
    match demand {
        DispatchDemand::Ignore | DispatchDemand::Whole => 0,
        DispatchDemand::ListShape(element) => 1 + demand_depth(element),
        DispatchDemand::TupleFields(fields) => 1 + fields.values().map(demand_depth).max().unwrap_or(0),
    }
}

fn emit_input_demand_derived(tel: &impl crate::telemetry::Telemetry, function: &FunctionId, demand: &InputDemand) {
    tel.raw_event2(&["fz", "compiler2", "input_demand", "derived"], function, demand);
}

/// Walks the reachable static call graph over the `StaticCallees` edge facts.
///
/// One fact read per reachable node, and a node already known costs the read
/// and nothing else -- no body is re-scanned when a later layer of the graph
/// arrives. Missing edge facts are recorded as waits, so the layers the walk
/// discovers are demand, not repeated work (fz-kdt.56).
fn collect_static_graph(
    world: &World,
    function: FunctionId,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    graph: &mut HashMap<FunctionId, Vec<FunctionId>>,
    seen: &mut HashSet<FunctionId>,
) {
    if !seen.insert(function) {
        return;
    }
    let callees = FactKey::StaticCallees(function);
    if !world.has_fact(&callees) {
        // `StaticCallees`'s sole producer arm is `Job::DeriveStaticCallees`.
        waits.insert(callees);
        return;
    }
    reads.push(callees);
    let edges = world.static_callees(function).to_vec();
    for target in &edges {
        collect_static_graph(world, *target, reads, waits, graph, seen);
    }
    graph.insert(function, edges);
}

/// The functions mutually reachable with `function`, `function` included.
///
/// `graph` is the subgraph reachable FROM `function`, which is all the walk needs:
/// a function mutually reachable with `function` is reachable from it by
/// definition, and so is every node on its path back. So membership reduces to
/// "which nodes of the subgraph reach `function`" -- a walk of its reversed
/// edges from `function`.
fn strong_component(function: FunctionId, graph: &HashMap<FunctionId, Vec<FunctionId>>) -> HashSet<FunctionId> {
    let mut reversed: HashMap<FunctionId, Vec<FunctionId>> = HashMap::new();
    for (caller, callees) in graph {
        for callee in callees {
            reversed.entry(*callee).or_default().push(*caller);
        }
    }
    let mut members = HashSet::from([function]);
    let mut frontier = vec![function];
    while let Some(next) = frontier.pop() {
        for caller in reversed.get(&next).into_iter().flatten() {
            if graph.contains_key(caller) && members.insert(*caller) {
                frontier.push(*caller);
            }
        }
    }
    members
}

fn static_edges(body: &LoweredBody) -> Vec<StaticEdge> {
    let mut edges = Vec::new();
    match body {
        LoweredBody::Extern { .. } => {}
        LoweredBody::Clauses { clauses, entries, .. } => {
            for clause in clauses {
                collect_step_edges(&clause.projections, &mut edges);
            }
            for entry in entries {
                collect_step_edges(&entry.steps, &mut edges);
                collect_tail_edges(&entry.tail, &mut edges);
            }
        }
    }
    edges.sort_by_key(|edge| {
        let rank = match edge {
            StaticEdge::Direct(_) => 0_u32,
            StaticEdge::Lambda(_) => 1_u32,
        };
        (edge.function().as_u32(), rank)
    });
    edges.dedup();
    edges
}

fn collect_step_edges(steps: &[LoweredStep], edges: &mut Vec<StaticEdge>) {
    for step in steps {
        match step {
            LoweredStep::Lambda { function, .. } => edges.push(StaticEdge::Lambda(*function)),
            LoweredStep::Const { .. }
            | LoweredStep::Tuple { .. }
            | LoweredStep::List { .. }
            | LoweredStep::Map { .. }
            | LoweredStep::MapUpdate { .. }
            | LoweredStep::Struct { .. }
            | LoweredStep::Bitstring { .. }
            | LoweredStep::FunctionRef { .. }
            | LoweredStep::BinaryOp { .. }
            | LoweredStep::UnaryOp { .. }
            | LoweredStep::MapIndex { .. }
            | LoweredStep::FieldAccess { .. }
            | LoweredStep::AssertLiteral { .. }
            | LoweredStep::AssertStruct { .. }
            | LoweredStep::RequireMapValue { .. }
            | LoweredStep::AssertTuple { .. }
            | LoweredStep::TupleField { .. }
            | LoweredStep::AssertEmptyList { .. }
            | LoweredStep::AssertSame { .. }
            | LoweredStep::SplitList { .. }
            | LoweredStep::BitstringInit { .. }
            | LoweredStep::BitstringRead { .. }
            | LoweredStep::AssertBitstringDone { .. } => {}
        }
    }
}

fn collect_tail_edges(tail: &LoweredTail, edges: &mut Vec<StaticEdge>) {
    match tail {
        LoweredTail::DirectCall { callee: function, .. } => edges.push(StaticEdge::Direct(*function)),
        LoweredTail::Value { .. }
        | LoweredTail::ClosureCall { .. }
        | LoweredTail::If { .. }
        | LoweredTail::Dispatch { .. }
        | LoweredTail::Receive(_)
        | LoweredTail::Halt { .. } => {}
    }
}

/// What THIS body's own entry dispatch asks about each of its inputs: the LOCAL
/// projection of `InputDemand`, before any forwarding join.
fn local_dispatch_mask(plan: &PatternDispatchPlan<Ty>) -> Vec<DispatchDemand> {
    let mut mask = vec![DispatchDemand::Ignore; plan.input_count];
    for arm in &plan.matrix.arms {
        for question in &arm.questions {
            mark_predicate_inputs(&plan.matrix.subjects, &question.predicate, &mut mask);
        }
    }
    for guard in &plan.guards {
        mark_guard_inputs(plan, guard, &mut mask);
    }
    mask
}

fn mark_predicate_inputs(subjects: &[Subject], predicate: &RegionPredicate<Ty>, mask: &mut [DispatchDemand]) {
    let demand = demand_for_region(&predicate.region);
    mark_subject_demand(subjects, predicate.subject, demand, mask);
}

fn demand_for_region(region: &Region<Ty>) -> DispatchDemand {
    match region {
        Region::List(ListRegion::Empty | ListRegion::Cons) => {
            DispatchDemand::ListShape(Box::new(DispatchDemand::Ignore))
        }
        Region::TupleArity(_) => DispatchDemand::TupleFields(BTreeMap::new()),
        Region::Equal(_)
        | Region::Type(_)
        | Region::MapKind
        | Region::MapKeyPresent { .. }
        | Region::Bitstring(_)
        | Region::Guard(_) => DispatchDemand::Whole,
    }
}

fn mark_subject_demand(subjects: &[Subject], subject: SubjectId, demand: DispatchDemand, mask: &mut [DispatchDemand]) {
    let Some((ordinal, path)) = subject_path(subjects, subject) else {
        return;
    };
    if let Some(slot) = mask.get_mut(ordinal as usize) {
        slot.join_assign(demand_at_path(&path, demand));
    }
}

fn subject_path(subjects: &[Subject], subject: SubjectId) -> Option<(u32, Vec<InputPathStep>)> {
    let subject = subjects.get(subject.0 as usize)?;
    match &subject.source {
        SubjectSource::Input { ordinal } => Some((*ordinal, Vec::new())),
        SubjectSource::Projection(projection) => {
            let (ordinal, mut path) = subject_path(subjects, projection.source)?;
            match &projection.kind {
                ProjectionKind::TupleField(field) => path.push(InputPathStep::TupleField(*field)),
                ProjectionKind::ListHead => path.push(InputPathStep::ListHead),
                ProjectionKind::ListTail => path.push(InputPathStep::ListTail),
                ProjectionKind::MapValue { key } => path.push(InputPathStep::MapValue(MapSelector::Known(
                    InputMapKey::from_ground(key),
                ))),
                ProjectionKind::BitstringField(index) => path.push(InputPathStep::BitstringField(
                    super::super::keying::BitstringSelector::Known(*index),
                )),
            }
            Some((ordinal, path))
        }
    }
}

fn demand_at_path(path: &[InputPathStep], demand: DispatchDemand) -> DispatchDemand {
    if demand == DispatchDemand::Ignore {
        return DispatchDemand::Ignore;
    }
    let Some((head, tail)) = path.split_first() else {
        return demand;
    };
    match head {
        InputPathStep::TupleField(field) => {
            let mut fields = BTreeMap::new();
            fields.insert(*field, demand_at_path(tail, demand));
            DispatchDemand::TupleFields(fields)
        }
        InputPathStep::ListHead => DispatchDemand::ListShape(Box::new(demand_at_path(tail, demand))),
        InputPathStep::ListTail => demand_at_path(tail, demand),
        InputPathStep::MapValue(_)
        | InputPathStep::MapKey(_)
        | InputPathStep::MapRemainder(_)
        | InputPathStep::BitstringField(_) => DispatchDemand::Whole,
    }
}

fn demand_below_path(demand: DispatchDemand, path: &[InputPathStep]) -> DispatchDemand {
    let Some((head, tail)) = path.split_first() else {
        return demand;
    };
    match (demand, head) {
        (DispatchDemand::Ignore, _) => DispatchDemand::Ignore,
        (DispatchDemand::Whole, _) => DispatchDemand::Whole,
        (DispatchDemand::TupleFields(mut fields), InputPathStep::TupleField(field)) => fields
            .remove(field)
            .map(|field_demand| demand_below_path(field_demand, tail))
            .unwrap_or(DispatchDemand::Ignore),
        (DispatchDemand::ListShape(element), InputPathStep::ListHead) => demand_below_path(*element, tail),
        (DispatchDemand::ListShape(element), InputPathStep::ListTail) => {
            demand_below_path(DispatchDemand::ListShape(element), tail)
        }
        (DispatchDemand::TupleFields(_) | DispatchDemand::ListShape(_), _) => DispatchDemand::Ignore,
    }
}

fn mark_guard_inputs(plan: &PatternDispatchPlan<Ty>, guard: &PatternGuardExpr<Ty>, mask: &mut [DispatchDemand]) {
    match guard {
        PatternGuardExpr::Const(_) | PatternGuardExpr::Pinned(_) => {}
        PatternGuardExpr::Subject(subject) => {
            mark_subject_demand(&plan.matrix.subjects, *subject, DispatchDemand::Whole, mask)
        }
        PatternGuardExpr::Unary { expr, .. } => mark_guard_inputs(plan, expr, mask),
        PatternGuardExpr::Binary { lhs, rhs, .. } => {
            mark_guard_inputs(plan, lhs, mask);
            mark_guard_inputs(plan, rhs, mask);
        }
        PatternGuardExpr::Dispatch { inputs, dispatch } => {
            for input in inputs {
                mark_guard_inputs(plan, input, mask);
            }
            for guard in &dispatch.plan.guards {
                mark_guard_inputs(&dispatch.plan, guard, mask);
            }
        }
    }
}
#[cfg(test)]
mod input_flow_tests {
    use super::super::super::body::{
        CallArg, ControlDestination, ControlEntryId, ControlEntryOrigin, LoweredClause, LoweredEntry, LoweredMapKey,
        ValueId,
    };
    use super::super::super::input_flow::{
        ValueLineage, ValueTransfer, collect_value_transfers, compose_paths, embed_lineage, map_entry_transfers,
    };
    use super::super::super::keying::{DirectCallFlow, InputBinding};
    use super::super::super::module_interface::{InterfaceCallableKind, ModuleInterface, ModuleInterfaceCallable};
    use super::super::super::protocol::{ProtocolCallbackImpl, ProtocolDispatchArm};
    use super::*;
    use crate::compiler2::{FactUse, Job};
    use crate::ground_value::GroundValue;
    use crate::source::Span;

    fn known(name: &str, value: u32) -> LoweredMapKey {
        LoweredMapKey {
            value: ValueId::from_u32(value),
            literal: Some(GroundValue::Atom(name.to_string())),
        }
    }

    fn dynamic(value: u32) -> LoweredMapKey {
        LoweredMapKey {
            value: ValueId::from_u32(value),
            literal: None,
        }
    }

    fn binding(origin: InputFlowOrigin, path: Box<[InputPathStep]>) -> InputBinding {
        InputBinding {
            origin,
            path,
            pullback: InputPullback::Structural,
        }
    }

    fn dependency_binding(origin: InputFlowOrigin, path: Box<[InputPathStep]>) -> InputBinding {
        InputBinding {
            origin,
            path,
            pullback: InputPullback::WholeOrigin,
        }
    }

    fn direct_call(callee: FunctionId, inputs: Vec<BTreeSet<InputBinding>>) -> DirectCallFlow {
        DirectCallFlow {
            callee,
            inputs: inputs.into_boxed_slice(),
        }
    }

    #[test]
    fn path_composition_preserves_prefixes_typed_intersections_and_remainders() {
        let a = InputMapKey::Atom("a".to_string());
        let b = InputMapKey::Atom("b".to_string());
        assert_eq!(
            compose_paths(
                &[InputPathStep::TupleField(1)],
                &[InputPathStep::TupleField(1), InputPathStep::ListHead],
            ),
            Some((vec![InputPathStep::ListHead].into_boxed_slice(), Box::default())),
        );
        assert_eq!(
            compose_paths(
                &[InputPathStep::MapRemainder(vec![a.clone()].into_boxed_slice())],
                &[InputPathStep::MapValue(MapSelector::Known(b.clone()))],
            ),
            Some((
                vec![InputPathStep::MapValue(MapSelector::Known(b))].into_boxed_slice(),
                Box::default(),
            )),
        );
        assert_eq!(
            compose_paths(
                &[InputPathStep::MapRemainder(vec![a.clone()].into_boxed_slice())],
                &[InputPathStep::MapValue(MapSelector::Known(a))],
            ),
            None,
        );
    }

    #[test]
    fn every_path_transform_preserves_bottom_demand() {
        let key = InputMapKey::Atom("a".to_string());
        let paths = [
            InputPathStep::TupleField(0),
            InputPathStep::ListHead,
            InputPathStep::ListTail,
            InputPathStep::MapValue(MapSelector::Known(key.clone())),
            InputPathStep::MapKey(MapSelector::Dynamic),
            InputPathStep::MapRemainder(vec![key].into_boxed_slice()),
            InputPathStep::BitstringField(super::super::super::keying::BitstringSelector::Dynamic),
        ];
        for path in paths {
            assert_eq!(demand_at_path(&[path], DispatchDemand::Ignore), DispatchDemand::Ignore);
        }
    }

    #[test]
    fn protocol_flow_publication_is_typed_staged_deduplicated_and_order_independent() {
        let mut world = World::new();
        let protocol = super::super::super::identity::ModuleId::GLOBAL;
        let callback = world.reference_function(protocol, "run", 2);
        let first_module = world.reference_module("A".to_string());
        let second_module = world.reference_module("B".to_string());
        let absent_module = world.reference_module("U".to_string());
        let first = world.reference_function(first_module, "run", 2);
        let second = world.reference_function(second_module, "run", 1);
        let arm = |target, function| ProtocolDispatchArm {
            target,
            callbacks: HashMap::from([(
                callback,
                ProtocolCallbackImpl {
                    function,
                    owner_module: target,
                },
            )]),
        };
        let relation = |arms| protocol_input_flow_relation(&world, callback, &ProtocolDispatch { arms });
        let expected = InputFlowRelation {
            local_dispatch: vec![DispatchDemand::Ignore; 2].into_boxed_slice(),
            flows: BTreeSet::from([
                InputFlow {
                    origin: InputFlowOrigin::Input(InputPosition::root(0)),
                    sink: InputFlowSink::ProtocolInput {
                        callee: first,
                        input: InputPosition::root(0),
                    },
                    pullback: InputPullback::Structural,
                },
                InputFlow {
                    origin: InputFlowOrigin::Input(InputPosition::root(1)),
                    sink: InputFlowSink::ProtocolInput {
                        callee: first,
                        input: InputPosition::root(1),
                    },
                    pullback: InputPullback::Structural,
                },
                InputFlow {
                    origin: InputFlowOrigin::Input(InputPosition::root(0)),
                    sink: InputFlowSink::ProtocolInput {
                        callee: second,
                        input: InputPosition::root(0),
                    },
                    pullback: InputPullback::Structural,
                },
            ]),
            ..InputFlowRelation::default()
        };
        let first_stage = relation(vec![arm(first_module, first)]);
        let second_stage = relation(vec![arm(first_module, first), arm(second_module, second)]);
        let empty_stage = relation(Vec::new());
        let duplicate_stage = relation(vec![
            arm(second_module, second),
            arm(first_module, first),
            arm(first_module, first),
        ]);
        let absent_stage = relation(vec![
            arm(second_module, second),
            arm(first_module, first),
            arm(first_module, first),
            ProtocolDispatchArm {
                target: absent_module,
                callbacks: HashMap::new(),
            },
        ]);
        assert_eq!(
            first_stage,
            InputFlowRelation {
                local_dispatch: vec![DispatchDemand::Ignore; 2].into_boxed_slice(),
                flows: expected
                    .flows
                    .iter()
                    .filter(|flow| {
                        matches!(flow.sink, InputFlowSink::ProtocolInput { callee, .. } if callee == first)
                    })
                    .cloned()
                    .collect(),
                ..InputFlowRelation::default()
            },
        );
        assert_ne!(
            first_stage, second_stage,
            "a newly reachable implementation adds exact typed edges"
        );
        assert!(
            first_stage.flows.is_subset(&second_stage.flows),
            "settled protocol dispatch grows monotonically as lazy implementations become reachable"
        );
        assert_eq!(second_stage, expected);
        assert_eq!(duplicate_stage, expected);
        assert_eq!(absent_stage, expected);
        assert_eq!(
            relation(vec![arm(second_module, second), arm(first_module, first)]),
            expected,
        );
        assert_eq!(
            relation(vec![ProtocolDispatchArm {
                target: first_module,
                callbacks: HashMap::new(),
            }]),
            InputFlowRelation {
                local_dispatch: vec![DispatchDemand::Ignore; 2].into_boxed_slice(),
                ..InputFlowRelation::default()
            },
        );

        let fact = FactKey::InputFlow(callback);
        let writer = Job::DeriveInputFlow(callback);
        let reader = Job::DeriveInputDemand(callback);
        world.define_protocol_callback(&callback, &protocol);
        let dispatch_fact = FactKey::ProtocolDispatch(protocol);
        let module_fact = FactKey::ModuleDefined(protocol);
        let module_job = Job::DefineModule(protocol);
        let tel = crate::telemetry::ConfiguredTelemetry::new();
        let publish = |world: &mut World, dispatch: ProtocolDispatch, expected: &InputFlowRelation| {
            let _ = world.complete_job(
                reader.clone(),
                JobEffects {
                    reads: vec![FactUse::current(fact.clone())],
                    ..JobEffects::default()
                },
            );
            let first_module_publication = !world.has_fact(&module_fact);
            let dispatch_changed = world.define_protocol_dispatch(protocol, dispatch);
            let mut changed = dispatch_changed
                .then_some(dispatch_fact.clone())
                .into_iter()
                .collect::<Vec<_>>();
            if first_module_publication {
                changed.push(module_fact.clone());
            }
            let _ = world.complete_job(
                module_job.clone(),
                JobEffects {
                    outputs: vec![module_fact.clone(), dispatch_fact.clone()],
                    changed,
                    ..JobEffects::default()
                },
            );
            let effects = derive_input_flow(world, &tel, callback).expect("protocol InputFlow derivation");
            let relation_changed = effects.changed == vec![fact.clone()];
            assert_eq!(world.input_flow(callback), Some(expected));
            let completion = world.complete_job(writer.clone(), effects);
            (
                relation_changed,
                world.fact_revision(&fact).expect("published InputFlow revision"),
                completion.wakes.iter().filter(|wake| wake.job == reader).count(),
                world
                    .input_flow(callback)
                    .expect("published InputFlow")
                    .local_dispatch
                    .as_ptr(),
            )
        };
        let (empty_changed, empty_revision, empty_wakes, _) =
            publish(&mut world, ProtocolDispatch { arms: Vec::new() }, &empty_stage);
        let (first_changed, first_revision, first_wakes, _) = publish(
            &mut world,
            ProtocolDispatch {
                arms: vec![arm(first_module, first)],
            },
            &first_stage,
        );
        let (second_changed, second_revision, second_wakes, retained) = publish(
            &mut world,
            ProtocolDispatch {
                arms: vec![arm(first_module, first), arm(second_module, second)],
            },
            &second_stage,
        );
        assert_eq!((empty_changed, first_changed, second_changed), (true, true, true));
        assert_eq!((empty_wakes, first_wakes, second_wakes), (1, 1, 1));
        assert!(empty_revision < first_revision && first_revision < second_revision);

        let (duplicate_changed, duplicate_revision, duplicate_wakes, duplicate_allocation) = publish(
            &mut world,
            ProtocolDispatch {
                arms: vec![
                    arm(second_module, second),
                    arm(first_module, first),
                    arm(first_module, first),
                ],
            },
            &duplicate_stage,
        );
        let pending_before = world.work_graph.pending_jobs();
        let (absent_changed, absent_revision, absent_wakes, absent_allocation) = publish(
            &mut world,
            ProtocolDispatch {
                arms: vec![
                    arm(second_module, second),
                    arm(first_module, first),
                    arm(first_module, first),
                    ProtocolDispatchArm {
                        target: absent_module,
                        callbacks: HashMap::new(),
                    },
                ],
            },
            &absent_stage,
        );
        assert_eq!((duplicate_changed, absent_changed), (false, false));
        assert_eq!((duplicate_wakes, absent_wakes), (0, 0));
        assert_eq!(
            (duplicate_revision, absent_revision),
            (second_revision, second_revision)
        );
        assert_eq!((duplicate_allocation, absent_allocation), (retained, retained));
        assert_eq!(world.work_graph.pending_jobs(), pending_before);
    }

    #[test]
    fn provider_boundary_relation_is_edge_empty_with_an_arity_sized_ignore_mask() {
        let mut world = World::new();
        let module = world.reference_module("External".to_string());
        let function = world.reference_function(module, "call", 2);
        let reference = world.function_ref(function).clone();
        world.submit_module_interface(
            "External".to_string(),
            ModuleInterface::new(vec![ModuleInterfaceCallable {
                function,
                reference,
                kind: InterfaceCallableKind::PublicFunction,
                variadic: false,
            }]),
        );
        let tel = crate::telemetry::ConfiguredTelemetry::new();
        let _ = super::super::super::drive::ExecutionContext::new(&mut world, &tel).drive();
        assert!(world.function_is_provider_boundary(function, &mut Vec::new()));

        let effects = derive_input_flow(&mut world, &tel, function).expect("provider InputFlow derivation");

        assert_eq!(effects.outputs, vec![FactKey::InputFlow(function)]);
        assert_eq!(
            world.input_flow(function),
            Some(&InputFlowRelation {
                local_dispatch: vec![DispatchDemand::Ignore; 2].into_boxed_slice(),
                ..InputFlowRelation::default()
            }),
        );
    }

    fn retained_provider_decisions() -> (
        World,
        super::super::super::identity::ModuleId,
        FunctionId,
        HashSet<super::super::super::drive::Job>,
    ) {
        let mut world = World::new();
        let module = world.reference_module("External".to_string());
        let function = world.reference_function(module, "call", 2);
        let reference = world.function_ref(function).clone();
        world.submit_module_interface(
            "External".to_string(),
            ModuleInterface::new(vec![ModuleInterfaceCallable {
                function,
                reference,
                kind: InterfaceCallableKind::PublicFunction,
                variadic: false,
            }]),
        );
        let tel = crate::telemetry::ConfiguredTelemetry::new();
        let _ = super::super::super::drive::ExecutionContext::new(&mut world, &tel).drive();
        let provider_reads = [
            FactKey::ModuleDefined(module),
            FactKey::FunctionDefined(function),
            FactKey::ModuleInterface(module),
        ]
        .map(super::super::super::facts::FactUse::current)
        .into_iter()
        .collect::<HashSet<_>>();

        let flow_producer = super::super::super::drive::Job::DeriveInputFlow(function);
        let effects = derive_input_flow(&mut world, &tel, function).expect("provider InputFlow derivation");
        assert_eq!(effects.reads.iter().cloned().collect::<HashSet<_>>(), provider_reads);
        let _ = world.complete_job(flow_producer.clone(), effects);

        let static_producer = super::super::super::drive::Job::DeriveStaticCallees(function);
        let effects = derive_static_callees(&mut world, &tel, function).expect("provider static-edge derivation");
        assert_eq!(effects.reads.iter().cloned().collect::<HashSet<_>>(), provider_reads);
        let _ = world.complete_job(static_producer.clone(), effects);

        let component_producer = super::super::super::drive::Job::DeriveCallGraphComponent(function);
        let effects = derive_call_graph_component(&mut world, function).expect("provider component derivation");
        assert_eq!(effects.reads.iter().cloned().collect::<HashSet<_>>(), provider_reads);
        let _ = world.complete_job(component_producer.clone(), effects);

        let caller = world.reference_function(super::super::super::identity::ModuleId::GLOBAL, "caller", 0);
        world.define_lowered_body(
            caller,
            LoweredBody::Clauses {
                clauses: Vec::new(),
                entries: vec![LoweredEntry {
                    span: Span::DUMMY,
                    origin: ControlEntryOrigin::Clause,
                    params: Vec::new(),
                    captures: Vec::new(),
                    reusable_cons_captures: Vec::new(),
                    steps: Vec::new(),
                    tail: LoweredTail::DirectCall {
                        value: ValueId::from_u32(0),
                        callsite: CallSiteId::from_u32(0),
                        callee: function,
                        args: Vec::new(),
                        dest: ControlDestination::Return,
                    },
                }],
                generated: Vec::new(),
            },
        );
        let lowered = FactKey::LoweredBody(caller);
        let _ = world.complete_job(
            super::super::super::drive::Job::LowerFunction(caller),
            JobEffects {
                outputs: vec![lowered.clone()],
                changed: vec![lowered],
                ..JobEffects::default()
            },
        );
        let target_producer = super::super::super::drive::Job::DeriveStaticCallees(caller);
        let effects = derive_static_callees(&mut world, &tel, caller).expect("caller static-edge derivation");
        assert!(provider_reads.iter().all(|read| effects.reads.contains(read)));
        let _ = world.complete_job(target_producer.clone(), effects);

        (
            world,
            module,
            function,
            HashSet::from([flow_producer, static_producer, component_producer, target_producer]),
        )
    }

    #[test]
    fn every_provider_classification_reacts_to_each_mutable_deciding_fact() {
        for movement in ["module", "function", "interface"] {
            let (mut world, module, function, producers) = retained_provider_decisions();
            let (job, fact) = match movement {
                "module" => (
                    super::super::super::drive::Job::DefineModule(module),
                    FactKey::ModuleDefined(module),
                ),
                "function" => (
                    super::super::super::drive::Job::DefineFunction(function),
                    FactKey::FunctionDefined(function),
                ),
                "interface" => {
                    assert!(world.define_module_interface(module, ModuleInterface::default()));
                    (
                        super::super::super::drive::Job::DefineModuleInterface(module),
                        FactKey::ModuleInterface(module),
                    )
                }
                _ => unreachable!(),
            };
            let completion = world.complete_job(
                job,
                JobEffects {
                    outputs: vec![fact.clone()],
                    changed: vec![fact],
                    ..JobEffects::default()
                },
            );
            assert_eq!(
                completion
                    .wakes
                    .iter()
                    .map(|wake| wake.job.clone())
                    .collect::<HashSet<_>>(),
                producers,
                "{movement} movement must invalidate every retained provider classification"
            );
        }
    }

    #[test]
    fn global_source_and_runtime_functions_add_no_provider_classification_reads() {
        let mut world = World::new();
        let global = world.reference_function(super::super::super::identity::ModuleId::GLOBAL, "global", 0);
        let runtime = world.reference_module("Utf8".to_string());
        let runtime_function = world.reference_function(runtime, "valid?", 1);
        let source = world.reference_module("Source".to_string());
        let source_function = world.reference_function(source, "run", 0);
        let code = world.submit_code(Some("source.fz".to_string()), String::new());
        world.index_module_body(
            source,
            code,
            super::super::super::identity::ModuleId::GLOBAL,
            "Source".to_string(),
            super::super::super::QuotedSourceRoot::empty(),
            super::super::super::quoted_surface::ScopeSurface {
                attrs: Vec::new(),
                forms: Vec::new(),
            },
        );

        for function in [global, source_function, runtime_function] {
            let mut reads = Vec::new();
            assert!(!world.function_is_provider_boundary(function, &mut reads));
            assert!(reads.is_empty());
        }
    }

    #[test]
    fn pending_static_callees_retains_the_external_classification_reads() {
        let mut world = World::new();
        let module = world.reference_module("External".to_string());
        let function = world.reference_function(module, "call", 1);
        let reference = world.function_ref(function).clone();
        world.submit_module_interface(
            "External".to_string(),
            ModuleInterface::new(vec![ModuleInterfaceCallable {
                function,
                reference,
                kind: InterfaceCallableKind::PublicFunction,
                variadic: false,
            }]),
        );
        let tel = crate::telemetry::ConfiguredTelemetry::new();

        let effects = derive_static_callees(&mut world, &tel, function).expect("pending static-edge derivation");

        assert_eq!(
            effects.reads,
            [
                FactKey::ModuleDefined(module),
                FactKey::FunctionDefined(function),
                FactKey::ModuleInterface(module),
            ]
            .map(super::super::super::facts::FactUse::current)
        );
        assert_eq!(
            effects.waits,
            vec![super::super::super::facts::FactUse::current(FactKey::ModuleDefined(
                module
            ))]
        );
        assert!(effects.outputs.is_empty());
    }

    #[test]
    fn input_flow_next_rung_waits_retain_the_upstream_fact_they_observed() {
        let tel = crate::telemetry::ConfiguredTelemetry::new();

        let mut protocol_world = World::new();
        let protocol = super::super::super::identity::ModuleId::GLOBAL;
        let callback = protocol_world.reference_function(protocol, "call", 1);
        protocol_world.define_protocol_callback(&callback, &protocol);
        let module = FactKey::ModuleDefined(protocol);
        let module_job = super::super::super::drive::Job::DefineModule(protocol);
        let _ = protocol_world.complete_job(
            module_job.clone(),
            JobEffects {
                outputs: vec![module.clone()],
                changed: vec![module.clone()],
                ..JobEffects::default()
            },
        );
        let callback_job = super::super::super::drive::Job::DeriveInputFlow(callback);
        let effects = derive_input_flow(&mut protocol_world, &tel, callback).expect("protocol InputFlow wait");
        assert_eq!(
            effects.reads,
            vec![super::super::super::facts::FactUse::current(module)]
        );
        assert_eq!(
            effects.waits,
            vec![super::super::super::facts::FactUse::current(FactKey::ProtocolDispatch(
                protocol
            ))]
        );
        let _ = protocol_world.complete_job(callback_job.clone(), effects);
        let retracted = protocol_world.complete_job(module_job, JobEffects::default());
        assert!(retracted.wakes.iter().any(|wake| wake.job == callback_job));

        let mut ordinary_world = World::new();
        let function = ordinary_world.reference_function(super::super::super::identity::ModuleId::GLOBAL, "body", 0);
        ordinary_world.define_lowered_body(
            function,
            LoweredBody::Clauses {
                clauses: Vec::new(),
                entries: Vec::new(),
                generated: Vec::new(),
            },
        );
        let lowered = FactKey::LoweredBody(function);
        let lowered_job = super::super::super::drive::Job::LowerFunction(function);
        let _ = ordinary_world.complete_job(
            lowered_job.clone(),
            JobEffects {
                outputs: vec![lowered.clone()],
                changed: vec![lowered.clone()],
                ..JobEffects::default()
            },
        );
        let flow_job = super::super::super::drive::Job::DeriveInputFlow(function);
        let effects = derive_input_flow(&mut ordinary_world, &tel, function).expect("ordinary InputFlow wait");
        assert_eq!(
            effects.reads,
            vec![super::super::super::facts::FactUse::current(lowered)]
        );
        assert_eq!(
            effects.waits,
            vec![super::super::super::facts::FactUse::current(FactKey::EntryDispatch(
                function
            ))]
        );
        let _ = ordinary_world.complete_job(flow_job.clone(), effects);
        let retracted = ordinary_world.complete_job(lowered_job, JobEffects::default());
        assert!(retracted.wakes.iter().any(|wake| wake.job == flow_job));
    }

    #[test]
    fn ordinary_missing_body_waits_for_lowering_instead_of_publishing_empty_flow() {
        let mut world = World::new();
        let function = world.reference_function(super::super::super::identity::ModuleId::GLOBAL, "pending", 1);
        let tel = crate::telemetry::ConfiguredTelemetry::new();

        let effects = derive_input_flow(&mut world, &tel, function).expect("missing body InputFlow demand");

        assert_eq!(
            effects.waits,
            vec![super::super::super::facts::FactUse::current(FactKey::LoweredBody(
                function
            ))]
        );
        assert!(effects.reads.is_empty());
        assert!(effects.outputs.is_empty());
        assert!(effects.changed.is_empty());
        assert_eq!(world.input_flow(function), None);
    }

    #[test]
    fn list_reconstruction_assigns_each_item_and_tail_one_exact_path() {
        let mut definitions = HashMap::new();
        let mut aliases = HashMap::new();
        collect_value_transfers(
            &LoweredStep::List {
                value: ValueId::from_u32(9),
                items: vec![ValueId::from_u32(1), ValueId::from_u32(2)],
                tail: Some(ValueId::from_u32(3)),
            },
            &mut definitions,
            &mut aliases,
        );
        let transfers = definitions.get(&ValueId::from_u32(9)).expect("list definition");
        let paths = transfers
            .iter()
            .filter_map(|transfer| match transfer {
                ValueTransfer::Embed { value, path } => Some((*value, path.clone())),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(
            paths,
            BTreeSet::from([
                (ValueId::from_u32(1), vec![InputPathStep::ListHead].into_boxed_slice()),
                (
                    ValueId::from_u32(2),
                    vec![InputPathStep::ListTail, InputPathStep::ListHead].into_boxed_slice(),
                ),
                (
                    ValueId::from_u32(3),
                    vec![InputPathStep::ListTail, InputPathStep::ListTail].into_boxed_slice(),
                ),
            ])
        );
    }

    #[test]
    fn map_writes_are_last_writer_and_dynamic_edges_exclude_later_known_keys() {
        let a = InputMapKey::Atom("a".to_string());
        let transfers = map_entry_transfers(&[
            (known("a", 1), ValueId::from_u32(11)),
            (dynamic(2), ValueId::from_u32(12)),
            (known("a", 3), ValueId::from_u32(13)),
        ]);
        assert!(!transfers.iter().any(|transfer| match transfer {
            ValueTransfer::Embed { value, .. } => *value == ValueId::from_u32(11),
            _ => false,
        }));
        assert!(transfers.iter().any(|transfer| match transfer {
            ValueTransfer::Embed { value, path } if *value == ValueId::from_u32(12) => {
                path.as_ref()
                    == [InputPathStep::MapValue(MapSelector::DynamicExcept(
                        vec![a.clone()].into_boxed_slice(),
                    ))]
            }
            _ => false,
        }));
        assert!(transfers.iter().any(|transfer| match transfer {
            ValueTransfer::EmbedWholeDependency { value, path } if *value == ValueId::from_u32(2) => {
                path.as_ref()
                    == [InputPathStep::MapKey(MapSelector::DynamicExcept(
                        vec![a.clone()].into_boxed_slice(),
                    ))]
            }
            _ => false,
        }));
    }

    #[test]
    fn nested_map_update_remainders_union_and_known_overwrites_disappear() {
        let a = InputMapKey::Atom("a".to_string());
        let b = InputMapKey::Atom("b".to_string());
        let lineage = ValueLineage {
            origin: InputFlowOrigin::Input(InputPosition::root(0)),
            destination: vec![InputPathStep::MapRemainder(vec![a.clone()].into_boxed_slice())].into_boxed_slice(),
            pullback: InputPullback::Structural,
        };
        let nested = embed_lineage(
            lineage,
            &[InputPathStep::MapRemainder(vec![b.clone()].into_boxed_slice())],
        )
        .expect("the retained base remainder survives");
        assert_eq!(
            nested.destination.as_ref(),
            [InputPathStep::MapRemainder(vec![a.clone(), b].into_boxed_slice())]
        );
        let overwritten = ValueLineage {
            origin: InputFlowOrigin::Input(InputPosition::root(0)),
            destination: vec![InputPathStep::MapValue(MapSelector::Known(a.clone()))].into_boxed_slice(),
            pullback: InputPullback::Structural,
        };
        assert!(embed_lineage(overwritten, &[InputPathStep::MapRemainder(vec![a].into_boxed_slice())]).is_none());
    }

    #[test]
    fn demand_solver_absorbs_recursive_structural_growth_in_the_finite_lattice() {
        let function = FunctionId::from_fn_id(crate::fz_ir::FnId(0));
        let callsite = CallSiteId::new(0, crate::source::Span::DUMMY);
        let relation = InputFlowRelation {
            local_dispatch: vec![DispatchDemand::Ignore].into_boxed_slice(),
            direct_calls: BTreeMap::from([(
                callsite,
                direct_call(
                    function,
                    vec![BTreeSet::from([binding(
                        InputFlowOrigin::Input(InputPosition {
                            input: 0,
                            path: vec![InputPathStep::TupleField(0)].into_boxed_slice(),
                        }),
                        Box::default(),
                    )])],
                ),
            )]),
            flows: BTreeSet::from([
                InputFlow {
                    origin: InputFlowOrigin::Input(InputPosition {
                        input: 0,
                        path: vec![InputPathStep::TupleField(0)].into_boxed_slice(),
                    }),
                    sink: InputFlowSink::FunctionReturn(Box::default()),
                    pullback: InputPullback::Structural,
                },
                InputFlow {
                    origin: InputFlowOrigin::CallResult {
                        callsite,
                        path: Box::default(),
                    },
                    sink: InputFlowSink::FunctionReturn(Box::default()),
                    pullback: InputPullback::Structural,
                },
            ]),
        };
        let graph = BTreeMap::from([(function, DemandNode { relation: &relation })]);
        assert_eq!(
            solve_demand_query_graph(&graph, function, DemandMode::Returned, DispatchDemand::Whole),
            vec![DispatchDemand::TupleFields(BTreeMap::from([(
                0,
                DispatchDemand::Whole,
            )]))]
        );
    }

    #[test]
    fn a_recursive_reconstructed_child_preserves_its_exact_return_path() {
        let function = FunctionId::from_fn_id(crate::fz_ir::FnId(0));
        let callsite = CallSiteId::new(0, crate::source::Span::DUMMY);
        let field = vec![InputPathStep::TupleField(0)].into_boxed_slice();
        let relation = InputFlowRelation {
            local_dispatch: Box::from([DispatchDemand::Ignore]),
            direct_calls: BTreeMap::from([(
                callsite,
                direct_call(
                    function,
                    vec![BTreeSet::from([binding(
                        InputFlowOrigin::Input(InputPosition {
                            input: 0,
                            path: field.clone(),
                        }),
                        field,
                    )])],
                ),
            )]),
            flows: BTreeSet::from([
                InputFlow {
                    origin: InputFlowOrigin::Input(InputPosition {
                        input: 0,
                        path: vec![InputPathStep::TupleField(0)].into_boxed_slice(),
                    }),
                    sink: InputFlowSink::FunctionReturn(Box::default()),
                    pullback: InputPullback::Structural,
                },
                InputFlow {
                    origin: InputFlowOrigin::CallResult {
                        callsite,
                        path: Box::default(),
                    },
                    sink: InputFlowSink::FunctionReturn(Box::default()),
                    pullback: InputPullback::Structural,
                },
            ]),
        };
        let graph = BTreeMap::from([(function, DemandNode { relation: &relation })]);

        assert_eq!(
            solve_demand_query_graph(&graph, function, DemandMode::Returned, DispatchDemand::Whole),
            vec![DispatchDemand::TupleFields(BTreeMap::from([(
                0,
                DispatchDemand::Whole,
            )]))]
        );
    }

    #[test]
    fn a_locally_supplied_recursive_argument_cannot_hide_a_whole_base_return() {
        let function = FunctionId::from_fn_id(crate::fz_ir::FnId(0));
        let callsite = CallSiteId::new(0, crate::source::Span::DUMMY);
        let relation = InputFlowRelation {
            local_dispatch: Box::from([DispatchDemand::Ignore]),
            direct_calls: BTreeMap::from([(callsite, direct_call(function, vec![BTreeSet::new()]))]),
            flows: BTreeSet::from([
                InputFlow {
                    origin: InputFlowOrigin::Input(InputPosition::root(0)),
                    sink: InputFlowSink::FunctionReturn(Box::default()),
                    pullback: InputPullback::Structural,
                },
                InputFlow {
                    origin: InputFlowOrigin::CallResult {
                        callsite,
                        path: Box::default(),
                    },
                    sink: InputFlowSink::FunctionReturn(Box::default()),
                    pullback: InputPullback::Structural,
                },
            ]),
        };
        let graph = BTreeMap::from([(function, DemandNode { relation: &relation })]);

        assert_eq!(
            solve_demand_query_graph(&graph, function, DemandMode::Returned, DispatchDemand::Whole),
            vec![DispatchDemand::Whole]
        );
    }

    #[test]
    fn a_local_recursive_call_cannot_hide_a_peer_call_that_carries_the_root() {
        let function = FunctionId::from_fn_id(crate::fz_ir::FnId(0));
        let local = CallSiteId::new(0, crate::source::Span::DUMMY);
        let carried = CallSiteId::new(1, crate::source::Span::DUMMY);
        let result_flow = |callsite| InputFlow {
            origin: InputFlowOrigin::CallResult {
                callsite,
                path: Box::default(),
            },
            sink: InputFlowSink::FunctionReturn(Box::default()),
            pullback: InputPullback::Structural,
        };
        let relation = InputFlowRelation {
            local_dispatch: Box::from([DispatchDemand::Ignore]),
            direct_calls: BTreeMap::from([
                (local, direct_call(function, vec![BTreeSet::new()])),
                (
                    carried,
                    direct_call(
                        function,
                        vec![BTreeSet::from([binding(
                            InputFlowOrigin::Input(InputPosition::root(0)),
                            Box::default(),
                        )])],
                    ),
                ),
            ]),
            flows: BTreeSet::from([
                InputFlow {
                    origin: InputFlowOrigin::Input(InputPosition::root(0)),
                    sink: InputFlowSink::FunctionReturn(Box::default()),
                    pullback: InputPullback::Structural,
                },
                result_flow(local),
                result_flow(carried),
            ]),
        };
        let graph = BTreeMap::from([(function, DemandNode { relation: &relation })]);

        assert_eq!(
            solve_demand_query_graph(&graph, function, DemandMode::Returned, DispatchDemand::Whole),
            vec![DispatchDemand::Whole]
        );
    }

    #[test]
    fn returned_demand_keeps_two_calls_to_one_callee_isolated() {
        let caller = FunctionId::from_fn_id(crate::fz_ir::FnId(0));
        let callee = FunctionId::from_fn_id(crate::fz_ir::FnId(1));
        let returned = CallSiteId::new(0, crate::source::Span::DUMMY);
        let discarded = CallSiteId::new(1, crate::source::Span::DUMMY);
        let caller_relation = InputFlowRelation {
            local_dispatch: vec![DispatchDemand::Ignore; 2].into_boxed_slice(),
            direct_calls: BTreeMap::from([
                (
                    returned,
                    direct_call(
                        callee,
                        vec![BTreeSet::from([binding(
                            InputFlowOrigin::Input(InputPosition::root(0)),
                            Box::default(),
                        )])],
                    ),
                ),
                (
                    discarded,
                    direct_call(
                        callee,
                        vec![BTreeSet::from([binding(
                            InputFlowOrigin::Input(InputPosition::root(1)),
                            Box::default(),
                        )])],
                    ),
                ),
            ]),
            flows: BTreeSet::from([InputFlow {
                origin: InputFlowOrigin::CallResult {
                    callsite: returned,
                    path: Box::default(),
                },
                sink: InputFlowSink::FunctionReturn(Box::default()),
                pullback: InputPullback::Structural,
            }]),
        };
        let callee_relation = InputFlowRelation {
            local_dispatch: vec![DispatchDemand::Ignore].into_boxed_slice(),
            flows: BTreeSet::from([InputFlow {
                origin: InputFlowOrigin::Input(InputPosition::root(0)),
                sink: InputFlowSink::FunctionReturn(Box::default()),
                pullback: InputPullback::Structural,
            }]),
            ..InputFlowRelation::default()
        };
        let graph = BTreeMap::from([
            (
                caller,
                DemandNode {
                    relation: &caller_relation,
                },
            ),
            (
                callee,
                DemandNode {
                    relation: &callee_relation,
                },
            ),
        ]);
        assert_eq!(
            solve_demand_query_graph(&graph, caller, DemandMode::Returned, DispatchDemand::Whole),
            vec![DispatchDemand::Whole, DispatchDemand::Ignore]
        );
    }

    #[test]
    fn returned_demand_pulls_a_dynamic_key_as_one_whole_dependency() {
        let caller = FunctionId::from_fn_id(crate::fz_ir::FnId(10));
        let callee = FunctionId::from_fn_id(crate::fz_ir::FnId(11));
        let callsite = CallSiteId::new(10, crate::source::Span::DUMMY);
        let caller_relation = InputFlowRelation {
            local_dispatch: vec![DispatchDemand::Ignore; 2].into_boxed_slice(),
            direct_calls: BTreeMap::from([(
                callsite,
                direct_call(
                    callee,
                    vec![BTreeSet::from([
                        binding(
                            InputFlowOrigin::Input(InputPosition {
                                input: 0,
                                path: vec![InputPathStep::MapValue(MapSelector::Dynamic)].into_boxed_slice(),
                            }),
                            Box::default(),
                        ),
                        dependency_binding(InputFlowOrigin::Input(InputPosition::root(1)), Box::default()),
                    ])],
                ),
            )]),
            flows: BTreeSet::from([InputFlow {
                origin: InputFlowOrigin::CallResult {
                    callsite,
                    path: Box::default(),
                },
                sink: InputFlowSink::FunctionReturn(Box::default()),
                pullback: InputPullback::Structural,
            }]),
        };
        let callee_relation = InputFlowRelation {
            local_dispatch: Box::from([DispatchDemand::Ignore]),
            flows: BTreeSet::from([InputFlow {
                origin: InputFlowOrigin::Input(InputPosition {
                    input: 0,
                    path: vec![InputPathStep::TupleField(0)].into_boxed_slice(),
                }),
                sink: InputFlowSink::FunctionReturn(Box::default()),
                pullback: InputPullback::Structural,
            }]),
            ..InputFlowRelation::default()
        };
        let graph = BTreeMap::from([
            (
                caller,
                DemandNode {
                    relation: &caller_relation,
                },
            ),
            (
                callee,
                DemandNode {
                    relation: &callee_relation,
                },
            ),
        ]);

        assert_eq!(
            solve_demand_query_graph(&graph, caller, DemandMode::Returned, DispatchDemand::Whole),
            vec![DispatchDemand::Whole, DispatchDemand::Whole],
        );
    }

    #[test]
    fn returned_demand_pulls_every_origin_of_a_reconstructed_dynamic_key() {
        let mut world = World::new();
        let caller = world.reference_function(super::super::super::identity::ModuleId::GLOBAL, "caller", 3);
        let callee = world.reference_function(super::super::super::identity::ModuleId::GLOBAL, "first", 1);
        let callsite = CallSiteId::new(20, Span::DUMMY);
        let key = ValueId::from_u32(10);
        let indexed = ValueId::from_u32(11);
        world.define_lowered_body(
            caller,
            LoweredBody::Clauses {
                clauses: vec![LoweredClause {
                    span: Span::DUMMY,
                    params: (0..3).map(ValueId::from_u32).collect(),
                    projections: Vec::new(),
                    entry: ControlEntryId::from_u32(0),
                }],
                entries: vec![LoweredEntry {
                    span: Span::DUMMY,
                    origin: ControlEntryOrigin::Clause,
                    params: Vec::new(),
                    captures: Vec::new(),
                    reusable_cons_captures: Vec::new(),
                    steps: vec![
                        LoweredStep::Tuple {
                            value: key,
                            items: vec![ValueId::from_u32(0), ValueId::from_u32(1)],
                        },
                        LoweredStep::MapIndex {
                            value: indexed,
                            base: ValueId::from_u32(2),
                            key: LoweredMapKey {
                                value: key,
                                literal: None,
                            },
                        },
                    ],
                    tail: LoweredTail::DirectCall {
                        value: ValueId::from_u32(12),
                        callsite,
                        callee,
                        args: vec![CallArg {
                            value: indexed,
                            ascription: None,
                        }],
                        dest: ControlDestination::Return,
                    },
                }],
                generated: Vec::new(),
            },
        );
        let caller_relation = super::super::super::input_flow::extract_input_flow_relation(
            &world,
            caller,
            vec![DispatchDemand::Ignore; 3].into_boxed_slice(),
        );
        let callee_relation = InputFlowRelation {
            local_dispatch: Box::from([DispatchDemand::Ignore]),
            flows: BTreeSet::from([InputFlow {
                origin: InputFlowOrigin::Input(InputPosition {
                    input: 0,
                    path: vec![InputPathStep::TupleField(0)].into_boxed_slice(),
                }),
                sink: InputFlowSink::FunctionReturn(Box::default()),
                pullback: InputPullback::Structural,
            }]),
            ..InputFlowRelation::default()
        };
        let graph = BTreeMap::from([
            (
                caller,
                DemandNode {
                    relation: &caller_relation,
                },
            ),
            (
                callee,
                DemandNode {
                    relation: &callee_relation,
                },
            ),
        ]);

        assert_eq!(
            solve_demand_query_graph(&graph, caller, DemandMode::Returned, DispatchDemand::Whole),
            vec![DispatchDemand::Whole, DispatchDemand::Whole, DispatchDemand::Whole],
        );
    }

    #[test]
    fn forwarded_result_demand_keeps_two_calls_to_one_callee_isolated() {
        let caller = FunctionId::from_fn_id(crate::fz_ir::FnId(0));
        let identity = FunctionId::from_fn_id(crate::fz_ir::FnId(1));
        let tester = FunctionId::from_fn_id(crate::fz_ir::FnId(2));
        let used = CallSiteId::new(0, crate::source::Span::DUMMY);
        let discarded = CallSiteId::new(1, crate::source::Span::DUMMY);
        let test = CallSiteId::new(2, crate::source::Span::DUMMY);
        let caller_relation = InputFlowRelation {
            local_dispatch: vec![DispatchDemand::Ignore; 2].into_boxed_slice(),
            direct_calls: BTreeMap::from([
                (
                    used,
                    direct_call(
                        identity,
                        vec![BTreeSet::from([binding(
                            InputFlowOrigin::Input(InputPosition::root(0)),
                            Box::default(),
                        )])],
                    ),
                ),
                (
                    discarded,
                    direct_call(
                        identity,
                        vec![BTreeSet::from([binding(
                            InputFlowOrigin::Input(InputPosition::root(1)),
                            Box::default(),
                        )])],
                    ),
                ),
                (
                    test,
                    direct_call(
                        tester,
                        vec![BTreeSet::from([binding(
                            InputFlowOrigin::CallResult {
                                callsite: used,
                                path: Box::default(),
                            },
                            Box::default(),
                        )])],
                    ),
                ),
            ]),
            flows: BTreeSet::new(),
        };
        let discarded_intrinsic = DispatchDemand::TupleFields(BTreeMap::from([(2, DispatchDemand::Whole)]));
        let identity_relation = InputFlowRelation {
            local_dispatch: vec![discarded_intrinsic.clone()].into_boxed_slice(),
            flows: BTreeSet::from([InputFlow {
                origin: InputFlowOrigin::Input(InputPosition::root(0)),
                sink: InputFlowSink::FunctionReturn(Box::default()),
                pullback: InputPullback::Structural,
            }]),
            ..InputFlowRelation::default()
        };
        let tester_relation = InputFlowRelation {
            local_dispatch: vec![DispatchDemand::Whole].into_boxed_slice(),
            ..InputFlowRelation::default()
        };
        let graph = BTreeMap::from([
            (
                caller,
                DemandNode {
                    relation: &caller_relation,
                },
            ),
            (
                identity,
                DemandNode {
                    relation: &identity_relation,
                },
            ),
            (
                tester,
                DemandNode {
                    relation: &tester_relation,
                },
            ),
        ]);
        assert_eq!(
            solve_demand_query_graph(&graph, caller, DemandMode::Dispatch, DispatchDemand::Ignore),
            vec![DispatchDemand::Whole, discarded_intrinsic]
        );
    }

    #[test]
    fn recursive_path_widening_preserves_unrelated_sibling_fields() {
        let function = FunctionId::from_fn_id(crate::fz_ir::FnId(0));
        let callsite = CallSiteId::new(0, crate::source::Span::DUMMY);
        let relation = InputFlowRelation {
            local_dispatch: vec![DispatchDemand::Ignore].into_boxed_slice(),
            direct_calls: BTreeMap::from([(
                callsite,
                direct_call(
                    function,
                    vec![BTreeSet::from([binding(
                        InputFlowOrigin::Input(InputPosition {
                            input: 0,
                            path: vec![InputPathStep::TupleField(0)].into_boxed_slice(),
                        }),
                        Box::default(),
                    )])],
                ),
            )]),
            flows: BTreeSet::from([
                InputFlow {
                    origin: InputFlowOrigin::Input(InputPosition {
                        input: 0,
                        path: vec![InputPathStep::TupleField(1)].into_boxed_slice(),
                    }),
                    sink: InputFlowSink::FunctionReturn(Box::default()),
                    pullback: InputPullback::Structural,
                },
                InputFlow {
                    origin: InputFlowOrigin::CallResult {
                        callsite,
                        path: Box::default(),
                    },
                    sink: InputFlowSink::FunctionReturn(Box::default()),
                    pullback: InputPullback::Structural,
                },
            ]),
        };
        let graph = BTreeMap::from([(function, DemandNode { relation: &relation })]);
        fn expected_growth(depth: usize) -> DispatchDemand {
            if depth == 0 {
                return DispatchDemand::Whole;
            }
            DispatchDemand::TupleFields(BTreeMap::from([
                (0, expected_growth(depth - 1)),
                (1, DispatchDemand::Whole),
            ]))
        }
        let depth = demand_recursion_plan(&graph, function).depth_bound;
        assert_eq!(
            solve_demand_query_graph(&graph, function, DemandMode::Returned, DispatchDemand::Whole),
            vec![expected_growth(depth)]
        );
    }

    #[test]
    fn acyclic_deep_paths_stay_exact_and_mutual_growth_is_order_independent() {
        fn nested_zero(depth: usize, leaf: DispatchDemand) -> DispatchDemand {
            (0..depth).fold(leaf, |demand, _| {
                DispatchDemand::TupleFields(BTreeMap::from([(0, demand)]))
            })
        }

        let functions = (0..8)
            .map(|raw| FunctionId::from_fn_id(crate::fz_ir::FnId(raw)))
            .collect::<Vec<_>>();
        let mut relations = BTreeMap::new();
        for (index, function) in functions.iter().copied().enumerate().rev() {
            let relation = if let Some(callee) = functions.get(index + 1).copied() {
                let callsite = CallSiteId::new(index as u32, crate::source::Span::DUMMY);
                InputFlowRelation {
                    local_dispatch: vec![DispatchDemand::Ignore].into_boxed_slice(),
                    direct_calls: BTreeMap::from([(
                        callsite,
                        direct_call(
                            callee,
                            vec![BTreeSet::from([binding(
                                InputFlowOrigin::Input(InputPosition {
                                    input: 0,
                                    path: vec![InputPathStep::TupleField(0)].into_boxed_slice(),
                                }),
                                Box::default(),
                            )])],
                        ),
                    )]),
                    flows: BTreeSet::from([InputFlow {
                        origin: InputFlowOrigin::CallResult {
                            callsite,
                            path: Box::default(),
                        },
                        sink: InputFlowSink::FunctionReturn(Box::default()),
                        pullback: InputPullback::Structural,
                    }]),
                }
            } else {
                InputFlowRelation {
                    local_dispatch: vec![DispatchDemand::Ignore].into_boxed_slice(),
                    flows: BTreeSet::from([InputFlow {
                        origin: InputFlowOrigin::Input(InputPosition {
                            input: 0,
                            path: vec![InputPathStep::TupleField(1)].into_boxed_slice(),
                        }),
                        sink: InputFlowSink::FunctionReturn(Box::default()),
                        pullback: InputPullback::Structural,
                    }]),
                    ..InputFlowRelation::default()
                }
            };
            relations.insert(function, relation);
        }
        let acyclic = relations
            .iter()
            .map(|(function, relation)| (*function, DemandNode { relation }))
            .collect();
        assert_eq!(
            solve_demand_query_graph(&acyclic, functions[0], DemandMode::Returned, DispatchDemand::Whole,),
            vec![nested_zero(
                functions.len() - 1,
                DispatchDemand::TupleFields(BTreeMap::from([(1, DispatchDemand::Whole)])),
            )]
        );

        let project = FunctionId::from_fn_id(crate::fz_ir::FnId(20));
        let twice = FunctionId::from_fn_id(crate::fz_ir::FnId(21));
        let four = FunctionId::from_fn_id(crate::fz_ir::FnId(22));
        let project_relation = InputFlowRelation {
            local_dispatch: vec![DispatchDemand::Ignore].into_boxed_slice(),
            flows: BTreeSet::from([InputFlow {
                origin: InputFlowOrigin::Input(InputPosition {
                    input: 0,
                    path: vec![InputPathStep::TupleField(0)].into_boxed_slice(),
                }),
                sink: InputFlowSink::FunctionReturn(Box::default()),
                pullback: InputPullback::Structural,
            }]),
            ..InputFlowRelation::default()
        };
        let repeated_relation = |callee: FunctionId, first_raw: u32, second_raw: u32| {
            let first = CallSiteId::new(first_raw, crate::source::Span::DUMMY);
            let second = CallSiteId::new(second_raw, crate::source::Span::DUMMY);
            InputFlowRelation {
                local_dispatch: vec![DispatchDemand::Ignore].into_boxed_slice(),
                direct_calls: BTreeMap::from([
                    (
                        first,
                        direct_call(
                            callee,
                            vec![BTreeSet::from([binding(
                                InputFlowOrigin::Input(InputPosition::root(0)),
                                Box::default(),
                            )])],
                        ),
                    ),
                    (
                        second,
                        direct_call(
                            callee,
                            vec![BTreeSet::from([binding(
                                InputFlowOrigin::CallResult {
                                    callsite: first,
                                    path: Box::default(),
                                },
                                Box::default(),
                            )])],
                        ),
                    ),
                ]),
                flows: BTreeSet::from([InputFlow {
                    origin: InputFlowOrigin::CallResult {
                        callsite: second,
                        path: Box::default(),
                    },
                    sink: InputFlowSink::FunctionReturn(Box::default()),
                    pullback: InputPullback::Structural,
                }]),
            }
        };
        let twice_relation = repeated_relation(project, 30, 31);
        let four_relation = repeated_relation(twice, 32, 33);
        let repeated = BTreeMap::from([
            (
                project,
                DemandNode {
                    relation: &project_relation,
                },
            ),
            (
                twice,
                DemandNode {
                    relation: &twice_relation,
                },
            ),
            (
                four,
                DemandNode {
                    relation: &four_relation,
                },
            ),
        ]);
        assert_eq!(
            solve_demand_query_graph(&repeated, four, DemandMode::Returned, DispatchDemand::Whole),
            vec![nested_zero(4, DispatchDemand::Whole)]
        );

        let mutual_relation = |callee: FunctionId, raw: u32, base: bool| {
            let callsite = CallSiteId::new(raw, crate::source::Span::DUMMY);
            let mut flows = BTreeSet::from([InputFlow {
                origin: InputFlowOrigin::CallResult {
                    callsite,
                    path: Box::default(),
                },
                sink: InputFlowSink::FunctionReturn(Box::default()),
                pullback: InputPullback::Structural,
            }]);
            if base {
                flows.insert(InputFlow {
                    origin: InputFlowOrigin::Input(InputPosition {
                        input: 0,
                        path: vec![InputPathStep::TupleField(1)].into_boxed_slice(),
                    }),
                    sink: InputFlowSink::FunctionReturn(Box::default()),
                    pullback: InputPullback::Structural,
                });
            }
            InputFlowRelation {
                local_dispatch: vec![DispatchDemand::Ignore].into_boxed_slice(),
                direct_calls: BTreeMap::from([(
                    callsite,
                    direct_call(
                        callee,
                        vec![BTreeSet::from([binding(
                            InputFlowOrigin::Input(InputPosition {
                                input: 0,
                                path: vec![InputPathStep::TupleField(0)].into_boxed_slice(),
                            }),
                            Box::default(),
                        )])],
                    ),
                )]),
                flows,
            }
        };
        let solve_mutual = |left_raw: u32, right_raw: u32, left_site: u32, right_site: u32| {
            let left = FunctionId::from_fn_id(crate::fz_ir::FnId(left_raw));
            let right = FunctionId::from_fn_id(crate::fz_ir::FnId(right_raw));
            let left_relation = mutual_relation(right, left_site, true);
            let right_relation = mutual_relation(left, right_site, false);
            let graph = BTreeMap::from([
                (
                    left,
                    DemandNode {
                        relation: &left_relation,
                    },
                ),
                (
                    right,
                    DemandNode {
                        relation: &right_relation,
                    },
                ),
            ]);
            solve_demand_query_graph(&graph, left, DemandMode::Returned, DispatchDemand::Whole)
        };
        let answer = solve_mutual(0, 1, 20, 21);
        assert_eq!(answer, solve_mutual(101, 17, 99, 3));
        assert!(matches!(
            answer.first(),
            Some(DispatchDemand::TupleFields(fields))
                if fields.get(&1) == Some(&DispatchDemand::Whole) && !fields.contains_key(&2)
        ));
    }

    #[test]
    fn recursive_normalization_is_extensive_monotone_and_idempotent() {
        fn below(left: &DispatchDemand, right: &DispatchDemand) -> bool {
            let mut joined = right.clone();
            joined.join_assign(left.clone());
            joined == *right
        }

        let samples = [
            DispatchDemand::Ignore,
            DispatchDemand::Whole,
            DispatchDemand::ListShape(Box::new(DispatchDemand::Whole)),
            DispatchDemand::TupleFields(BTreeMap::from([(
                0,
                DispatchDemand::TupleFields(BTreeMap::from([(1, DispatchDemand::Whole)])),
            )])),
        ];
        for depth in 0..=3 {
            for demand in &samples {
                let normalized = normalize_demand(demand.clone(), depth);
                assert!(below(demand, &normalized), "normalization must only add demand");
                assert_eq!(normalize_demand(normalized.clone(), depth), normalized);
            }
            for left in &samples {
                for right in &samples {
                    if below(left, right) {
                        assert!(below(
                            &normalize_demand(left.clone(), depth),
                            &normalize_demand(right.clone(), depth),
                        ));
                    }
                }
            }
        }
    }
}
