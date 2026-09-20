//! Jobs that derive the stable facts used for activation keying.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::dispatch_matrix::demand::{DemandPathStep, DispatchDemand};

use super::super::body::{CallInputMode, LoweredBody, LoweredStep, LoweredTail, ValueId};
use super::super::drive::{FactKey, JobEffects, current_uses};
use super::super::identity::FunctionId;
use std::rc::Rc;

use super::super::keying::{BodyKeying, InputDemand};
use super::super::return_skeleton::FunctionSkeleton;
use super::super::scheduler::FatalError;
use super::super::world::World;
use crate::telemetry::TelemetryExt as _;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StaticEdge {
    Direct(FunctionId),
    Construction(FunctionId),
}

impl StaticEdge {
    fn function(self) -> FunctionId {
        match self {
            StaticEdge::Direct(function) | StaticEdge::Construction(function) => function,
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
    if world.function_is_provider_boundary(function) {
        // A provider boundary has an interface but no body in this program:
        // no edges. The boundary test is not monotone -- a definition landing
        // later dissolves it -- so the conclusion subscribes to the facts it
        // consulted rather than freezing the filter's answer.
        let module = world.function_module(function);
        return Ok(publish_static_callees(
            world,
            function,
            Vec::new(),
            vec![FactKey::FunctionDefined(function), FactKey::ModuleDefined(module)],
        ));
    }
    if world.function_defined_revision(function).is_none() {
        if world.protocol_callback(function).is_some() {
            // A protocol callback is dispatched through, never lowered: it is
            // a leaf of the static graph, not a wait that would never resolve.
            return Ok(publish_static_callees(
                world,
                function,
                Vec::new(),
                vec![FactKey::FunctionDefined(function)],
            ));
        }
        let module = world.function_module(function);
        if !module.is_global() && world.module_defined_revision(module).is_none() {
            // Demand the scope that produces the `ModuleDefined` this site
            // waits on, not the body: `ensure_runtime_module`
            // mints a runtime module's code the first time the call graph
            // reaches it, instead of leaving that submission to whenever
            // `Job::DefineModule` happens to run. `ModuleDefined`'s sole
            // producer arm is `Job::DefineModule`; `demand_function_scope`'s
            // only other branch (`CodeScoped`, for `module.is_global()`) is
            // ruled out by the guard above.
            super::super::drive::ExecutionContext::new(world, tel).ensure_runtime_module(module);
            return Ok(JobEffects::wait_on_current(FactKey::ModuleDefined(module)));
        }
    }

    let lowered = FactKey::LoweredBody(function);
    if !world.has_fact(&lowered) {
        // One wait, for the one fact this derivation reads. `LoweredBody`'s
        // sole producer arm is `Job::LowerFunction`, and the chain behind it
        // (`DefineFunction` -> `ExpandFunctionSource` -> `demand_function_scope`)
        // is what scopes the code the body comes from. Waiting on
        // `FunctionDefined` first, as a separate rung, would buy nothing but
        // one more blocked evaluation per function.
        return Ok(JobEffects::wait_on_current(lowered));
    }
    let mut reads = vec![FactKey::FunctionDefined(function), lowered];
    let callees = body_static_callees(world, function, &mut reads);
    Ok(publish_static_callees(world, function, callees, reads))
}

/// The callees one lowered body names, in the order `static_edges` yields
/// them -- ascending by function id, so the published `Vec` is deterministic
/// by construction and adjacent duplicates (a function both called directly
/// and captured as a lambda) collapse without a second sort.
fn body_static_callees(world: &World, function: FunctionId, reads: &mut Vec<FactKey>) -> Vec<FunctionId> {
    let mut callees: Vec<FunctionId> = Vec::new();
    for edge in static_edges(&world.lowered_body(function)) {
        let target = edge.function();
        if world.function_is_provider_boundary(target) {
            // The boundary test consults the target's definedness, and it is
            // not monotone: a module or function defined later dissolves the
            // boundary. Record the read so that definition grows this edge
            // set instead of leaving the filter frozen in a fact.
            reads.push(FactKey::FunctionDefined(target));
            continue;
        }
        if matches!(edge, StaticEdge::Construction(_)) {
            reads.push(FactKey::FunctionDefined(target));
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
/// Callable construction is a static edge from the owner to its named or
/// generated function, so recursion through references and closures is handled
/// the same way as direct or mutual recursion.
pub(super) fn derive_call_graph_component(world: &mut World, function: FunctionId) -> Result<JobEffects, FatalError> {
    if world.function_is_provider_boundary(function) {
        // No body in this program: no edges, so the component is the function
        // alone and nothing it does can reach back to it.
        return Ok(publish_call_graph_node(
            world,
            function,
            function,
            BodyKeying { recursive: false },
            Vec::new(),
        ));
    }

    let mut reads = Vec::new();
    let mut waits = HashSet::new();
    let mut graph = HashMap::new();
    let mut seen = HashSet::new();
    collect_static_graph(world, function, &mut reads, &mut waits, &mut graph, &mut seen);
    // The component walk needs the body, which a `StaticCallees` fact
    // published for an undefined protocol callback does not imply.
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

/// One node of the input-demand graph: a body's OWN dispatch demand, and the
/// parameters it hands on unchanged.
#[derive(Debug, Clone, Default)]
struct DemandNode {
    local: Vec<DispatchDemand>,
    forwards: Vec<ForwardEdge>,
}

/// `slot` of this body is passed, UNCHANGED, as `callee`'s `callee_slot`th
/// input. Nothing else counts: a projection (`[head | tail]`), a construction
/// (`[head | acc]`) and a closure call are all opaque, so the value that
/// arrives at the callee is not the value this slot names.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ForwardEdge {
    slot: usize,
    callee: FunctionId,
    callee_slot: usize,
}

/// Derives which function inputs are DEMANDED -- by this body's own entry
/// dispatch, or by a callee this body forwards them to, transitively.
///
/// Dispatch demand alone answers "what does this body ASK about its inputs",
/// and that was never the question activation keying needs. The question is
/// "what does this activation's published return DEPEND on", and a body that
/// hands a parameter straight to a callee depends on everything that callee's
/// KEY names at that position: the element decides which callee activation is
/// reached, and therefore what comes back. `List.reduce_step/3` forwards its
/// list to `List.reduce_cont/3`, whose key is ground in the element, so the
/// element is part of `reduce_step/3`'s meaning even though `reduce_step/3`
/// dispatches only on its accumulator tag -- and without it two `Enum.reduce/3`
/// users share one activation and one JOINED return (fz-kdt.183, fz-kdt.122).
///
/// So the published demand is a JOIN over the `DispatchDemand` lattice
/// (`Ignore` < `ListShape`/`TupleFields` < `Whole`, `DispatchDemand::join_assign`):
/// the demand on slot `i` of `f` is `f`'s own local demand on `i` joined with
/// the demand on every position `g@j` that `f` forwards `i` to.
///
/// Forwarding is cyclic (`reduce_cont/3` <-> `reduce_step/3`), so this is a
/// least fixpoint, computed by Kleene iteration over the forwarding graph one walk
/// discovers -- the same shape `derive_call_graph_component` uses for the
/// strong component, and terminating for the same reason: the join is monotone
/// and no join deepens a demand tree past the deepest local mask in the graph,
/// which is a fixed finite depth once the graph is fixed.
///
/// The body's OWN demand is more than its entry dispatch, because a closure
/// call is a question too: the callable decides which body runs and that body
/// decides what it asks of the arguments, so a slot a closure call touches --
/// and a slot a lambda captures -- is demanded `Whole` before any forwarding
/// is joined in ([`join_closure_observations`]).
///
/// A slot NOT reached this way is freight: the body neither asks about it nor
/// hands it to anyone who does. It stays collapsed, which is what keeps one
/// activation for `loop(n, junk)` and one for `partition/4`'s two accumulators.
///
/// What a body asks of a slot by itself is an intermediate of this walk, not a
/// published answer: every consumer wants the question the whole reachable set
/// asks (see [`InputDemand`]).
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

    let demand = InputDemand {
        forwarded_dispatch: solve_forwarded_demand(&graph, function, |node| &node.local),
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

/// Walks the input FORWARDING graph from `function`: only a callee that receives
/// one of this body's parameters unchanged is entered, so the graph is a fraction
/// of the call graph and a body that forwards nothing reads exactly the facts
/// the local mask always needed.
fn collect_input_forwarding_graph(
    world: &World,
    function: FunctionId,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    graph: &mut BTreeMap<FunctionId, DemandNode>,
) {
    if graph.contains_key(&function) {
        return;
    }
    // `StaticCallees` is the fact whose producer scopes a runtime module and
    // settles the provider-boundary question; waiting on it first means this
    // walk never has to re-derive either.
    let callees = FactKey::StaticCallees(function);
    if !world.has_fact(&callees) {
        waits.insert(callees);
        return;
    }
    reads.push(callees);
    if let Some(callback) = world.protocol_callback(function) {
        collect_protocol_callback_node(world, function, callback.protocol, reads, waits, graph);
        return;
    }
    let lowered = FactKey::LoweredBody(function);
    if world.function_is_provider_boundary(function) || !world.has_fact(&lowered) {
        // No body in this program: it asks nothing and forwards nothing. Every
        // fact that conclusion rests on is READ -- including the module whose
        // definition dissolves the provider boundary -- so a definition landing
        // later grows the forwarding graph instead of leaving this answer frozen.
        reads.push(FactKey::FunctionDefined(function));
        reads.push(FactKey::ModuleDefined(world.function_module(function)));
        reads.push(lowered);
        graph.insert(function, DemandNode::default());
        return;
    }
    let dispatch = FactKey::EntryDispatch(function);
    if !world.has_fact(&dispatch) {
        // `EntryDispatch`'s sole producer arm is `Job::PlanEntryDispatch`
        // (`World::demand_fact_producer`).
        waits.insert(dispatch);
        return;
    }
    reads.push(dispatch);
    reads.push(lowered);
    // The plan states what it reads of its inputs; this walk raises that with
    // the questions a closure call asks, then joins it across the bodies a
    // value is forwarded to.
    let body = world.lowered_body(function);
    let mut local = world.entry_dispatch(function).input_demand().to_vec();
    let slots_of = direct_input_slots(&body, local.len());
    join_closure_observations(&body, &slots_of, &mut local);
    let forwards = forwarded_inputs(world, &body, &slots_of);
    let next = forwards.iter().map(|edge| edge.callee).collect::<Vec<_>>();
    graph.insert(function, DemandNode { local, forwards });
    for callee in next {
        collect_input_forwarding_graph(world, callee, reads, waits, graph);
    }
}

/// A protocol callback has no body: it is a NAME for the set of implementations
/// dispatch can reach. Every input is handed to every implementation unchanged,
/// so its demand is the join over them -- the same forwarding edge, one per
/// implementation.
///
/// This is a STATIC OVER-APPROXIMATION of a runtime dispatch, and the cost is
/// anti-monotone in the program: an unrelated `defimpl` that asks more about
/// its argument raises the demand of every forwarder that reaches the callback,
/// because the static arm set names it whether or not any value can reach it.
/// `ProtocolDispatch` is READ, so an implementation landing later grows this
/// demand rather than leaving the conclusion frozen.
fn collect_protocol_callback_node(
    world: &World,
    function: FunctionId,
    protocol: super::super::identity::ModuleId,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    graph: &mut BTreeMap<FunctionId, DemandNode>,
) {
    // The same rung order as `semantic::resolve_protocol_call`: `ModuleDefined`
    // first, because it is the arm-covered wait that can actually be produced;
    // `ProtocolDispatch` is a co-output of the same `Job::DefineModule` run
    // (`source_publish::publish_protocol_surface` pushes both into one
    // `JobEffects`), so it carries no arm of its own in
    // `World::demand_fact_producer` -- its demand rides `ModuleDefined`'s. A
    // waiter re-runs only when ALL of its waits are satisfied, so an arm-less
    // wait must never be the first rung.
    let protocol_fact = FactKey::ModuleDefined(protocol);
    if world.module_defined_revision(protocol).is_none() {
        waits.insert(protocol_fact);
        return;
    }
    reads.push(protocol_fact);
    let dispatch_fact = FactKey::ProtocolDispatch(protocol);
    let Some(dispatch) = world.protocol_dispatch(protocol) else {
        // `ModuleDefined(protocol)` is proven `Some` above, so the run that
        // claims this fact has already happened; defensive rather than
        // provably dead, exactly as the twin, and a bare wait rather than an
        // assert.
        waits.insert(dispatch_fact);
        return;
    };
    reads.push(dispatch_fact);
    let arity = world.function_arity(function);
    let mut forwards = Vec::new();
    for arm in &dispatch.arms {
        let Some(implementation) = arm.callbacks.get(&function).map(|target| target.function) else {
            continue;
        };
        for slot in 0..arity.min(world.function_arity(implementation)) {
            forwards.push(ForwardEdge {
                slot,
                callee: implementation,
                callee_slot: slot,
            });
        }
    }
    forwards.sort_unstable();
    forwards.dedup();
    let next = forwards.iter().map(|edge| edge.callee).collect::<Vec<_>>();
    graph.insert(
        function,
        DemandNode {
            local: vec![DispatchDemand::Ignore; arity],
            forwards,
        },
    );
    for callee in next {
        collect_input_forwarding_graph(world, callee, reads, waits, graph);
    }
}

/// The parameters this body hands on unchanged, and where they land.
///
/// A clause binds each of the function's semantic inputs to one `ValueId`
/// (`clause.params[i]`), and those ids are function-wide, so a direct call's
/// argument IS a parameter exactly when its value is one of them. A direct
/// call's args are its callee's inputs one-for-one (`CallInputMode::Direct`),
/// which is why the callee slot is the argument index.
fn forwarded_inputs(world: &World, body: &LoweredBody, slots_of: &HashMap<ValueId, Vec<usize>>) -> Vec<ForwardEdge> {
    let LoweredBody::Clauses { entries, .. } = body else {
        return Vec::new();
    };
    let mut edges = Vec::new();
    for entry in entries {
        let LoweredTail::DirectCall { callee, args, .. } = &entry.tail else {
            continue;
        };
        let callee_inputs = world.function_arity(*callee);
        for (arg_index, arg) in args.iter().enumerate() {
            let Some(callee_slot) = CallInputMode::Direct.semantic_index(callee_inputs, args.len(), arg_index) else {
                continue;
            };
            for slot in slots_of.get(&arg.value).into_iter().flatten().copied() {
                edges.push(ForwardEdge {
                    slot,
                    callee: *callee,
                    callee_slot,
                });
            }
        }
    }
    edges.sort_unstable();
    edges.dedup();
    edges
}

/// Every input slot a value names DIRECTLY -- the parameter itself, not a
/// piece of it. A projection reaches a slot at a non-empty path, so the value
/// standing there is no longer what the slot names, and neither forwarding nor
/// observation of the slot can be read off it.
fn direct_input_slots(body: &LoweredBody, input_count: usize) -> HashMap<ValueId, Vec<usize>> {
    input_positions(body, input_count)
        .into_iter()
        .map(|(value, positions)| {
            (
                value,
                positions
                    .into_iter()
                    .filter_map(|(slot, path)| path.is_empty().then_some(slot))
                    .collect::<Vec<_>>(),
            )
        })
        .collect()
}

/// Raises this body's own demand to `Whole` on every input a closure call
/// touches, and on every input a lambda closes over.
///
/// A closure call is a dispatch question about all of them. Which callable
/// arrived decides which body runs, so the called slot is asked about; and
/// that body -- which this one cannot know statically -- decides what it asks
/// of the arguments handed to it, so the honest answer for each argument is
/// the whole value. A lambda bakes the identity of what it captures into the
/// closure it builds, and that closure's consumers depend on the correlation,
/// so a captured input is asked about too.
///
/// `ClosureCall` only occurs as an entry tail and `Lambda` only as a step, so
/// the flat scan covers every dispatch arm, branch and receive clause.
fn join_closure_observations(
    body: &LoweredBody,
    slots_of: &HashMap<ValueId, Vec<usize>>,
    local: &mut [DispatchDemand],
) {
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return;
    };
    let mut touched = Vec::new();
    for entry in entries {
        if let LoweredTail::ClosureCall { callee, args, .. } = &entry.tail {
            touched.push(*callee);
            touched.extend(args.iter().map(|arg| arg.value));
        }
        touched.extend(entry.steps.iter().flat_map(lambda_captures).copied());
    }
    for clause in clauses {
        touched.extend(clause.projections.iter().flat_map(lambda_captures).copied());
    }
    for value in touched {
        for slot in slots_of.get(&value).into_iter().flatten().copied() {
            if let Some(demand) = local.get_mut(slot) {
                demand.join_assign(DispatchDemand::Whole);
            }
        }
    }
}

/// What a step closes over, which is nothing unless the step builds a lambda.
fn lambda_captures(step: &LoweredStep) -> &[ValueId] {
    match step {
        LoweredStep::Lambda { captures, .. } => captures,
        _ => &[],
    }
}

/// Every value that names an input position, and which position(s) it names.
///
/// A clause parameter names its own slot at the empty path; a projection step
/// names its source's position one step deeper. One value can name more than
/// one position -- `f(x, x)` binds one `ValueId` to two slots -- exactly as
/// `forwarded_inputs` records.
fn input_positions(body: &LoweredBody, input_count: usize) -> HashMap<ValueId, Vec<(usize, Vec<DemandPathStep>)>> {
    use super::super::executable_facts::{collect_callsite_return_origins, collect_value_origins};
    let LoweredBody::Clauses { clauses, .. } = body else {
        return HashMap::new();
    };
    let origins = collect_value_origins(body, &collect_callsite_return_origins(body));
    let mut positions = HashMap::<ValueId, Vec<(usize, Vec<DemandPathStep>)>>::new();
    for clause in clauses {
        for (slot, value) in clause.params.iter().copied().enumerate().take(input_count) {
            let known = positions.entry(value).or_default();
            let position = (slot, Vec::new());
            if !known.contains(&position) {
                known.push(position);
            }
        }
    }
    for value in origins.keys() {
        resolve_input_positions(body, *value, &origins, &mut positions, &mut HashSet::new());
    }
    positions
}

fn resolve_input_positions(
    body: &LoweredBody,
    value: ValueId,
    origins: &HashMap<ValueId, super::super::executable_facts::TransportOrigin>,
    positions: &mut HashMap<ValueId, Vec<(usize, Vec<DemandPathStep>)>>,
    visiting: &mut HashSet<ValueId>,
) -> Vec<(usize, Vec<DemandPathStep>)> {
    if let Some(known) = positions.get(&value) {
        return known.clone();
    }
    if !visiting.insert(value) {
        return Vec::new();
    }
    let found = origins
        .get(&value)
        .map(|origin| input_origin_positions(body, origin, origins, positions, visiting))
        .unwrap_or_default();
    visiting.remove(&value);
    positions.insert(value, found.clone());
    found
}

fn input_origin_positions(
    body: &LoweredBody,
    origin: &super::super::executable_facts::TransportOrigin,
    origins: &HashMap<ValueId, super::super::executable_facts::TransportOrigin>,
    positions: &mut HashMap<ValueId, Vec<(usize, Vec<DemandPathStep>)>>,
    visiting: &mut HashSet<ValueId>,
) -> Vec<(usize, Vec<DemandPathStep>)> {
    use super::super::executable_facts::TransportOrigin;
    let (source, path) = match origin {
        TransportOrigin::LocalValue(value) => (*value, Vec::new()),
        TransportOrigin::Projection { source, kind } => (*source, vec![kind]),
        TransportOrigin::OutcomeSubject { owner, subject } => {
            let (root, path) = body.dispatch_subject_origin(*owner, *subject);
            let super::super::body::SubjectOriginRoot::Value(value) = root else {
                return Vec::new();
            };
            (value, path)
        }
        TransportOrigin::Join(children) => {
            let mut all = children
                .iter()
                .flat_map(|child| input_origin_positions(body, child, origins, positions, visiting))
                .collect::<Vec<_>>();
            all.sort_unstable();
            all.dedup();
            return all;
        }
        _ => return Vec::new(),
    };
    let mut found = resolve_input_positions(body, source, origins, positions, visiting);
    for (_, steps) in &mut found {
        steps.extend(path.iter().copied().map(DemandPathStep::from));
    }
    found
}

/// The least fixpoint of the input-forwarding graph, projected onto `function`.
/// Kleene iteration joins each edge's callee demand into its caller slot and
/// stops when one pass changes nothing.
fn solve_forwarded_demand(
    graph: &BTreeMap<FunctionId, DemandNode>,
    function: FunctionId,
    axis: impl Fn(&DemandNode) -> &Vec<DispatchDemand>,
) -> Vec<DispatchDemand> {
    let mut demand = graph
        .iter()
        .map(|(id, node)| (*id, axis(node).clone()))
        .collect::<BTreeMap<_, _>>();
    loop {
        let mut changed = false;
        for (id, node) in graph {
            for edge in &node.forwards {
                let Some(inherited) = demand
                    .get(&edge.callee)
                    .and_then(|callee| callee.get(edge.callee_slot))
                    .cloned()
                else {
                    continue;
                };
                let Some(slot) = demand.get_mut(id).and_then(|mine| mine.get_mut(edge.slot)) else {
                    continue;
                };
                let before = slot.clone();
                slot.join_assign(inherited);
                changed |= *slot != before;
            }
        }
        if !changed {
            return demand.remove(&function).unwrap_or_default();
        }
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
            StaticEdge::Construction(_) => 1_u32,
        };
        (edge.function().as_u32(), rank)
    });
    edges.dedup();
    edges
}

fn collect_step_edges(steps: &[LoweredStep], edges: &mut Vec<StaticEdge>) {
    for step in steps {
        match step {
            LoweredStep::Lambda { function, .. } | LoweredStep::FunctionRef { function, .. } => {
                edges.push(StaticEdge::Construction(*function));
            }
            LoweredStep::Const { .. }
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

/// Derives one function's static shape: its return and each of its call
/// sites' arguments, written over its own input slots and its own call
/// results.
///
/// The answer depends on one body and nothing else, which is what makes the
/// closure below cheap: the walk that spans the call graph reads one
/// published skeleton per function instead of re-lowering every body it can
/// reach.
pub(super) fn derive_return_skeleton(world: &mut World, function: FunctionId) -> Result<JobEffects, FatalError> {
    let lowered = FactKey::LoweredBody(function);
    if !world.has_fact(&lowered) {
        if world.function_is_provider_boundary(function) {
            // No body in this program: it returns nothing this compilation
            // can name and hands nobody anything. Every fact that conclusion
            // rests on is READ, so a definition landing later re-derives it.
            let module = world.function_module(function);
            let reads = current_uses([
                FactKey::FunctionDefined(function),
                FactKey::ModuleDefined(module),
                lowered,
            ]);
            let changed = world.define_return_skeleton(function, Rc::new(FunctionSkeleton::default()));
            return Ok(JobEffects {
                reads,
                outputs: vec![FactKey::ReturnSkeleton(function)],
                changed: changed
                    .then_some(FactKey::ReturnSkeleton(function))
                    .into_iter()
                    .collect(),
                ..JobEffects::default()
            });
        }
        // `LoweredBody`'s sole producer arm is `Job::LowerFunction`.
        return Ok(JobEffects::wait_on_current(lowered));
    }
    let skeleton = Rc::new(super::super::return_skeleton::lower(&world.lowered_body(function)));
    let changed = world.define_return_skeleton(function, skeleton);
    Ok(JobEffects {
        reads: current_uses([lowered]),
        outputs: vec![FactKey::ReturnSkeleton(function)],
        changed: changed
            .then_some(FactKey::ReturnSkeleton(function))
            .into_iter()
            .collect(),
        ..JobEffects::default()
    })
}

/// Derives which of one function's positions the fixpoint is still solving.
///
/// A position is one the fixpoint solves when it sits on a cycle of the
/// skeleton graph that crosses a constructor, so the walk has to span the
/// call graph: a helper's slot joins its caller's cycle without either body
/// mentioning the other's return. The span is this function's own static
/// callees, transitively -- a cycle a position of this function sits on runs
/// through calls this function makes, so it lies inside that reach.
///
/// This is the fact a call site's key coordinate reads, and it is decided
/// before any activation exists. That is the whole point: an answer derived
/// from an activation's own companions would be derived from evidence the
/// answer then destroys, and the discovery would oscillate forever.
pub(super) fn derive_return_unknowns(world: &mut World, function: FunctionId) -> Result<JobEffects, FatalError> {
    let mut reads = Vec::new();
    let mut waits = HashSet::new();
    let mut skeletons = HashMap::new();
    let mut reached = vec![function];
    let mut next = 0;
    while next < reached.len() {
        let reached_function = reached[next];
        next += 1;
        // A DEFINED function's skeleton is waited on: keying must be decided
        // in its first round, and an answer published before a callee's shape
        // is visible would key that callee verbatim and mint the very ascent
        // this fact exists to prevent.
        //
        // A function this program has not defined is READ instead. Waiting on
        // one would demand a body for every function the static graph can
        // name -- including ones no activation ever reaches -- and a body
        // whose own definition chain never completes would wedge every caller
        // behind it. No call is keyed against such a function either: a caller
        // cannot resolve a call to a function it has no definition for, so by
        // the time the answer is asked for, the definition is there and this
        // read has already re-derived it.
        let fact = FactKey::ReturnSkeleton(reached_function);
        let Some(skeleton) = world.return_skeleton(reached_function).cloned() else {
            match world.function_defined_revision(reached_function).is_some() {
                true => waits.insert(fact),
                false => {
                    reads.push(fact);
                    continue;
                }
            };
            continue;
        };
        reads.push(fact);
        for (callee, _) in skeleton.callees.values().copied() {
            if !reached.contains(&callee) {
                reached.push(callee);
            }
        }
        skeletons.insert(reached_function, skeleton);
    }
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads: current_uses(reads),
            waits: current_uses(waits),
            ..JobEffects::default()
        });
    }
    let unknowns = Rc::new(super::super::return_unknowns::derive(&skeletons, function));
    let changed = world.define_return_unknowns(function, unknowns);
    Ok(JobEffects {
        reads: current_uses(reads),
        outputs: vec![FactKey::ReturnUnknowns(function)],
        changed: changed
            .then_some(FactKey::ReturnUnknowns(function))
            .into_iter()
            .collect(),
        ..JobEffects::default()
    })
}

#[cfg(test)]
#[path = "keying_test.rs"]
mod keying_test;
