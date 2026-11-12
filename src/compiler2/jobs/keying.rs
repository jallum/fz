//! Jobs that derive the stable facts used for activation keying.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::dispatch_matrix::demand::{DemandPathStep, DispatchDemand, demand_at_path, demand_within_path};

use super::super::body::{
    CallInputMode, ControlDestination, LoweredBody, LoweredStep, LoweredTail, ValueId, delivered_value_joins,
};
use super::super::drive::{AnswerUse, FactKey, Job, JobEffects, ProductAddress, UseCollector, current_uses};
use super::super::identity::{FunctionId, ModuleId};
use super::super::keying::{BodyKeying, InputDemand};
use super::super::pull::{ProductKey, ProductSessions, ProductValue};
use super::super::reach::ReachKey;
use super::super::scheduler::FatalError;
use super::super::world::{BodyShape, World};
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
/// True when `function` concludes immediately, with no gate at all: a
/// provider boundary has no body to derive edges from, an undefined
/// protocol callback is a leaf of the static graph by construction, never a
/// body waiting to be lowered, and an extern names no fz callees -- its
/// wire ABI lives on its contract, not a lowered body.
fn derive_static_callees_concludes_without_body(world: &World, function: FunctionId) -> bool {
    world.function_is_provider_boundary(function)
        || matches!(
            world.function_body_shape(function),
            BodyShape::ProtocolCallback | BodyShape::Extern
        )
}

/// The facts `derive_static_callees` cannot conclude without, once the
/// no-body cases above are ruled out: the module that would dissolve an
/// as-yet-undefined function's provider boundary, then the function's own
/// definition, then the lowered body its edges come from.
pub(super) fn derive_static_callees_gates(world: &World, function: FunctionId) -> Vec<FactKey> {
    if derive_static_callees_concludes_without_body(world, function) {
        return Vec::new();
    }
    let shape = world.function_body_shape(function);
    if let Some(gate) = shape.undefined_gate(function) {
        let module = world.function_module(function);
        if !module.is_global() && world.module_defined_revision(module).is_none() {
            return vec![FactKey::ModuleDefined(module)];
        }
        return vec![gate];
    }
    let lowered = FactKey::LoweredBody(function);
    if !world.has_fact(&lowered) {
        return vec![lowered];
    }
    Vec::new()
}

pub(super) fn derive_static_callees(world: &mut World, function: FunctionId) -> Result<JobEffects, FatalError> {
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
    match world.function_body_shape(function) {
        BodyShape::ProtocolCallback => {
            // A protocol callback is dispatched through, never lowered: it is
            // a leaf of the static graph, not a wait that would never resolve.
            return Ok(publish_static_callees(
                world,
                function,
                Vec::new(),
                vec![FactKey::FunctionDefined(function)],
            ));
        }
        BodyShape::Extern => {
            // An extern names no fz callees, known from its source head
            // alone: its wire ABI lives on its contract, and it never gets a
            // lowered body to derive edges from. The conclusion reads
            // nothing, so a later `FunctionDefined` does not re-run it.
            return Ok(publish_static_callees(world, function, Vec::new(), Vec::new()));
        }
        BodyShape::Unknown | BodyShape::Clauses => {}
    }

    if let Some(gate) = derive_static_callees_gates(world, function).into_iter().next() {
        return Ok(JobEffects::wait_on_current(gate));
    }

    let lowered = FactKey::LoweredBody(function);
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
        if matches!(edge, StaticEdge::Lambda(_)) {
            // A lambda target is an edge only once its generated function
            // exists. The conclusion consulted that fact, so it is read
            // whether or not it was there -- a definition that lands later
            // must be able to grow this edge set.
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

/// The functions one lowered body calls DIRECTLY -- never a lambda it merely
/// constructs. A constructed lambda is reached only once something calls it,
/// which is a different edge at a different function; naming it here would
/// have the module gate (`analyze_activation_gates`) wait on a module that
/// deciding whether to analyze this body never needs.
pub(super) fn direct_callees(world: &World, function: FunctionId) -> Vec<FunctionId> {
    static_edges(&world.lowered_body(function))
        .into_iter()
        .filter_map(|edge| match edge {
            StaticEdge::Direct(callee) => Some(callee),
            StaticEdge::Lambda(_) => None,
        })
        .collect()
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

/// Derives whether one function is RECURSIVE: does it reach itself through
/// the static call graph (`StaticCallees`), directly, mutually across a
/// cycle, or through a generated lambda? Lambda creation is a static edge
/// from the owner to the generated function, so recursion through a
/// generated closure is handled the same way as direct or mutual recursion.
///
/// The graph is not walked here: `function` is recursive exactly when it is
/// in its own static reach, a program-scoped product shared by every
/// function that asks (`ReachKey::Static`). Identity consumption is a
/// body-local property with no call-graph content, but it has always ridden
/// `FactKey::Recursive`'s one value and still does.
///
/// The facts `derive_recursive` cannot conclude without, for `function`
/// itself: its own static edges, and its own lowered body. Both are named
/// from `function` alone, so the scheduler checks them before ever starting
/// a never-run `DeriveRecursive` (`Job::missing_gates`). The reach of its
/// callees is a wait the job discovers on the product.
pub(super) fn derive_recursive_gates(world: &World, function: FunctionId) -> Vec<FactKey> {
    if world.function_is_provider_boundary(function) {
        return Vec::new();
    }
    let shape = world.function_body_shape(function);
    if let Some(gate) = shape.undefined_gate(function) {
        return vec![gate];
    }
    let mut gates = Vec::new();
    if !world.has_fact(&FactKey::StaticCallees(function)) {
        gates.push(FactKey::StaticCallees(function));
    }
    // Only `Clauses` ever gets a `LowerFunction` job: a protocol callback
    // stays undefined forever, and an extern's wire ABI lives on its
    // contract, so neither has a body to gate on here.
    if matches!(shape, BodyShape::Clauses) && !world.has_fact(&FactKey::LoweredBody(function)) {
        gates.push(FactKey::LoweredBody(function));
    }
    gates
}

pub(super) fn derive_recursive(
    world: &mut World,
    products: Option<&ProductSessions>,
    function: FunctionId,
) -> Result<JobEffects, FatalError> {
    if world.function_is_provider_boundary(function) {
        // No body in this program: no edges, so nothing it does can reach
        // back to it.
        return Ok(publish_recursive(
            world,
            function,
            BodyKeying {
                recursive: false,
                consumes_callable_identity: false,
            },
            Vec::new(),
        ));
    }

    // Identity consumption is a property of this body alone, so it rides the
    // same conclusion -- but it needs the body, which a `StaticCallees` fact
    // published for an undefined protocol callback does not imply. A protocol
    // callback and an extern both have no body to wait for: their identity
    // consumption is false by construction (checked below without reading
    // one).
    let mut reads = Vec::new();
    if matches!(world.function_body_shape(function), BodyShape::Clauses) {
        let lowered = FactKey::LoweredBody(function);
        if !world.has_fact(&lowered) {
            return Ok(JobEffects::wait_on_current(lowered));
        }
        reads.push(lowered);
    }

    let address = ProductAddress::program(ProductKey::Reach(ReachKey::Static(function)));
    let Some(ProductValue::Reach(reach)) = products.and_then(|sessions| sessions.product(&address)) else {
        return Ok(JobEffects {
            reads: current_uses(reads),
            product_waits: vec![address],
            ..JobEffects::default()
        });
    };
    let keying = BodyKeying {
        recursive: reach.contains(&ReachKey::Static(function)),
        consumes_callable_identity: body_consumes_callable_identity(world, function),
    };
    let mut effects = publish_recursive(world, function, keying, reads);
    effects.product_reads.push(address);
    Ok(effects)
}

fn publish_recursive(world: &mut World, function: FunctionId, keying: BodyKeying, reads: Vec<FactKey>) -> JobEffects {
    let keying_fact = FactKey::Recursive(function);
    let keying_changed = world.define_body_keying(function, keying);
    JobEffects {
        reads: current_uses(reads),
        outputs: vec![keying_fact.clone()],
        changed: keying_changed.then_some(keying_fact).into_iter().collect(),
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
    if !matches!(world.function_body_shape(function), BodyShape::Clauses) {
        // A protocol callback or an extern has no fz body to construct or
        // call through: neither captures nor dispatches callable identity.
        return false;
    }
    let LoweredBody::Clauses { clauses, entries, .. } = &*world.lowered_body(function);
    let step_constructs = |step: &LoweredStep| matches!(step, LoweredStep::Lambda { .. });
    entries
        .iter()
        .any(|entry| matches!(entry.tail, LoweredTail::ClosureCall { .. }) || entry.steps.iter().any(step_constructs))
        || clauses
            .iter()
            .any(|clause| clause.projections.iter().any(step_constructs))
}

/// One node of the input-demand graph: a body's OWN dispatch demand, and the
/// parameters it hands on unchanged.
#[derive(Debug, Clone, Default)]
struct DemandNode {
    local: Vec<DispatchDemand>,
    /// What the rest of this body does with its inputs, apart from its entry
    /// dispatch and the calls it forwards them to: a comparison reads one
    /// literal-blind, a closure call or a branch reads one whole. Joined with
    /// `local` on the forwarded axis only; `local` stays the plan's own
    /// question, which is what brand erasure asks.
    uses: Vec<DispatchDemand>,
    /// The positions this body's OWN returns are built from (fz-kdt.199),
    /// before any forwarding join.
    local_result: Vec<DispatchDemand>,
    forwards: Vec<ForwardEdge>,
}

/// The position `path` inside this body's `slot`th input reaches `callee`'s
/// `callee_slot`th input after `descent` more steps: `path` is empty for a
/// parameter passed on as it is, names the projection for `f(elem)`, and
/// `descent` names where a construction (`[head | acc]`) holds the position.
/// What the callee asks of the position comes back to the slot by the
/// descent, then the path ([`lifted_demand`]).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ForwardEdge {
    slot: usize,
    path: Vec<DemandPathStep>,
    descent: Vec<DemandPathStep>,
    callee: FunctionId,
    callee_slot: usize,
}

fn lifted_demand(edge: &ForwardEdge, callee: &DispatchDemand) -> DispatchDemand {
    let inside = demand_within_path(callee, &edge.descent);
    if !inside.asks_anything() {
        return DispatchDemand::Ignore;
    }
    demand_at_path(&edge.path, inside)
}

/// What a callee's returned demand asks of the caller's slot: only a slot
/// passed on as it is carries the callee's return back to the caller's own.
/// A position handed on (`f(elem)`) or held in a construction names a value
/// the caller's return is not built from, so it asks nothing of the slot.
fn returned_through_edge(edge: &ForwardEdge, callee: &DispatchDemand) -> DispatchDemand {
    if edge.path.is_empty() && edge.descent.is_empty() {
        callee.clone()
    } else {
        DispatchDemand::Ignore
    }
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
/// A callee's concluded `InputDemand` already is that join for the callee, so
/// the demand composes from callee answers: a caller reads each answer once and
/// never walks the callee's body ([`ForwardingWalk`]).
///
/// Forwarding is cyclic (`reduce_cont/3` <-> `reduce_step/3`), and neither half
/// of a cycle can wait for the other's answer. The half that runs second finds
/// the first already waiting on it -- a partner -- and walks the partner's body
/// itself, so the whole cycle is one least fixpoint, computed by Kleene
/// iteration over the graph that walk builds. It terminates because the join is
/// monotone and no join deepens a demand tree past the deepest mask in the
/// graph, which is a fixed finite depth once the graph is fixed. The partner
/// then reads the published answer and concludes too.
///
/// A slot NOT reached this way is freight: the body neither asks about it nor
/// hands it to anyone who does. It stays collapsed, which is what keeps one
/// activation for `loop(n, junk)` and one for `partition/4`'s two accumulators.
///
/// The LOCAL half publishes beside the forwarded one, because brand erasure
/// asks the local question and only the local question (see [`InputDemand`]).
/// The facts `derive_input_demand` cannot conclude without, for `function`
/// itself: its own static edges, then -- once neither a protocol callback nor
/// a bodyless conclusion applies -- its own entry dispatch plan. Callee
/// answers, and a partner's body facts, are waits [`ForwardingWalk`]
/// discovers, not named here.
pub(super) fn derive_input_demand_gates(world: &World, function: FunctionId) -> Vec<FactKey> {
    let callees = FactKey::StaticCallees(function);
    if !world.has_fact(&callees) {
        return vec![callees];
    }
    if world.protocol_callback(function).is_some() {
        return Vec::new();
    }
    let lowered = FactKey::LoweredBody(function);
    if world.function_is_provider_boundary(function) || !world.has_fact(&lowered) {
        return Vec::new();
    }
    let dispatch = FactKey::EntryDispatch(function);
    if !world.has_fact(&dispatch) {
        return vec![dispatch];
    }
    Vec::new()
}

pub(super) fn derive_input_demand(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
) -> Result<JobEffects, FatalError> {
    let mut walk = ForwardingWalk::new(world, function);
    walk.visit_body(function);
    let ForwardingWalk { uses, graph, .. } = walk;
    let (reads, waits) = uses.into_reads_waits();
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads,
            waits: waits.into_iter().collect(),
            ..JobEffects::default()
        });
    }

    let demand = InputDemand {
        local_dispatch: graph.get(&function).map(|node| node.local.clone()).unwrap_or_default(),
        forwarded_dispatch: solve_forwarded_demand(&graph, function, DemandNode::dispatch_and_uses, lifted_demand),
        returned: solve_forwarded_demand(
            &graph,
            function,
            |node| node.local_result.clone(),
            returned_through_edge,
        ),
    };
    emit_input_demand_derived(tel, &function, &demand);
    let changed = world.define_input_demand(function, demand);
    Ok(JobEffects {
        reads,
        outputs: vec![FactKey::InputDemand(function)],
        changed: changed.then_some(FactKey::InputDemand(function)).into_iter().collect(),
        ..JobEffects::default()
    })
}

/// One run's walk of the input FORWARDING graph from the function whose demand
/// it derives. Only a callee that receives one of a body's parameters
/// unchanged is entered, so the graph is a fraction of the call graph and a
/// body that forwards nothing reads exactly the facts its local mask needs.
///
/// A callee is met in one of three ways ([`World::answer_use`]):
///
/// - its `InputDemand` has concluded: that answer already is the join over
///   everything the callee forwards to, so it becomes a leaf of this graph and
///   the callee's body is never read;
/// - it is a partner, already waiting on this job: the two demands are one
///   fixpoint, so its body is walked here and the cycle is solved in this run;
/// - otherwise this run waits for its answer and publishes nothing.
struct ForwardingWalk<'w> {
    world: &'w mut World,
    uses: UseCollector,
    graph: BTreeMap<FunctionId, DemandNode>,
}

impl<'w> ForwardingWalk<'w> {
    fn new(world: &'w mut World, function: FunctionId) -> Self {
        Self {
            world,
            uses: UseCollector::new(Job::DeriveInputDemand(function)),
            graph: BTreeMap::new(),
        }
    }

    fn read(&mut self, fact: FactKey) {
        self.uses.read(fact);
    }

    fn wait(&mut self, fact: FactKey) {
        self.uses.wait(fact);
    }

    fn visit_callee(&mut self, callee: FunctionId) {
        if self.graph.contains_key(&callee) {
            return;
        }
        // Classified, not answered: a partner callee is walked whole below,
        // so its plain `InputDemand` fact is never itself a read. Recording
        // one here, the way `answer` would, would subscribe this walk to a
        // fact it otherwise never touches.
        let fact = FactKey::InputDemand(callee);
        match self.uses.classify(&*self.world, fact) {
            AnswerUse::Concluded(read) => {
                let answer = self
                    .world
                    .input_demand(callee)
                    .expect("a concluded InputDemand is present");
                let leaf = DemandNode {
                    local: answer.forwarded_dispatch.clone(),
                    uses: Vec::new(),
                    local_result: answer.returned.clone(),
                    forwards: Vec::new(),
                };
                self.uses.record_read(read);
                self.graph.insert(callee, leaf);
            }
            AnswerUse::Partner(_) => self.visit_body(callee),
            AnswerUse::Wait(wait) => self.uses.record_wait(wait),
        }
    }

    fn visit_body(&mut self, function: FunctionId) {
        if self.graph.contains_key(&function) {
            return;
        }
        // `StaticCallees` is the fact whose producer scopes a runtime module and
        // settles the provider-boundary question; waiting on it first means this
        // walk never has to re-derive either.
        let callees = FactKey::StaticCallees(function);
        if !self.world.has_fact(&callees) {
            self.wait(callees);
            return;
        }
        self.read(callees);
        if self.world.protocol_callback(function).is_some() {
            self.visit_protocol_callback(function);
            return;
        }
        if matches!(self.world.function_body_shape(function), BodyShape::Extern) {
            // An extern is a leaf, known from its source head: it has no fz
            // body to forward through, and that answer never changes, so
            // nothing here is read beyond the `StaticCallees` fact above. Its
            // result is typed by its declaration, never by which literal it
            // was handed, so it asks nothing of an argument: the forwarded
            // answer is `Ignore` per slot, while the entry-plan answer stays
            // empty, which keeps every brand it is handed.
            let node = DemandNode {
                uses: vec![DispatchDemand::Ignore; self.world.function_arity(function)],
                ..DemandNode::default()
            };
            self.graph.insert(function, node);
            return;
        }
        let lowered = FactKey::LoweredBody(function);
        if self.world.function_is_provider_boundary(function) || !self.world.has_fact(&lowered) {
            // No body in this program: it asks nothing and forwards nothing. Every
            // fact that conclusion rests on is READ -- including the module whose
            // definition dissolves the provider boundary -- so a definition landing
            // later grows the forwarding graph instead of leaving this answer frozen.
            self.read(FactKey::FunctionDefined(function));
            self.read(FactKey::ModuleDefined(self.world.function_module(function)));
            self.read(lowered);
            self.graph.insert(function, DemandNode::default());
            return;
        }
        let dispatch = FactKey::EntryDispatch(function);
        if !self.world.has_fact(&dispatch) {
            // `EntryDispatch`'s sole producer arm is `Job::PlanEntryDispatch`
            // (`World::demand_fact_producer`).
            self.wait(dispatch);
            return;
        }
        self.read(dispatch);
        self.read(lowered);
        // The plan states what it reads of its inputs; this walk only joins that
        // across the bodies a value is forwarded to.
        let world = &*self.world;
        let local = world.entry_dispatch(function).input_demand().to_vec();
        let local_result = return_flow_mask(world, function, local.len());
        let BodyFlows { uses, forwards } = body_flows(world, function, local.len());
        self.visit_node(
            function,
            DemandNode {
                local,
                uses,
                local_result,
                forwards,
            },
        );
    }

    /// A protocol callback has no body: it is a name dispatch resolves to an
    /// implementation. Its own question is which implementation to reach,
    /// and that is answered from the receiver's type: the receiver is `Class`
    /// when no implementation's target can tell one literal from another --
    /// the receiver's literals then pick no implementation -- and `Whole`
    /// otherwise.
    ///
    /// Everything else a call to the callback asks is asked by the
    /// implementation it reaches, so the callback hands every input, and what
    /// its result is built from, to the implementation of each arm of the
    /// protocol's dispatch (`resolve_protocol_call`, `jobs/semantic.rs`, picks
    /// one from the receiver's type and keys its activation with the
    /// implementation's own demand). A callback that asked nothing of an
    /// accumulator the implementation returns would let two callers that differ
    /// only in that literal share a key and blend their answers.
    ///
    /// The providers and the dispatch are read, so an implementation that lands
    /// later revises the answer.
    fn visit_protocol_callback(&mut self, function: FunctionId) {
        let callback = self
            .world
            .protocol_callback(function)
            .expect("a protocol callback is visited as one");
        let arity = self.world.function_arity(function);
        let receiver = self.receiver_demand(callback.protocol);
        let mut local = vec![DispatchDemand::Ignore; arity];
        if let Some(slot) = local.first_mut() {
            *slot = receiver;
        }
        // The implementation is reached by the receiver's type, and what it
        // does with the other inputs is not known here: it may hand an
        // accumulator back. Asking the implementation would make this answer
        // depend on which implementations have landed, so a revision of the
        // dispatch would re-key activations already made. The callback instead
        // states the conservative fact itself: every other input may flow into
        // the result.
        let mut local_result = vec![DispatchDemand::Whole; arity];
        if let Some(slot) = local_result.first_mut() {
            *slot = DispatchDemand::Ignore;
        }
        self.visit_node(
            function,
            DemandNode {
                local,
                uses: Vec::new(),
                local_result,
                forwards: Vec::new(),
            },
        );
    }

    fn receiver_demand(&mut self, protocol: ModuleId) -> DispatchDemand {
        self.read(FactKey::ProtocolImplProviders(protocol));
        let mut blind = true;
        for (target, _provider) in self.world.protocol_impl_providers(protocol) {
            let mut reads = Vec::new();
            let target_ty = self.world.module_impl_target_ty(target, &mut reads);
            for read in reads {
                self.read(read);
            }
            blind &= self.world.types().is_literal_blind(&target_ty);
        }
        if blind {
            DispatchDemand::Class
        } else {
            DispatchDemand::Whole
        }
    }

    fn visit_node(&mut self, function: FunctionId, node: DemandNode) {
        let next = node.forwards.iter().map(|edge| edge.callee).collect::<Vec<_>>();
        self.graph.insert(function, node);
        for callee in next {
            self.visit_callee(callee);
        }
    }
}

/// What the rest of a body does with its inputs: the demand its own uses put
/// on each slot, and the calls that carry a position on to a callee.
struct BodyFlows {
    uses: Vec<DispatchDemand>,
    forwards: Vec<ForwardEdge>,
}

/// One way a value is used, as far as the demand on an input is concerned.
#[derive(Debug, Clone)]
enum ValueUse {
    /// Read by something that asks this much of it.
    Asks(DispatchDemand),
    /// An argument of a direct call: the callee's demand is the demand.
    Call { callee: FunctionId, callee_slot: usize },
    /// Held by `container` at `step`: the container's demand, taken inside the
    /// step, is the demand.
    Within { container: ValueId, step: DemandPathStep },
    /// Delivered into `join`: the demand on the delivered value is the demand
    /// on the join.
    Alias(ValueId),
}

/// Every use of every input-derived value, classified.
///
/// A clause binds each of the function's semantic inputs to one `ValueId`
/// (`clause.params[i]`), and those ids are function-wide, so a use of a value
/// is a use of the input positions that value names ([`input_positions`]).
/// A direct call's args are its callee's inputs one-for-one
/// (`CallInputMode::Direct`), which is why the callee slot is the argument
/// index.
///
/// ```text
/// returned                        nothing: the returned axis asks it
/// a comparison, arithmetic        Class: the result cannot name a literal
/// a branch, closure-call argument Whole
/// a direct call's argument        what the callee asks, lifted back
/// a construction                  what its holder asks, taken inside it
/// ```
fn body_flows(world: &World, function: FunctionId, input_count: usize) -> BodyFlows {
    let body = world.lowered_body(function);
    let positions = input_positions(&body, input_count);
    let uses_of = value_uses(world, &body);
    let mut flows = BodyFlows {
        uses: vec![DispatchDemand::Ignore; input_count],
        forwards: Vec::new(),
    };
    for (value, held_at) in &positions {
        let mut asks = Vec::new();
        let mut calls = Vec::new();
        collect_demands(
            &uses_of,
            *value,
            &mut Vec::new(),
            &mut HashSet::new(),
            &mut asks,
            &mut calls,
            &mut Vec::new(),
        );
        for (slot, path) in held_at {
            for ask in &asks {
                if let Some(mine) = flows.uses.get_mut(*slot) {
                    mine.join_assign(demand_at_path(path, ask.clone()));
                }
            }
            for (callee, callee_slot, descent) in &calls {
                flows.forwards.push(ForwardEdge {
                    slot: *slot,
                    path: path.clone(),
                    descent: descent.clone(),
                    callee: *callee,
                    callee_slot: *callee_slot,
                });
            }
        }
    }
    flows.forwards.sort_unstable();
    flows.forwards.dedup();
    flows
}

/// Follows a value up through what holds it, to the reads and calls that
/// decide what is asked of it. `inside` is the path from the value that is
/// finally read down to `value`; `active` is the values on the way up to it.
///
/// A value reached again while it is still being followed, by a different
/// path, is held by a construction that feeds itself (`acc = [x | acc]`):
/// each trip around deepens the path, so what is asked of it is asked of the
/// whole value. Every other revisit repeats a path already followed.
fn collect_demands(
    uses_of: &HashMap<ValueId, Vec<ValueUse>>,
    value: ValueId,
    inside: &mut Vec<DemandPathStep>,
    seen: &mut HashSet<(ValueId, Vec<DemandPathStep>)>,
    asks: &mut Vec<DispatchDemand>,
    calls: &mut Vec<(FunctionId, usize, Vec<DemandPathStep>)>,
    active: &mut Vec<ValueId>,
) {
    if !seen.insert((value, inside.clone())) {
        return;
    }
    if active.contains(&value) {
        asks.push(DispatchDemand::Whole);
        return;
    }
    active.push(value);
    for usage in uses_of.get(&value).into_iter().flatten() {
        match usage {
            ValueUse::Asks(demand) => asks.push(demand_within_path(demand, inside)),
            ValueUse::Call { callee, callee_slot } => calls.push((*callee, *callee_slot, inside.clone())),
            ValueUse::Within { container, step } => {
                inside.insert(0, *step);
                collect_demands(uses_of, *container, inside, seen, asks, calls, active);
                inside.remove(0);
            }
            ValueUse::Alias(join) => collect_demands(uses_of, *join, inside, seen, asks, calls, active),
        }
    }
    active.pop();
}

fn value_uses(world: &World, body: &LoweredBody) -> HashMap<ValueId, Vec<ValueUse>> {
    let LoweredBody::Clauses { clauses, entries, .. } = body;
    let joins = delivered_value_joins(body);
    let mut uses = HashMap::<ValueId, Vec<ValueUse>>::new();
    let mut add = |value: ValueId, usage: ValueUse| uses.entry(value).or_default().push(usage);
    for step in clauses
        .iter()
        .flat_map(|clause| clause.projections.iter())
        .chain(entries.iter().flat_map(|entry| entry.steps.iter()))
    {
        step_value_uses(step, &mut add);
    }
    for entry in entries {
        tail_value_uses(world, &entry.tail, &joins, &mut add);
    }
    uses
}

fn step_value_uses(step: &LoweredStep, add: &mut impl FnMut(ValueId, ValueUse)) {
    use super::super::body::LoweredBitSize;
    let whole = || ValueUse::Asks(DispatchDemand::Whole);
    let class = || ValueUse::Asks(DispatchDemand::Class);
    let within = |container: ValueId, step: DemandPathStep| ValueUse::Within { container, step };
    match step {
        // A projection's result is a position of its source
        // (`input_positions`), so what asks of the result asks of the source
        // there, and the source is asked nothing more.
        LoweredStep::Const { .. }
        | LoweredStep::FunctionRef { .. }
        | LoweredStep::TupleField { .. }
        | LoweredStep::SplitList { .. }
        | LoweredStep::FieldAccess { .. }
        | LoweredStep::RequireMapValue { .. } => {}
        // Leaving a `try` reads no value.
        LoweredStep::PopHandler => {}
        LoweredStep::Tuple { value, items } => {
            for (index, item) in items.iter().enumerate() {
                add(item.value, within(*value, DemandPathStep::TupleField(index as u32)));
            }
        }
        LoweredStep::List { value, items, tail, .. } => {
            for item in items {
                add(*item, within(*value, DemandPathStep::ListHead));
            }
            if let Some(tail) = tail {
                add(*tail, within(*value, DemandPathStep::ListTail));
            }
        }
        LoweredStep::Map { value, entries, .. } => {
            for (key, item) in entries {
                add(key.value, whole());
                add(*item, within(*value, DemandPathStep::MapValue));
            }
        }
        LoweredStep::MapUpdate { value, base, entries } => {
            add(*base, whole());
            for (key, item) in entries {
                add(key.value, whole());
                add(*item, within(*value, DemandPathStep::MapValue));
            }
        }
        LoweredStep::Struct { value, fields, .. } => {
            for (_name, item) in fields {
                add(*item, within(*value, DemandPathStep::StructField));
            }
        }
        LoweredStep::Bitstring { fields, .. } => {
            for field in fields {
                add(field.value, whole());
                if let Some(size) = field.spec.size.as_ref().and_then(LoweredBitSize::read_value) {
                    add(size, whole());
                }
            }
        }
        LoweredStep::Lambda { function, captures, .. } => {
            // The captures are the lambda's leading inputs, so what the lambda
            // asks of them is what the capturing body is asked.
            for (callee_slot, capture) in captures.iter().enumerate() {
                add(
                    *capture,
                    ValueUse::Call {
                        callee: *function,
                        callee_slot,
                    },
                );
            }
        }
        LoweredStep::BinaryOp { left, right, .. } => {
            add(*left, class());
            add(*right, class());
        }
        LoweredStep::UnaryOp { input, .. } => add(*input, class()),
        LoweredStep::MapIndex { base, key, .. } => {
            add(*base, whole());
            add(key.value, if key.literal.is_some() { class() } else { whole() });
        }
        LoweredStep::BitstringInit { source, .. } => add(*source, whole()),
        LoweredStep::BitstringRead { reader, spec, .. } => {
            add(*reader, whole());
            if let Some(size) = spec.size.as_ref().and_then(LoweredBitSize::read_value) {
                add(size, whole());
            }
        }
    }
}

fn tail_value_uses(
    world: &World,
    tail: &LoweredTail,
    joins: &HashMap<super::super::body::ControlEntryId, super::super::body::DeliveredValueJoin>,
    add: &mut impl FnMut(ValueId, ValueUse),
) {
    let whole = || ValueUse::Asks(DispatchDemand::Whole);
    match tail {
        LoweredTail::Value { value, dest } => match dest {
            ControlDestination::Return => {}
            ControlDestination::Deliver(entry) => match joins.get(entry) {
                Some(join) => add(*value, ValueUse::Alias(join.value)),
                None => add(*value, whole()),
            },
        },
        LoweredTail::DirectCall { callee, args, .. } => {
            let callee_inputs = world.function_arity(*callee);
            for (arg_index, arg) in args.iter().enumerate() {
                match CallInputMode::Direct.semantic_index(callee_inputs, args.len(), arg_index) {
                    Some(callee_slot) => add(
                        arg.value,
                        ValueUse::Call {
                            callee: *callee,
                            callee_slot,
                        },
                    ),
                    None => add(arg.value, whole()),
                }
            }
        }
        LoweredTail::ClosureCall { args, .. } => {
            // The callee is not a literal the call can read: which closure it
            // is has its own question (brand erasure), and what it captured
            // widens with the rest of the key.
            for arg in args {
                add(arg.value, whole());
            }
        }
        LoweredTail::If { cond, .. } => add(*cond, whole()),
        LoweredTail::Dispatch {
            inputs,
            bindings,
            dispatch,
        } => {
            let asked = dispatch.plan.input_demand();
            for (input, demand) in inputs.iter().zip(asked) {
                if demand.asks_anything() {
                    add(*input, ValueUse::Asks(demand.clone()));
                }
            }
            for value in bindings.pinned.iter().chain(&bindings.prepared) {
                add(*value, whole());
            }
        }
        LoweredTail::Receive(receive) => {
            for value in receive.bindings.pinned.iter().chain(&receive.bindings.prepared) {
                add(*value, whole());
            }
            if let Some(after) = &receive.after {
                add(after.timeout, whole());
            }
        }
        // A `try` moves control into its body under a handler; it reads no
        // value, and what its body and handler read is read by their entries.
        LoweredTail::Try { .. } | LoweredTail::Unreachable => {}
    }
}

/// The input positions this body's OWN returns are built from: the LOCAL half
/// of the `returned` axis (fz-kdt.199), before any forwarding join.
///
/// fz-kdt.183 asked "does anything on the forwarding chain DISPATCH on this
/// slot", and a slot nothing dispatches on is freight -- collapsed, so two
/// callers key one activation. That is sound for a slot the activation only
/// carries, and unsound the moment the activation RETURNS it: an activation
/// publishes ONE return, so two callers that reach one activation read one
/// JOINED return, and a returned position the key erased is a position on
/// which two callers' answers blend. `loop(0, junk), do: junk` at `[1, 2]` and
/// at `["a", "b"]` keys one activation whose published return is
/// `non_empty_list(int) | non_empty_list(binary)`, and `walk({:done, acc}, n)`
/// -- the tuple-field shape, where the key names the TAG and the return IS the
/// payload -- does the same one field down.
///
/// So a position is on this axis when the returned value IS it, CONTAINS it,
/// or is a PROJECTION of it:
///
/// ```text
/// defp f({:done, acc}, _n), do: acc          -- projection: slot 0, field 1
/// defp f([], acc, _r), do: {:done, acc}      -- containment: slot 1
/// def loop(0, junk), do: junk               -- identity:    slot 1
/// ```
///
/// Everything else is opaque and contributes nothing: a call result, a closure
/// call, an arithmetic result, a constant, a constructed lambda's captures
/// (that is fz-kdt.165's callable axis, not this one). A call whose result is
/// returned needs no rule here -- the forwarding edge already joins the
/// callee's whole demand into the caller's slot, and the callee's own returned
/// axis rides that join.
///
/// That join rides `forwarded_inputs`, which is fz-kdt.183's DISPATCH edge
/// set, and this axis inherits its three holes -- all measured, all cost or
/// missed cure rather than unsoundness, and all owned by fz-kdt.214. It
/// ignores a `LoweredTail::DirectCall`'s `dest`, so a slot handed to a call
/// whose result is DELIVERED and discarded is keyed anyway (a body returning
/// the constant `0` goes 7 -> 9 executables). A RECONSTRUCTED argument is not
/// a forward edge, so `outer({:go, acc}, n), do: mid({:go, acc}, n)` splits
/// `mid` and `inner` while `outer` stays collapsed and re-joins -- two keys
/// that both publish the join. A PROJECTED argument is not one either, so a
/// protocol callback handed `acc` rather than a whole parameter stays
/// uncured.
fn return_flow_mask(world: &World, function: FunctionId, input_count: usize) -> Vec<DispatchDemand> {
    let mut mask = vec![DispatchDemand::Ignore; input_count];
    let body = world.lowered_body(function);
    let LoweredBody::Clauses { clauses, entries, .. } = &*body;
    let origins = input_positions(&body, input_count);
    let rebuilt = recursion_supplied_positions(function, entries, &origins, input_count);
    for (slot, path) in returned_values(&body, clauses, entries)
        .iter()
        .filter_map(|value| origins.get(value))
        .flatten()
        .filter(|position| !rebuilt.contains(*position))
    {
        if let Some(demand) = mask.get_mut(*slot) {
            demand.join_assign(demand_at_path(path, DispatchDemand::Whole));
        }
    }
    mask
}

/// The input slots `function`'s recursion supplies WHOLE: each is rebuilt by a
/// self call rather than carried, so what a self call hands it is a state of
/// the ascent and not a caller's choice.
///
/// Only a call made from inside `function`'s own body asks, and a body that is
/// being analysed is lowered, so the body is always there to read.
pub(super) fn supplied_whole_slots(world: &World, function: FunctionId, input_count: usize) -> Vec<usize> {
    let body = world.lowered_body(function);
    let LoweredBody::Clauses { entries, .. } = &*body;
    let origins = input_positions(&body, input_count);
    recursion_supplied_positions(function, entries, &origins, input_count)
        .into_iter()
        .filter(|(_, path)| path.is_empty())
        .map(|(slot, _)| slot)
        .collect()
}

/// The positions the RECURSION itself supplies, as a LEAST FIXPOINT: a
/// position is supplied when a self-call hands it a value the caller held
/// nowhere, or held only at positions that are themselves supplied.
///
/// The fixpoint is what makes the rule sound. An eager rule -- "the
/// caller did not hold this value at this same position, so the position is
/// rebuilt" -- misreads a PERMUTATION. `go(n - 1, b, a)` hands each slot a
/// value the caller held at the OTHER slot, which supplies neither, and the
/// eager rule marks both (and poisons both, since each is held elsewhere).
/// Measured: `go(0, a, _b), do: a` at `["x"]` and at `[9]` then blends into
/// one key publishing `non_empty_list(binary) | non_empty_list(int)`, the
/// exact defect this axis exists to remove. Under the fixpoint the
/// permutation's obligations never discharge, the set settles empty, and
/// `go/3` keys its two users apart.
///
/// A supplied position is keyed by the CALLER, never by the recursion. An
/// accumulator visits `[]` and then `list(tau)` within ONE caller, and those
/// different denotations intern apart, so letting each self call key the slot
/// from the type it hands over mints one activation per state and k
/// accumulators mint their product. Instead a self call keeps its own
/// activation's column at a supplied whole slot (`supplied_whole_slots`): the
/// outside caller's seed is what tells callers apart, the self call stays in
/// the activation it was made from, and the type it hands over still joins that
/// activation's input evidence. `walk/2` keys one activation per outside seed.
///
/// A position the recursion does NOT supply is constant along the ascent, so
/// two keys there ARE two callers -- `loop(n, junk)`'s junk, the two slots
/// `go/3` permutes, and the payload of `walk({:go, acc}, n - 1)`, which the
/// reconstructed tuple hands on unchanged.
///
/// Only SELF calls are read, so the rule is INCOMPLETE by construction and
/// holds with a named exception: a position the
/// recursion supplies ACROSS a cycle, or through a generated lambda, is not
/// seen here and is keyed anyway. That is a cost, never an unsoundness -- the
/// key names more than the return depends on. Measured corpus-wide (604
/// fixtures, 475 backend dumps, added executables attributed to the function
/// they key): 36 land on a function that gains a distinct published return and
/// 91 do not, the 91 dominated by `List.reduce_cont/3` (21),
/// `List.reduce_while_cont/3` (18), `Range.reduce_while_cont/6` (9) and
/// `List.reduce_while_step/3` (6) minting `empty_list()`/`list(tau)`
/// ascent rungs across the cont<->step cycle. Closing it wants the call
/// graph's strong components, which `DeriveInputDemand` does not read today,
/// and the reverse call edge, because the rebuild belongs to the CALLEE's
/// position.
fn recursion_supplied_positions(
    function: FunctionId,
    entries: &[super::super::body::LoweredEntry],
    origins: &HashMap<ValueId, Vec<(usize, Vec<DemandPathStep>)>>,
    input_count: usize,
) -> HashSet<(usize, Vec<DemandPathStep>)> {
    let mut rebuilt = HashSet::new();
    let mut obligations: Vec<RebuildObligation> = Vec::new();
    let mut constructions: HashMap<ValueId, Vec<ValueId>> = HashMap::new();
    for step in entries.iter().flat_map(|entry| entry.steps.iter()) {
        if let LoweredStep::Tuple { value, items } = step {
            constructions.insert(*value, items.iter().map(|item| item.value).collect());
        }
    }
    for entry in entries {
        let LoweredTail::DirectCall { callee, args, .. } = &entry.tail else {
            continue;
        };
        if *callee != function {
            continue;
        }
        for (arg_index, arg) in args.iter().enumerate() {
            let Some(slot) = CallInputMode::Direct.semantic_index(input_count, args.len(), arg_index) else {
                continue;
            };
            collect_rebuild_obligations(
                arg.value,
                slot,
                &mut Vec::new(),
                origins,
                &constructions,
                &mut obligations,
            );
        }
    }
    // Least fixpoint: a position is SUPPLIED only when the value handed to it
    // is not one the caller already held at a position the recursion itself
    // leaves constant. A permutation (`go(n - 1, b, a)`) hands each slot a
    // value the caller held elsewhere and supplies nothing, so it settles at
    // the empty set; a rebuild (`go(n - 1, [h | a], a)`) supplies the built
    // slot in the first round and drags the slot fed from it in the second.
    loop {
        let mut changed = false;
        for (position, held) in &obligations {
            if rebuilt.contains(position) {
                continue;
            }
            if held.is_empty() || held.iter().all(|source| rebuilt.contains(source)) {
                rebuilt.insert(position.clone());
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    rebuilt
}

/// One "this self-call hands POSITION a value the caller held at HELD" record.
/// An empty `held` is a value built here, which supplies the position outright.
type RebuildObligation = ((usize, Vec<DemandPathStep>), Vec<(usize, Vec<DemandPathStep>)>);

fn collect_rebuild_obligations(
    value: ValueId,
    slot: usize,
    path: &mut Vec<DemandPathStep>,
    origins: &HashMap<ValueId, Vec<(usize, Vec<DemandPathStep>)>>,
    constructions: &HashMap<ValueId, Vec<ValueId>>,
    obligations: &mut Vec<RebuildObligation>,
) {
    let held = origins.get(&value).map(Vec::as_slice).unwrap_or_default();
    if held
        .iter()
        .any(|(held_slot, held_path)| *held_slot == slot && held_path == path)
    {
        // The caller already held this exact position, so the recursion carries
        // it rather than supplying it.
        return;
    }
    obligations.push(((slot, path.clone()), held.to_vec()));
    // A reconstructed tuple is rebuilt at its own position and no deeper: a
    // field it hands on unchanged is still carried.
    for (index, item) in constructions.get(&value).into_iter().flatten().copied().enumerate() {
        path.push(DemandPathStep::TupleField(index as u32));
        collect_rebuild_obligations(item, slot, path, origins, constructions, obligations);
        path.pop();
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
    let LoweredBody::Clauses { clauses, .. } = body;
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

/// Every value this body can publish as its return, plus everything such a
/// value is built from.
///
/// The roots are the tails that RETURN rather than deliver; a delivered value
/// counts through its join, so a non-tail `if` whose branches deliver into a
/// resume entry is followed one hop per join. Construction steps are opened --
/// `{:done, acc}` returns `acc` -- because an activation's published return
/// carries the field's type whether or not the tuple around it is new.
fn returned_values(
    body: &LoweredBody,
    clauses: &[super::super::body::LoweredClause],
    entries: &[super::super::body::LoweredEntry],
) -> HashSet<ValueId> {
    let mut returned = HashSet::new();
    let mut frontier = Vec::new();
    for entry in entries {
        if let LoweredTail::Value {
            value,
            dest: super::super::body::ControlDestination::Return,
        } = &entry.tail
            && returned.insert(*value)
        {
            frontier.push(*value);
        }
    }
    let mut built: HashMap<ValueId, Vec<ValueId>> = HashMap::new();
    for step in clauses
        .iter()
        .flat_map(|clause| clause.projections.iter())
        .chain(entries.iter().flat_map(|entry| entry.steps.iter()))
    {
        match step {
            LoweredStep::Tuple { value, items } => {
                built.insert(*value, items.iter().map(|item| item.value).collect());
            }
            LoweredStep::List { value, items, tail, .. } => {
                built.insert(*value, items.iter().copied().chain(*tail).collect());
            }
            LoweredStep::Map { value, entries, .. } => {
                built.insert(*value, entries.iter().map(|(_key, item)| *item).collect());
            }
            LoweredStep::MapUpdate { value, base, entries } => {
                built.insert(
                    *value,
                    std::iter::once(*base)
                        .chain(entries.iter().map(|(_key, item)| *item))
                        .collect(),
                );
            }
            LoweredStep::Struct { value, fields, .. } => {
                built.insert(*value, fields.iter().map(|(_name, item)| *item).collect());
            }
            _ => {}
        }
    }
    for join in super::super::body::delivered_value_joins(body).into_values() {
        let sources = join
            .sources
            .iter()
            .filter_map(|source| match source {
                super::super::body::DeliveredValueSource::LocalValue(value) => Some(*value),
                super::super::body::DeliveredValueSource::CallsiteReturn(_) => None,
            })
            .collect::<Vec<_>>();
        built.entry(join.value).or_default().extend(sources);
    }
    while let Some(value) = frontier.pop() {
        for source in built.get(&value).into_iter().flatten().copied() {
            if returned.insert(source) {
                frontier.push(source);
            }
        }
    }
    returned
}

/// The least fixpoint of the input-forwarding graph, projected onto `function`.
/// Kleene iteration joins each edge's callee demand into its caller slot and
/// stops when one pass changes nothing.
///
/// Every edge is lifted from the callee's demand to the caller's slot, and a
/// lift can deepen it (`go({_, rest})` asks `go(rest)`'s question one
/// tuple deeper). An edge on a cycle that deepens would deepen its own input
/// again on the next pass, without end, so it asks about the whole slot:
/// the only lifts left to the cycle keep a demand's depth, and a demand's
/// depth is bounded by the deepest seed, so the iteration ends.
fn solve_forwarded_demand(
    graph: &BTreeMap<FunctionId, DemandNode>,
    function: FunctionId,
    axis: impl Fn(&DemandNode) -> Vec<DispatchDemand>,
    lift: impl Fn(&ForwardEdge, &DispatchDemand) -> DispatchDemand,
) -> Vec<DispatchDemand> {
    let reaches = forwarding_reach(graph);
    let mut demand = graph
        .iter()
        .map(|(id, node)| (*id, axis(node)))
        .collect::<BTreeMap<_, _>>();
    loop {
        let mut changed = false;
        for (id, node) in graph {
            for edge in &node.forwards {
                let Some(callee) = demand.get(&edge.callee).and_then(|callee| callee.get(edge.callee_slot)) else {
                    continue;
                };
                let mut inherited = lift(edge, callee);
                let on_a_cycle =
                    edge.callee == *id || reaches.get(&edge.callee).is_some_and(|onward| onward.contains(id));
                if on_a_cycle && inherited.depth() > callee.depth() {
                    inherited = DispatchDemand::Whole;
                }
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

/// The functions each function of the graph forwards an input to, directly or
/// through others.
fn forwarding_reach(graph: &BTreeMap<FunctionId, DemandNode>) -> BTreeMap<FunctionId, BTreeSet<FunctionId>> {
    let mut reach = graph
        .iter()
        .map(|(id, node)| {
            (
                *id,
                node.forwards.iter().map(|edge| edge.callee).collect::<BTreeSet<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    loop {
        let mut changed = false;
        for id in graph.keys() {
            let through = reach[id]
                .iter()
                .filter_map(|callee| reach.get(callee))
                .flatten()
                .copied()
                .collect::<Vec<_>>();
            let mine = reach.get_mut(id).expect("every function of the graph has a reach");
            for function in through {
                changed |= mine.insert(function);
            }
        }
        if !changed {
            return reach;
        }
    }
}

impl DemandNode {
    /// The forwarded axis's seed: what the entry plan asks, joined with what
    /// the rest of the body does with its inputs.
    fn dispatch_and_uses(&self) -> Vec<DispatchDemand> {
        let mut seed = self.local.clone();
        seed.resize(seed.len().max(self.uses.len()), DispatchDemand::Ignore);
        for (slot, used) in seed.iter_mut().zip(&self.uses) {
            slot.join_assign(used.clone());
        }
        seed
    }
}

fn emit_input_demand_derived(tel: &impl crate::telemetry::Telemetry, function: &FunctionId, demand: &InputDemand) {
    tel.raw_event2(&["fz", "compiler2", "input_demand", "derived"], function, demand);
}

fn static_edges(body: &LoweredBody) -> Vec<StaticEdge> {
    let mut edges = Vec::new();
    let LoweredBody::Clauses { clauses, entries, .. } = body;
    for clause in clauses {
        collect_step_edges(&clause.projections, &mut edges);
    }
    for entry in entries {
        collect_step_edges(&entry.steps, &mut edges);
        collect_tail_edges(&entry.tail, &mut edges);
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
            | LoweredStep::RequireMapValue { .. }
            | LoweredStep::TupleField { .. }
            | LoweredStep::SplitList { .. }
            | LoweredStep::BitstringInit { .. }
            | LoweredStep::BitstringRead { .. }
            | LoweredStep::PopHandler => {}
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
        | LoweredTail::Try { .. }
        | LoweredTail::Unreachable => {}
    }
}

#[cfg(test)]
#[path = "keying_test.rs"]
mod keying_test;
