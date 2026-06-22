//! Jobs that derive the stable facts used for activation keying.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardExpr};
use crate::dispatch_matrix::{ListRegion, ProjectionKind, Region, RegionPredicate, Subject, SubjectId, SubjectSource};

use super::super::body::{LoweredBody, LoweredStep, LoweredTail};
use super::super::drive::{FactKey, Job, JobEffects, current_uses};
use super::super::identity::FunctionId;
use super::super::keying::DispatchDemand;
use super::super::scheduler::FatalError;
use super::super::types::Ty;
use super::super::world::World;
use crate::telemetry::opaque_debug;
use crate::{measurements, metadata};

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

/// Derives whether one function can reach itself through static calls.
///
/// Lambda creation is a static edge from the owner to the generated function,
/// so recursion through generated closures is handled the same way as direct
/// or mutual recursion.
pub(super) fn derive_recursive(world: &mut World<'_>, function: FunctionId) -> Result<JobEffects, FatalError> {
    if world.function_is_provider_boundary(function) {
        let changed = world.define_recursive(function, false);
        return Ok(JobEffects {
            outputs: vec![FactKey::Recursive(function)],
            changed: changed.then_some(FactKey::Recursive(function)).into_iter().collect(),
            ..JobEffects::default()
        });
    }
    if world.function_defined_revision(function).is_none() {
        return Ok(world.wait_for_function_definition(function));
    }

    let mut reads = Vec::new();
    let mut waits = HashSet::new();
    let mut follow_up = HashSet::new();
    let mut graph = HashMap::new();
    let mut seen = HashSet::new();
    collect_static_graph(
        world,
        function,
        &mut reads,
        &mut waits,
        &mut follow_up,
        &mut graph,
        &mut seen,
    );
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads: current_uses(reads),
            waits: current_uses(waits),
            follow_up: follow_up.into_iter().collect(),
            ..JobEffects::default()
        });
    }

    let recursive = reaches_self(function, &graph);
    let changed = world.define_recursive(function, recursive);
    Ok(JobEffects {
        reads: current_uses(reads),
        outputs: vec![FactKey::Recursive(function)],
        changed: changed.then_some(FactKey::Recursive(function)).into_iter().collect(),
        ..JobEffects::default()
    })
}

/// Derives which function inputs participate in entry dispatch.
pub(super) fn derive_dispatch_mask(world: &mut World<'_>, function: FunctionId) -> Result<JobEffects, FatalError> {
    let dispatch_fact = FactKey::EntryDispatch(function);
    if !world.has_fact(&dispatch_fact) {
        return Ok(JobEffects::wait_on_current(
            dispatch_fact,
            [Job::PlanEntryDispatch(function)],
        ));
    }

    let plan = world.entry_dispatch(function);
    let mask = dispatch_input_mask(&plan);
    world.tel().execute(
        &["fz", "compiler2", "dispatch_mask", "derived"],
        &measurements! {
            function_id: function.as_u32(),
            arity: mask.len(),
        },
        &metadata! {
            mask: opaque_debug(&mask),
        },
    );
    let changed = world.define_dispatch_mask(function, mask);
    Ok(JobEffects {
        reads: current_uses([FactKey::EntryDispatch(function)]),
        outputs: vec![FactKey::DispatchMask(function)],
        changed: changed.then_some(FactKey::DispatchMask(function)).into_iter().collect(),
        ..JobEffects::default()
    })
}

fn collect_static_graph(
    world: &mut World<'_>,
    function: FunctionId,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
    graph: &mut HashMap<FunctionId, Vec<FunctionId>>,
    seen: &mut HashSet<FunctionId>,
) {
    if !seen.insert(function) {
        return;
    }

    if world.function_defined_revision(function).is_none() {
        if world.protocol_callback(function).is_some() {
            return;
        }
        let module = world.function_module(function);
        if !module.is_global() && world.module_defined_revision(module).is_none() {
            waits.insert(FactKey::ModuleDefined(module));
            follow_up.extend(world.ensure_function_source(function));
            return;
        }
        waits.insert(FactKey::FunctionDefined(function));
        follow_up.insert(Job::DefineFunction(function));
        return;
    }

    let lowered_fact = FactKey::LoweredBody(function);
    if !world.has_fact(&lowered_fact) {
        waits.insert(lowered_fact);
        follow_up.insert(Job::LowerFunction(function));
        return;
    }
    reads.push(lowered_fact);

    let edges = static_edges(&world.lowered_body(function));
    let mut ready_edges = Vec::new();
    for edge in edges {
        let target = edge.function();
        if world.function_is_provider_boundary(target) {
            continue;
        }
        if matches!(edge, StaticEdge::Lambda(_)) && world.function_defined_revision(target).is_none() {
            continue;
        }
        ready_edges.push(target);
        collect_static_graph(world, target, reads, waits, follow_up, graph, seen);
    }
    ready_edges.sort_by_key(|function| function.as_u32());
    ready_edges.dedup();
    graph.insert(function, ready_edges);
}

fn reaches_self(function: FunctionId, graph: &HashMap<FunctionId, Vec<FunctionId>>) -> bool {
    let mut stack = graph.get(&function).cloned().unwrap_or_default();
    let mut seen = HashSet::new();
    while let Some(next) = stack.pop() {
        if next == function {
            return true;
        }
        if seen.insert(next)
            && let Some(edges) = graph.get(&next)
        {
            stack.extend(edges.iter().copied());
        }
    }
    false
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DemandPathStep {
    TupleField(u32),
    ListHead,
    ListTail,
    MapValue,
    BitstringField,
}

fn dispatch_input_mask(plan: &PatternDispatchPlan<Ty>) -> Vec<DispatchDemand> {
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

fn subject_path(subjects: &[Subject], subject: SubjectId) -> Option<(u32, Vec<DemandPathStep>)> {
    let subject = subjects.get(subject.0 as usize)?;
    match &subject.source {
        SubjectSource::Input { ordinal } => Some((*ordinal, Vec::new())),
        SubjectSource::Projection(projection) => {
            let (ordinal, mut path) = subject_path(subjects, projection.source)?;
            match &projection.kind {
                ProjectionKind::TupleField(field) => path.push(DemandPathStep::TupleField(*field)),
                ProjectionKind::ListHead => path.push(DemandPathStep::ListHead),
                ProjectionKind::ListTail => path.push(DemandPathStep::ListTail),
                ProjectionKind::MapValue { .. } => path.push(DemandPathStep::MapValue),
                ProjectionKind::BitstringField(_) => path.push(DemandPathStep::BitstringField),
            }
            Some((ordinal, path))
        }
    }
}

fn demand_at_path(path: &[DemandPathStep], demand: DispatchDemand) -> DispatchDemand {
    let Some((head, tail)) = path.split_first() else {
        return demand;
    };
    match head {
        DemandPathStep::TupleField(field) => {
            let mut fields = BTreeMap::new();
            fields.insert(*field, demand_at_path(tail, demand));
            DispatchDemand::TupleFields(fields)
        }
        DemandPathStep::ListHead => DispatchDemand::ListShape(Box::new(demand_at_path(tail, demand))),
        DemandPathStep::ListTail | DemandPathStep::MapValue | DemandPathStep::BitstringField => DispatchDemand::Whole,
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
