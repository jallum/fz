//! Jobs that derive the stable facts used for activation keying.

use std::collections::{HashMap, HashSet};

use crate::dispatch_matrix::SubjectSource;
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardExpr};

use super::super::body::{DirectCallee, LoweredBody, LoweredStep, LoweredTail};
use super::super::drive::{FactKey, Job, JobEffects};
use super::super::facts::FactValue;
use super::super::identity::FunctionId;
use super::super::scheduler::FatalError;
use super::super::types::Ty;
use super::super::world::World;

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
            reads,
            waits: waits.into_iter().collect(),
            follow_up: follow_up.into_iter().collect(),
            ..JobEffects::default()
        });
    }

    let recursive = reaches_self(function, &graph);
    let revision = world.define_recursive(function, recursive);
    Ok(JobEffects {
        reads,
        outputs: vec![(FactKey::Recursive(function), FactValue::presence(revision))],
        ..JobEffects::default()
    })
}

/// Derives which function inputs participate in entry dispatch.
pub(super) fn derive_dispatch_mask(world: &mut World<'_>, function: FunctionId) -> Result<JobEffects, FatalError> {
    let dispatch_fact = FactKey::EntryDispatch(function);
    if world.fact_revision(dispatch_fact.clone()).is_none() {
        return Ok(JobEffects::wait_on(dispatch_fact, [Job::PlanEntryDispatch(function)]));
    }

    let plan = world.entry_dispatch(function);
    let mask = dispatch_input_mask(&plan);
    let revision = world.define_dispatch_mask(function, mask);
    Ok(JobEffects {
        reads: vec![FactKey::EntryDispatch(function)],
        outputs: vec![(FactKey::DispatchMask(function), FactValue::presence(revision))],
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
    if world.fact_revision(lowered_fact.clone()).is_none() {
        waits.insert(lowered_fact);
        follow_up.insert(Job::LowerFunction(function));
        return;
    }
    reads.push(lowered_fact);

    let edges = static_edges(&world.lowered_body(function));
    let mut ready_edges = Vec::new();
    for edge in edges {
        let target = edge.function();
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
            | LoweredStep::NamedFunctionRef { .. }
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
        LoweredTail::DirectCall {
            callee: DirectCallee::Function(function),
            ..
        } => edges.push(StaticEdge::Direct(*function)),
        LoweredTail::Value { .. }
        | LoweredTail::DirectCall {
            callee: DirectCallee::Named { .. },
            ..
        }
        | LoweredTail::ClosureCall { .. }
        | LoweredTail::If { .. }
        | LoweredTail::Dispatch { .. }
        | LoweredTail::Receive(_)
        | LoweredTail::Halt { .. } => {}
    }
}

fn dispatch_input_mask(plan: &PatternDispatchPlan<Ty>) -> Vec<bool> {
    let mut mask = vec![false; plan.input_count];
    for arm in &plan.matrix.arms {
        for question in &arm.questions {
            mark_subject_inputs(&plan.matrix.subjects, question.predicate.subject, &mut mask);
        }
    }
    for guard in &plan.guards {
        mark_guard_inputs(plan, guard, &mut mask);
    }
    mask
}

fn mark_subject_inputs(
    subjects: &[crate::dispatch_matrix::Subject],
    subject: crate::dispatch_matrix::SubjectId,
    mask: &mut [bool],
) {
    let Some(subject) = subjects.get(subject.0 as usize) else {
        return;
    };
    match &subject.source {
        SubjectSource::Input { ordinal } => {
            if let Some(slot) = mask.get_mut(*ordinal as usize) {
                *slot = true;
            }
        }
        SubjectSource::Projection(projection) => {
            mark_subject_inputs(subjects, projection.source, mask);
        }
    }
}

fn mark_guard_inputs(plan: &PatternDispatchPlan<Ty>, guard: &PatternGuardExpr<Ty>, mask: &mut [bool]) {
    match guard {
        PatternGuardExpr::Const(_) | PatternGuardExpr::Pinned(_) => {}
        PatternGuardExpr::Subject(subject) => mark_subject_inputs(&plan.matrix.subjects, *subject, mask),
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
