//! Compiler2 semantic-analysis jobs.
//!
//! This module walks lowered function bodies through already-planned entry
//! dispatch, derives direct-call summaries, and settles per-activation return
//! types without calling the legacy whole-program pipeline.

use std::collections::{HashMap, HashSet};

use crate::ast::{BinOp, UnOp};
use crate::dispatch_matrix::pattern::PatternDispatchPlan;
use crate::dispatch_matrix::{
    ComparisonValue, DispatchConst, DispatchNode, EdgeEvidence, GraphNodeId, ListRegion, Region, RegionPredicate,
    SubjectId, SubjectSource,
};
use crate::types::{self, ClosureTarget, ClosureTypes, Ty, Types};

use super::super::body::{CallSiteId, DirectCallee, Literal, LoweredBlock, LoweredBody, LoweredStep, ValueId};
use super::super::drive::{FactKey, Job, JobEffects};
use super::super::facts::FactValue;
use super::super::identity::{ActivationKey, ExecutableNeed, FunctionId, ModuleId};
use super::super::scheduler::FatalError;
use super::super::semantic::{ActivationAnalysis, CallSiteKey, CallSiteSummary, SelectedCallee};
use super::super::world::World;

type ValueTypes = HashMap<ValueId, Ty>;

#[derive(Debug, Clone)]
struct CallEmission {
    key: CallSiteKey,
    summary: CallSiteSummary,
}

/// Analyzes one rooted function activation against its lowered body.
///
/// The job waits until the activation, lowered body, and entry dispatch all
/// exist. It then walks only the dispatch-reachable clauses, publishes direct
/// callsite summaries, and settles the activation's current return type.
pub(super) fn analyze_activation(world: &mut World<'_>, activation: &ActivationKey) -> Result<JobEffects, FatalError> {
    let activation_fact = FactKey::Activation(activation.clone());
    let Some(_) = world.fact_revision(activation_fact.clone()) else {
        return Ok(JobEffects::default());
    };

    let function = activation.function;
    let function_fact = FactKey::FunctionDefined(function);
    let Some(_) = world.function_defined_revision(function) else {
        return Ok(world.wait_for_function_definition(function));
    };

    let lowered_fact = FactKey::LoweredBody(function);
    let Some(_) = world.fact_revision(lowered_fact.clone()) else {
        return Ok(JobEffects::wait_on(lowered_fact, [Job::LowerFunction(function)]));
    };

    let dispatch_fact = FactKey::EntryDispatch(function);
    let Some(_) = world.fact_revision(dispatch_fact.clone()) else {
        return Ok(JobEffects::wait_on(dispatch_fact, [Job::PlanEntryDispatch(function)]));
    };

    let mut reads = vec![activation_fact, function_fact, lowered_fact, dispatch_fact];
    let mut waits = HashSet::new();
    let mut follow_up = HashSet::from([Job::CheckSemanticClosure(activation.root)]);
    let mut outputs = Vec::new();

    let entry_dispatch = world.entry_dispatch(function);
    let lowered_body = world.lowered_body(function);
    let inputs = world.activation_summary(activation).inputs.clone();
    let reachable_clauses = reachable_clause_ids(&entry_dispatch, &inputs);

    let mut analysis_calls = Vec::new();
    let mut return_ty = types::new().none();
    match lowered_body {
        LoweredBody::Extern { .. } => {
            return_ty = types::new().any();
        }
        LoweredBody::Clauses { clauses, .. } => {
            for clause_id in &reachable_clauses {
                let clause = &clauses[*clause_id as usize];
                let mut values = HashMap::new();
                for (value, ty) in clause.params.iter().copied().zip(inputs.iter().cloned()) {
                    values.insert(value, ty);
                }
                apply_steps(
                    world,
                    &clause.projections,
                    &mut values,
                    &mut analysis_calls,
                    activation,
                    &mut reads,
                    &mut waits,
                    &mut follow_up,
                )?;
                let clause_return = analyze_block(
                    world,
                    &clause.body,
                    &mut values,
                    &mut analysis_calls,
                    activation,
                    &mut reads,
                    &mut waits,
                    &mut follow_up,
                )?;
                let mut t = types::new();
                return_ty = if t.is_empty(&return_ty) {
                    clause_return
                } else {
                    t.union(return_ty, clause_return)
                };
            }
        }
    }

    if !waits.is_empty() {
        return Ok(JobEffects {
            reads,
            waits: waits.into_iter().collect(),
            follow_up: follow_up.into_iter().collect(),
            ..JobEffects::default()
        });
    }

    for call in &analysis_calls {
        let revision = world.define_callsite_summary(call.key.clone(), call.summary.clone());
        outputs.push((FactKey::SelectedCallee(call.key.clone()), FactValue::presence(revision)));
        outputs.push((FactKey::ReturnNeed(call.key.clone()), FactValue::presence(revision)));
    }

    let return_revision = world.define_activation_return(activation, return_ty);
    outputs.push((
        FactKey::ReturnType(activation.clone()),
        FactValue::presence(return_revision),
    ));

    let analysis_revision = world.define_activation_analysis(
        activation,
        ActivationAnalysis {
            reachable_clauses: reachable_clauses.clone(),
            callsites: analysis_calls.iter().map(|call| call.key.callsite).collect(),
        },
    );
    outputs.push((
        FactKey::ActivationAnalyzed(activation.clone()),
        FactValue::presence(analysis_revision),
    ));

    follow_up.insert(Job::CheckSemanticClosure(activation.root));
    Ok(JobEffects {
        reads,
        outputs: dedupe_outputs(outputs),
        follow_up: follow_up.into_iter().collect(),
        ..JobEffects::default()
    })
}

fn analyze_block(
    world: &mut World<'_>,
    block: &LoweredBlock,
    values: &mut ValueTypes,
    calls: &mut Vec<CallEmission>,
    activation: &ActivationKey,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<Ty, FatalError> {
    apply_steps(world, &block.steps, values, calls, activation, reads, waits, follow_up)?;
    Ok(values.get(&block.result).cloned().unwrap_or_else(|| types::new().any()))
}

fn apply_steps(
    world: &mut World<'_>,
    steps: &[LoweredStep],
    values: &mut ValueTypes,
    calls: &mut Vec<CallEmission>,
    activation: &ActivationKey,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<(), FatalError> {
    let return_needs = block_return_needs(steps);
    for step in steps {
        apply_step(
            world,
            step,
            values,
            calls,
            activation,
            &return_needs,
            reads,
            waits,
            follow_up,
        )?;
    }
    Ok(())
}

fn apply_step(
    world: &mut World<'_>,
    step: &LoweredStep,
    values: &mut ValueTypes,
    calls: &mut Vec<CallEmission>,
    activation: &ActivationKey,
    return_needs: &HashMap<CallSiteId, ExecutableNeed>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<(), FatalError> {
    match step {
        LoweredStep::Const { value, literal } => {
            values.insert(*value, literal_ty(literal));
        }
        LoweredStep::Tuple { value, items } => {
            let mut t = types::new();
            let items = items.iter().map(|item| value_ty(values, *item)).collect::<Vec<_>>();
            values.insert(*value, t.tuple(&items));
        }
        LoweredStep::List { value, items, tail } => {
            values.insert(*value, list_ty(values, items, *tail));
        }
        LoweredStep::FunctionRef { value, function } => {
            let arity = world.function_arity(*function);
            let mut t = types::new();
            values.insert(*value, t.fn_ref_lit(ClosureTarget(function.as_u32()), arity));
        }
        LoweredStep::NamedFunctionRef { value, .. } => {
            values.insert(*value, types::new().any());
        }
        LoweredStep::DirectCall {
            value,
            callsite,
            callee,
            args,
        } => {
            let need = return_needs.get(callsite).cloned().unwrap_or(ExecutableNeed::Value);
            let arg_types = args.iter().map(|arg| value_ty(values, *arg)).collect::<Vec<_>>();
            let (summary, return_ty) = resolve_direct_call(
                world,
                activation,
                *callsite,
                callee,
                arg_types.clone(),
                need,
                reads,
                waits,
                follow_up,
            )?;
            if let Some(summary) = summary {
                let key = CallSiteKey {
                    activation: activation.clone(),
                    callsite: *callsite,
                };
                calls.push(CallEmission { key, summary });
            }
            values.insert(*value, return_ty);
        }
        LoweredStep::ClosureCall {
            value,
            callsite,
            callee,
            args,
        } => {
            let need = return_needs.get(callsite).cloned().unwrap_or(ExecutableNeed::Value);
            let callee_ty = value_ty(values, *callee);
            let arg_types = args.iter().map(|arg| value_ty(values, *arg)).collect::<Vec<_>>();
            let (summary, return_ty) = resolve_closure_call(
                world,
                activation,
                *callsite,
                callee_ty,
                arg_types.clone(),
                need,
                reads,
                waits,
                follow_up,
            )?;
            if let Some(summary) = summary {
                let key = CallSiteKey {
                    activation: activation.clone(),
                    callsite: *callsite,
                };
                calls.push(CallEmission { key, summary });
            }
            values.insert(*value, return_ty);
        }
        LoweredStep::Lambda {
            value,
            function,
            captures,
        } => {
            let captures = captures.iter().map(|capture| value_ty(values, *capture)).collect();
            values.insert(*value, world.closure_ty(*function, captures));
        }
        LoweredStep::BinaryOp { value, op, left, right } => {
            let left = value_ty(values, *left);
            let right = value_ty(values, *right);
            values.insert(*value, binop_ty(*op, left, right));
        }
        LoweredStep::UnaryOp { value, op, input } => {
            let input = value_ty(values, *input);
            values.insert(*value, unop_ty(*op, input));
        }
        LoweredStep::MapIndex { value, .. } => {
            values.insert(*value, types::new().any());
        }
        LoweredStep::If {
            value,
            then_block,
            else_block,
            ..
        } => {
            let mut then_values = values.clone();
            let mut else_values = values.clone();
            let then_ty = analyze_block(
                world,
                then_block,
                &mut then_values,
                calls,
                activation,
                reads,
                waits,
                follow_up,
            )?;
            let else_ty = analyze_block(
                world,
                else_block,
                &mut else_values,
                calls,
                activation,
                reads,
                waits,
                follow_up,
            )?;
            let mut t = types::new();
            values.insert(*value, t.union(then_ty, else_ty));
        }
        LoweredStep::AssertLiteral { source, literal } => {
            let mut t = types::new();
            let refined = t.intersect(value_ty(values, *source), literal_ty(literal));
            values.insert(*source, refined);
        }
        LoweredStep::AssertTuple { source, arity } => {
            let mut t = types::new();
            let any = t.any();
            let fields = t.repeat(any, *arity);
            let tuple = t.tuple(&fields);
            let refined = t.intersect(value_ty(values, *source), tuple);
            values.insert(*source, refined);
        }
        LoweredStep::TupleField { value, source, index } => {
            let mut t = types::new();
            let source = value_ty(values, *source);
            values.insert(*value, t.tuple_field_type(&source, *index));
        }
        LoweredStep::AssertEmptyList { source } => {
            let mut t = types::new();
            let empty = t.empty_list();
            let refined = t.intersect(value_ty(values, *source), empty);
            values.insert(*source, refined);
        }
        LoweredStep::AssertSame { source, value } => {
            let mut t = types::new();
            let both = t.intersect(value_ty(values, *source), value_ty(values, *value));
            values.insert(*source, both.clone());
            values.insert(*value, both);
        }
        LoweredStep::SplitList { source, head, tail } => {
            let source_ty = value_ty(values, *source);
            let mut t = types::new();
            let elem = t.list_element_type(&source_ty);
            let tail_ty = t.list(elem.clone());
            values.insert(*head, elem.clone());
            values.insert(*tail, tail_ty);
        }
    }
    Ok(())
}

fn resolve_direct_call(
    world: &mut World<'_>,
    caller: &ActivationKey,
    _callsite: CallSiteId,
    callee: &DirectCallee,
    arg_types: Vec<Ty>,
    _need: ExecutableNeed,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<(Option<CallSiteSummary>, Ty), FatalError> {
    let mut t = types::new();
    if arg_types.iter().any(|arg| t.is_empty(arg)) {
        return Ok((
            call_summary(selected_callee(callee), arg_types, _need, t.none()),
            t.none(),
        ));
    }

    match callee {
        DirectCallee::Function(function) => {
            resolve_function_call(world, caller, *function, arg_types, _need, reads, waits, follow_up)
        }
        DirectCallee::Named { .. } => Ok((
            call_summary(selected_callee(callee), arg_types, _need, types::new().any()),
            types::new().any(),
        )),
    }
}

fn resolve_function_call(
    world: &mut World<'_>,
    caller: &ActivationKey,
    function: FunctionId,
    input_types: Vec<Ty>,
    need: ExecutableNeed,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<(Option<CallSiteSummary>, Ty), FatalError> {
    if let Some(callback) = world.protocol_callback(function) {
        return resolve_protocol_call(
            world,
            caller,
            function,
            callback.protocol,
            input_types,
            need,
            reads,
            waits,
            follow_up,
        );
    }
    let return_ty = activate_function_call(world, caller, function, input_types.clone(), reads, waits, follow_up);
    Ok((
        Some(CallSiteSummary {
            callee: SelectedCallee::Function(function),
            input_types,
            need,
            return_ty: return_ty.clone(),
        }),
        return_ty,
    ))
}

fn resolve_protocol_call(
    world: &mut World<'_>,
    caller: &ActivationKey,
    callback_function: FunctionId,
    protocol: ModuleId,
    input_types: Vec<Ty>,
    need: ExecutableNeed,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<(Option<CallSiteSummary>, Ty), FatalError> {
    let protocol_fact = FactKey::ModuleDefined(protocol);
    if world.module_defined_revision(protocol).is_none() {
        wait_for_protocol_module(world, protocol, waits, follow_up);
        return Ok((None, types::new().any()));
    }
    reads.push(protocol_fact);

    let receiver_ty = input_types.first().cloned().unwrap_or_else(|| types::new().any());
    let function_ref = world.function_ref(callback_function).clone();

    let mut matches = Vec::new();
    for (key, protocol_impl) in world.protocol_impls_for(protocol) {
        let target_ty = world.module_impl_target_ty(key.target);
        let t = types::new();
        if !t.is_subtype(&receiver_ty, &target_ty) {
            continue;
        }
        let callback = protocol_impl
            .callbacks
            .get(&(function_ref.name.clone(), function_ref.arity))
            .copied();
        if let Some(callback) = callback {
            matches.push(callback);
        }
    }

    if matches.is_empty() {
        for module in world.runtime_impl_target_modules(&receiver_ty) {
            if world.protocol_impl(protocol, module).is_some() {
                continue;
            }
            wait_for_runtime_module(world, module, waits, follow_up);
        }
        return Ok((None, types::new().any()));
    }

    if matches.len() != 1 {
        return Ok((None, types::new().any()));
    }

    let selected = matches[0];
    let owner_fact = FactKey::ModuleDefined(selected.owner_module);
    if world.module_defined_revision(selected.owner_module).is_none() {
        waits.insert(owner_fact);
        follow_up.insert(Job::DefineModule(selected.owner_module));
        return Ok((None, types::new().any()));
    }
    reads.push(owner_fact);

    let return_ty = activate_function_call(
        world,
        caller,
        selected.function,
        input_types.clone(),
        reads,
        waits,
        follow_up,
    );
    Ok((
        Some(CallSiteSummary {
            callee: SelectedCallee::Function(selected.function),
            input_types,
            need,
            return_ty: return_ty.clone(),
        }),
        return_ty,
    ))
}

fn resolve_closure_call(
    world: &mut World<'_>,
    caller: &ActivationKey,
    _callsite: CallSiteId,
    callee_ty: Ty,
    arg_types: Vec<Ty>,
    _need: ExecutableNeed,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<(Option<CallSiteSummary>, Ty), FatalError> {
    let mut t = types::new();
    if t.is_empty(&callee_ty) || arg_types.iter().any(|arg| t.is_empty(arg)) {
        return Ok((None, t.none()));
    }
    let Some(parts) = t.closure_lit_parts(&callee_ty) else {
        return Ok((None, t.any()));
    };
    let function = FunctionId::from_u32(parts.target.0);
    let mut inputs = parts.captures;
    inputs.extend(arg_types);
    resolve_function_call(world, caller, function, inputs, _need, reads, waits, follow_up)
}

fn activate_function_call(
    world: &mut World<'_>,
    caller: &ActivationKey,
    function: FunctionId,
    arg_types: Vec<Ty>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Ty {
    if !world.require_activation_key_facts(function, reads, waits, follow_up) {
        return types::new().any();
    }

    let (activation, _) = world.activate(caller.root, function, arg_types);
    reads.push(FactKey::ReturnType(activation.clone()));
    follow_up.insert(Job::CheckSemanticClosure(caller.root));
    world
        .activation_return(&activation)
        .unwrap_or_else(|| world.activation_summary(&activation).return_ty.clone())
}

fn wait_for_runtime_module(
    world: &mut World<'_>,
    module: ModuleId,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) {
    if let Some(code_id) = world.ensure_runtime_module(module) {
        let indexed_fact = FactKey::CodeIndexed(code_id);
        if world.fact_revision(indexed_fact.clone()).is_none() {
            waits.insert(indexed_fact);
            follow_up.insert(Job::IndexCode(code_id));
        }
    }
    waits.insert(FactKey::ModuleDefined(module));
    follow_up.insert(Job::DefineModule(module));
}

fn wait_for_protocol_module(
    world: &mut World<'_>,
    protocol: ModuleId,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) {
    if let Some(code_id) = world.ensure_runtime_module(protocol) {
        let indexed_fact = FactKey::CodeIndexed(code_id);
        if world.fact_revision(indexed_fact.clone()).is_none() {
            waits.insert(indexed_fact);
            follow_up.insert(Job::IndexCode(code_id));
        }
    }
    waits.insert(FactKey::ModuleDefined(protocol));
    follow_up.insert(Job::DefineModule(protocol));
}

fn selected_callee(callee: &DirectCallee) -> Option<SelectedCallee> {
    Some(match callee {
        DirectCallee::Function(function) => SelectedCallee::Function(*function),
        DirectCallee::Named { name, arity } => SelectedCallee::Named {
            name: name.clone(),
            arity: *arity,
        },
    })
}

fn call_summary(
    callee: Option<SelectedCallee>,
    input_types: Vec<Ty>,
    need: ExecutableNeed,
    return_ty: Ty,
) -> Option<CallSiteSummary> {
    Some(CallSiteSummary {
        callee: callee?,
        input_types,
        need,
        return_ty,
    })
}

fn reachable_clause_ids(plan: &PatternDispatchPlan, inputs: &[Ty]) -> Vec<u32> {
    let mut subjects = HashMap::new();
    for ordinal in 0..plan.input_count {
        let input = inputs.get(ordinal).cloned().unwrap_or_else(|| types::new().any());
        let Some(subject_id) = plan.matrix.subjects.iter().find_map(|subject| match subject.source {
            SubjectSource::Input { ordinal: input_ordinal } if input_ordinal as usize == ordinal => Some(subject.id),
            _ => None,
        }) else {
            continue;
        };
        subjects.insert(subject_id, input);
    }
    let mut outcomes = HashSet::new();
    collect_reachable_outcomes(plan, plan.graph.root, &subjects, &mut outcomes);
    let mut reachable = plan
        .outcomes
        .iter()
        .filter(|outcome| outcomes.contains(&outcome.outcome))
        .map(|outcome| outcome.body_id)
        .collect::<Vec<_>>();
    reachable.sort_unstable();
    reachable
}

fn collect_reachable_outcomes(
    plan: &PatternDispatchPlan,
    node_id: GraphNodeId,
    subjects: &HashMap<SubjectId, Ty>,
    outcomes: &mut HashSet<crate::dispatch_matrix::OutcomeId>,
) {
    let Some(node) = plan.graph.node(node_id) else {
        return;
    };
    match node {
        DispatchNode::Fail => {}
        DispatchNode::Outcome { outcome, .. } => {
            outcomes.insert(*outcome);
        }
        DispatchNode::Test {
            predicate,
            on_match,
            on_miss,
        } => {
            let source = subjects
                .get(&predicate.subject)
                .cloned()
                .unwrap_or_else(|| types::new().any());
            if branch_possible(predicate, &source, true) {
                let mut next = subjects.clone();
                apply_evidence(plan, &mut next, &source, predicate, &on_match.evidence, true);
                collect_reachable_outcomes(plan, on_match.target, &next, outcomes);
            }
            if branch_possible(predicate, &source, false) {
                let mut next = subjects.clone();
                apply_evidence(plan, &mut next, &source, predicate, &on_miss.evidence, false);
                collect_reachable_outcomes(plan, on_miss.target, &next, outcomes);
            }
        }
    }
}

fn branch_possible(predicate: &RegionPredicate, source: &Ty, is_match: bool) -> bool {
    let mut t = types::new();
    match &predicate.region {
        Region::Type(ty) => {
            if is_match {
                let overlap = t.intersect(source.clone(), ty.clone());
                !t.is_empty(&overlap)
            } else {
                !t.is_subtype(source, ty)
            }
        }
        Region::Equal(value) => {
            let target = comparison_ty(value);
            if is_match {
                let overlap = t.intersect(source.clone(), target);
                !t.is_empty(&overlap)
            } else {
                !t.is_subtype(source, &target)
            }
        }
        Region::TupleArity(arity) => {
            let any = t.any();
            let fields = t.repeat(any, *arity as usize);
            let tuple = t.tuple(&fields);
            if is_match {
                let overlap = t.intersect(source.clone(), tuple);
                !t.is_empty(&overlap)
            } else {
                !t.is_subtype(source, &tuple)
            }
        }
        Region::List(ListRegion::Empty) => {
            let empty = t.empty_list();
            if is_match {
                let overlap = t.intersect(source.clone(), empty);
                !t.is_empty(&overlap)
            } else {
                !t.is_subtype(source, &empty)
            }
        }
        Region::List(ListRegion::Cons) => {
            let any = t.any();
            let cons = t.non_empty_list(any);
            if is_match {
                let overlap = t.intersect(source.clone(), cons);
                !t.is_empty(&overlap)
            } else {
                !t.is_subtype(source, &cons)
            }
        }
        Region::MapKind => {
            let map = t.map_top();
            if is_match {
                let overlap = t.intersect(source.clone(), map);
                !t.is_empty(&overlap)
            } else {
                !t.is_subtype(source, &map)
            }
        }
        Region::Guard(_) => true,
        Region::MapKeyPresent { .. } | Region::Bitstring(_) | Region::Any | Region::Never => true,
    }
}

fn apply_evidence(
    plan: &PatternDispatchPlan,
    subjects: &mut HashMap<SubjectId, Ty>,
    source: &Ty,
    predicate: &RegionPredicate,
    evidence: &EdgeEvidence,
    is_match: bool,
) {
    let mut t = types::new();
    let refined = match &predicate.region {
        Region::Type(ty) if is_match => t.intersect(source.clone(), ty.clone()),
        Region::Equal(value) if is_match => t.intersect(source.clone(), comparison_ty(value)),
        Region::TupleArity(arity) if is_match => {
            let any = t.any();
            let fields = t.repeat(any, *arity as usize);
            let tuple = t.tuple(&fields);
            t.intersect(source.clone(), tuple)
        }
        Region::List(ListRegion::Empty) if is_match => {
            let empty = t.empty_list();
            t.intersect(source.clone(), empty)
        }
        Region::List(ListRegion::Cons) if is_match => {
            let any = t.any();
            let cons = t.non_empty_list(any);
            t.intersect(source.clone(), cons)
        }
        _ => source.clone(),
    };
    subjects.insert(predicate.subject, refined.clone());

    for projection in &evidence.projections {
        let base = subjects
            .get(&projection.source)
            .cloned()
            .unwrap_or_else(|| source.clone());
        let projected = match &projection.kind {
            crate::dispatch_matrix::ProjectionKind::TupleField(index) => t.tuple_field_type(&base, *index as usize),
            crate::dispatch_matrix::ProjectionKind::ListHead => t.list_element_type(&base),
            crate::dispatch_matrix::ProjectionKind::ListTail => {
                let elem = t.list_element_type(&base);
                t.list(elem)
            }
            crate::dispatch_matrix::ProjectionKind::MapValue { .. } => t.any(),
            crate::dispatch_matrix::ProjectionKind::BitstringField(_) => t.any(),
        };
        subjects.insert(projection.result, projected);
    }

    for proof in &evidence.proofs {
        if proof.predicate.subject != predicate.subject {
            let _ = plan.subject_ref(proof.predicate.subject);
        }
    }
}

fn block_return_needs(steps: &[LoweredStep]) -> HashMap<CallSiteId, ExecutableNeed> {
    let mut needs = HashMap::new();
    for (index, step) in steps.iter().enumerate() {
        let LoweredStep::DirectCall { value, callsite, .. } = step else {
            continue;
        };
        if let Some(arity) = tuple_destructure_arity(*value, &steps[index + 1..]) {
            needs.insert(*callsite, ExecutableNeed::TupleFields(arity));
        } else {
            needs.insert(*callsite, ExecutableNeed::Value);
        }
    }
    needs
}

fn tuple_destructure_arity(value: ValueId, later_steps: &[LoweredStep]) -> Option<usize> {
    for step in later_steps {
        match step {
            LoweredStep::AssertTuple { source, arity } if *source == value => {
                return Some(*arity);
            }
            LoweredStep::AssertTuple { .. } => {}
            LoweredStep::Const { .. }
            | LoweredStep::Tuple { .. }
            | LoweredStep::List { .. }
            | LoweredStep::FunctionRef { .. }
            | LoweredStep::NamedFunctionRef { .. }
            | LoweredStep::DirectCall { .. }
            | LoweredStep::ClosureCall { .. }
            | LoweredStep::Lambda { .. }
            | LoweredStep::BinaryOp { .. }
            | LoweredStep::UnaryOp { .. }
            | LoweredStep::MapIndex { .. }
            | LoweredStep::AssertLiteral { .. }
            | LoweredStep::AssertEmptyList { .. }
            | LoweredStep::AssertSame { .. }
            | LoweredStep::TupleField { .. }
            | LoweredStep::SplitList { .. } => {}
            LoweredStep::If { .. } => {}
        }
    }
    None
}

fn value_ty(values: &ValueTypes, value: ValueId) -> Ty {
    values.get(&value).cloned().unwrap_or_else(|| types::new().any())
}

fn literal_ty(literal: &Literal) -> Ty {
    let mut t = types::new();
    match literal {
        Literal::Int(value) => t.int_lit(*value),
        Literal::Float(value) => t.float_lit(*value),
        Literal::Binary(_) => t.str_t(),
        Literal::Atom(name) => t.atom_lit(name),
        Literal::Bool(value) => t.bool_lit(*value),
        Literal::Nil => t.nil(),
    }
}

fn comparison_ty(value: &ComparisonValue) -> Ty {
    match value {
        ComparisonValue::Const(value) => dispatch_const_ty(value),
        ComparisonValue::Pinned(_) => types::new().any(),
    }
}

fn dispatch_const_ty(value: &DispatchConst) -> Ty {
    let mut t = types::new();
    match value {
        DispatchConst::Int(value) => t.int_lit(*value),
        DispatchConst::FloatBits(value) => t.float_lit(f64::from_bits(*value)),
        DispatchConst::AtomName(name) => t.atom_lit(name),
        DispatchConst::Bool(value) => t.bool_lit(*value),
        DispatchConst::Nil | DispatchConst::EmptyList => t.empty_list(),
        DispatchConst::Utf8Binary(_) => t.str_t(),
    }
}

fn list_ty(values: &ValueTypes, items: &[ValueId], tail: Option<ValueId>) -> Ty {
    let mut t = types::new();
    let mut elem_ty = t.none();
    for item in items {
        let item_ty = value_ty(values, *item);
        elem_ty = if t.is_empty(&elem_ty) {
            item_ty
        } else {
            t.union(elem_ty, item_ty)
        };
    }
    match tail {
        Some(tail) => {
            let tail_ty = value_ty(values, tail);
            if t.has_list_shape(&tail_ty) {
                let tail_elem = t.list_element_type(&tail_ty);
                let elem_ty = if t.is_empty(&elem_ty) {
                    tail_elem
                } else {
                    t.union(elem_ty, tail_elem)
                };
                t.list(elem_ty)
            } else if t.is_empty(&elem_ty) {
                let any = t.any();
                t.list(any)
            } else {
                t.non_empty_list(elem_ty)
            }
        }
        None => {
            if items.is_empty() {
                t.empty_list()
            } else if t.is_empty(&elem_ty) {
                let any = t.any();
                t.list(any)
            } else {
                t.non_empty_list(elem_ty)
            }
        }
    }
}

fn binop_ty(op: BinOp, left: Ty, right: Ty) -> Ty {
    let mut t = types::new();
    match op {
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
            let int = t.int();
            let float = t.float();
            if t.is_subtype(&left, &int) && t.is_subtype(&right, &int) {
                t.int()
            } else if t.is_subtype(&left, &float) || t.is_subtype(&right, &float) {
                t.float()
            } else {
                t.any()
            }
        }
        BinOp::Eq
        | BinOp::Neq
        | BinOp::Lt
        | BinOp::LtEq
        | BinOp::Gt
        | BinOp::GtEq
        | BinOp::And
        | BinOp::Or
        | BinOp::In
        | BinOp::NotIn => t.bool(),
        BinOp::Pipe
        | BinOp::Cons
        | BinOp::ListConcat
        | BinOp::ListSubtract
        | BinOp::BinConcat
        | BinOp::Range
        | BinOp::RangeStep => t.any(),
    }
}

fn unop_ty(op: UnOp, input: Ty) -> Ty {
    let mut t = types::new();
    match op {
        UnOp::Not => t.bool(),
        UnOp::Neg => {
            let int = t.int();
            let float = t.float();
            if t.is_subtype(&input, &int) {
                t.int()
            } else if t.is_subtype(&input, &float) {
                t.float()
            } else {
                t.any()
            }
        }
    }
}

fn dedupe_outputs(outputs: Vec<(FactKey, FactValue)>) -> Vec<(FactKey, FactValue)> {
    let mut deduped: HashMap<FactKey, FactValue> = HashMap::new();
    for (fact, value) in outputs {
        let FactValue::Presence(revision) = value else {
            panic!("semantic job emits only presence facts")
        };
        deduped
            .entry(fact)
            .and_modify(|current| match current {
                FactValue::Presence(current_revision) => {
                    *current_revision = (*current_revision).max(revision);
                }
                FactValue::Inputs(_) => panic!("semantic job emits only presence facts"),
            })
            .or_insert(FactValue::Presence(revision));
    }
    deduped.into_iter().collect()
}
