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

use super::super::body::{
    CallSiteId, DirectCallee, Literal, LoweredBlock, LoweredBody, LoweredClause, LoweredStep, ValueId,
};
use super::super::drive::{FactKey, Job, JobEffects};
use super::super::facts::FactValue;
use super::super::identity::{ActivationKey, ExecutableNeed, FunctionId, ModuleId};
use super::super::scheduler::FatalError;
use super::super::semantic::{ActivationAnalysis, CallSiteKey, CallSiteSummary, SelectedCallee};
use super::super::types::{ClosureTarget, Ty, Types};
use super::super::world::World;

type DispatchPlan = PatternDispatchPlan<Ty>;
type ValueTypes = HashMap<ValueId, Ty>;

#[derive(Debug, Clone)]
struct CallEmission {
    key: CallSiteKey,
    summary: CallSiteSummary,
    callee_activation: Option<ActivationContribution>,
}

#[derive(Debug, Clone)]
struct ActivationContribution {
    key: ActivationKey,
    already_present: bool,
}

/// Analyzes one rooted function activation against its lowered body.
///
/// The job waits until the activation, lowered body, and entry dispatch all
/// exist. It then walks only the dispatch-reachable clauses, publishes direct
/// callsite summaries, and settles the activation's current return type.
pub(super) fn analyze_activation(world: &mut World<'_>, activation: &ActivationKey) -> Result<JobEffects, FatalError> {
    let activation_fact = FactKey::Activation(activation.clone());
    let Some(inputs) = world.activation_inputs(activation) else {
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
    let mut follow_up = HashSet::from([Job::SealSemanticClosure(activation.root)]);
    let mut outputs = Vec::new();

    let entry_dispatch = world.entry_dispatch(function);
    let lowered_body = world.lowered_body(function);
    let reachable_clauses = reachable_clause_ids(world, &entry_dispatch, &inputs);

    let mut analysis_calls = Vec::new();
    let mut value_types = HashMap::new();
    let mut return_ty = none_ty(world);
    match lowered_body {
        LoweredBody::Extern { signature } => {
            return_ty = signature.return_ty;
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
                merge_value_types(world, &mut value_types, &values);
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
                merge_value_types(world, &mut value_types, &values);
                return_ty = if world.types().is_empty(&return_ty) {
                    clause_return
                } else {
                    world.types_mut().union(return_ty, clause_return)
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
        outputs.push((
            FactKey::CallSiteSummary(call.key.clone()),
            FactValue::presence(revision),
        ));
        if let Some(callee_activation) = &call.callee_activation {
            outputs.push((
                FactKey::Activation(callee_activation.key.clone()),
                FactValue::inputs(world.types_mut(), call.summary.input_types.clone()),
            ));
            if !callee_activation.already_present {
                follow_up.insert(Job::AnalyzeActivation(callee_activation.key.clone()));
            }
            follow_up.insert(Job::SealSemanticClosure(activation.root));
        }
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
            value_types,
        },
    );
    outputs.push((
        FactKey::ActivationAnalyzed(activation.clone()),
        FactValue::presence(analysis_revision),
    ));

    follow_up.insert(Job::SealSemanticClosure(activation.root));
    Ok(JobEffects {
        reads,
        outputs: dedupe_outputs(world.types_mut(), outputs),
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
    Ok(values.get(&block.result).cloned().unwrap_or_else(|| any_ty(world)))
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
    for step in steps {
        apply_step(world, step, values, calls, activation, reads, waits, follow_up)?;
    }
    Ok(())
}

fn apply_step(
    world: &mut World<'_>,
    step: &LoweredStep,
    values: &mut ValueTypes,
    calls: &mut Vec<CallEmission>,
    activation: &ActivationKey,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<(), FatalError> {
    match step {
        LoweredStep::Const { value, literal } => {
            values.insert(*value, literal_ty(world, literal));
        }
        LoweredStep::Tuple { value, items } => {
            let items = items
                .iter()
                .map(|item| value_ty(world, values, *item))
                .collect::<Vec<_>>();
            values.insert(*value, world.types_mut().tuple(&items));
        }
        LoweredStep::List { value, items, tail } => {
            values.insert(*value, list_ty(world, values, items, *tail));
        }
        LoweredStep::FunctionRef { value, function } => {
            let arity = world.function_arity(*function);
            values.insert(
                *value,
                world.types_mut().fn_ref_lit(ClosureTarget(function.as_u32()), arity),
            );
        }
        LoweredStep::NamedFunctionRef { value, .. } => {
            values.insert(*value, any_ty(world));
        }
        LoweredStep::DirectCall {
            value,
            callsite,
            callee,
            args,
        } => {
            let arg_types = args
                .iter()
                .map(|arg| value_ty(world, values, arg.value))
                .collect::<Vec<_>>();
            let (emission, return_ty) = resolve_direct_call(
                world,
                activation,
                *callsite,
                callee,
                arg_types.clone(),
                reads,
                waits,
                follow_up,
            )?;
            if let Some(emission) = emission {
                calls.push(emission);
            }
            values.insert(*value, return_ty);
        }
        LoweredStep::ClosureCall {
            value,
            callsite,
            callee,
            args,
        } => {
            let callee_ty = value_ty(world, values, *callee);
            let arg_types = args
                .iter()
                .map(|arg| value_ty(world, values, arg.value))
                .collect::<Vec<_>>();
            let (emission, return_ty) = resolve_closure_call(
                world,
                activation,
                *callsite,
                callee_ty,
                arg_types.clone(),
                reads,
                waits,
                follow_up,
            )?;
            if let Some(emission) = emission {
                calls.push(emission);
            }
            values.insert(*value, return_ty);
        }
        LoweredStep::Lambda {
            value,
            function,
            captures,
        } => {
            let captures = captures
                .iter()
                .map(|capture| value_ty(world, values, *capture))
                .collect();
            values.insert(*value, world.closure_ty(*function, captures));
        }
        LoweredStep::BinaryOp { value, op, left, right } => {
            let left = value_ty(world, values, *left);
            let right = value_ty(world, values, *right);
            values.insert(*value, binop_ty(world, *op, left, right));
        }
        LoweredStep::UnaryOp { value, op, input } => {
            let input = value_ty(world, values, *input);
            values.insert(*value, unop_ty(world, *op, input));
        }
        LoweredStep::MapIndex { value, .. } => {
            values.insert(*value, any_ty(world));
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
            values.insert(*value, world.types_mut().union(then_ty, else_ty));
        }
        LoweredStep::AssertLiteral { source, literal } => {
            let source_ty = value_ty(world, values, *source);
            let literal_ty = literal_ty(world, literal);
            let refined = world.types_mut().intersect(source_ty, literal_ty);
            values.insert(*source, refined);
        }
        LoweredStep::AssertTuple { source, arity } => {
            let any = world.types_mut().any();
            let fields = world.types_mut().repeat(any, *arity);
            let tuple = world.types_mut().tuple(&fields);
            let source_ty = value_ty(world, values, *source);
            let refined = world.types_mut().intersect(source_ty, tuple);
            values.insert(*source, refined);
        }
        LoweredStep::TupleField { value, source, index } => {
            let source = value_ty(world, values, *source);
            values.insert(*value, world.types_mut().tuple_field_type(&source, *index));
        }
        LoweredStep::AssertEmptyList { source } => {
            let empty = world.types_mut().empty_list();
            let source_ty = value_ty(world, values, *source);
            let refined = world.types_mut().intersect(source_ty, empty);
            values.insert(*source, refined);
        }
        LoweredStep::AssertSame { source, value } => {
            let source_ty = value_ty(world, values, *source);
            let value_ty = value_ty(world, values, *value);
            let both = world.types_mut().intersect(source_ty, value_ty);
            values.insert(*source, both);
            values.insert(*value, both);
        }
        LoweredStep::SplitList { source, head, tail } => {
            let source_ty = value_ty(world, values, *source);
            let elem = world.types_mut().list_element_type(&source_ty);
            let tail_ty = world.types_mut().list(elem);
            values.insert(*head, elem);
            values.insert(*tail, tail_ty);
        }
    }
    Ok(())
}

fn resolve_direct_call(
    world: &mut World<'_>,
    caller: &ActivationKey,
    callsite: CallSiteId,
    callee: &DirectCallee,
    arg_types: Vec<Ty>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<(Option<CallEmission>, Ty), FatalError> {
    if arg_types.iter().any(|arg| world.types().is_empty(arg)) {
        let none = none_ty(world);
        let summary = call_summary(selected_callee(callee), arg_types, none);
        return Ok((
            summary.map(|summary| CallEmission {
                key: CallSiteKey {
                    activation: caller.clone(),
                    callsite,
                },
                summary,
                callee_activation: None,
            }),
            none,
        ));
    }

    let (summary, callee_activation, return_ty) = match callee {
        DirectCallee::Function(function) => {
            resolve_function_call(world, caller, *function, arg_types, reads, waits, follow_up)?
        }
        DirectCallee::Named { .. } => (
            call_summary(selected_callee(callee), arg_types, any_ty(world)),
            None,
            any_ty(world),
        ),
    };
    Ok((
        summary.map(|summary| CallEmission {
            key: CallSiteKey {
                activation: caller.clone(),
                callsite,
            },
            summary,
            callee_activation,
        }),
        return_ty,
    ))
}

fn merge_value_types(world: &mut World<'_>, merged: &mut ValueTypes, observed: &ValueTypes) {
    for (&value, &ty) in observed {
        match merged.get(&value).copied() {
            Some(current) if current != ty => {
                merged.insert(value, world.types_mut().union(current, ty));
            }
            Some(_) => {}
            None => {
                merged.insert(value, ty);
            }
        }
    }
}

fn resolve_function_call(
    world: &mut World<'_>,
    caller: &ActivationKey,
    function: FunctionId,
    input_types: Vec<Ty>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<(Option<CallSiteSummary>, Option<ActivationContribution>, Ty), FatalError> {
    if let Some(callback) = world.protocol_callback(function) {
        return resolve_protocol_call(
            world,
            caller,
            function,
            callback.protocol,
            input_types,
            reads,
            waits,
            follow_up,
        );
    }
    if wait_for_unresolved_function_module(world, function, waits, follow_up) {
        return Ok((None, None, any_ty(world)));
    }
    let Some((activation, already_present, return_ty)) =
        prepare_function_call(world, caller, function, input_types.clone(), reads, waits, follow_up)
    else {
        return Ok((None, None, any_ty(world)));
    };
    Ok((
        Some(CallSiteSummary {
            callee: SelectedCallee::Function(function),
            input_types,
            return_ty,
        }),
        Some(ActivationContribution {
            key: activation,
            already_present,
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
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<(Option<CallSiteSummary>, Option<ActivationContribution>, Ty), FatalError> {
    let protocol_fact = FactKey::ModuleDefined(protocol);
    if world.module_defined_revision(protocol).is_none() {
        wait_for_protocol_module(world, protocol, waits, follow_up);
        return Ok((None, None, any_ty(world)));
    }
    reads.push(protocol_fact);

    let receiver_ty = input_types.first().cloned().unwrap_or_else(|| any_ty(world));
    let function_ref = world.function_ref(callback_function).clone();

    let mut matches = Vec::new();
    for (key, protocol_impl) in world.protocol_impls_for(protocol) {
        let target_ty = world.module_impl_target_ty(key.target);
        if !world.types().is_subtype(&receiver_ty, &target_ty) {
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
        return Ok((None, None, any_ty(world)));
    }

    if matches.len() != 1 {
        return Ok((None, None, any_ty(world)));
    }

    let selected = matches[0];
    let owner_fact = FactKey::ModuleDefined(selected.owner_module);
    if world.module_defined_revision(selected.owner_module).is_none() {
        waits.insert(owner_fact);
        follow_up.insert(Job::DefineModule(selected.owner_module));
        return Ok((None, None, any_ty(world)));
    }
    reads.push(owner_fact);

    let Some((activation, already_present, return_ty)) = prepare_function_call(
        world,
        caller,
        selected.function,
        input_types.clone(),
        reads,
        waits,
        follow_up,
    ) else {
        return Ok((None, None, any_ty(world)));
    };
    Ok((
        Some(CallSiteSummary {
            callee: SelectedCallee::Function(selected.function),
            input_types,
            return_ty,
        }),
        Some(ActivationContribution {
            key: activation,
            already_present,
        }),
        return_ty,
    ))
}

fn resolve_closure_call(
    world: &mut World<'_>,
    caller: &ActivationKey,
    callsite: CallSiteId,
    callee_ty: Ty,
    arg_types: Vec<Ty>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<(Option<CallEmission>, Ty), FatalError> {
    if world.types().is_empty(&callee_ty) || arg_types.iter().any(|arg| world.types().is_empty(arg)) {
        return Ok((None, none_ty(world)));
    }
    let Some(parts) = world.types().closure_lit_parts(&callee_ty) else {
        return Ok((None, any_ty(world)));
    };
    let function = FunctionId::from_u32(parts.target.0);
    let mut inputs = parts.captures;
    inputs.extend(arg_types);
    let (summary, callee_activation, return_ty) =
        resolve_function_call(world, caller, function, inputs, reads, waits, follow_up)?;
    Ok((
        summary.map(|summary| CallEmission {
            key: CallSiteKey {
                activation: caller.clone(),
                callsite,
            },
            summary,
            callee_activation,
        }),
        return_ty,
    ))
}

fn prepare_function_call(
    world: &mut World<'_>,
    caller: &ActivationKey,
    function: FunctionId,
    arg_types: Vec<Ty>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Option<(ActivationKey, bool, Ty)> {
    if !world.require_activation_key_facts(function, reads, waits, follow_up) {
        return None;
    }

    let activation = world.activation_key(caller.root, function, &arg_types);
    let already_present = world.fact_revision(FactKey::Activation(activation.clone())).is_some();
    reads.push(FactKey::ReturnType(activation.clone()));
    follow_up.insert(Job::SealSemanticClosure(caller.root));
    let return_ty = world.activation_return(&activation).unwrap_or_else(|| none_ty(world));
    Some((activation, already_present, return_ty))
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

fn wait_for_unresolved_function_module(
    world: &mut World<'_>,
    function: FunctionId,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> bool {
    if world.function_defined_revision(function).is_some() {
        return false;
    }
    let module = world.function_module(function);
    if module.is_global() || world.module_defined_revision(module).is_some() {
        return false;
    }
    waits.insert(FactKey::ModuleDefined(module));
    follow_up.extend(world.ensure_function_surface(function));
    true
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

fn call_summary(callee: Option<SelectedCallee>, input_types: Vec<Ty>, return_ty: Ty) -> Option<CallSiteSummary> {
    Some(CallSiteSummary {
        callee: callee?,
        input_types,
        return_ty,
    })
}

fn reachable_clause_ids(world: &mut World<'_>, plan: &DispatchPlan, inputs: &[Ty]) -> Vec<u32> {
    let mut subjects = HashMap::new();
    for ordinal in 0..plan.input_count {
        let input = inputs.get(ordinal).cloned().unwrap_or_else(|| any_ty(world));
        let Some(subject_id) = plan.matrix.subjects.iter().find_map(|subject| match subject.source {
            SubjectSource::Input { ordinal: input_ordinal } if input_ordinal as usize == ordinal => Some(subject.id),
            _ => None,
        }) else {
            continue;
        };
        subjects.insert(subject_id, input);
    }
    let mut outcomes = HashSet::new();
    collect_reachable_outcomes(world, plan, plan.graph.root, &subjects, &mut outcomes);
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
    world: &mut World<'_>,
    plan: &DispatchPlan,
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
                .unwrap_or_else(|| any_ty(world));
            if branch_possible(world, predicate, &source, true) {
                let mut next = subjects.clone();
                apply_evidence(world, plan, &mut next, &source, predicate, &on_match.evidence, true);
                collect_reachable_outcomes(world, plan, on_match.target, &next, outcomes);
            }
            if branch_possible(world, predicate, &source, false) {
                let mut next = subjects.clone();
                apply_evidence(world, plan, &mut next, &source, predicate, &on_miss.evidence, false);
                collect_reachable_outcomes(world, plan, on_miss.target, &next, outcomes);
            }
        }
    }
}

fn branch_possible(world: &mut World<'_>, predicate: &RegionPredicate<Ty>, source: &Ty, is_match: bool) -> bool {
    match &predicate.region {
        Region::Type(ty) => {
            if is_match {
                let overlap = world.types_mut().intersect(*source, *ty);
                !world.types().is_empty(&overlap)
            } else {
                !world.types().is_subtype(source, ty)
            }
        }
        Region::Equal(value) => {
            let target = comparison_ty(world, value);
            if is_match {
                let overlap = world.types_mut().intersect(*source, target);
                !world.types().is_empty(&overlap)
            } else {
                !world.types().is_subtype(source, &target)
            }
        }
        Region::TupleArity(arity) => {
            let any = world.types_mut().any();
            let fields = world.types_mut().repeat(any, *arity as usize);
            let tuple = world.types_mut().tuple(&fields);
            if is_match {
                let overlap = world.types_mut().intersect(*source, tuple);
                !world.types().is_empty(&overlap)
            } else {
                !world.types().is_subtype(source, &tuple)
            }
        }
        Region::List(ListRegion::Empty) => {
            let empty = world.types_mut().empty_list();
            if is_match {
                let overlap = world.types_mut().intersect(*source, empty);
                !world.types().is_empty(&overlap)
            } else {
                !world.types().is_subtype(source, &empty)
            }
        }
        Region::List(ListRegion::Cons) => {
            let any = world.types_mut().any();
            let cons = world.types_mut().non_empty_list(any);
            if is_match {
                let overlap = world.types_mut().intersect(*source, cons);
                !world.types().is_empty(&overlap)
            } else {
                !world.types().is_subtype(source, &cons)
            }
        }
        Region::MapKind => {
            let map = world.types_mut().map_top();
            if is_match {
                let overlap = world.types_mut().intersect(*source, map);
                !world.types().is_empty(&overlap)
            } else {
                !world.types().is_subtype(source, &map)
            }
        }
        Region::Guard(_) => true,
        Region::MapKeyPresent { .. } | Region::Bitstring(_) | Region::Any | Region::Never => true,
    }
}

fn apply_evidence(
    world: &mut World<'_>,
    plan: &DispatchPlan,
    subjects: &mut HashMap<SubjectId, Ty>,
    source: &Ty,
    predicate: &RegionPredicate<Ty>,
    evidence: &EdgeEvidence<Ty>,
    is_match: bool,
) {
    let refined = match &predicate.region {
        Region::Type(ty) if is_match => world.types_mut().intersect(*source, *ty),
        Region::Equal(value) if is_match => {
            let target = comparison_ty(world, value);
            world.types_mut().intersect(*source, target)
        }
        Region::TupleArity(arity) if is_match => {
            let any = world.types_mut().any();
            let fields = world.types_mut().repeat(any, *arity as usize);
            let tuple = world.types_mut().tuple(&fields);
            world.types_mut().intersect(*source, tuple)
        }
        Region::List(ListRegion::Empty) if is_match => {
            let empty = world.types_mut().empty_list();
            world.types_mut().intersect(*source, empty)
        }
        Region::List(ListRegion::Cons) if is_match => {
            let any = world.types_mut().any();
            let cons = world.types_mut().non_empty_list(any);
            world.types_mut().intersect(*source, cons)
        }
        _ => *source,
    };
    subjects.insert(predicate.subject, refined);

    for projection in &evidence.projections {
        let base = subjects.get(&projection.source).cloned().unwrap_or(*source);
        let projected = match &projection.kind {
            crate::dispatch_matrix::ProjectionKind::TupleField(index) => {
                world.types_mut().tuple_field_type(&base, *index as usize)
            }
            crate::dispatch_matrix::ProjectionKind::ListHead => world.types_mut().list_element_type(&base),
            crate::dispatch_matrix::ProjectionKind::ListTail => {
                let elem = world.types_mut().list_element_type(&base);
                world.types_mut().list(elem)
            }
            crate::dispatch_matrix::ProjectionKind::MapValue { .. } => any_ty(world),
            crate::dispatch_matrix::ProjectionKind::BitstringField(_) => any_ty(world),
        };
        subjects.insert(projection.result, projected);
    }

    for proof in &evidence.proofs {
        if proof.predicate.subject != predicate.subject {
            let _ = plan.subject_ref(proof.predicate.subject);
        }
    }
}

pub(super) fn executable_callsite_needs(
    body: &LoweredBody,
    reachable_clauses: &[u32],
    executable_need: ExecutableNeed,
) -> HashMap<CallSiteId, ExecutableNeed> {
    let mut needs = HashMap::new();
    let LoweredBody::Clauses { clauses, .. } = body else {
        return needs;
    };
    for clause_id in reachable_clauses {
        collect_clause_callsite_needs(&clauses[*clause_id as usize], executable_need, &mut needs);
    }
    needs
}

fn collect_clause_callsite_needs(
    clause: &LoweredClause,
    executable_need: ExecutableNeed,
    out: &mut HashMap<CallSiteId, ExecutableNeed>,
) {
    let mut tuple_demands = HashMap::new();
    if let ExecutableNeed::TupleFields(arity) = executable_need {
        tuple_demands.insert(clause.body.result, arity);
    }
    collect_steps_callsite_needs_reverse(&clause.body.steps, &mut tuple_demands, out);
    collect_steps_callsite_needs_reverse(&clause.projections, &mut tuple_demands, out);
}

fn collect_block_callsite_needs(
    block: &LoweredBlock,
    block_need: ExecutableNeed,
    out: &mut HashMap<CallSiteId, ExecutableNeed>,
) {
    let mut tuple_demands = HashMap::new();
    if let ExecutableNeed::TupleFields(arity) = block_need {
        tuple_demands.insert(block.result, arity);
    }
    collect_steps_callsite_needs_reverse(&block.steps, &mut tuple_demands, out);
}

fn collect_steps_callsite_needs_reverse(
    steps: &[LoweredStep],
    tuple_demands: &mut HashMap<ValueId, usize>,
    out: &mut HashMap<CallSiteId, ExecutableNeed>,
) {
    for step in steps.iter().rev() {
        match step {
            LoweredStep::AssertTuple { source, arity } => {
                tuple_demands.insert(*source, *arity);
            }
            LoweredStep::DirectCall { value, callsite, .. } | LoweredStep::ClosureCall { value, callsite, .. } => {
                let need = tuple_demands
                    .remove(value)
                    .map(ExecutableNeed::TupleFields)
                    .unwrap_or(ExecutableNeed::Value);
                record_callsite_need(out, *callsite, need);
            }
            LoweredStep::If {
                value,
                then_block,
                else_block,
                ..
            } => {
                let branch_need = tuple_demands
                    .remove(value)
                    .map(ExecutableNeed::TupleFields)
                    .unwrap_or(ExecutableNeed::Value);
                collect_block_callsite_needs(then_block, branch_need, out);
                collect_block_callsite_needs(else_block, branch_need, out);
            }
            LoweredStep::Const { value, .. }
            | LoweredStep::Tuple { value, .. }
            | LoweredStep::List { value, .. }
            | LoweredStep::FunctionRef { value, .. }
            | LoweredStep::NamedFunctionRef { value, .. }
            | LoweredStep::Lambda { value, .. }
            | LoweredStep::BinaryOp { value, .. }
            | LoweredStep::UnaryOp { value, .. }
            | LoweredStep::MapIndex { value, .. }
            | LoweredStep::TupleField { value, .. } => {
                tuple_demands.remove(value);
            }
            LoweredStep::SplitList { head, tail, .. } => {
                tuple_demands.remove(head);
                tuple_demands.remove(tail);
            }
            LoweredStep::AssertLiteral { .. }
            | LoweredStep::AssertEmptyList { .. }
            | LoweredStep::AssertSame { .. } => {}
        }
    }
}

fn record_callsite_need(out: &mut HashMap<CallSiteId, ExecutableNeed>, callsite: CallSiteId, observed: ExecutableNeed) {
    use std::collections::hash_map::Entry;

    match out.entry(callsite) {
        Entry::Vacant(entry) => {
            entry.insert(observed);
        }
        Entry::Occupied(mut entry) => match (*entry.get(), observed) {
            (ExecutableNeed::Value, ExecutableNeed::Value)
            | (ExecutableNeed::TupleFields(_), ExecutableNeed::Value) => {}
            (ExecutableNeed::Value, tuple_fields @ ExecutableNeed::TupleFields(_)) => {
                entry.insert(tuple_fields);
            }
            (ExecutableNeed::TupleFields(existing), ExecutableNeed::TupleFields(observed)) => {
                assert_eq!(
                    existing, observed,
                    "one callsite cannot require two different tuple-field return arities"
                );
            }
        },
    }
}

fn value_ty(world: &mut World<'_>, values: &ValueTypes, value: ValueId) -> Ty {
    values.get(&value).cloned().unwrap_or_else(|| any_ty(world))
}

fn literal_ty(world: &mut World<'_>, literal: &Literal) -> Ty {
    match literal {
        Literal::Int(value) => world.types_mut().int_lit(*value),
        Literal::Float(value) => world.types_mut().float_lit(*value),
        Literal::Binary(_) => world.types_mut().str_t(),
        Literal::Atom(name) => world.types_mut().atom_lit(name),
        Literal::Bool(value) => world.types_mut().bool_lit(*value),
        Literal::Nil => world.types_mut().nil(),
    }
}

fn comparison_ty(world: &mut World<'_>, value: &ComparisonValue) -> Ty {
    match value {
        ComparisonValue::Const(value) => dispatch_const_ty(world, value),
        ComparisonValue::Pinned(_) => any_ty(world),
    }
}

fn dispatch_const_ty(world: &mut World<'_>, value: &DispatchConst) -> Ty {
    match value {
        DispatchConst::Int(value) => world.types_mut().int_lit(*value),
        DispatchConst::FloatBits(value) => world.types_mut().float_lit(f64::from_bits(*value)),
        DispatchConst::AtomName(name) => world.types_mut().atom_lit(name),
        DispatchConst::Bool(value) => world.types_mut().bool_lit(*value),
        DispatchConst::Nil | DispatchConst::EmptyList => world.types_mut().empty_list(),
        DispatchConst::Utf8Binary(_) => world.types_mut().str_t(),
    }
}

fn list_ty(world: &mut World<'_>, values: &ValueTypes, items: &[ValueId], tail: Option<ValueId>) -> Ty {
    let mut elem_ty = none_ty(world);
    for item in items {
        let item_ty = value_ty(world, values, *item);
        elem_ty = if world.types().is_empty(&elem_ty) {
            item_ty
        } else {
            world.types_mut().union(elem_ty, item_ty)
        };
    }
    match tail {
        Some(tail) => {
            let tail_ty = value_ty(world, values, tail);
            if world.types().has_list_shape(&tail_ty) {
                let tail_elem = world.types_mut().list_element_type(&tail_ty);
                let elem_ty = if world.types().is_empty(&elem_ty) {
                    tail_elem
                } else {
                    world.types_mut().union(elem_ty, tail_elem)
                };
                world.types_mut().list(elem_ty)
            } else if world.types().is_empty(&elem_ty) {
                let any = any_ty(world);
                world.types_mut().list(any)
            } else {
                world.types_mut().non_empty_list(elem_ty)
            }
        }
        None => {
            if items.is_empty() {
                world.types_mut().empty_list()
            } else if world.types().is_empty(&elem_ty) {
                let any = any_ty(world);
                world.types_mut().list(any)
            } else {
                world.types_mut().non_empty_list(elem_ty)
            }
        }
    }
}

fn binop_ty(world: &mut World<'_>, op: BinOp, left: Ty, right: Ty) -> Ty {
    match op {
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
            let int = world.types_mut().int();
            let float = world.types_mut().float();
            if world.types().is_subtype(&left, &int) && world.types().is_subtype(&right, &int) {
                world.types_mut().int()
            } else if world.types().is_subtype(&left, &float) || world.types().is_subtype(&right, &float) {
                world.types_mut().float()
            } else {
                any_ty(world)
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
        | BinOp::NotIn => world.types_mut().bool(),
        BinOp::Pipe
        | BinOp::Cons
        | BinOp::ListConcat
        | BinOp::ListSubtract
        | BinOp::BinConcat
        | BinOp::Range
        | BinOp::RangeStep => any_ty(world),
    }
}

fn unop_ty(world: &mut World<'_>, op: UnOp, input: Ty) -> Ty {
    match op {
        UnOp::Not => world.types_mut().bool(),
        UnOp::Neg => {
            let int = world.types_mut().int();
            let float = world.types_mut().float();
            if world.types().is_subtype(&input, &int) {
                world.types_mut().int()
            } else if world.types().is_subtype(&input, &float) {
                world.types_mut().float()
            } else {
                any_ty(world)
            }
        }
    }
}

fn dedupe_outputs(types: &mut Types, outputs: Vec<(FactKey, FactValue)>) -> Vec<(FactKey, FactValue)> {
    let mut deduped: HashMap<FactKey, FactValue> = HashMap::new();
    for (fact, value) in outputs {
        deduped
            .entry(fact)
            .and_modify(|current| {
                let joined = FactValue::join(types, [&*current, &value])
                    .expect("deduping one current value with one new value should produce a value");
                *current = joined;
            })
            .or_insert(value);
    }
    deduped.into_iter().collect()
}

fn any_ty(world: &mut World<'_>) -> Ty {
    world.types_mut().any()
}

fn none_ty(world: &mut World<'_>) -> Ty {
    world.types_mut().none()
}
