//! Compiler2 semantic-analysis jobs.
//!
//! This module walks lowered function bodies through already-planned entry
//! dispatch, derives direct-call summaries, and settles per-activation return
//! types without calling the legacy whole-program pipeline.

use std::collections::{BTreeMap, HashMap, HashSet, hash_map::Entry};

use crate::ast::{BinOp, UnOp};
use crate::dispatch_matrix::pattern::PatternDispatchPlan;
use crate::dispatch_matrix::{
    ComparisonValue, DispatchConst, DispatchNode, EdgeEvidence, GraphNodeId, ListRegion, Region, RegionPredicate,
    SubjectId, SubjectSource,
};

use super::super::body::{
    CallSiteId, ControlDestination, DirectCallee, Literal, LoweredBody, LoweredClause, LoweredEntry, LoweredMapKey,
    LoweredStep, LoweredTail, ValueId,
};
use super::super::contract::FunctionContract;
use super::super::drive::{FactKey, Job, JobEffects, current_uses};
use super::super::identity::{
    ActivationKey, ExecutableKey, ExecutableNeed, FunctionId, ModuleId, function_id_of_closure_target,
};
use super::super::scheduler::FatalError;
use super::super::semantic::{ActivationAnalysis, CallSiteKey, CallSiteSummary, CallTargetSummary, SelectedCallee};
use super::super::types::{ClosureTarget, Ty};
use super::super::world::World;

type DispatchPlan = PatternDispatchPlan<Ty>;
type SemanticValues = HashMap<ValueId, Ty>;
type ValueTypes = HashMap<ValueId, Ty>;
type RefinedCallSurface = (Vec<Ty>, Option<Ty>);
/// One resolved call: its summary (when a single emission applies), the
/// activation demand it contributes, and its return evidence.
type ResolvedCall = (Option<CallSiteSummary>, Vec<ActivationContribution>, Option<Ty>);

#[derive(Debug, Clone)]
struct CallEmission {
    key: CallSiteKey,
    summary: Option<CallSiteSummary>,
    activations: Vec<ActivationContribution>,
    latent_executables: Vec<super::super::identity::ExecutableKey>,
}

#[derive(Debug, Clone)]
struct ActivationContribution {
    key: ActivationKey,
    inputs: Vec<Ty>,
    already_present: bool,
}

#[derive(Debug, Clone)]
struct CoalescedCallEmission {
    call: CallEmission,
    observations: usize,
}

/// Analyzes one rooted function activation against its lowered body.
///
/// The job waits until the activation, lowered body, and entry dispatch all
/// exist. It then walks only the dispatch-reachable clauses, publishes direct
/// callsite summaries, and settles the activation's current return type.
pub(super) fn analyze_activation(world: &mut World<'_>, activation: &ActivationKey) -> Result<JobEffects, FatalError> {
    let activation_fact = FactKey::Activation(activation.clone());
    if !world.has_fact(&activation_fact) {
        return Ok(JobEffects::default());
    }
    let activation_inputs_fact = FactKey::ActivationInputs(activation.clone());
    let Some(inputs) = world.activation_inputs(activation) else {
        return Ok(JobEffects::wait_on_current(activation_inputs_fact, []));
    };

    let function = activation.function;
    let function_fact = FactKey::FunctionDefined(function);
    let Some(_) = world.function_defined_revision(function) else {
        return Ok(world.wait_for_function_definition(function));
    };

    let lowered_fact = FactKey::LoweredBody(function);
    if !world.has_fact(&lowered_fact) {
        return Ok(JobEffects::wait_on_current(
            lowered_fact,
            [Job::LowerFunction(function)],
        ));
    }

    let dispatch_fact = FactKey::EntryDispatch(function);
    if !world.has_fact(&dispatch_fact) {
        return Ok(JobEffects::wait_on_current(
            dispatch_fact,
            [Job::PlanEntryDispatch(function)],
        ));
    }

    let mut reads = vec![
        FactKey::Activation(activation.clone()),
        FactKey::ActivationInputs(activation.clone()),
        function_fact,
        lowered_fact,
        dispatch_fact,
    ];
    let mut waits = HashSet::new();
    let mut follow_up = HashSet::from([Job::SealSemanticClosure(activation.root)]);
    let mut outputs = Vec::new();
    let mut changed = Vec::new();

    let entry_dispatch = world.entry_dispatch(function);
    let lowered_body = world.lowered_body(function);
    let reachable_clauses = reachable_clause_ids(world, &entry_dispatch, &inputs);

    let mut analysis_calls = Vec::new();
    let mut reachable_entries = HashSet::new();
    let mut value_types = HashMap::new();
    // The activation's return evidence. `None` is the ascent's bottom — "no
    // path has produced a value yet" — never the type `none`, which remains
    // a provable fact (a body all of whose paths halt). At the fixpoint the
    // two coincide; mid-climb only readers of settled facts may conflate
    // them, and the settled gate keeps everyone else out.
    let mut return_evidence: Option<Ty> = None;
    match lowered_body {
        LoweredBody::Extern { signature } => {
            return_evidence = Some(signature.return_ty);
        }
        LoweredBody::Clauses { clauses, entries, .. } => {
            for clause_id in &reachable_clauses {
                let clause = &clauses[*clause_id as usize];
                // Input evidence that has not caught up to the clause's
                // arity cannot bind its params. Like an absent capture,
                // incomplete evidence yields no evidence — the analysis
                // re-runs when the joined inputs grow. Never `any`.
                if clause.params.len() > inputs.len() {
                    continue;
                }
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
                let clause_return = analyze_entry(
                    world,
                    entries.as_slice(),
                    clause.entry,
                    &values,
                    &mut reachable_entries,
                    &mut value_types,
                    &mut analysis_calls,
                    activation,
                    &mut reads,
                    &mut waits,
                    &mut follow_up,
                )?;
                return_evidence = join_evidence(world, return_evidence, clause_return);
            }
        }
    }

    if let Some(contract_return_ty) =
        activation_contract_return(world, function, &inputs, &mut reads, &mut waits, &mut follow_up)?
    {
        return_evidence = refine_call_return(world, return_evidence, Some(contract_return_ty));
    }

    // Waits no longer bail: a waiting completion extends the job's standing
    // claims (it cannot retract), so partial evidence publishes safely and
    // the waits simply ride the final effects.
    analysis_calls = coalesce_call_emissions(
        world,
        activation,
        analysis_calls,
        &mut reads,
        &mut waits,
        &mut follow_up,
    )?;

    let covered_callable_activations = covered_callable_activations(&analysis_calls);
    let latent_callable_activations = match return_evidence {
        Some(return_ty) => resolve_escaping_callable_activations_from_type(
            world,
            activation,
            return_ty,
            &covered_callable_activations,
            &mut reads,
            &mut waits,
            &mut follow_up,
        ),
        None => Vec::new(),
    };

    let mut emitted_activations = HashSet::new();
    let mut emitted_executables = HashSet::new();
    let mut activation_input_contributions = Vec::new();
    for call in &analysis_calls {
        if let Some(summary) = &call.summary {
            let callsite_fact = FactKey::CallSiteSummary(call.key.clone());
            let callsite_changed = world.define_callsite_summary(call.key.clone(), summary.clone());
            outputs.push(callsite_fact.clone());
            if callsite_changed {
                changed.push(callsite_fact);
            }
        }
        for callee_activation in &call.activations {
            if emitted_activations.insert(callee_activation.key.clone()) {
                outputs.push(FactKey::Activation(callee_activation.key.clone()));
            }
            outputs.push(FactKey::ActivationInputs(callee_activation.key.clone()));
            activation_input_contributions.push((callee_activation.key.clone(), callee_activation.inputs.clone()));
            if !callee_activation.already_present {
                follow_up.insert(Job::AnalyzeActivation(callee_activation.key.clone()));
            }
            follow_up.insert(Job::SealSemanticClosure(activation.root));
        }
        for executable in &call.latent_executables {
            if emitted_executables.insert(executable.clone()) {
                outputs.push(FactKey::Executable(executable.clone()));
            }
        }
    }

    for callable_activation in &latent_callable_activations {
        if emitted_activations.insert(callable_activation.key.clone()) {
            outputs.push(FactKey::Activation(callable_activation.key.clone()));
        }
        outputs.push(FactKey::ActivationInputs(callable_activation.key.clone()));
        activation_input_contributions.push((callable_activation.key.clone(), callable_activation.inputs.clone()));
        if !callable_activation.already_present {
            follow_up.insert(Job::AnalyzeActivation(callable_activation.key.clone()));
        }
        follow_up.insert(Job::SealSemanticClosure(activation.root));
    }

    let return_changed = world.define_activation_return(activation, return_evidence);
    let return_fact = FactKey::ReturnType(activation.clone());
    outputs.push(return_fact.clone());
    if return_changed {
        changed.push(return_fact);
    }

    let analysis_changed = world.define_activation_analysis(
        activation,
        ActivationAnalysis {
            reachable_clauses: reachable_clauses.clone(),
            reachable_entries: {
                let mut entries = reachable_entries.into_iter().collect::<Vec<_>>();
                entries.sort_by_key(|entry| entry.as_u32());
                entries
            },
            callsites: analysis_calls
                .iter()
                .filter_map(|call| call.summary.as_ref().map(|_| call.key.callsite))
                .collect(),
            latent_executables: analysis_calls
                .iter()
                .flat_map(|call| call.latent_executables.iter().cloned())
                .chain(latent_callable_activations.iter().map(|activation| ExecutableKey {
                    activation: activation.key.clone(),
                    need: ExecutableNeed::Value,
                }))
                .collect(),
            value_types,
        },
    );
    let analyzed_fact = FactKey::ActivationAnalyzed(activation.clone());
    outputs.push(analyzed_fact.clone());
    if analysis_changed {
        changed.push(analyzed_fact);
    }

    follow_up.insert(Job::SealSemanticClosure(activation.root));
    Ok(JobEffects {
        reads: current_uses(reads),
        waits: current_uses(waits),
        outputs: dedupe_facts(outputs),
        changed: dedupe_facts(changed),
        activation_input_contributions,
        follow_up: follow_up.into_iter().collect(),
    })
}

fn analyze_entry(
    world: &mut World<'_>,
    entries: &[LoweredEntry],
    entry_id: super::super::body::ControlEntryId,
    values: &SemanticValues,
    reachable_entries: &mut HashSet<super::super::body::ControlEntryId>,
    value_types: &mut ValueTypes,
    calls: &mut Vec<CallEmission>,
    activation: &ActivationKey,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<Option<Ty>, FatalError> {
    reachable_entries.insert(entry_id);
    let entry = &entries[entry_id.as_u32() as usize];
    let mut local = values.clone();
    apply_steps(
        world,
        &entry.steps,
        &mut local,
        calls,
        activation,
        reads,
        waits,
        follow_up,
    )?;
    merge_value_types(world, value_types, &local);
    analyze_tail(
        world,
        entries,
        &entry.tail,
        &local,
        reachable_entries,
        value_types,
        calls,
        activation,
        reads,
        waits,
        follow_up,
    )
}

fn apply_steps(
    world: &mut World<'_>,
    steps: &[LoweredStep],
    values: &mut SemanticValues,
    _calls: &mut Vec<CallEmission>,
    _activation: &ActivationKey,
    _reads: &mut Vec<FactKey>,
    _waits: &mut HashSet<FactKey>,
    _follow_up: &mut HashSet<Job>,
) -> Result<(), FatalError> {
    for step in steps {
        apply_step(world, step, values, _calls, _activation, _reads, _waits, _follow_up)?;
    }
    Ok(())
}

fn apply_step(
    world: &mut World<'_>,
    step: &LoweredStep,
    values: &mut SemanticValues,
    _calls: &mut Vec<CallEmission>,
    _activation: &ActivationKey,
    _reads: &mut Vec<FactKey>,
    _waits: &mut HashSet<FactKey>,
    _follow_up: &mut HashSet<Job>,
) -> Result<(), FatalError> {
    match step {
        LoweredStep::Const { value, literal } => {
            let literal_ty = literal_ty(world, literal);
            values.insert(*value, literal_ty);
        }
        LoweredStep::Tuple { value, items } => {
            let items = items
                .iter()
                .map(|item| value_ty(world, values, *item))
                .collect::<Vec<_>>();
            let tuple = world.types_mut().tuple(&items);
            values.insert(*value, tuple);
        }
        LoweredStep::List { value, items, tail } => {
            let list = list_ty(world, values, items, *tail);
            values.insert(*value, list);
        }
        LoweredStep::Map { value, entries } => {
            let map = map_ty(world, values, entries);
            values.insert(*value, map);
        }
        LoweredStep::MapUpdate { value, base, entries } => {
            let mut map_ty = value_ty(world, values, *base);
            for (key, item) in entries {
                if let Some(key) = lowered_map_key(world, values, key) {
                    let item_ty = value_ty(world, values, *item);
                    map_ty = world.types_mut().refine_map_field(&map_ty, &key, &item_ty);
                } else {
                    map_ty = world.types_mut().map_top();
                    break;
                }
            }
            values.insert(*value, map_ty);
        }
        LoweredStep::Struct { value, module, fields } => {
            let field_tys = fields
                .iter()
                .map(|(_, value)| value_ty(world, values, *value))
                .collect::<Vec<_>>();
            let struct_ty = world.module_struct_value_ty(*module, &field_tys);
            values.insert(*value, struct_ty);
        }
        LoweredStep::Bitstring { value, .. } => {
            values.insert(*value, world.types_mut().str_t());
        }
        LoweredStep::FunctionRef { value, function } => {
            let arity = world.function_arity(*function);
            values.insert(
                *value,
                world.types_mut().fn_ref_lit(ClosureTarget(function.as_u32()), arity),
            );
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
            let closure = world.closure_ty(*function, captures);
            values.insert(*value, closure);
        }
        LoweredStep::BinaryOp { value, op, left, right } => {
            let left = value_ty(world, values, *left);
            let right = value_ty(world, values, *right);
            values.insert(*value, lowered_binop_ty(world, *op, left, right));
        }
        LoweredStep::UnaryOp { value, op, input } => {
            let input = value_ty(world, values, *input);
            values.insert(*value, lowered_unop_ty(world, *op, input));
        }
        LoweredStep::MapIndex { value, base, key } => {
            let base_ty = value_ty(world, values, *base);
            let field_ty = lowered_map_key(world, values, key)
                .and_then(|key| world.types_mut().map_field_lookup(&base_ty, &key))
                .unwrap_or_else(|| any_ty(world));
            values.insert(*value, field_ty);
        }
        LoweredStep::FieldAccess { value, base, field } => {
            let base_ty = value_ty(world, values, *base);
            let field_ty = world
                .types_mut()
                .map_field_lookup(&base_ty, &super::super::types::MapKey::Atom(field.clone()))
                .unwrap_or_else(|| any_ty(world));
            values.insert(*value, field_ty);
        }
        LoweredStep::AssertLiteral { source, literal } => {
            let source_ty = value_ty(world, values, *source);
            let literal_ty = literal_ty(world, literal);
            let refined = world.types_mut().intersect(source_ty, literal_ty);
            values.insert(*source, refined);
        }
        LoweredStep::AssertStruct { source, module } => {
            let source_ty = value_ty(world, values, *source);
            let asserted = struct_assertion_ty(world, *module);
            let refined = world.types_mut().intersect(source_ty, asserted);
            values.insert(*source, refined);
        }
        LoweredStep::RequireMapValue { value, source, key } => {
            let source_ty = value_ty(world, values, *source);
            let field_ty = literal_map_key(key)
                .and_then(|key| world.types_mut().map_field_lookup(&source_ty, &key))
                .unwrap_or_else(|| any_ty(world));
            values.insert(*value, field_ty);
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
            let source_ty = value_ty(world, values, *source);
            let field_ty = world.types_mut().tuple_field_type(&source_ty, *index);
            values.insert(*value, field_ty);
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
            let rest = world.types_mut().list(elem);
            values.insert(*head, elem);
            values.insert(*tail, rest);
        }
        LoweredStep::BitstringInit { reader, source } => {
            values.insert(*reader, value_fact(world, values, *source));
        }
        LoweredStep::BitstringRead {
            ok,
            value,
            next_reader,
            reader,
            spec,
            ..
        } => {
            values.insert(*ok, world.types_mut().bool());
            values.insert(*value, bitfield_value_ty(world, spec));
            values.insert(*next_reader, value_fact(world, values, *reader));
        }
        LoweredStep::AssertBitstringDone { reader: _ } => {}
    }
    Ok(())
}

/// Join two path results. `None` ("no evidence on this path yet") is the
/// identity; evidence joins by union, which preserves closure identities.
fn join_evidence(world: &mut World<'_>, a: Option<Ty>, b: Option<Ty>) -> Option<Ty> {
    match (a, b) {
        (None, x) | (x, None) => x,
        (Some(a), Some(b)) if a == b => Some(a),
        (Some(a), Some(b)) => Some(world.types_mut().union(a, b)),
    }
}

/// Analyze one entry reached as a plain branch (no delivered value). A
/// branch whose scope cannot be built yet contributes no evidence.
#[allow(clippy::too_many_arguments)]
fn analyze_branch(
    world: &mut World<'_>,
    entries: &[LoweredEntry],
    entry_id: super::super::body::ControlEntryId,
    values: &SemanticValues,
    params: &[(ValueId, Ty)],
    reachable_entries: &mut HashSet<super::super::body::ControlEntryId>,
    value_types: &mut ValueTypes,
    calls: &mut Vec<CallEmission>,
    activation: &ActivationKey,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<Option<Ty>, FatalError> {
    let Some(scope) = entry_scope(entries, entry_id, values, None, params) else {
        return Ok(None);
    };
    analyze_entry(
        world,
        entries,
        entry_id,
        &scope,
        reachable_entries,
        value_types,
        calls,
        activation,
        reads,
        waits,
        follow_up,
    )
}

#[allow(clippy::too_many_arguments)]
fn analyze_tail(
    world: &mut World<'_>,
    entries: &[LoweredEntry],
    tail: &LoweredTail,
    values: &SemanticValues,
    reachable_entries: &mut HashSet<super::super::body::ControlEntryId>,
    value_types: &mut ValueTypes,
    calls: &mut Vec<CallEmission>,
    activation: &ActivationKey,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<Option<Ty>, FatalError> {
    match tail {
        LoweredTail::Value { value, dest } => deliver_tail_value(
            world,
            entries,
            dest,
            *value,
            values,
            reachable_entries,
            value_types,
            calls,
            activation,
            reads,
            waits,
            follow_up,
        ),
        LoweredTail::DirectCall {
            value,
            callsite,
            callee,
            args,
            dest,
        } => {
            let arg_types = args
                .iter()
                .map(|arg| value_ty(world, values, arg.value))
                .collect::<Vec<_>>();
            let (emission, return_ty) =
                resolve_direct_call(world, activation, *callsite, callee, arg_types, reads, waits, follow_up)?;
            if let Some(emission) = emission {
                calls.push(emission);
            }
            let Some(return_ty) = return_ty else {
                return Ok(None);
            };
            let mut delivered = values.clone();
            delivered.insert(*value, return_ty);
            merge_value_types(world, value_types, &delivered);
            deliver_tail_value(
                world,
                entries,
                dest,
                *value,
                &delivered,
                reachable_entries,
                value_types,
                calls,
                activation,
                reads,
                waits,
                follow_up,
            )
        }
        LoweredTail::ClosureCall {
            value,
            callsite,
            callee,
            args,
            dest,
        } => {
            let callee_ty = value_ty(world, values, *callee);
            let arg_types = args
                .iter()
                .map(|arg| value_ty(world, values, arg.value))
                .collect::<Vec<_>>();
            let (emission, return_ty) = resolve_closure_call(
                world, activation, *callsite, callee_ty, arg_types, reads, waits, follow_up,
            )?;
            if let Some(emission) = emission {
                calls.push(emission);
            }
            let Some(return_ty) = return_ty else {
                return Ok(None);
            };
            let mut delivered = values.clone();
            delivered.insert(*value, return_ty);
            merge_value_types(world, value_types, &delivered);
            deliver_tail_value(
                world,
                entries,
                dest,
                *value,
                &delivered,
                reachable_entries,
                value_types,
                calls,
                activation,
                reads,
                waits,
                follow_up,
            )
        }
        LoweredTail::If {
            then_entry, else_entry, ..
        } => {
            let then_ty = analyze_branch(
                world,
                entries,
                *then_entry,
                values,
                &[],
                reachable_entries,
                value_types,
                calls,
                activation,
                reads,
                waits,
                follow_up,
            )?;
            let else_ty = analyze_branch(
                world,
                entries,
                *else_entry,
                values,
                &[],
                reachable_entries,
                value_types,
                calls,
                activation,
                reads,
                waits,
                follow_up,
            )?;
            Ok(join_evidence(world, then_ty, else_ty))
        }
        LoweredTail::Dispatch { inputs, dispatch, .. } => {
            let input_tys = inputs
                .iter()
                .map(|input| value_ty(world, values, *input))
                .collect::<Vec<_>>();
            let reachable = reachable_clause_ids(world, &dispatch.plan, &input_tys);
            let mut merged = None;
            for body_id in reachable {
                let arm_entry = *dispatch
                    .arm_entries
                    .get(body_id as usize)
                    .unwrap_or_else(|| panic!("compiler2 local dispatch arm {} is out of bounds", body_id));
                let arm_ty = analyze_branch(
                    world,
                    entries,
                    arm_entry,
                    values,
                    &[],
                    reachable_entries,
                    value_types,
                    calls,
                    activation,
                    reads,
                    waits,
                    follow_up,
                )?;
                merged = join_evidence(world, merged, arm_ty);
            }
            let miss_ty = analyze_branch(
                world,
                entries,
                dispatch.miss_entry,
                values,
                &[],
                reachable_entries,
                value_types,
                calls,
                activation,
                reads,
                waits,
                follow_up,
            )?;
            Ok(join_evidence(world, merged, miss_ty))
        }
        LoweredTail::Receive(receive) => {
            // Mailbox messages are a runtime boundary: `any` is earned here.
            let any = world.types_mut().any();
            let mut merged = None;
            for clause in &receive.clauses {
                let clause_entry = &entries[clause.entry.as_u32() as usize];
                let clause_params = clause_entry
                    .params
                    .iter()
                    .map(|param| (*param, any))
                    .collect::<Vec<_>>();
                let clause_ty = analyze_branch(
                    world,
                    entries,
                    clause.entry,
                    values,
                    &clause_params,
                    reachable_entries,
                    value_types,
                    calls,
                    activation,
                    reads,
                    waits,
                    follow_up,
                )?;
                merged = join_evidence(world, merged, clause_ty);
            }
            if let Some(after) = &receive.after {
                let after_ty = analyze_branch(
                    world,
                    entries,
                    after.entry,
                    values,
                    &[],
                    reachable_entries,
                    value_types,
                    calls,
                    activation,
                    reads,
                    waits,
                    follow_up,
                )?;
                merged = join_evidence(world, merged, after_ty);
            }
            Ok(merged)
        }
        // A halt path contributes no value: the join identity, not a type.
        LoweredTail::Halt { .. } => Ok(None),
    }
}

#[allow(clippy::too_many_arguments)]
fn deliver_tail_value(
    world: &mut World<'_>,
    entries: &[LoweredEntry],
    dest: &ControlDestination,
    value: ValueId,
    values: &SemanticValues,
    reachable_entries: &mut HashSet<super::super::body::ControlEntryId>,
    value_types: &mut ValueTypes,
    calls: &mut Vec<CallEmission>,
    activation: &ActivationKey,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<Option<Ty>, FatalError> {
    let delivered = value_fact(world, values, value);
    // A proven-empty value is evidence: nothing flows past this point, the
    // path is dead. (Absence of evidence never reaches here — an
    // unresolved call short-circuits to a `None` path before delivery.)
    if world.types().is_empty(&delivered) {
        return Ok(Some(delivered));
    }
    match dest {
        ControlDestination::Return => Ok(Some(delivered)),
        ControlDestination::Deliver(entry_id) => {
            let Some(scope) = entry_scope(entries, *entry_id, values, Some((value, delivered)), &[]) else {
                return Ok(None);
            };
            analyze_entry(
                world,
                entries,
                *entry_id,
                &scope,
                reachable_entries,
                value_types,
                calls,
                activation,
                reads,
                waits,
                follow_up,
            )
        }
    }
}

/// Build an entry's scope, or `None` when a required capture is absent —
/// meaning the path that defines it produced no evidence this round, so the
/// entry cannot be analyzed yet. Absence never defaults to a type.
fn entry_scope(
    entries: &[LoweredEntry],
    entry_id: super::super::body::ControlEntryId,
    values: &SemanticValues,
    delivered: Option<(ValueId, Ty)>,
    params: &[(ValueId, Ty)],
) -> Option<SemanticValues> {
    let entry = &entries[entry_id.as_u32() as usize];
    let mut scope = HashMap::new();
    if let Some((_, value)) = delivered
        && let Some(input) = entry.origin.input_value()
    {
        scope.insert(input, value);
    }
    for (param, value) in params {
        scope.insert(*param, *value);
    }
    for capture in &entry.captures {
        if scope.contains_key(capture) {
            continue;
        }
        scope.insert(*capture, values.get(capture).copied()?);
    }
    Some(scope)
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
) -> Result<(Option<CallEmission>, Option<Ty>), FatalError> {
    // A proven-empty argument type is a real fact: no value can reach this
    // call, the path is dead. (Absence cannot arrive here — an unresolved
    // upstream call already short-circuited the path.)
    if arg_types.iter().any(|arg| world.types().is_empty(arg)) {
        return Ok((None, Some(none_ty(world))));
    }

    let DirectCallee::Function(function) = callee;
    let (summary, mut activations, return_ty) =
        resolve_function_call(world, caller, *function, arg_types.clone(), reads, waits, follow_up)?;
    let mut latent_executables = Vec::new();
    if let Some(summary) = &summary {
        for target in &summary.targets {
            let SelectedCallee::Function(function) = target.callee else {
                continue;
            };
            let runtime_activations = resolve_runtime_callable_boundary_activations(
                world,
                caller,
                function,
                target.input_types.as_slice(),
                reads,
                waits,
                follow_up,
            )?;
            latent_executables.extend(runtime_activations.iter().map(|activation| ExecutableKey {
                activation: activation.key.clone(),
                need: ExecutableNeed::Value,
            }));
            activations.extend(runtime_activations);
        }
    }
    Ok((
        summary.map(|summary| CallEmission {
            key: CallSiteKey {
                activation: caller.clone(),
                callsite,
            },
            summary: Some(summary),
            latent_executables,
            activations,
        }),
        return_ty,
    ))
}

fn merge_value_types(world: &mut World<'_>, merged: &mut ValueTypes, observed: &SemanticValues) {
    for (&value, &ty) in observed {
        match merged.get(&value).copied() {
            Some(current) if current != ty => {
                merged.insert(value, widen_semantic_summary_ty(world, current, ty));
            }
            Some(_) => {}
            None => {
                merged.insert(value, ty);
            }
        }
    }
}

fn coalesce_call_emissions(
    world: &mut World<'_>,
    caller: &ActivationKey,
    calls: Vec<CallEmission>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<Vec<CallEmission>, FatalError> {
    let mut order = Vec::new();
    let mut grouped = HashMap::<CallSiteKey, CoalescedCallEmission>::new();
    for call in calls {
        match grouped.entry(call.key.clone()) {
            Entry::Vacant(entry) => {
                order.push(call.key.clone());
                entry.insert(CoalescedCallEmission { call, observations: 1 });
            }
            Entry::Occupied(mut entry) => {
                let grouped = entry.get_mut();
                grouped.observations += 1;
                merge_call_emission(world, &mut grouped.call, call)?;
            }
        }
    }

    let mut coalesced = Vec::with_capacity(order.len());
    for key in order {
        let grouped = grouped
            .remove(&key)
            .expect("callsite order should resolve to a coalesced call");
        if grouped.observations == 1 {
            coalesced.push(grouped.call);
            continue;
        }
        coalesced.push(rebuild_coalesced_call_emission(
            world,
            caller,
            grouped.call,
            reads,
            waits,
            follow_up,
        )?);
    }
    Ok(coalesced)
}

fn merge_call_emission(
    world: &mut World<'_>,
    current: &mut CallEmission,
    observed: CallEmission,
) -> Result<(), FatalError> {
    match (&mut current.summary, observed.summary) {
        (Some(current_summary), Some(observed_summary)) => {
            merge_call_targets(world, &mut current_summary.targets, observed_summary.targets)?;
            current_summary.return_ty = join_evidence(world, current_summary.return_ty, observed_summary.return_ty);
        }
        (None, None) => {}
        (Some(_), None) | (None, Some(_)) => return Err(FatalError),
    }
    current.activations.extend(observed.activations);
    current.latent_executables.extend(observed.latent_executables);
    Ok(())
}

fn rebuild_coalesced_call_emission(
    world: &mut World<'_>,
    caller: &ActivationKey,
    call: CallEmission,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<CallEmission, FatalError> {
    let Some(summary) = &call.summary else {
        return Ok(call);
    };
    let mut rebuilt_targets = Vec::new();
    let mut rebuilt_return = None;
    let mut rebuilt_activations = Vec::new();
    let mut rebuilt_latent = Vec::new();

    for target in &summary.targets {
        match target.callee.clone() {
            SelectedCallee::Function(function) => {
                let Some(rebuilt) = call_emission_for_function(
                    world,
                    caller,
                    call.key.clone(),
                    function,
                    target.input_types.clone(),
                    reads,
                    waits,
                    follow_up,
                )?
                else {
                    return Ok(call);
                };
                let Some(rebuilt_summary) = rebuilt.summary else {
                    return Ok(call);
                };
                let Some(rebuilt_target) = rebuilt_summary.single_target().cloned() else {
                    return Ok(call);
                };
                rebuilt_return = join_evidence(world, rebuilt_return, rebuilt_target.return_ty);
                rebuilt_targets.push(rebuilt_target);
                rebuilt_activations.extend(rebuilt.activations);
                rebuilt_latent.extend(rebuilt.latent_executables);
            }
            SelectedCallee::ProviderBoundary(_) => {
                rebuilt_return = join_evidence(world, rebuilt_return, target.return_ty);
                rebuilt_targets.push(target.clone());
            }
        }
    }

    rebuilt_activations.extend(call.activations);
    rebuilt_latent.extend(call.latent_executables);
    Ok(CallEmission {
        key: call.key,
        summary: Some(CallSiteSummary {
            targets: rebuilt_targets,
            return_ty: rebuilt_return,
        }),
        activations: rebuilt_activations,
        latent_executables: rebuilt_latent,
    })
}

fn call_emission_for_function(
    world: &mut World<'_>,
    caller: &ActivationKey,
    key: CallSiteKey,
    function: FunctionId,
    input_types: Vec<Ty>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<Option<CallEmission>, FatalError> {
    let Some((input_types, contract_return_ty)) =
        refine_function_call_surface(world, function, input_types, reads, waits, follow_up)?
    else {
        return Ok(None);
    };
    if world.function_is_provider_boundary(function) {
        // The earned dynamic edge: a boundary with no contract is `any`.
        let return_ty = Some(contract_return_ty.unwrap_or_else(|| any_ty(world)));
        return Ok(Some(CallEmission {
            key,
            summary: Some(CallSiteSummary {
                targets: vec![CallTargetSummary {
                    callee: SelectedCallee::ProviderBoundary(function),
                    input_types,
                    return_ty,
                }],
                return_ty,
            }),
            activations: Vec::new(),
            latent_executables: Vec::new(),
        }));
    }
    let Some((activation, already_present, return_ty)) =
        prepare_function_call(world, caller, function, input_types.clone(), reads, waits, follow_up)
    else {
        return Ok(None);
    };
    let return_ty = refine_call_return(world, return_ty, contract_return_ty);
    let mut activations = vec![ActivationContribution {
        key: activation,
        inputs: input_types.clone(),
        already_present,
    }];
    let runtime_activations = resolve_runtime_callable_boundary_activations(
        world,
        caller,
        function,
        input_types.as_slice(),
        reads,
        waits,
        follow_up,
    )?;
    let latent_executables = runtime_activations
        .iter()
        .map(|activation| ExecutableKey {
            activation: activation.key.clone(),
            need: ExecutableNeed::Value,
        })
        .collect();
    activations.extend(runtime_activations);
    Ok(Some(CallEmission {
        key,
        summary: Some(CallSiteSummary {
            targets: vec![CallTargetSummary {
                callee: SelectedCallee::Function(function),
                input_types,
                return_ty,
            }],
            return_ty,
        }),
        activations,
        latent_executables,
    }))
}

fn resolve_function_call(
    world: &mut World<'_>,
    caller: &ActivationKey,
    function: FunctionId,
    input_types: Vec<Ty>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<ResolvedCall, FatalError> {
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
        return Ok((None, Vec::new(), None));
    }
    let Some((input_types, contract_return_ty)) =
        refine_function_call_surface(world, function, input_types, reads, waits, follow_up)?
    else {
        return Ok((None, Vec::new(), None));
    };
    if world.function_is_provider_boundary(function) {
        // The provider boundary is the public dynamic edge: `any` is earned
        // here (and only here and at unresolvable callable values).
        let return_ty = contract_return_ty.unwrap_or_else(|| any_ty(world));
        return Ok((
            Some(CallSiteSummary {
                targets: vec![call_target_summary(
                    SelectedCallee::ProviderBoundary(function),
                    input_types,
                    Some(return_ty),
                )],
                return_ty: Some(return_ty),
            }),
            Vec::new(),
            Some(return_ty),
        ));
    }
    let Some((activation, already_present, return_evidence)) =
        prepare_function_call(world, caller, function, input_types.clone(), reads, waits, follow_up)
    else {
        return Ok((None, Vec::new(), None));
    };
    let return_ty = refine_call_return(world, return_evidence, contract_return_ty);
    Ok((
        Some(CallSiteSummary {
            targets: vec![call_target_summary(
                SelectedCallee::Function(function),
                input_types.clone(),
                return_ty,
            )],
            return_ty,
        }),
        vec![ActivationContribution {
            key: activation,
            inputs: input_types.clone(),
            already_present,
        }],
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
) -> Result<ResolvedCall, FatalError> {
    let protocol_fact = FactKey::ModuleDefined(protocol);
    if world.module_defined_revision(protocol).is_none() {
        wait_for_protocol_module(world, protocol, waits, follow_up);
        return Ok((None, Vec::new(), None));
    }
    reads.push(protocol_fact);
    let dispatch_fact = FactKey::ProtocolDispatch(protocol);
    if !world.has_fact(&dispatch_fact) {
        waits.insert(dispatch_fact);
        follow_up.insert(Job::DefineModule(protocol));
        return Ok((None, Vec::new(), None));
    }
    reads.push(dispatch_fact);

    let receiver_ty = input_types.first().cloned().unwrap_or_else(|| any_ty(world));
    let function_ref = world.function_ref(callback_function).clone();

    let mut matches = Vec::new();
    let dispatch = world
        .protocol_dispatch(protocol)
        .expect("protocol dispatch fact should be stored before semantic reads it")
        .clone();
    for arm in dispatch.arms {
        let target_ty = world.module_impl_target_ty(arm.target);
        let overlap = world.types_mut().intersect(receiver_ty, target_ty);
        if world.types().is_empty(&overlap) {
            continue;
        }
        let callback = arm
            .callbacks
            .get(&(function_ref.name.clone(), function_ref.arity))
            .copied();
        if let Some(callback) = callback {
            matches.push((callback, overlap));
        }
    }

    if matches.is_empty() {
        for module in world.runtime_impl_target_modules(&receiver_ty) {
            if world.protocol_impl(protocol, module).is_some() {
                continue;
            }
            wait_for_runtime_module(world, module, waits, follow_up);
        }
        return Ok((None, Vec::new(), None));
    }

    let mut targets = Vec::new();
    let mut activations = Vec::new();
    let mut return_ty = None;
    for (selected, overlap) in matches {
        let owner_fact = FactKey::ModuleDefined(selected.owner_module);
        if world.module_defined_revision(selected.owner_module).is_none() {
            waits.insert(owner_fact);
            follow_up.insert(Job::DefineModule(selected.owner_module));
            return Ok((None, Vec::new(), None));
        }
        reads.push(owner_fact);

        let refined_inputs = refine_protocol_target_inputs(world, &input_types, receiver_ty, overlap);
        let Some((refined_inputs, contract_return_ty)) =
            refine_function_call_surface(world, selected.function, refined_inputs, reads, waits, follow_up)?
        else {
            return Ok((None, Vec::new(), None));
        };
        let Some((activation, already_present, observed_return)) = prepare_function_call(
            world,
            caller,
            selected.function,
            refined_inputs.clone(),
            reads,
            waits,
            follow_up,
        ) else {
            return Ok((None, Vec::new(), None));
        };
        let target_return = refine_call_return(world, observed_return, contract_return_ty);
        return_ty = join_evidence(world, return_ty, target_return);
        targets.push(call_target_summary(
            SelectedCallee::Function(selected.function),
            refined_inputs.clone(),
            target_return,
        ));
        activations.push(ActivationContribution {
            key: activation,
            inputs: refined_inputs.clone(),
            already_present,
        });
    }
    Ok((Some(CallSiteSummary { targets, return_ty }), activations, return_ty))
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
) -> Result<(Option<CallEmission>, Option<Ty>), FatalError> {
    if world.types().is_empty(&callee_ty) || arg_types.iter().any(|arg| world.types().is_empty(arg)) {
        // Proven-empty callee or argument: the call site is dead. This is
        // evidence (the empty type), not absence — absence short-circuits
        // upstream before any argument reaches a call.
        return Ok((None, Some(none_ty(world))));
    }
    let Some(clauses) = world.types_mut().callable_value_clauses(&callee_ty) else {
        // A callable value the engine cannot resolve to closure targets is a
        // dynamic edge: `any` is earned here, as at provider boundaries.
        return Ok((None, Some(any_ty(world))));
    };
    let mut selected_functions = Vec::new();
    let mut singleton_summary_inputs = None;
    let mut activations = Vec::new();
    let mut callable_target_executables = Vec::new();
    let mut latent_executables = Vec::new();
    let mut return_ty = None;

    for clause in clauses {
        let Some(closure) = clause.closure else {
            continue;
        };
        if clause.args.len() != arg_types.len() {
            continue;
        }

        let function = function_id_of_closure_target(closure.target);
        if !selected_functions.contains(&function) {
            selected_functions.push(function);
        }

        let refined_args = refine_contract_inputs(world, arg_types.clone(), std::iter::once(clause.args.as_slice()));
        let mut inputs = closure.captures;
        inputs.extend(refined_args);
        let (summary, clause_activations, observed_return) =
            resolve_function_call(world, caller, function, inputs, reads, waits, follow_up)?;
        for activation in &clause_activations {
            let executable = ExecutableKey {
                activation: activation.key.clone(),
                need: ExecutableNeed::Value,
            };
            if !callable_target_executables.contains(&executable) {
                callable_target_executables.push(executable);
            }
        }
        let clause_return = refine_call_return(world, observed_return, Some(clause.ret));
        return_ty = join_evidence(world, return_ty, clause_return);

        if let Some(summary) = summary {
            let Some(target) = summary.single_target() else {
                return Err(FatalError);
            };
            merge_call_inputs(world, &mut singleton_summary_inputs, &target.input_types);
            let runtime_activations = resolve_runtime_callable_boundary_activations(
                world,
                caller,
                function,
                target.input_types.as_slice(),
                reads,
                waits,
                follow_up,
            )?;
            latent_executables.extend(runtime_activations.iter().map(|activation| ExecutableKey {
                activation: activation.key.clone(),
                need: ExecutableNeed::Value,
            }));
            activations.extend(runtime_activations);
            activations.extend(clause_activations);
        }
    }

    if selected_functions.is_empty() {
        // No closure-shaped clause: a dynamic callable, the other earned-any
        // edge.
        return Ok((None, Some(any_ty(world))));
    };
    let summary = if selected_functions.len() == 1 {
        let function = selected_functions[0];
        singleton_summary_inputs.map(|input_types| CallSiteSummary {
            targets: vec![call_target_summary(
                SelectedCallee::Function(function),
                input_types,
                return_ty,
            )],
            return_ty,
        })
    } else {
        latent_executables.extend(callable_target_executables);
        None
    };
    Ok((
        Some(CallEmission {
            key: CallSiteKey {
                activation: caller.clone(),
                callsite,
            },
            summary,
            latent_executables,
            activations,
        }),
        return_ty,
    ))
}

fn resolve_runtime_callable_boundary_activations(
    world: &mut World<'_>,
    caller: &ActivationKey,
    function: FunctionId,
    arg_types: &[Ty],
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<Vec<ActivationContribution>, FatalError> {
    let lowered_fact = FactKey::LoweredBody(function);
    if !world.has_fact(&lowered_fact) {
        waits.insert(lowered_fact);
        follow_up.insert(Job::LowerFunction(function));
        return Ok(Vec::new());
    }
    reads.push(lowered_fact);
    let LoweredBody::Extern { signature: _ } = world.lowered_body(function) else {
        return Ok(Vec::new());
    };

    let mut activations = Vec::new();
    for &callable_ty in arg_types {
        if world.types_mut().callable_clauses(&callable_ty).is_none() {
            continue;
        }
        activations.extend(resolve_callable_activations_from_type(
            world,
            caller,
            callable_ty,
            reads,
            waits,
            follow_up,
        ));
    }
    Ok(activations)
}

fn covered_callable_activations(calls: &[CallEmission]) -> HashSet<ActivationKey> {
    calls
        .iter()
        .flat_map(|call| call.activations.iter())
        .map(|activation| activation.key.clone())
        .collect()
}

fn resolve_escaping_callable_activations_from_type(
    world: &mut World<'_>,
    caller: &ActivationKey,
    ty: Ty,
    covered_activations: &HashSet<ActivationKey>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Vec<ActivationContribution> {
    let mut callable_types = Vec::new();
    collect_escaping_callable_types(world, ty, &mut HashSet::new(), &mut callable_types);
    let mut seen = HashSet::new();
    let mut activations = Vec::new();
    for callable_ty in callable_types {
        for activation in resolve_uncovered_callable_activations_from_type(
            world,
            caller,
            callable_ty,
            covered_activations,
            reads,
            waits,
            follow_up,
        ) {
            if seen.insert(activation.key.clone()) {
                activations.push(activation);
            }
        }
    }
    activations
}

fn collect_escaping_callable_types(world: &mut World<'_>, ty: Ty, seen: &mut HashSet<Ty>, out: &mut Vec<Ty>) {
    if !seen.insert(ty) || world.types().is_empty(&ty) {
        return;
    }
    if world.types_mut().callable_value_clauses(&ty).is_some() {
        out.push(ty);
    }

    for index in 0..world.types().max_tuple_arity(&ty) {
        let field = world.types_mut().tuple_field_type(&ty, index);
        collect_escaping_callable_types(world, field, seen, out);
    }

    if world.types().has_list_shape(&ty) {
        let elem = world.types_mut().list_element_type(&ty);
        collect_escaping_callable_types(world, elem, seen, out);
    }

    let map_keys = world.types().map_known_keys(&ty);
    for key in map_keys {
        if let Some(field) = world.types_mut().map_field_lookup(&ty, &key) {
            collect_escaping_callable_types(world, field, seen, out);
        }
    }
}

fn resolve_uncovered_callable_activations_from_type(
    world: &mut World<'_>,
    caller: &ActivationKey,
    callable_ty: Ty,
    covered_activations: &HashSet<ActivationKey>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Vec<ActivationContribution> {
    let Some(clauses) = world.types_mut().callable_value_clauses(&callable_ty) else {
        return Vec::new();
    };
    let mut activations = Vec::new();
    for clause in clauses {
        let Some(closure) = clause.closure else {
            continue;
        };
        let function = function_id_of_closure_target(closure.target);
        if !world.require_activation_key_facts(function, reads, waits, follow_up) {
            continue;
        }
        let mut input_types = closure.captures;
        input_types.extend(clause.args);
        let activation = world.activation_key(caller.root, function, &input_types);
        if covered_activations.contains(&activation) {
            continue;
        }
        let already_present = world.fact_revision(FactKey::Activation(activation.clone())).is_some();
        activations.push(ActivationContribution {
            key: activation,
            inputs: input_types.clone(),
            already_present,
        });
    }
    activations
}

fn refine_function_call_surface(
    world: &mut World<'_>,
    function: FunctionId,
    input_types: Vec<Ty>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<Option<RefinedCallSurface>, FatalError> {
    if !world.function_declares_contract(function) {
        return Ok(Some((input_types, None)));
    }
    let contract_fact = FactKey::FunctionContract(function);
    let Some(_) = world.function_contract_revision(function) else {
        waits.insert(contract_fact);
        follow_up.insert(Job::DeriveFunctionContract(function));
        return Ok(None);
    };
    reads.push(contract_fact);
    let contract = world
        .function_contract(function)
        .cloned()
        .expect("function contract fact should resolve to a stored contract");
    Ok(Some(apply_function_contract(world, &contract, input_types)))
}

fn apply_function_contract(
    world: &mut World<'_>,
    contract: &FunctionContract,
    input_types: Vec<Ty>,
) -> (Vec<Ty>, Option<Ty>) {
    let application = contract.apply(world.types_mut(), &input_types);
    (
        refine_contract_inputs(
            world,
            input_types,
            application.matched_arrows.iter().map(|arrow| arrow.params.as_slice()),
        ),
        application.result,
    )
}

fn activation_contract_return(
    world: &mut World<'_>,
    function: FunctionId,
    input_types: &[Ty],
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<Option<Ty>, FatalError> {
    let Some((_, contract_return_ty)) =
        refine_function_call_surface(world, function, input_types.to_vec(), reads, waits, follow_up)?
    else {
        return Ok(None);
    };
    Ok(contract_return_ty)
}

fn refine_contract_inputs<'a>(
    world: &mut World<'_>,
    observed: Vec<Ty>,
    arrows: impl Iterator<Item = &'a [Ty]>,
) -> Vec<Ty> {
    let mut joined = Vec::<Option<Ty>>::new();
    for params in arrows {
        if joined.len() < params.len() {
            joined.resize(params.len(), None);
        }
        for (index, ty) in params.iter().copied().enumerate() {
            joined[index] = Some(match joined[index].take() {
                Some(current) => world.types_mut().union(current, ty),
                None => ty,
            });
        }
    }
    observed
        .into_iter()
        .enumerate()
        .map(|(index, input)| {
            let Some(surface) = joined.get(index).and_then(|ty| *ty) else {
                return input;
            };
            let refined = world.types_mut().intersect(input, surface);
            if world.types().is_empty(&refined) {
                input
            } else {
                refined
            }
        })
        .collect()
}

fn refine_call_return(world: &mut World<'_>, observed: Option<Ty>, contract: Option<Ty>) -> Option<Ty> {
    let Some(observed) = observed else {
        // No body evidence yet: a contract bounds the eventual value but
        // does not witness that the call returns at all. Nothing is
        // manufactured from absence.
        return None;
    };
    Some(refine_observed_return(world, observed, contract))
}

fn refine_observed_return(world: &mut World<'_>, observed: Ty, contract: Option<Ty>) -> Ty {
    let Some(contract) = contract else {
        return observed;
    };
    if world.types().is_empty(&observed) {
        return observed;
    }
    if world.types().has_vars(&contract) {
        return observed;
    }
    let any = world.types_mut().any();
    let observed_is_unconstrained = world.types().is_equivalent(&observed, &any) || world.types().has_vars(&observed);
    if !observed_is_unconstrained
        && world.types().is_subtype(&contract, &observed)
        && !world.types().is_subtype(&observed, &contract)
    {
        return observed;
    }
    let refined = world.types_mut().intersect(observed, contract);
    if world.types().is_empty(&refined) {
        observed
    } else {
        refined
    }
}

fn resolve_callable_activations_from_type(
    world: &mut World<'_>,
    caller: &ActivationKey,
    callable_ty: Ty,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Vec<ActivationContribution> {
    let Some(clauses) = world.types_mut().callable_value_clauses(&callable_ty) else {
        return Vec::new();
    };
    let mut activations = Vec::new();
    for clause in clauses {
        let Some(closure) = clause.closure else {
            continue;
        };
        let function = function_id_of_closure_target(closure.target);
        if !world.require_activation_key_facts(function, reads, waits, follow_up) {
            continue;
        }
        let mut input_types = closure.captures;
        input_types.extend(clause.args);
        let activation = world.activation_key(caller.root, function, &input_types);
        let already_present = world.has_fact(&FactKey::Activation(activation.clone()));
        activations.push(ActivationContribution {
            key: activation,
            inputs: input_types.clone(),
            already_present,
        });
    }
    activations
}

fn prepare_function_call(
    world: &mut World<'_>,
    caller: &ActivationKey,
    function: FunctionId,
    arg_types: Vec<Ty>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Option<(ActivationKey, bool, Option<Ty>)> {
    if !world.require_activation_key_facts(function, reads, waits, follow_up) {
        return None;
    }

    let activation = world.activation_key(caller.root, function, &arg_types);
    let already_present = world.has_fact(&FactKey::Activation(activation.clone()));
    // The read is the subscription that re-wakes this caller when the
    // callee's return evidence rises — chaotic iteration needs no wait here,
    // so mutual recursion cannot deadlock. Absent evidence stays absent: it
    // is the ascent's bottom, never the type `none`.
    reads.push(FactKey::ReturnType(activation.clone()));
    follow_up.insert(Job::SealSemanticClosure(caller.root));
    let return_evidence = world.activation_return(&activation);
    Some((activation, already_present, return_evidence))
}

fn wait_for_runtime_module(
    world: &mut World<'_>,
    module: ModuleId,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) {
    if let Some(code_id) = world.ensure_runtime_module(module) {
        let indexed_fact = FactKey::CodeIndexed(code_id);
        if !world.has_fact(&indexed_fact) {
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
        if !world.has_fact(&indexed_fact) {
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
    if !world.module_has_source_state(module) && !world.is_runtime_module(module) {
        return false;
    }
    waits.insert(FactKey::ModuleDefined(module));
    follow_up.extend(world.ensure_function_source(function));
    true
}

fn merge_call_targets(
    world: &mut World<'_>,
    current: &mut Vec<CallTargetSummary>,
    observed: Vec<CallTargetSummary>,
) -> Result<(), FatalError> {
    for observed_target in observed {
        if let Some(current_target) = current
            .iter_mut()
            .find(|target| target.callee == observed_target.callee)
        {
            merge_call_input_vec(world, &mut current_target.input_types, &observed_target.input_types);
            current_target.return_ty = join_evidence(world, current_target.return_ty, observed_target.return_ty);
            continue;
        }
        current.push(observed_target);
    }
    if current.is_empty() {
        return Err(FatalError);
    }
    Ok(())
}

fn merge_call_inputs(world: &mut World<'_>, merged: &mut Option<Vec<Ty>>, observed: &[Ty]) {
    match merged {
        Some(current) => merge_call_input_vec(world, current, observed),
        None => {
            *merged = Some(observed.to_vec());
        }
    }
}

fn merge_call_input_vec(world: &mut World<'_>, current: &mut Vec<Ty>, observed: &[Ty]) {
    if current.len() < observed.len() {
        current.resize_with(observed.len(), || any_ty(world));
    }
    for (slot, next_ty) in observed.iter().copied().enumerate() {
        current[slot] = widen_semantic_summary_ty(world, current[slot], next_ty);
    }
}

fn widen_semantic_summary_ty(world: &mut World<'_>, current: Ty, observed: Ty) -> Ty {
    if current == observed {
        current
    } else {
        world.types_mut().refine_widen(&current, &observed)
    }
}

fn refine_protocol_target_inputs(world: &mut World<'_>, input_types: &[Ty], receiver_ty: Ty, target_ty: Ty) -> Vec<Ty> {
    let mut refined = input_types.to_vec();
    if let Some(receiver) = refined.first_mut() {
        *receiver = world.types_mut().intersect(receiver_ty, target_ty);
    }
    refined
}

fn call_target_summary(callee: SelectedCallee, input_types: Vec<Ty>, return_ty: Option<Ty>) -> CallTargetSummary {
    CallTargetSummary {
        input_types,
        callee,
        return_ty,
    }
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
                match value {
                    // No type can witness "the scrutinee always equals this
                    // constant" for numbers and strings: string literals
                    // have no singleton types at all (the old subtype check
                    // wrongly pruned live miss edges), and numeric literal
                    // types are leaving the lattice. Equality is a VALUE
                    // test the matcher performs at runtime; its miss edge
                    // is always statically possible. Atoms, bools, nil and
                    // the empty list keep their exact singleton proofs.
                    ComparisonValue::Const(
                        DispatchConst::Int(_) | DispatchConst::FloatBits(_) | DispatchConst::Utf8Binary(_),
                    ) => true,
                    _ => !world.types().is_subtype(source, &target),
                }
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
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return needs;
    };
    for clause_id in reachable_clauses {
        collect_clause_callsite_needs(&clauses[*clause_id as usize], entries, executable_need, &mut needs);
    }
    needs
}

fn collect_clause_callsite_needs(
    clause: &LoweredClause,
    entries: &[LoweredEntry],
    executable_need: ExecutableNeed,
    out: &mut HashMap<CallSiteId, ExecutableNeed>,
) {
    collect_entry_callsite_needs(entries, clause.entry, executable_need, out);
}

fn collect_entry_callsite_needs(
    entries: &[LoweredEntry],
    entry_id: super::super::body::ControlEntryId,
    outgoing_need: ExecutableNeed,
    out: &mut HashMap<CallSiteId, ExecutableNeed>,
) -> Option<usize> {
    let entry = &entries[entry_id.as_u32() as usize];
    let mut tuple_demands = HashMap::new();
    match &entry.tail {
        LoweredTail::Value { value, dest } => {
            if let Some(arity) = destination_need(entries, dest, outgoing_need, out) {
                tuple_demands.insert(*value, arity);
            }
        }
        LoweredTail::DirectCall {
            value, callsite, dest, ..
        }
        | LoweredTail::ClosureCall {
            value, callsite, dest, ..
        } => {
            let need = destination_need(entries, dest, outgoing_need, out)
                .map(ExecutableNeed::TupleFields)
                .unwrap_or(ExecutableNeed::Value);
            record_callsite_need(out, *callsite, need);
            if let ExecutableNeed::TupleFields(arity) = need {
                tuple_demands.insert(*value, arity);
            }
        }
        LoweredTail::If {
            then_entry, else_entry, ..
        } => {
            let _ = collect_entry_callsite_needs(entries, *then_entry, outgoing_need, out);
            let _ = collect_entry_callsite_needs(entries, *else_entry, outgoing_need, out);
        }
        LoweredTail::Dispatch { dispatch, .. } => {
            for arm_entry in &dispatch.arm_entries {
                let _ = collect_entry_callsite_needs(entries, *arm_entry, outgoing_need, out);
            }
            let _ = collect_entry_callsite_needs(entries, dispatch.miss_entry, outgoing_need, out);
        }
        LoweredTail::Receive(receive) => {
            for clause in &receive.clauses {
                let _ = collect_entry_callsite_needs(entries, clause.entry, outgoing_need, out);
            }
            if let Some(after) = &receive.after {
                let _ = collect_entry_callsite_needs(entries, after.entry, outgoing_need, out);
            }
        }
        LoweredTail::Halt { .. } => {}
    }
    for step in entry.steps.iter().rev() {
        match step {
            LoweredStep::AssertTuple { source, arity } => {
                tuple_demands.insert(*source, *arity);
            }
            LoweredStep::Const { value, .. }
            | LoweredStep::Tuple { value, .. }
            | LoweredStep::List { value, .. }
            | LoweredStep::Map { value, .. }
            | LoweredStep::MapUpdate { value, .. }
            | LoweredStep::Struct { value, .. }
            | LoweredStep::Bitstring { value, .. }
            | LoweredStep::FunctionRef { value, .. }
            | LoweredStep::Lambda { value, .. }
            | LoweredStep::BinaryOp { value, .. }
            | LoweredStep::UnaryOp { value, .. }
            | LoweredStep::MapIndex { value, .. }
            | LoweredStep::FieldAccess { value, .. }
            | LoweredStep::RequireMapValue { value, .. }
            | LoweredStep::TupleField { value, .. } => {
                tuple_demands.remove(value);
            }
            LoweredStep::SplitList { head, tail, .. } => {
                tuple_demands.remove(head);
                tuple_demands.remove(tail);
            }
            LoweredStep::BitstringInit { reader, .. } => {
                tuple_demands.remove(reader);
            }
            LoweredStep::BitstringRead {
                ok, value, next_reader, ..
            } => {
                tuple_demands.remove(ok);
                tuple_demands.remove(value);
                tuple_demands.remove(next_reader);
            }
            LoweredStep::AssertLiteral { .. }
            | LoweredStep::AssertStruct { .. }
            | LoweredStep::AssertEmptyList { .. }
            | LoweredStep::AssertSame { .. }
            | LoweredStep::AssertBitstringDone { .. } => {}
        }
    }
    entry
        .origin
        .input_value()
        .and_then(|value| tuple_demands.remove(&value))
}

fn destination_need(
    entries: &[LoweredEntry],
    dest: &ControlDestination,
    outgoing_need: ExecutableNeed,
    out: &mut HashMap<CallSiteId, ExecutableNeed>,
) -> Option<usize> {
    match dest {
        ControlDestination::Return => match outgoing_need {
            ExecutableNeed::Value => None,
            ExecutableNeed::TupleFields(arity) => Some(arity),
        },
        ControlDestination::Deliver(entry_id) => collect_entry_callsite_needs(entries, *entry_id, outgoing_need, out),
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

fn value_fact(_world: &mut World<'_>, values: &SemanticValues, value: ValueId) -> Ty {
    // Scope construction is total (`entry_scope` yields no scope at all when
    // a capture is absent), so every value an analyzed entry touches is
    // present. `any` is earned at boundaries, never defaulted here.
    *values
        .get(&value)
        .unwrap_or_else(|| panic!("semantic value {value:?} must be in scope for an analyzed entry"))
}

fn value_ty(world: &mut World<'_>, values: &SemanticValues, value: ValueId) -> Ty {
    value_fact(world, values, value)
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

fn list_ty(world: &mut World<'_>, values: &SemanticValues, items: &[ValueId], tail: Option<ValueId>) -> Ty {
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

fn map_ty(world: &mut World<'_>, values: &SemanticValues, entries: &[(LoweredMapKey, ValueId)]) -> Ty {
    let mut fields = BTreeMap::new();
    for (key, value) in entries {
        let Some(key) = lowered_map_key(world, values, key) else {
            return world.types_mut().map_top();
        };
        fields.insert(key, value_ty(world, values, *value));
    }
    world.types_mut().map(&fields.into_iter().collect::<Vec<_>>())
}

/// The map key at a lowered key position: the carried compile-time constant
/// when the source wrote a literal (keys are values), falling back to the
/// observed singleton type while numeric literal types still exist.
fn lowered_map_key(
    world: &mut World<'_>,
    values: &SemanticValues,
    key: &LoweredMapKey,
) -> Option<super::super::types::MapKey> {
    if let Some(literal) = &key.literal {
        return literal_map_key(literal);
    }
    let key_ty = value_ty(world, values, key.value);
    map_key_from_ty(world, key_ty)
}

fn struct_assertion_ty(world: &mut World<'_>, module: ModuleId) -> Ty {
    let field_count = world.module_struct_fields(module).map_or(0, |fields| fields.len());
    let any = world.types_mut().any();
    let fields = vec![any; field_count];
    world.module_struct_value_ty(module, &fields)
}

fn map_key_from_ty(world: &World<'_>, ty: Ty) -> Option<super::super::types::MapKey> {
    world.types().as_map_key(&ty)
}

fn literal_map_key(literal: &Literal) -> Option<super::super::types::MapKey> {
    match literal {
        Literal::Int(value) => Some(super::super::types::MapKey::Int(*value)),
        Literal::Atom(name) => Some(super::super::types::MapKey::Atom(name.clone())),
        Literal::Float(_) | Literal::Binary(_) | Literal::Bool(_) | Literal::Nil => None,
    }
}

fn bitfield_value_ty(world: &mut World<'_>, spec: &super::super::body::LoweredBitFieldSpec) -> Ty {
    match spec.ty {
        crate::ast::BitType::Integer
        | crate::ast::BitType::Utf8
        | crate::ast::BitType::Utf16
        | crate::ast::BitType::Utf32 => world.types_mut().int(),
        crate::ast::BitType::Float => world.types_mut().float(),
        crate::ast::BitType::Binary | crate::ast::BitType::Bits => world.types_mut().str_t(),
    }
}

fn lowered_binop_ty(world: &mut World<'_>, op: BinOp, _left: Ty, _right: Ty) -> Ty {
    match op {
        BinOp::And | BinOp::Or | BinOp::In | BinOp::NotIn => world.types_mut().bool(),
        BinOp::Pipe
        | BinOp::Cons
        | BinOp::ListConcat
        | BinOp::ListSubtract
        | BinOp::BinConcat
        | BinOp::Range
        | BinOp::RangeStep => any_ty(world),
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::Div
        | BinOp::Rem
        | BinOp::Eq
        | BinOp::Neq
        | BinOp::Lt
        | BinOp::LtEq
        | BinOp::Gt
        | BinOp::GtEq => panic!("lowering should route {op:?} through direct calls"),
    }
}

fn lowered_unop_ty(world: &mut World<'_>, op: UnOp, input: Ty) -> Ty {
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

/// One body can demand the same callee activation from several call sites;
/// those duplicates are the same fact.
fn dedupe_facts(facts: Vec<FactKey>) -> Vec<FactKey> {
    facts.into_iter().collect::<HashSet<_>>().into_iter().collect()
}

fn any_ty(world: &mut World<'_>) -> Ty {
    world.types_mut().any()
}

fn none_ty(world: &mut World<'_>) -> Ty {
    world.types_mut().none()
}
