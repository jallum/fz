//! Compiler2 semantic-analysis jobs.
//!
//! This module walks lowered function bodies through already-planned entry
//! dispatch, derives direct-call summaries, and settles per-activation return
//! types without calling the legacy whole-program pipeline.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::ast::{BinOp, UnOp};
use crate::dispatch_matrix::pattern::PatternDispatchPlan;
use crate::dispatch_matrix::{
    ComparisonValue, DispatchConst, DispatchNode, EdgeEvidence, GraphNodeId, ListRegion, Region, RegionPredicate,
    SubjectId, SubjectSource,
};

use super::super::body::{
    CallSiteId, ControlDestination, DirectCallee, Literal, LoweredBody, LoweredClause, LoweredEntry, LoweredStep,
    LoweredTail, ValueId,
};
use super::super::contract::FunctionContract;
use super::super::drive::{FactKey, Job, JobEffects};
use super::super::facts::FactValue;
use super::super::identity::{ActivationKey, ExecutableKey, ExecutableNeed, FunctionId, ModuleId};
use super::super::scheduler::FatalError;
use super::super::semantic::{ActivationAnalysis, CallSiteKey, CallSiteSummary, SelectedCallee};
use super::super::types::{ClosureTarget, Ty, Types};
use super::super::world::World;

type DispatchPlan = PatternDispatchPlan<Ty>;
type ValueTypes = HashMap<ValueId, Ty>;
type RefinedCallSurface = (Vec<Ty>, Option<Ty>);

#[derive(Debug, Clone)]
struct CallEmission {
    key: CallSiteKey,
    summary: CallSiteSummary,
    activations: Vec<ActivationContribution>,
    latent_executables: Vec<super::super::identity::ExecutableKey>,
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
    let mut reachable_entries = HashSet::new();
    let mut value_types = HashMap::new();
    let mut return_ty = none_ty(world);
    match lowered_body {
        LoweredBody::Extern { signature } => {
            return_ty = signature.return_ty;
        }
        LoweredBody::Clauses { clauses, entries, .. } => {
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
        for callee_activation in &call.activations {
            outputs.push((
                FactKey::Activation(callee_activation.key.clone()),
                FactValue::inputs(world.types_mut(), callee_activation.key.input.clone()),
            ));
            if !callee_activation.already_present {
                follow_up.insert(Job::AnalyzeActivation(callee_activation.key.clone()));
            }
            follow_up.insert(Job::SealSemanticClosure(activation.root));
        }
        for executable in &call.latent_executables {
            outputs.push((FactKey::Executable(executable.clone()), FactValue::presence(1)));
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
            reachable_entries: {
                let mut entries = reachable_entries.into_iter().collect::<Vec<_>>();
                entries.sort_by_key(|entry| entry.as_u32());
                entries
            },
            callsites: analysis_calls.iter().map(|call| call.key.callsite).collect(),
            latent_executables: analysis_calls
                .iter()
                .flat_map(|call| call.latent_executables.iter().cloned())
                .collect(),
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

fn analyze_entry(
    world: &mut World<'_>,
    entries: &[LoweredEntry],
    entry_id: super::super::body::ControlEntryId,
    values: &ValueTypes,
    reachable_entries: &mut HashSet<super::super::body::ControlEntryId>,
    value_types: &mut ValueTypes,
    calls: &mut Vec<CallEmission>,
    activation: &ActivationKey,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<Ty, FatalError> {
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
    values: &mut ValueTypes,
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
    values: &mut ValueTypes,
    _calls: &mut Vec<CallEmission>,
    _activation: &ActivationKey,
    _reads: &mut Vec<FactKey>,
    _waits: &mut HashSet<FactKey>,
    _follow_up: &mut HashSet<Job>,
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
        LoweredStep::Map { value, entries } => {
            values.insert(*value, map_ty(world, values, entries));
        }
        LoweredStep::MapUpdate { value, base, entries } => {
            let mut map_ty = value_ty(world, values, *base);
            for (key, item) in entries {
                let key_ty = value_ty(world, values, *key);
                if let Some(key) = map_key_from_ty(world, key_ty) {
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
            let map_ty = struct_map_ty(world, values, fields);
            let nominal = struct_nominal_ty(world, *module);
            values.insert(*value, world.types_mut().union(nominal, map_ty));
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
        LoweredStep::NamedFunctionRef { value, .. } => {
            values.insert(*value, any_ty(world));
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
        LoweredStep::MapIndex { value, base, key } => {
            let key_ty = value_ty(world, values, *key);
            let base_ty = value_ty(world, values, *base);
            let value_ty = map_key_from_ty(world, key_ty)
                .and_then(|key| world.types_mut().map_field_lookup(&base_ty, &key))
                .unwrap_or_else(|| any_ty(world));
            values.insert(*value, value_ty);
        }
        LoweredStep::FieldAccess { value, base, field } => {
            let base_ty = value_ty(world, values, *base);
            let value_ty = world
                .types_mut()
                .map_field_lookup(&base_ty, &super::super::types::MapKey::Atom(field.clone()))
                .unwrap_or_else(|| any_ty(world));
            values.insert(*value, value_ty);
        }
        LoweredStep::AssertLiteral { source, literal } => {
            let source_ty = value_ty(world, values, *source);
            let literal_ty = literal_ty(world, literal);
            let refined = world.types_mut().intersect(source_ty, literal_ty);
            values.insert(*source, refined);
        }
        LoweredStep::AssertStruct { source, module } => {
            let source_ty = value_ty(world, values, *source);
            let nominal = struct_nominal_ty(world, *module);
            let refined = world.types_mut().intersect(source_ty, nominal);
            values.insert(*source, refined);
        }
        LoweredStep::RequireMapValue { value, source, key } => {
            let source_ty = value_ty(world, values, *source);
            let value_ty = literal_map_key(key)
                .and_then(|key| world.types_mut().map_field_lookup(&source_ty, &key))
                .unwrap_or_else(|| any_ty(world));
            values.insert(*value, value_ty);
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
        LoweredStep::BitstringInit { reader, source } => {
            values.insert(*reader, value_ty(world, values, *source));
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
            values.insert(*next_reader, value_ty(world, values, *reader));
        }
        LoweredStep::AssertBitstringDone { reader: _ } => {}
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn analyze_tail(
    world: &mut World<'_>,
    entries: &[LoweredEntry],
    tail: &LoweredTail,
    values: &ValueTypes,
    reachable_entries: &mut HashSet<super::super::body::ControlEntryId>,
    value_types: &mut ValueTypes,
    calls: &mut Vec<CallEmission>,
    activation: &ActivationKey,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<Ty, FatalError> {
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
            let then_ty = analyze_entry(
                world,
                entries,
                *then_entry,
                &entry_scope(entries, *then_entry, values, None, &[]),
                reachable_entries,
                value_types,
                calls,
                activation,
                reads,
                waits,
                follow_up,
            )?;
            let else_ty = analyze_entry(
                world,
                entries,
                *else_entry,
                &entry_scope(entries, *else_entry, values, None, &[]),
                reachable_entries,
                value_types,
                calls,
                activation,
                reads,
                waits,
                follow_up,
            )?;
            Ok(world.types_mut().union(then_ty, else_ty))
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
                let arm_ty = analyze_entry(
                    world,
                    entries,
                    arm_entry,
                    &entry_scope(entries, arm_entry, values, None, &[]),
                    reachable_entries,
                    value_types,
                    calls,
                    activation,
                    reads,
                    waits,
                    follow_up,
                )?;
                merged = Some(match merged {
                    None => arm_ty,
                    Some(current) => world.types_mut().union(current, arm_ty),
                });
            }
            let miss_ty = analyze_entry(
                world,
                entries,
                dispatch.miss_entry,
                &entry_scope(entries, dispatch.miss_entry, values, None, &[]),
                reachable_entries,
                value_types,
                calls,
                activation,
                reads,
                waits,
                follow_up,
            )?;
            Ok(match merged {
                None => miss_ty,
                Some(current) => world.types_mut().union(current, miss_ty),
            })
        }
        LoweredTail::Receive(receive) => {
            let any = world.types_mut().any();
            let mut merged = None;
            for clause in &receive.clauses {
                let clause_entry = &entries[clause.entry.as_u32() as usize];
                let clause_params = clause_entry
                    .params
                    .iter()
                    .map(|param| (*param, any))
                    .collect::<Vec<_>>();
                let clause_ty = analyze_entry(
                    world,
                    entries,
                    clause.entry,
                    &entry_scope(entries, clause.entry, values, None, &clause_params),
                    reachable_entries,
                    value_types,
                    calls,
                    activation,
                    reads,
                    waits,
                    follow_up,
                )?;
                merged = Some(match merged {
                    None => clause_ty,
                    Some(current) => world.types_mut().union(current, clause_ty),
                });
            }
            if let Some(after) = &receive.after {
                let after_ty = analyze_entry(
                    world,
                    entries,
                    after.entry,
                    &entry_scope(entries, after.entry, values, None, &[]),
                    reachable_entries,
                    value_types,
                    calls,
                    activation,
                    reads,
                    waits,
                    follow_up,
                )?;
                merged = Some(match merged {
                    None => after_ty,
                    Some(current) => world.types_mut().union(current, after_ty),
                });
            }
            Ok(merged.unwrap_or_else(|| world.types_mut().none()))
        }
        LoweredTail::Halt { .. } => Ok(world.types_mut().none()),
    }
}

#[allow(clippy::too_many_arguments)]
fn deliver_tail_value(
    world: &mut World<'_>,
    entries: &[LoweredEntry],
    dest: &ControlDestination,
    value: ValueId,
    values: &ValueTypes,
    reachable_entries: &mut HashSet<super::super::body::ControlEntryId>,
    value_types: &mut ValueTypes,
    calls: &mut Vec<CallEmission>,
    activation: &ActivationKey,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<Ty, FatalError> {
    let delivered_ty = value_ty(world, values, value);
    match dest {
        ControlDestination::Return => Ok(delivered_ty),
        ControlDestination::Deliver(entry_id) => analyze_entry(
            world,
            entries,
            *entry_id,
            &entry_scope(entries, *entry_id, values, Some((value, delivered_ty)), &[]),
            reachable_entries,
            value_types,
            calls,
            activation,
            reads,
            waits,
            follow_up,
        ),
    }
}

fn entry_scope(
    entries: &[LoweredEntry],
    entry_id: super::super::body::ControlEntryId,
    values: &ValueTypes,
    delivered: Option<(ValueId, Ty)>,
    params: &[(ValueId, Ty)],
) -> ValueTypes {
    let entry = &entries[entry_id.as_u32() as usize];
    let mut scope = HashMap::new();
    if let Some((_, ty)) = delivered
        && let Some(input) = entry.origin.input_value()
    {
        scope.insert(input, ty);
    }
    for (param, ty) in params {
        scope.insert(*param, *ty);
    }
    for capture in &entry.captures {
        if let Some(ty) = values.get(capture).copied() {
            scope.insert(*capture, ty);
        }
    }
    scope
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
                activations: Vec::new(),
                latent_executables: Vec::new(),
            }),
            none,
        ));
    }

    let (summary, mut activations, return_ty) = match callee {
        DirectCallee::Function(function) => {
            resolve_function_call(world, caller, *function, arg_types.clone(), reads, waits, follow_up)?
        }
        DirectCallee::Named { .. } => (
            call_summary(selected_callee(callee), arg_types.clone(), any_ty(world)),
            Vec::new(),
            any_ty(world),
        ),
    };
    let mut latent_executables = Vec::new();
    if let Some((function, runtime_inputs)) = summary.as_ref().and_then(|summary| {
        match summary.callee {
            SelectedCallee::Function(function) => Some(function),
            SelectedCallee::Named { .. } => None,
        }
        .map(|function| (function, summary.input_types.as_slice()))
    }) {
        let runtime_activations = resolve_runtime_callable_boundary_activations(
            world,
            caller,
            function,
            runtime_inputs,
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
    Ok((
        summary.map(|summary| CallEmission {
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
) -> Result<(Option<CallSiteSummary>, Vec<ActivationContribution>, Ty), FatalError> {
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
        return Ok((None, Vec::new(), any_ty(world)));
    }
    let Some((input_types, contract_return_ty)) =
        refine_function_call_surface(world, function, input_types, reads, waits, follow_up)?
    else {
        return Ok((None, Vec::new(), any_ty(world)));
    };
    let Some((activation, already_present, return_ty)) =
        prepare_function_call(world, caller, function, input_types.clone(), reads, waits, follow_up)
    else {
        return Ok((None, Vec::new(), any_ty(world)));
    };
    let return_ty = refine_call_return(world, return_ty, contract_return_ty);
    Ok((
        Some(CallSiteSummary {
            callee: SelectedCallee::Function(function),
            input_types,
            return_ty,
        }),
        vec![ActivationContribution {
            key: activation,
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
) -> Result<(Option<CallSiteSummary>, Vec<ActivationContribution>, Ty), FatalError> {
    let protocol_fact = FactKey::ModuleDefined(protocol);
    if world.module_defined_revision(protocol).is_none() {
        wait_for_protocol_module(world, protocol, waits, follow_up);
        return Ok((None, Vec::new(), any_ty(world)));
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
        return Ok((None, Vec::new(), any_ty(world)));
    }

    if matches.len() != 1 {
        return Ok((None, Vec::new(), any_ty(world)));
    }

    let selected = matches[0];
    let owner_fact = FactKey::ModuleDefined(selected.owner_module);
    if world.module_defined_revision(selected.owner_module).is_none() {
        waits.insert(owner_fact);
        follow_up.insert(Job::DefineModule(selected.owner_module));
        return Ok((None, Vec::new(), any_ty(world)));
    }
    reads.push(owner_fact);

    let Some((input_types, contract_return_ty)) =
        refine_function_call_surface(world, selected.function, input_types, reads, waits, follow_up)?
    else {
        return Ok((None, Vec::new(), any_ty(world)));
    };
    let Some((activation, already_present, return_ty)) = prepare_function_call(
        world,
        caller,
        selected.function,
        input_types.clone(),
        reads,
        waits,
        follow_up,
    ) else {
        return Ok((None, Vec::new(), any_ty(world)));
    };
    let return_ty = refine_call_return(world, return_ty, contract_return_ty);
    Ok((
        Some(CallSiteSummary {
            callee: SelectedCallee::Function(selected.function),
            input_types,
            return_ty,
        }),
        vec![ActivationContribution {
            key: activation,
            already_present,
        }],
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
    let Some(clauses) = world.types_mut().callable_value_clauses(&callee_ty) else {
        return Ok((None, any_ty(world)));
    };
    let mut selected_function = None;
    let mut summary_inputs = None;
    let mut activations = Vec::new();
    let mut return_ty = none_ty(world);

    for clause in clauses {
        let Some(closure) = clause.closure else {
            continue;
        };
        if clause.args.len() != arg_types.len() {
            continue;
        }

        let function = FunctionId::from_u32(closure.target.0);
        match selected_function {
            Some(current) if current != function => return Ok((None, any_ty(world))),
            None => selected_function = Some(function),
            Some(_) => {}
        }

        let refined_args = refine_contract_inputs(world, arg_types.clone(), std::iter::once(clause.args.as_slice()));
        let mut inputs = closure.captures;
        inputs.extend(refined_args);
        let (summary, clause_activations, observed_return) =
            resolve_function_call(world, caller, function, inputs, reads, waits, follow_up)?;
        let clause_return = refine_call_return(world, observed_return, Some(clause.ret));
        return_ty = if world.types().is_empty(&return_ty) {
            clause_return
        } else {
            world.types_mut().union(return_ty, clause_return)
        };

        if let Some(summary) = summary {
            merge_call_inputs(world, &mut summary_inputs, &summary.input_types);
            activations.extend(clause_activations);
        }
    }

    let Some(function) = selected_function else {
        return Ok((None, any_ty(world)));
    };
    let summary = summary_inputs.map(|input_types| CallSiteSummary {
        callee: SelectedCallee::Function(function),
        input_types,
        return_ty,
    });
    let mut latent_executables = Vec::new();
    if let Some(summary) = summary.as_ref() {
        let runtime_activations = resolve_runtime_callable_boundary_activations(
            world,
            caller,
            function,
            summary.input_types.as_slice(),
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
    Ok((
        summary.map(|summary| CallEmission {
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
    let Some(_) = world.fact_revision(lowered_fact.clone()) else {
        waits.insert(lowered_fact);
        follow_up.insert(Job::LowerFunction(function));
        return Ok(Vec::new());
    };
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

fn refine_call_return(world: &mut World<'_>, observed: Ty, contract: Option<Ty>) -> Ty {
    let Some(contract) = contract else {
        return observed;
    };
    if world.types().is_empty(&observed) {
        return contract;
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
        let function = FunctionId::from_u32(closure.target.0);
        if !world.require_activation_key_facts(function, reads, waits, follow_up) {
            continue;
        }
        let mut input_types = closure.captures;
        input_types.extend(clause.args);
        let activation = world.activation_key(caller.root, function, &input_types);
        let already_present = world.fact_revision(FactKey::Activation(activation.clone())).is_some();
        activations.push(ActivationContribution {
            key: activation,
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

fn merge_call_inputs(world: &mut World<'_>, merged: &mut Option<Vec<Ty>>, observed: &[Ty]) {
    match merged {
        Some(current) => {
            if current.len() < observed.len() {
                current.resize_with(observed.len(), || any_ty(world));
            }
            for (slot, observed_ty) in observed.iter().copied().enumerate() {
                current[slot] = world.types_mut().union(current[slot], observed_ty);
            }
        }
        None => {
            *merged = Some(observed.to_vec());
        }
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
            | LoweredStep::NamedFunctionRef { value, .. }
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

fn map_ty(world: &mut World<'_>, values: &ValueTypes, entries: &[(ValueId, ValueId)]) -> Ty {
    let mut fields = BTreeMap::new();
    for (key, value) in entries {
        let key_ty = value_ty(world, values, *key);
        let Some(key) = map_key_from_ty(world, key_ty) else {
            return world.types_mut().map_top();
        };
        fields.insert(key, value_ty(world, values, *value));
    }
    world.types_mut().map(&fields.into_iter().collect::<Vec<_>>())
}

fn struct_map_ty(world: &mut World<'_>, values: &ValueTypes, fields: &[(String, ValueId)]) -> Ty {
    let map_fields = fields
        .iter()
        .map(|(name, value)| {
            (
                super::super::types::MapKey::Atom(name.clone()),
                value_ty(world, values, *value),
            )
        })
        .collect::<Vec<_>>();
    world.types_mut().map(&map_fields)
}

fn struct_nominal_ty(world: &mut World<'_>, module: ModuleId) -> Ty {
    let name = world
        .module_name(module)
        .unwrap_or_else(|| panic!("named struct module {} should have a reverse lookup", module.as_u32()))
        .to_string();
    crate::frontend::protocols::struct_impl_target_type(
        world.types_mut(),
        name.rsplit('.').next().unwrap_or(name.as_str()),
    )
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
