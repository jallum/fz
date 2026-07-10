//! Compiler2 semantic-analysis jobs.
//!
//! This module walks lowered function bodies through already-planned entry
//! dispatch, derives direct-call summaries, and settles per-activation return
//! types without calling the legacy whole-program pipeline.

use std::collections::{BTreeMap, HashMap, HashSet, hash_map::Entry};

use crate::ast::{BinOp, UnOp};
use crate::diag::driver::emit_through;
use crate::diag::{Diagnostic, codes};
use crate::dispatch_matrix::pattern::PatternDispatchPlan;
use crate::dispatch_matrix::{
    ComparisonValue, DispatchNode, EdgeEvidence, GraphNodeId, ListRegion, Region, RegionPredicate, SubjectId,
    SubjectSource,
};
use crate::ground_value::GroundValue;
use crate::source::Span;

use super::super::body::{
    CallSiteId, ControlDestination, LoweredBody, LoweredClause, LoweredEntry, LoweredMapKey, LoweredStep, LoweredTail,
    ValueId,
};
use super::super::contract::FunctionContract;
use super::super::drive::{FactKey, JobEffects, current_uses};
use super::super::identity::{
    ActivationKey, ExecutableNeed, FunctionId, ModuleId, TypeName, function_id_of_closure_target,
};
use super::super::protocol::ProtocolCallbackImpl;
use super::super::scheduler::FatalError;
use super::super::semantic::{
    ActivationAnalysis, CallSiteKey, CallSiteSummary, CallSiteTargets, CallTargetSummary, SelectedCallee,
};
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
        // Mirrors the `ActivationInputs` gate just below: absence of the seed
        // fact is a genuine block on `Job::SeedActivation`, not a conclusion.
        // Returning an empty `JobEffects` here would be a silent
        // conclude-by-omission with no subscription to re-wake it; a bare
        // wait lets the ordinary blocked-waiter expansion
        // (`demand_blocked_wait_producers`) carry it instead.
        return Ok(JobEffects::wait_on_current(activation_fact));
    }
    let activation_inputs_fact = FactKey::ActivationInputs(activation.clone());
    let Some(inputs) = world.activation_inputs(activation) else {
        return Ok(JobEffects::wait_on_current(activation_inputs_fact));
    };

    let function = activation.function;
    let function_fact = FactKey::FunctionDefined(function);
    let Some(_) = world.function_defined_revision(function) else {
        return Ok(world.wait_for_function_definition(function));
    };

    let lowered_fact = FactKey::LoweredBody(function);
    if !world.has_fact(&lowered_fact) {
        // `LoweredBody`'s sole producer arm is `Job::LowerFunction`
        // (`World::demand_fact_producer`).
        return Ok(JobEffects::wait_on_current(lowered_fact));
    }

    let dispatch_fact = FactKey::EntryDispatch(function);
    if !world.has_fact(&dispatch_fact) {
        // `EntryDispatch`'s sole producer arm is `Job::PlanEntryDispatch`
        // (`World::demand_fact_producer`).
        return Ok(JobEffects::wait_on_current(dispatch_fact));
    }

    let mut reads = vec![
        FactKey::Activation(activation.clone()),
        FactKey::ActivationInputs(activation.clone()),
        function_fact,
        lowered_fact,
        dispatch_fact,
    ];
    let mut waits = HashSet::new();
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
        LoweredBody::Extern { ref signature } => {
            return_evidence = Some(signature.return_ty);
        }
        LoweredBody::Clauses {
            ref clauses,
            ref entries,
            ..
        } => {
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
                )?;
                return_evidence = join_evidence(world, return_evidence, clause_return);
            }
        }
    }

    if let Some(contract_return_ty) = activation_contract_return(world, function, &inputs, &mut reads, &mut waits)? {
        return_evidence = refine_call_return(world, return_evidence, Some(contract_return_ty));
    }

    // Waits no longer bail: a waiting completion extends the job's standing
    // claims (it cannot retract), so partial evidence publishes safely and
    // the waits simply ride the final effects.
    analysis_calls = coalesce_call_emissions(world, activation, analysis_calls, &mut reads, &mut waits)?;

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
            let targets_fact = FactKey::CallSiteTargets(call.key.clone());
            let targets_changed =
                world.define_callsite_targets(call.key.clone(), CallSiteTargets::from_summary(summary));
            outputs.push(targets_fact.clone());
            if targets_changed {
                changed.push(targets_fact);
            }
        }
        for callee_activation in &call.activations {
            if emitted_activations.insert(callee_activation.key.clone()) {
                outputs.push(FactKey::Activation(callee_activation.key.clone()));
            }
            outputs.push(FactKey::ActivationInputs(callee_activation.key.clone()));
            activation_input_contributions.push((callee_activation.key.clone(), callee_activation.inputs.clone()));
            // No wait+push pair here: `prepare_function_call` only `reads`
            // the callee's `ReturnType` (so mutual recursion cannot
            // deadlock), so nothing ever blocks on the callee's analysis
            // itself. Publishing `Activation(callee_activation.key)` above is
            // the frontier's own record site — `World::complete_job` folds it
            // into `activation_frontier`, and `demand_activation_frontier_analyses`
            // ignites the callee's first analysis when the agenda drains.
        }
        for executable in &call.latent_executables {
            if emitted_executables.insert(executable.clone()) {
                outputs.push(FactKey::Executable(executable.clone()));
            }
        }
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
            reachable_clauses,
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
                .collect(),
            value_types,
        },
    );
    let analyzed_fact = FactKey::ActivationAnalyzed(activation.clone());
    outputs.push(analyzed_fact.clone());
    if analysis_changed {
        changed.push(analyzed_fact);
    }

    Ok(JobEffects {
        reads: current_uses(reads),
        waits: current_uses(waits),
        outputs: dedupe_facts(outputs),
        changed: dedupe_facts(changed),
        activation_input_contributions,
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
) -> Result<Option<Ty>, FatalError> {
    reachable_entries.insert(entry_id);
    let entry = &entries[entry_id.as_u32() as usize];
    let mut local = values.clone();
    apply_steps(world, &entry.steps, &mut local, calls, activation, reads, waits)?;
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
    )
}

fn apply_steps(
    world: &mut World<'_>,
    steps: &[LoweredStep],
    values: &mut SemanticValues,
    calls: &mut Vec<CallEmission>,
    activation: &ActivationKey,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<(), FatalError> {
    for step in steps {
        apply_step(world, step, values, calls, activation, reads, waits)?;
    }
    Ok(())
}

fn apply_step(
    world: &mut World<'_>,
    step: &LoweredStep,
    values: &mut SemanticValues,
    _calls: &mut Vec<CallEmission>,
    _activation: &ActivationKey,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<(), FatalError> {
    match step {
        LoweredStep::Const { value, literal } => {
            let literal_ty = literal_ty(world, literal);
            values.insert(*value, literal_ty);
        }
        LoweredStep::Tuple { value, items } => {
            let Some(items) = items
                .iter()
                .map(|item| value_ty(values, *item))
                .collect::<Option<Vec<_>>>()
            else {
                return Ok(());
            };
            let tuple = world.types_mut().tuple(&items);
            values.insert(*value, tuple);
        }
        LoweredStep::List { value, items, tail } => {
            if let Some(list) = list_ty(world, values, items, *tail) {
                values.insert(*value, list);
            }
        }
        LoweredStep::Map { value, entries } => {
            if let Some(map) = map_ty(world, values, entries) {
                values.insert(*value, map);
            }
        }
        LoweredStep::MapUpdate { value, base, entries } => {
            let Some(mut map_ty) = value_ty(values, *base) else {
                return Ok(());
            };
            for (key, item) in entries {
                let Some(key) = lowered_map_key(world, values, key) else {
                    return Ok(());
                };
                let Some(item_ty) = value_ty(values, *item) else {
                    return Ok(());
                };
                if let Some(key) = key {
                    map_ty = world.types_mut().refine_map_field(&map_ty, &key, &item_ty);
                } else {
                    map_ty = world.types_mut().map_top();
                    break;
                }
            }
            values.insert(*value, map_ty);
        }
        LoweredStep::Struct { value, module, fields } => {
            let Some(field_tys) = fields
                .iter()
                .map(|(_, value)| value_ty(values, *value))
                .collect::<Option<Vec<_>>>()
            else {
                return Ok(());
            };
            // `fields` is already ordered against the struct's schema by body
            // lowering (which waited on `StructDefined` before producing this
            // step), so the field names travel with the step itself — no
            // separate schema lookup needed here.
            let field_names = fields.iter().map(|(name, _)| name.clone()).collect::<Vec<_>>();
            let struct_ty = world.struct_module_value_ty(*module, &field_names, &field_tys);
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
            let Some(captures) = captures
                .iter()
                .map(|capture| value_ty(values, *capture))
                .collect::<Option<Vec<_>>>()
            else {
                return Ok(());
            };
            let closure = world.closure_ty(*function, captures);
            values.insert(*value, closure);
        }
        LoweredStep::BinaryOp { value, op, left, right } => {
            let (Some(left), Some(right)) = (value_ty(values, *left), value_ty(values, *right)) else {
                return Ok(());
            };
            values.insert(*value, lowered_binop_ty(world, *op, left, right));
        }
        LoweredStep::UnaryOp { value, op, input } => {
            let Some(input) = value_ty(values, *input) else {
                return Ok(());
            };
            values.insert(*value, lowered_unop_ty(world, *op, input));
        }
        LoweredStep::MapIndex { value, base, key } => {
            let Some(base_ty) = value_ty(values, *base) else {
                return Ok(());
            };
            let Some(key) = lowered_map_key(world, values, key) else {
                return Ok(());
            };
            let field_ty = key
                .and_then(|key| world.types_mut().map_field_lookup(&base_ty, &key))
                .unwrap_or_else(|| any_ty(world));
            values.insert(*value, field_ty);
        }
        LoweredStep::FieldAccess { value, base, field } => {
            let Some(base_ty) = value_ty(values, *base) else {
                return Ok(());
            };
            let field_ty = world
                .types_mut()
                .map_field_lookup(&base_ty, &super::super::types::MapKey::Atom(field.clone()))
                .unwrap_or_else(|| any_ty(world));
            values.insert(*value, field_ty);
        }
        LoweredStep::AssertLiteral { source, literal } => {
            let Some(source_ty) = value_ty(values, *source) else {
                return Ok(());
            };
            let literal_ty = literal_ty(world, literal);
            let refined = world.types_mut().intersect(source_ty, literal_ty);
            values.insert(*source, refined);
        }
        LoweredStep::AssertStruct { source, module } => {
            let Some(source_ty) = value_ty(values, *source) else {
                return Ok(());
            };
            let asserted = struct_assertion_ty(world, *module, reads, waits);
            let refined = world.types_mut().intersect(source_ty, asserted);
            values.insert(*source, refined);
        }
        LoweredStep::RequireMapValue { value, source, key } => {
            let Some(source_ty) = value_ty(values, *source) else {
                return Ok(());
            };
            let field_ty = literal_map_key(key)
                .and_then(|key| world.types_mut().map_field_lookup(&source_ty, &key))
                .unwrap_or_else(|| any_ty(world));
            values.insert(*value, field_ty);
        }
        LoweredStep::AssertTuple { source, arity } => {
            let any = world.types_mut().any();
            let fields = world.types_mut().repeat(any, *arity);
            let tuple = world.types_mut().tuple(&fields);
            let Some(source_ty) = value_ty(values, *source) else {
                return Ok(());
            };
            let refined = world.types_mut().intersect(source_ty, tuple);
            values.insert(*source, refined);
        }
        LoweredStep::TupleField { value, source, index } => {
            let Some(source_ty) = value_ty(values, *source) else {
                return Ok(());
            };
            let field_ty = world.types_mut().tuple_field_type(&source_ty, *index);
            values.insert(*value, field_ty);
        }
        LoweredStep::AssertEmptyList { source } => {
            let empty = world.types_mut().empty_list();
            let Some(source_ty) = value_ty(values, *source) else {
                return Ok(());
            };
            let refined = world.types_mut().intersect(source_ty, empty);
            values.insert(*source, refined);
        }
        LoweredStep::AssertSame { source, value } => {
            let (Some(source_ty), Some(value_ty)) = (value_ty(values, *source), value_ty(values, *value)) else {
                return Ok(());
            };
            let both = world.types_mut().intersect(source_ty, value_ty);
            values.insert(*source, both);
            values.insert(*value, both);
        }
        LoweredStep::SplitList { source, head, tail } => {
            let Some(source_ty) = value_ty(values, *source) else {
                return Ok(());
            };
            let elem = world.types_mut().list_element_type(&source_ty);
            let rest = world.types_mut().list(elem);
            // A successful split proves the source is a non-empty list. Record
            // that refinement on the source, mirroring how `AssertEmptyList`
            // refines its source to the empty list: the proof a clause was
            // entered must reach the source's type, or typed head/tail
            // projection (and the owned-cons reuse it unlocks) is left on the
            // table for any list whose static type is the proper `[T] | []`.
            let any = world.types_mut().any();
            let non_empty = world.types_mut().non_empty_list(any);
            let refined_source = world.types_mut().intersect(source_ty, non_empty);
            values.insert(*source, refined_source);
            values.insert(*head, elem);
            values.insert(*tail, rest);
        }
        LoweredStep::BitstringInit { reader, source } => {
            if let Some(source_ty) = value_ty(values, *source) {
                values.insert(*reader, source_ty);
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
            values.insert(*ok, world.types_mut().bool());
            values.insert(*value, bitfield_value_ty(world, spec));
            if let Some(reader_ty) = value_ty(values, *reader) {
                values.insert(*next_reader, reader_ty);
            }
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

/// Analyze one entry reached as a plain branch (no delivered value).
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
) -> Result<Option<Ty>, FatalError> {
    let scope = entry_scope(entries, entry_id, values, None, params);
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
        ),
        LoweredTail::DirectCall {
            value,
            callsite,
            callee,
            args,
            dest,
        } => {
            let Some(arg_types) = args
                .iter()
                .map(|arg| value_ty(values, arg.value))
                .collect::<Option<Vec<_>>>()
            else {
                return Ok(None);
            };
            let (emission, return_ty) =
                resolve_direct_call(world, activation, *callsite, *callee, arg_types, reads, waits)?;
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
            )
        }
        LoweredTail::ClosureCall {
            value,
            callsite,
            callee,
            args,
            dest,
        } => {
            let (Some(callee_ty), Some(arg_types)) = (
                value_ty(values, *callee),
                args.iter()
                    .map(|arg| value_ty(values, arg.value))
                    .collect::<Option<Vec<_>>>(),
            ) else {
                return Ok(None);
            };
            let (emission, return_ty) =
                resolve_closure_call(world, activation, *callsite, callee_ty, arg_types, reads, waits)?;
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
            )?;
            Ok(join_evidence(world, then_ty, else_ty))
        }
        LoweredTail::Dispatch { inputs, dispatch, .. } => {
            let Some(input_tys) = inputs
                .iter()
                .map(|input| value_ty(values, *input))
                .collect::<Option<Vec<_>>>()
            else {
                return Ok(None);
            };
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
) -> Result<Option<Ty>, FatalError> {
    // No evidence for the delivered value means no evidence for the path.
    let Some(delivered) = value_ty(values, value) else {
        return Ok(None);
    };
    // A proven-empty value is evidence: nothing flows past this point, the
    // path is dead.
    if world.types().is_empty(&delivered) {
        return Ok(Some(delivered));
    }
    match dest {
        ControlDestination::Return => Ok(Some(delivered)),
        ControlDestination::Deliver(entry_id) => {
            let scope = entry_scope(entries, *entry_id, values, Some((value, delivered)), &[]);
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
            )
        }
    }
}

/// Build an entry's scope from whatever evidence exists. Captures are the
/// TRANSITIVE free-value closure (`compute_entry_captures`): an entry lists
/// values only its children read, so a missing capture must not suppress the
/// entry — every read enforces its own availability via `value_ty`, and a
/// child entry re-scopes and gates itself.
fn entry_scope(
    entries: &[LoweredEntry],
    entry_id: super::super::body::ControlEntryId,
    values: &SemanticValues,
    delivered: Option<(ValueId, Ty)>,
    params: &[(ValueId, Ty)],
) -> SemanticValues {
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
        if let Some(value) = values.get(capture).copied() {
            scope.insert(*capture, value);
        }
    }
    scope
}

fn resolve_direct_call(
    world: &mut World<'_>,
    caller: &ActivationKey,
    callsite: CallSiteId,
    function: FunctionId,
    arg_types: Vec<Ty>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<(Option<CallEmission>, Option<Ty>), FatalError> {
    // A proven-empty argument type is a real fact: no value can reach this
    // call, the path is dead. (Absence cannot arrive here — an unresolved
    // upstream call already short-circuited the path.)
    if arg_types.iter().any(|arg| world.types().is_empty(arg)) {
        return Ok((None, Some(none_ty(world))));
    }

    let (summary, activations, return_ty) =
        resolve_function_call(world, caller, function, arg_types, callsite.span(), reads, waits)?;
    Ok((
        summary.map(|summary| CallEmission {
            key: CallSiteKey {
                activation: caller.clone(),
                callsite,
            },
            summary: Some(summary),
            latent_executables: Vec::new(),
            activations,
        }),
        return_ty,
    ))
}

/// Merge one path's observed value types into the activation's published
/// summary. Paths join by clause-preserving UNION: the summary is what
/// materialization reads to resolve escaped callables, so a case that yields
/// `add_a` on one arm and `add_b` on the other must publish both closure
/// identities — `refine_widen` merges the arrows into an anonymous clause
/// and is reserved for the activation-key plane (`merge_call_input_vec`).
fn merge_value_types(world: &mut World<'_>, merged: &mut ValueTypes, observed: &SemanticValues) {
    for (&value, &ty) in observed {
        match merged.get(&value).copied() {
            Some(current) if current != ty => {
                let joined = world.types_mut().union(current, ty);
                merged.insert(value, joined);
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
                // `surface_inputs` is the declared call surface only -- a
                // closure target's real activation carries a leading
                // capture-environment slot that `surface_inputs` never
                // names. Rebuilding from `surface_inputs` alone silently
                // drops that capture slot and hands `call_emission_for_function`
                // an under-arity input vector, which mints a truncated
                // activation. The kept activation's own `.inputs()` still
                // carries the true capture prefix, so splice today's
                // widened surface back onto it instead of substituting
                // for it.
                let captures_len = target
                    .activation
                    .as_ref()
                    .map(|activation| {
                        activation
                            .input_len(world.types())
                            .saturating_sub(target.surface_inputs.len())
                    })
                    .unwrap_or(0);
                let mut input_types = target
                    .activation
                    .as_ref()
                    .map(|activation| activation.inputs(world.types()))
                    .unwrap_or_default();
                input_types.truncate(captures_len);
                input_types.extend(target.surface_inputs.iter().copied());
                let Some(rebuilt) =
                    call_emission_for_function(world, caller, call.key.clone(), function, input_types, reads, waits)?
                else {
                    return Ok(call);
                };
                let Some(rebuilt_summary) = rebuilt.summary else {
                    return Ok(call);
                };
                let Some(mut rebuilt_target) = rebuilt_summary.single_target().cloned() else {
                    return Ok(call);
                };
                // `call_emission_for_function` published `surface_inputs` as
                // the full vector it was handed; strip the capture prefix
                // back off so the published surface stays capture-free, as
                // every other producer of `CallTargetSummary` guarantees.
                if captures_len > 0 {
                    rebuilt_target.surface_inputs.drain(..captures_len);
                }
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
) -> Result<Option<CallEmission>, FatalError> {
    let Some((input_types, contract_return_ty)) =
        refine_function_call_surface(world, function, input_types, key.callsite.span(), reads, waits)?
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
                    surface_inputs: input_types,
                    activation: None,
                    return_ty,
                }],
                return_ty,
            }),
            activations: Vec::new(),
            latent_executables: Vec::new(),
        }));
    }
    let Some((activation, return_ty)) = prepare_function_call(world, caller, function, &input_types, reads, waits)
    else {
        return Ok(None);
    };
    let return_ty = refine_call_return(world, return_ty, contract_return_ty);
    let activations = vec![ActivationContribution {
        key: activation.clone(),
        inputs: input_types.clone(),
    }];
    Ok(Some(CallEmission {
        key,
        summary: Some(CallSiteSummary {
            targets: vec![CallTargetSummary {
                callee: SelectedCallee::Function(function),
                surface_inputs: input_types,
                activation: Some(activation),
                return_ty,
            }],
            return_ty,
        }),
        activations,
        latent_executables: Vec::new(),
    }))
}

fn resolve_function_call(
    world: &mut World<'_>,
    caller: &ActivationKey,
    function: FunctionId,
    input_types: Vec<Ty>,
    call_span: Span,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<ResolvedCall, FatalError> {
    if let Some(callback) = world.protocol_callback(function) {
        return resolve_protocol_call(
            world,
            caller,
            function,
            callback.protocol,
            input_types,
            call_span,
            reads,
            waits,
        );
    }
    if wait_for_unresolved_function_module(world, function, waits) {
        return Ok((None, Vec::new(), None));
    }
    let Some((input_types, contract_return_ty)) =
        refine_function_call_surface(world, function, input_types, call_span, reads, waits)?
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
                    None,
                    Some(return_ty),
                )],
                return_ty: Some(return_ty),
            }),
            Vec::new(),
            Some(return_ty),
        ));
    }
    let Some((activation, return_evidence)) =
        prepare_function_call(world, caller, function, &input_types, reads, waits)
    else {
        return Ok((None, Vec::new(), None));
    };
    let return_ty = refine_call_return(world, return_evidence, contract_return_ty);
    Ok((
        Some(CallSiteSummary {
            targets: vec![call_target_summary(
                SelectedCallee::Function(function),
                input_types.clone(),
                Some(activation.clone()),
                return_ty,
            )],
            return_ty,
        }),
        vec![ActivationContribution {
            key: activation,
            inputs: input_types.clone(),
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
    call_span: Span,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<ResolvedCall, FatalError> {
    // VERDICT (fz-rh2.17.5.9): body readiness, not interface visibility.
    // Defining the protocol module is what registers its callbacks and
    // publishes ProtocolDispatch — the precise fact read just below. This
    // gate bootstraps that demand (including runtime code ensure/indexing);
    // it is not a stand-in for ModuleInterface.
    let protocol_fact = FactKey::ModuleDefined(protocol);
    if world.module_defined_revision(protocol).is_none() {
        wait_for_protocol_module(world, protocol, waits);
        return Ok((None, Vec::new(), None));
    }
    reads.push(protocol_fact);
    let dispatch_fact = FactKey::ProtocolDispatch(protocol);
    if !world.has_fact(&dispatch_fact) {
        // `ProtocolDispatch` is a co-output of the same `Job::DefineModule`
        // run that publishes `ModuleDefined` for a protocol module
        // (`source_publish::publish_protocol_surface` pushes both into one
        // `JobEffects`), so it carries no arm of its own in
        // `demand_fact_producer` — its demand rides `ModuleDefined`'s. Since
        // `module_defined_revision(protocol)` is already proven `Some` above,
        // `Job::DefineModule(protocol)` has already run and already claimed
        // this fact for a true protocol module; this branch is defensive
        // (unreachable in practice) rather than provably dead by construction,
        // so it stays a bare wait instead of an assert/panic.
        waits.insert(dispatch_fact);
        return Ok((None, Vec::new(), None));
    }
    reads.push(dispatch_fact);

    let receiver_ty = input_types.first().cloned().unwrap_or_else(|| any_ty(world));

    let mut matches = Vec::new();
    let dispatch = world
        .protocol_dispatch(protocol)
        .expect("protocol dispatch fact should be stored before semantic reads it")
        .clone();
    for arm in dispatch.arms {
        let target_ty = world.module_impl_target_ty(arm.target, reads);
        if !protocol_receiver_target_overlaps(world, receiver_ty, target_ty) {
            continue;
        }
        let overlap = world.types_mut().intersect(receiver_ty, target_ty);
        if let Some(callback) = arm.callbacks.get(&callback_function).copied() {
            matches.push((callback, overlap));
        }
    }

    if matches.is_empty() {
        // The dispatch holds no arm for this receiver yet. Each `defimpl` is its
        // own `Protocol.Target` module recorded in the provider index at scope
        // time (including built-ins co-located with the protocol, and impls in a
        // module the program never otherwise reaches by name). Demand the impl
        // module whose target overlaps the receiver — the impl is the unit of
        // demand. The provider index grows across the drive as more source is
        // scoped (every module containing a `defimpl` for this protocol is a
        // separate publisher), so the read must be registered unconditionally —
        // even before any provider has been indexed — or a later `defimpl`
        // discovery would never re-wake this callsite. There is no
        // receiver-type module-name scan: referencing the protocol is the
        // single discovery path.
        reads.push(FactKey::ProtocolImplProviders(protocol));
        for (target, provider) in world.protocol_impl_providers(protocol) {
            let target_ty = world.module_impl_target_ty(target, reads);
            if !protocol_receiver_target_overlaps(world, receiver_ty, target_ty) {
                continue;
            }
            if world.module_defined_revision(provider).is_none() {
                waits.insert(FactKey::ModuleDefined(provider));
            }
        }
        return Ok((None, Vec::new(), None));
    }

    let matches = merge_protocol_matches_by_function(world, matches);
    let mut targets = Vec::new();
    let mut activations = Vec::new();
    let mut return_ty = None;
    for (selected, overlap) in matches {
        // VERDICT (fz-rh2.17.5.9): the old ModuleDefined(owner_module) wait
        // here was over-waiting — holding a ProtocolCallbackImpl proves the
        // impl fragment already published its function, and re-serializing
        // every protocol call behind whole-module scoping is readiness the
        // call does not require. Gate per FUNCTION, exactly as the
        // direct-call path does.
        if wait_for_unresolved_function_module(world, selected.function, waits) {
            return Ok((None, Vec::new(), None));
        }

        let refined_inputs = refine_protocol_target_inputs(world, &input_types, receiver_ty, overlap);
        let Some((refined_inputs, contract_return_ty)) =
            refine_function_call_surface(world, selected.function, refined_inputs, call_span, reads, waits)?
        else {
            return Ok((None, Vec::new(), None));
        };
        let Some((activation, observed_return)) =
            prepare_function_call(world, caller, selected.function, &refined_inputs, reads, waits)
        else {
            return Ok((None, Vec::new(), None));
        };
        let target_return = refine_call_return(world, observed_return, contract_return_ty);
        return_ty = join_evidence(world, return_ty, target_return);
        targets.push(call_target_summary(
            SelectedCallee::Function(selected.function),
            refined_inputs.clone(),
            Some(activation.clone()),
            target_return,
        ));
        activations.push(ActivationContribution {
            key: activation,
            inputs: refined_inputs.clone(),
        });
    }
    Ok((Some(CallSiteSummary { targets, return_ty }), activations, return_ty))
}

fn protocol_receiver_target_overlaps(world: &mut World<'_>, receiver_ty: Ty, target_ty: Ty) -> bool {
    let receiver = world.types().runtime_type_predicate(&receiver_ty);
    let target = world.types().runtime_type_predicate(&target_ty);
    receiver.overlaps(&target) && {
        let overlap = world.types_mut().intersect(receiver_ty, target_ty);
        !world.types().is_empty(&overlap)
    }
}

fn merge_protocol_matches_by_function(
    world: &mut World<'_>,
    matches: Vec<(ProtocolCallbackImpl, Ty)>,
) -> Vec<(ProtocolCallbackImpl, Ty)> {
    let mut merged = Vec::<(ProtocolCallbackImpl, Ty)>::new();
    for (selected, overlap) in matches {
        if let Some((_, existing_overlap)) = merged
            .iter_mut()
            .find(|(existing, _)| existing.function == selected.function)
        {
            *existing_overlap = world.types_mut().union(*existing_overlap, overlap);
        } else {
            merged.push((selected, overlap));
        }
    }
    merged
}

fn resolve_closure_call(
    world: &mut World<'_>,
    caller: &ActivationKey,
    callsite: CallSiteId,
    callee_ty: Ty,
    arg_types: Vec<Ty>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
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
    let mut selected_targets = Vec::new();
    let mut activations = Vec::new();
    let latent_executables = Vec::new();
    let mut return_ty = None;

    // A closure-shaped clause whose arity matches names a concrete target. Its
    // analysis may still be pending this round (no summary yet), which is
    // *absence of evidence*, not proof of a dynamic edge. We must not manufacture
    // `any` from that absence: the cumulative `ReturnType` join would union the
    // stale `any` and never retract it once the target settles to its real type.
    let mut named_concrete_target = false;
    for clause in clauses {
        let Some(closure) = clause.closure else {
            continue;
        };
        if clause.args.len() != arg_types.len() {
            continue;
        }
        named_concrete_target = true;
        let function = function_id_of_closure_target(closure.target);

        let refined_args = refine_contract_inputs(world, arg_types.clone(), std::iter::once(clause.args.as_slice()));
        let mut inputs = closure.captures;
        inputs.extend(refined_args.clone());
        let (summary, clause_activations, observed_return) =
            resolve_function_call(world, caller, function, inputs, callsite.span(), reads, waits)?;
        let clause_return = refine_call_return(world, observed_return, Some(clause.ret));
        return_ty = join_evidence(world, return_ty, clause_return);

        if let Some(summary) = summary {
            let Some(target) = summary.single_target() else {
                return Err(FatalError);
            };
            let rebuilt_target = call_target_summary(
                target.callee.clone(),
                refined_args.clone(),
                target.activation.clone(),
                clause_return,
            );
            if !selected_targets.contains(&rebuilt_target) {
                selected_targets.push(rebuilt_target.clone());
            }
            activations.extend(clause_activations);
        }
    }

    if selected_targets.is_empty() {
        // A matching closure clause names a concrete target whose analysis is
        // still pending: report no evidence yet (the `reads`/`waits` registered
        // above re-wake this call when the target settles), never the earned
        // `any`. Only a callee with no matching closure-shaped clause is the
        // genuine dynamic edge that earns `any`.
        if named_concrete_target {
            return Ok((None, return_ty));
        }
        return Ok((None, Some(any_ty(world))));
    };
    Ok((
        Some(CallEmission {
            key: CallSiteKey {
                activation: caller.clone(),
                callsite,
            },
            summary: Some(CallSiteSummary {
                targets: selected_targets,
                return_ty,
            }),
            latent_executables,
            activations,
        }),
        return_ty,
    ))
}

fn refine_function_call_surface(
    world: &mut World<'_>,
    function: FunctionId,
    input_types: Vec<Ty>,
    violation_span: Span,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<Option<RefinedCallSurface>, FatalError> {
    if !world.function_declares_contract(function) {
        return Ok(Some((input_types, None)));
    }
    let contract_fact = FactKey::FunctionContract(function);
    let Some(_) = world.function_contract_revision(function) else {
        waits.insert(contract_fact);
        return Ok(None);
    };
    reads.push(contract_fact);
    let contract = world
        .function_contract(function)
        .cloned()
        .expect("function contract fact should resolve to a stored contract");
    Ok(Some(apply_function_contract(
        world,
        function,
        &contract,
        input_types,
        violation_span,
    )?))
}

fn apply_function_contract(
    world: &mut World<'_>,
    function: FunctionId,
    contract: &FunctionContract,
    input_types: Vec<Ty>,
    violation_span: Span,
) -> Result<(Vec<Ty>, Option<Ty>), FatalError> {
    let application = contract.apply(world.types_mut(), &input_types);
    if !application.enforceable_satisfied
        && function_contract_is_enforced(world, function)
        && spec_violation_is_actionable(world, &input_types)
    {
        return Err(emit_spec_violation(world, function, &input_types, violation_span));
    }
    Ok((
        refine_contract_inputs(
            world,
            input_types,
            application.matched_arrows.iter().map(|params| params.as_slice()),
        ),
        application.result,
    ))
}

fn function_contract_is_enforced(world: &World<'_>, function: FunctionId) -> bool {
    let (source, surface) = world.function_definition(function);
    !world.is_bootstrap(source.code) && surface.extern_abi.is_none()
}

fn spec_violation_is_actionable(world: &mut World<'_>, input_types: &[Ty]) -> bool {
    let any = world.types_mut().any();
    input_types
        .iter()
        .all(|ty| !world.types().has_vars(ty) && !world.types().is_equivalent(ty, &any))
}

fn activation_contract_return(
    world: &mut World<'_>,
    function: FunctionId,
    input_types: &[Ty],
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<Option<Ty>, FatalError> {
    let violation_span = world.function_surface(function).span;
    let Some((_, contract_return_ty)) =
        refine_function_call_surface(world, function, input_types.to_vec(), violation_span, reads, waits)?
    else {
        return Ok(None);
    };
    Ok(contract_return_ty)
}

fn emit_spec_violation(world: &World<'_>, function: FunctionId, input_types: &[Ty], span: Span) -> FatalError {
    let function_ref = world.function_ref(function);
    let observed = input_types
        .iter()
        .map(|ty| world.types().display_for_diag(ty))
        .collect::<Vec<_>>()
        .join(", ");
    emit_through(
        world.tel(),
        &[Diagnostic::error(
            codes::SPEC_VIOLATION,
            format!(
                "call to `{}/{}` violates its @spec for arguments ({})",
                function_ref.name, function_ref.arity, observed
            ),
            span,
        )
        .with_label("no declared @spec accepts these arguments")],
    );
    FatalError
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

fn prepare_function_call(
    world: &mut World<'_>,
    caller: &ActivationKey,
    function: FunctionId,
    arg_types: &[Ty],
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Option<(ActivationKey, Option<Ty>)> {
    if !world.require_activation_key_facts(function, reads, waits) {
        return None;
    }

    let activation = world.activation_key(caller.root, function, arg_types);
    // The read is the subscription that re-wakes this caller when the
    // callee's return evidence rises — chaotic iteration needs no wait here,
    // so mutual recursion cannot deadlock. Absent evidence stays absent: it
    // is the ascent's bottom, never the type `none`.
    reads.push(FactKey::ReturnType(activation.clone()));
    let return_evidence = world.activation_return(&activation);
    Some((activation, return_evidence))
}

/// VERDICT (fz-rh2.17.5.9): body readiness. A runtime module's defimpls
/// register during its definition, so a receiver type implying an unloaded
/// runtime module genuinely needs DefineModule — this is demand
/// bootstrapping, not a ModuleInterface stand-in.
fn wait_for_protocol_module(world: &mut World<'_>, protocol: ModuleId, waits: &mut HashSet<FactKey>) {
    if let Some(code_id) = world.ensure_runtime_module(protocol) {
        let indexed_fact = FactKey::CodeIndexed(code_id);
        if !world.has_fact(&indexed_fact) {
            waits.insert(indexed_fact);
        }
    }
    waits.insert(FactKey::ModuleDefined(protocol));
}

/// VERDICT (fz-rh2.17.5.9): body readiness. The caller holds a FunctionId
/// and needs its DEFINITION, which module scope publication produces; the
/// exported-callable surface (ModuleInterface) answers a different question
/// and is consumed where names resolve — body lowering — not here.
fn wait_for_unresolved_function_module(
    world: &mut World<'_>,
    function: FunctionId,
    waits: &mut HashSet<FactKey>,
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
    // This site needs the function's module DEFINED (its scope walked), not its
    // body published: a protocol callback has no body of its own, so pulling
    // `PublishFunctionSource` here would chase a source that never exists
    // (fz-f98.14.5). The wait names `ModuleDefined(module)` directly — its
    // producer arm is `Job::DefineModule`, which bootstraps a runtime
    // module's code (`World::ensure_runtime_module`) itself when it runs, so
    // this site does not need to call `demand_function_scope` for that side
    // effect. `demand_function_scope`'s `CodeScoped`/`ScopeCode` branch (for
    // `module.is_global()`) is unreachable from here: the early return above
    // already rules out a global module before this wait registers.
    waits.insert(FactKey::ModuleDefined(module));
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
            .find(|target| same_call_target(target, &observed_target))
        {
            merge_summary_input_vec(
                world,
                &mut current_target.surface_inputs,
                &observed_target.surface_inputs,
            );
            current_target.activation =
                merge_target_activation(world, current_target.activation.take(), observed_target.activation)?;
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

fn same_call_target(left: &CallTargetSummary, right: &CallTargetSummary) -> bool {
    left.callee == right.callee && left.activation == right.activation
}

fn merge_target_activation(
    _world: &mut World<'_>,
    current: Option<ActivationKey>,
    observed: Option<ActivationKey>,
) -> Result<Option<ActivationKey>, FatalError> {
    match (current, observed) {
        (Some(current), Some(observed)) => {
            if current.root != observed.root || current.function != observed.function {
                return Err(FatalError);
            }
            Ok(Some(current))
        }
        (None, None) => Ok(None),
        (Some(_), None) | (None, Some(_)) => Err(FatalError),
    }
}

/// Published call-edge summaries live on the semantic/artifact plane, not the
/// activation-key plane. They must preserve every shape the callsite can send,
/// so later materialization can see the full semantic call surface. Key
/// coarsening belongs in `ActivationInputs`, not in published call summaries.
fn merge_summary_input_vec(world: &mut World<'_>, current: &mut Vec<Ty>, observed: &[Ty]) {
    if current.len() < observed.len() {
        current.resize_with(observed.len(), || any_ty(world));
    }
    for (slot, next_ty) in observed.iter().copied().enumerate() {
        if current[slot] == next_ty {
            continue;
        }
        if world.types().is_equivalent(&current[slot], &next_ty) {
            continue;
        } else {
            current[slot] = world.types_mut().union(current[slot], next_ty);
        }
    }
}

fn refine_protocol_target_inputs(world: &mut World<'_>, input_types: &[Ty], receiver_ty: Ty, target_ty: Ty) -> Vec<Ty> {
    let mut refined = input_types.to_vec();
    if let Some(receiver) = refined.first_mut() {
        *receiver = world.types_mut().intersect(receiver_ty, target_ty);
    }
    refined
}

fn call_target_summary(
    callee: SelectedCallee,
    surface_inputs: Vec<Ty>,
    activation: Option<ActivationKey>,
    return_ty: Option<Ty>,
) -> CallTargetSummary {
    CallTargetSummary {
        callee,
        surface_inputs,
        activation,
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
                        GroundValue::Int(_) | GroundValue::Float(_) | GroundValue::Utf8Binary(_),
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
        Region::MapKeyPresent { key } => {
            // A map literal's sig is an open-record LOWER bound: "at least
            // these keys, with these value types" (`types/sigs.rs`'s
            // `MapSig` doc). So `source <: map({key: any})` is exactly the
            // proof that every value of `source` carries `key` — the same
            // shape-overlap/subtype pair `Region::Type` and `Region::TupleArity`
            // already use above, just phrased over one required field instead
            // of a whole type or arity. Reusing `intersect`/`is_subtype` here
            // (rather than the previous unconditional `true`) lets a
            // known-closed map (built from a literal `%{...}` at this
            // callsite) prune the impossible "key is absent" miss edge,
            // exactly as an atom literal already prunes its miss edge below.
            //
            // The prune only applies when the key resolves to a form the map
            // lattice can carry as a required field: an atom singleton. The
            // `nil` key resolves here — it is the atom `:nil`, so a `%{nil =>
            // ...}` pattern prunes its miss edge exactly like any other atom
            // key. `map_key` also accepts int/float/string map-pattern keys
            // (`dispatch_matrix/pattern.rs`), but the lattice erases numeric
            // literals to their kind (`Types::int_lit`/`as_int_singleton` is a
            // permanent stub) and has no singleton for float/string keys, so
            // `as_map_key` returns `None` for them. Absence of a resolvable
            // key is absence of proof: we cannot show the key is present, so
            // we must not prune either edge — falling back to the old
            // unconditional `true` keeps those (valid, working) programs
            // dispatching both ways.
            let key_ty = dispatch_const_ty(world, key);
            if let Some(map_key) = world.types().as_map_key(&key_ty) {
                let any = world.types_mut().any();
                let required = world.types_mut().map(&[(map_key, any)]);
                if is_match {
                    let overlap = world.types_mut().intersect(*source, required);
                    !world.types().is_empty(&overlap)
                } else {
                    !world.types().is_subtype(source, &required)
                }
            } else {
                true
            }
        }
        Region::Bitstring(_) => true,
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

/// Read one value's evidence. `None` means the path that defines it has
/// produced no evidence this round — the reader contributes nothing and is
/// re-run when the evidence lands. Absence never defaults to a type.
fn value_ty(values: &SemanticValues, value: ValueId) -> Option<Ty> {
    values.get(&value).copied()
}

fn literal_ty(world: &mut World<'_>, literal: &GroundValue) -> Ty {
    use crate::ground_value::BodyLiteral;
    match literal
        .as_body_literal()
        .expect("literal_ty only ever sees a lowered-body literal")
    {
        BodyLiteral::Int(value) => world.types_mut().int_lit(value),
        BodyLiteral::Float(bits) => world.types_mut().float_lit(f64::from_bits(bits)),
        BodyLiteral::Binary(_) => world.types_mut().str_t(),
        BodyLiteral::Atom(name) => world.types_mut().atom_lit(name),
        BodyLiteral::Bool(value) => world.types_mut().bool_lit(value),
        BodyLiteral::Nil => world.types_mut().nil(),
    }
}

fn comparison_ty(world: &mut World<'_>, value: &ComparisonValue) -> Ty {
    match value {
        ComparisonValue::Const(value) => dispatch_const_ty(world, value),
        ComparisonValue::Pinned(_) => any_ty(world),
    }
}

fn dispatch_const_ty(world: &mut World<'_>, value: &GroundValue) -> Ty {
    use crate::ground_value::DispatchShape;
    match value
        .as_dispatch_shape()
        .expect("dispatch_const_ty only ever sees a dispatch-matrix const")
    {
        DispatchShape::Int(value) => world.types_mut().int_lit(value),
        DispatchShape::Float(value) => world.types_mut().float_lit(f64::from_bits(value)),
        DispatchShape::Atom(name) => world.types_mut().atom_lit(name),
        DispatchShape::Bool(value) => world.types_mut().bool_lit(value),
        // The `nil` keyword is the atom `nil` in every position, expression
        // or pattern (Elixir parity: `is_nil(nil)` holds, `nil == []` does
        // not). `[]` is the empty list, but it never reaches this function:
        // `[]` patterns lower to `Region::List(ListRegion::Empty)` instead
        // (see `dispatch_matrix::pattern::append_list_pattern`), a
        // structurally distinct region with no `GroundValue` counterpart.
        DispatchShape::Nil => world.types_mut().nil(),
        DispatchShape::Utf8Binary(_) => world.types_mut().str_t(),
    }
}

fn list_ty(world: &mut World<'_>, values: &SemanticValues, items: &[ValueId], tail: Option<ValueId>) -> Option<Ty> {
    let mut elem_ty = none_ty(world);
    for item in items {
        let item_ty = value_ty(values, *item)?;
        elem_ty = if world.types().is_empty(&elem_ty) {
            item_ty
        } else {
            world.types_mut().union(elem_ty, item_ty)
        };
    }
    let list = match tail {
        Some(tail) => {
            let tail_ty = value_ty(values, tail)?;
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
    };
    Some(list)
}

fn map_ty(world: &mut World<'_>, values: &SemanticValues, entries: &[(LoweredMapKey, ValueId)]) -> Option<Ty> {
    let mut fields = BTreeMap::new();
    for (key, value) in entries {
        let Some(key) = lowered_map_key(world, values, key)? else {
            return Some(world.types_mut().map_top());
        };
        fields.insert(key, value_ty(values, *value)?);
    }
    Some(world.types_mut().map(&fields.into_iter().collect::<Vec<_>>()))
}

/// The map key at a lowered key position. Outer `None` = no evidence yet for
/// the key value (the reader contributes nothing this round); inner `None` =
/// evidence exists but the key is not a singleton. The key is the carried
/// compile-time constant when the source wrote a literal (keys are values),
/// falling back to the observed singleton type.
fn lowered_map_key(
    world: &mut World<'_>,
    values: &SemanticValues,
    key: &LoweredMapKey,
) -> Option<Option<super::super::types::MapKey>> {
    if let Some(literal) = &key.literal {
        return Some(literal_map_key(literal));
    }
    let key_ty = value_ty(values, key.value)?;
    Some(map_key_from_ty(world, key_ty))
}

fn struct_assertion_ty(
    world: &mut World<'_>,
    module: ModuleId,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Ty {
    // Honor the struct's declared field types (`@type t`) so a destructure
    // recovers them even after a value crossed a protocol boundary that erased
    // its concrete shape (fz-f98.8: an integer `Range` whose fields graduate to
    // `any` makes `current + step` an `any + any` the `+` overload widens to
    // `int | float`). The declared type is a fact, so wait on it like any other
    // (mirrors the `TypeDefined` wait-set in body/contract derivation): a struct
    // that declares `@type t` but whose definition has not settled defers here
    // rather than baking in the `any` default. Only a struct with no `@type`
    // declaration defaults its fields to `any`.
    let name = TypeName {
        module,
        name: "t".to_string(),
        arity: 0,
    };
    if world.type_decl(&name).is_some() {
        let fact = FactKey::TypeDefined(name);
        if world.has_fact(&fact) {
            reads.push(fact);
            if let Some(declared) = world.declared_struct_value_ty(module) {
                return declared;
            }
        } else {
            waits.insert(fact);
        }
    }
    // The field schema itself is fact-backed too: `module` is always a real
    // struct here (body lowering already fataled on `%Module{}` patterns
    // whose module has no `defstruct`), so `StructDefined(module)` is
    // guaranteed to publish eventually — waiting on it, unlike the impl-target
    // classification above, carries no deadlock risk.
    let struct_fact = FactKey::StructDefined(module);
    let field_names = match world.struct_def(module) {
        Some(def) => {
            reads.push(struct_fact);
            def.fields.clone()
        }
        None => {
            waits.insert(struct_fact);
            Vec::new()
        }
    };
    let any = world.types_mut().any();
    let field_tys = vec![any; field_names.len()];
    world.struct_module_value_ty(module, &field_names, &field_tys)
}

fn map_key_from_ty(world: &World<'_>, ty: Ty) -> Option<super::super::types::MapKey> {
    world.types().as_map_key(&ty)
}

fn literal_map_key(literal: &GroundValue) -> Option<super::super::types::MapKey> {
    use crate::ground_value::BodyLiteral;
    match literal
        .as_body_literal()
        .expect("literal_map_key only ever sees a lowered-body literal")
    {
        BodyLiteral::Int(value) => Some(super::super::types::MapKey::Int(value)),
        BodyLiteral::Atom(name) => Some(super::super::types::MapKey::Atom(name.to_string())),
        BodyLiteral::Float(_) | BodyLiteral::Binary(_) | BodyLiteral::Bool(_) | BodyLiteral::Nil => None,
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
/// those duplicates are the same fact. Dedup preserves first-occurrence
/// order (a round trip through `HashSet` would scramble it to a per-process
/// `RandomState` order): this list becomes a job's published reads/waits and
/// its `changed` outputs, and the scheduler drains `changed` facts off a
/// stack (`Scheduler::complete`'s `pending_changes.pop()`), so the order
/// facts appear in here decides the interleaving of the dependent jobs each
/// one wakes.
fn dedupe_facts(facts: Vec<FactKey>) -> Vec<FactKey> {
    let mut seen = HashSet::with_capacity(facts.len());
    facts.into_iter().filter(|fact| seen.insert(fact.clone())).collect()
}

fn any_ty(world: &mut World<'_>) -> Ty {
    world.types_mut().any()
}

fn none_ty(world: &mut World<'_>) -> Ty {
    world.types_mut().none()
}

#[cfg(test)]
mod dispatch_const_ty_tests {
    use super::*;
    use crate::ground_value::MapKey;
    use crate::telemetry::ConfiguredTelemetry;

    /// The `nil` keyword types as the atom `nil` in both expression and
    /// pattern position; `[]` types as the empty list; the two are
    /// distinct. This pins the fix for the divergence where pattern
    /// position used to type `nil` as `empty_list()` while expression
    /// position (`literal_ty`, `BodyLiteral::Nil`) already typed it as the
    /// atom -- same keyword, same `GroundValue::Nil` payload, one `Ty`.
    #[test]
    fn nil_keyword_types_as_the_atom_in_pattern_position_not_the_empty_list() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);

        let nil_pattern_ty = dispatch_const_ty(&mut world, &GroundValue::Nil);
        let nil_expr_ty = world.types_mut().nil();
        let empty_list_ty = world.types_mut().empty_list();

        assert_eq!(
            world.types_mut().display(&nil_pattern_ty),
            world.types_mut().display(&nil_expr_ty),
            "the `nil` keyword should type the same way (the atom nil) in pattern position as it does in expression position",
        );
        assert_ne!(
            world.types_mut().display(&nil_pattern_ty),
            world.types_mut().display(&empty_list_ty),
            "the `nil` keyword must not type as the empty list -- `nil` and `[]` are distinct values with distinct types",
        );

        // `[]` never reaches `dispatch_const_ty` at all: `GroundValue` has
        // no empty-list variant, so `[]` patterns lower to
        // `Region::List(ListRegion::Empty)` instead (see
        // `dispatch_matrix::pattern::append_list_pattern`). The distinction
        // pinned above holds by construction -- there is no `GroundValue`
        // an empty-list pattern could ever be confused with `Nil` through.
    }

    /// Because `nil` now types as the atom `:nil`, a `nil` map-pattern key
    /// resolves to a `MapKey::Atom` singleton -- so `%{nil => ...}` prunes
    /// its present/absent miss edge in the `Region::MapKeyPresent` proof
    /// exactly like any other atom key. Before the fix, `nil` typed as the
    /// empty list, `as_map_key` returned `None`, and the proof fell back to
    /// the unconditional "cannot prune". This pins the resolvable-key path
    /// that the type change unlocked so it is not silently untested.
    #[test]
    fn nil_map_pattern_key_resolves_to_the_nil_atom_singleton() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);

        let nil_key_ty = dispatch_const_ty(&mut world, &GroundValue::Nil);
        let resolved = world.types().as_map_key(&nil_key_ty);

        assert_eq!(
            resolved,
            Some(MapKey::Atom("nil".to_string())),
            "a `nil` map-pattern key should resolve to the `:nil` atom singleton so `MapKeyPresent` can prune its miss edge",
        );
    }
}
