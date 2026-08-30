//! Compiler2 semantic-analysis jobs.
//!
//! This module walks lowered function bodies through already-planned entry
//! dispatch, derives direct-call summaries, and settles per-activation return
//! types without calling the legacy whole-program pipeline.

use std::collections::{BTreeMap, HashMap, HashSet, hash_map::Entry};

use crate::ast::{BinOp, UnOp};
use crate::diag::driver::emit_through;
use crate::diag::{Diagnostic, codes};
use crate::ground_value::GroundValue;
use crate::source::Span;

use super::super::body::{
    CallSiteId, ControlDestination, LoweredBody, LoweredClause, LoweredEntry, LoweredMapKey, LoweredStep, LoweredTail,
    ValueId,
};
use super::super::contract::FunctionContract;
use super::super::dispatch_reachability::calculate_dispatch_reachability;
use super::super::drive::{FactKey, Job, JobEffects, current_uses};
use super::super::identity::{
    ActivationKey, ExecutableNeed, FunctionId, ModuleId, TypeName, function_id_of_closure_target,
};
use super::super::protocol::ProtocolCallbackImpl;
use super::super::scheduler::FatalError;
use super::super::semantic::{
    ActivationAnalysis, CallSiteKey, CallSiteResolution, CallSiteSummary, CallSiteTargets, CallTargetSummary,
    SelectedCallee,
};
use super::super::types::{ClosureTarget, Ty, Types};
use super::super::world::World;

type SemanticValues = HashMap<ValueId, Ty>;
type ValueTypes = HashMap<ValueId, Ty>;
type RefinedCallSurface = (Vec<Ty>, Option<Ty>);
/// One reached call: what it resolved to, and its return evidence. The
/// activation demand is not a third element -- it IS the resolution
/// (`CallSiteSummary::demanded_activations`).
type ResolvedCall = (CallSiteResolution<CallSiteSummary>, Option<Ty>);

/// A call the walk REACHED. It exists for every live call on a reached path;
/// a call proven dead never happens and so has no emission at all.
#[derive(Debug, Clone)]
struct CallEmission {
    key: CallSiteKey,
    resolution: CallSiteResolution<CallSiteSummary>,
    latent_executables: Vec<super::super::identity::ExecutableKey>,
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
pub(super) fn analyze_activation(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    activation: &ActivationKey,
) -> Result<JobEffects, FatalError> {
    let activation_fact = FactKey::Activation(activation.clone());
    if !world.has_fact(&activation_fact) {
        // Nothing claims this activation -- no caller has reached it yet, or
        // every caller has withdrawn it. That is an answer, not a block: a
        // wait here would have no producer (`World::seed_activation_producer`
        // refuses a key whose inputs anything else supplies), and a wedged
        // waiter stalls retraction-heavy drives. The conclusion re-lists the
        // job's standing claims AND the reads standing behind them: claims
        // keep the subscriptions that derived them, so the parked cone stays
        // exactly as final as its ground -- never settled from amnesia (the
        // one-absent-read conclusion was measured to do exactly that). The
        // `Activation` read wakes this job on a first or later claim; the
        // full cone retires in fz-kdt.69's decommission conclusion, with its
        // `ActivationSlot` reset.
        let (outputs, standing_reads) = world.standing_claims_and_reads(&Job::AnalyzeActivation(activation.clone()));
        // Order is immaterial: JobEffects.reads lands in the ledger's read
        // SET; nothing observes this Vec's sequence.
        let mut reads: Vec<_> = standing_reads.into_iter().collect();
        reads.extend(current_uses([activation_fact]));
        return Ok(JobEffects {
            reads,
            outputs,
            ..JobEffects::default()
        });
    }
    // One gate, not two. Demand is DERIVED, so every publisher of
    // `Activation(k)` publishes `ActivationInputs(k)` from the same derivation
    // in the same completion -- the fold emits both from one demand set, and
    // the two seed jobs list both. The separate `ActivationInputs` wait that
    // used to stand here could therefore never fire, and never did: measured
    // zero across the target fixtures, the 574-fixture corpus and
    // `cargo test --lib` (fz-kdt.69.1's sweep) before it was collapsed.
    let alternatives = world
        .activation_input_alternatives(activation)
        .expect("Activation and ActivationInputs are one derivation's two claims")
        .clone();

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
    // Each correlated row is dispatched and analyzed on its own
    // (fz-9i4.7.10.2): a row's columns arrived together and only ever bind a
    // clause together. Only post-analysis results merge — reachable clauses
    // by set union, failure by OR, return evidence by join, call emissions by
    // coalescing. No column of one row ever meets a column of another.
    let mut reachable_clauses = Vec::new();
    let mut fail_reachable = false;
    let mut row_clause_inputs = Vec::new();
    for row in alternatives.rows() {
        let dispatch_reachability = calculate_dispatch_reachability(world.types_mut(), &entry_dispatch, row.columns());
        fail_reachable |= dispatch_reachability.fail_reachable;
        let clause_inputs = dispatch_reachability
            .outcome_inputs
            .iter()
            .cloned()
            .filter_map(|(outcome, inputs)| entry_dispatch.outcome(outcome).map(|outcome| (outcome.body_id, inputs)))
            .collect::<Vec<_>>();
        for (clause, _) in &clause_inputs {
            if !reachable_clauses.contains(clause) {
                reachable_clauses.push(*clause);
            }
        }
        row_clause_inputs.push(clause_inputs);
    }
    let entry_reachability = super::super::semantic::EntryReachability::new(reachable_clauses, fail_reachable);

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
            for (clause_id, clause_inputs) in row_clause_inputs.iter().flatten() {
                let clause = &clauses[*clause_id as usize];
                // Input evidence that has not caught up to the clause's
                // arity cannot bind its params. Like an absent capture,
                // incomplete evidence yields no evidence — the analysis
                // re-runs when the joined inputs grow. Never `any`.
                if clause.params.len() > clause_inputs.len() {
                    continue;
                }
                let mut values = HashMap::new();
                for (value, ty) in clause.params.iter().copied().zip(clause_inputs.iter().cloned()) {
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
                    tel,
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

    for row in alternatives.rows() {
        if let Some(contract_return_ty) =
            activation_contract_return(world, tel, function, row.columns(), &mut reads, &mut waits)?
        {
            return_evidence = refine_call_return(world, return_evidence, Some(contract_return_ty));
        }
    }

    // Waits no longer bail: a waiting completion extends the job's standing
    // claims (it cannot retract), so partial evidence publishes safely and
    // the waits simply ride the final effects.
    analysis_calls = coalesce_call_emissions(world, tel, activation, analysis_calls, &mut reads, &mut waits)?;

    let mut emitted_executables = HashSet::new();
    for call in &analysis_calls {
        // EVERY reached callsite publishes its edge, resolved or not: the
        // unresolved answer is a value, so the analysis's silence about a
        // callsite means the walk no longer reaches it and nothing here needs
        // preserving (fz-kdt.69.2).
        let callsite_fact = FactKey::CallSiteSummary(call.key.clone());
        let callsite_changed = super::super::drive::ExecutionContext::new(world, tel)
            .define_callsite_summary(call.key.clone(), call.resolution.clone());
        outputs.push(callsite_fact.clone());
        if callsite_changed {
            changed.push(callsite_fact);
        }
        let targets_fact = FactKey::CallSiteTargets(call.key.clone());
        let targets_changed = world.define_callsite_targets(call.key.clone(), CallSiteTargets::of(&call.resolution));
        outputs.push(targets_fact.clone());
        if targets_changed {
            changed.push(targets_fact);
        }
        // No `Activation`/`ActivationInputs` push here, and no wait+push
        // pair either. The callee demand this analysis states IS the edge
        // just published: `World::complete_job` folds every live edge's
        // `CallSiteSummary::demanded_activations` into this job's
        // `Activation`/`ActivationInputs` claims and its input rows, and into
        // the demand index that ignites the callee's own first analysis when
        // the agenda drains. `prepare_function_call` only `reads` the
        // callee's `ReturnType` (so mutual recursion cannot deadlock), so
        // nothing ever blocks on the callee's analysis itself.
        for executable in &call.latent_executables {
            if emitted_executables.insert(executable.clone()) {
                outputs.push(FactKey::Executable(executable.clone()));
            }
        }
    }

    let return_changed =
        super::super::drive::ExecutionContext::new(world, tel).define_activation_return(activation, return_evidence);
    let return_fact = FactKey::ReturnType(activation.clone());
    outputs.push(return_fact.clone());
    if return_changed {
        changed.push(return_fact);
    }

    let analysis_changed = super::super::drive::ExecutionContext::new(world, tel).define_activation_analysis(
        activation,
        ActivationAnalysis {
            entry_reachability,
            reachable_entries: {
                let mut entries = reachable_entries.into_iter().collect::<Vec<_>>();
                entries.sort_by_key(|entry| entry.as_u32());
                entries
            },
            // The callsites this analysis RESOLVED. An unresolved edge names
            // no targets, so the products keyed off this list -- materialized
            // call edges, runtime demand, the canonical call-edge snapshot --
            // see exactly what they always saw.
            callsites: analysis_calls
                .iter()
                .filter_map(|call| call.resolution.resolved().map(|_| call.key.callsite))
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
        ..JobEffects::default()
    })
}

fn analyze_entry(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
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
        tel,
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
    world: &mut World,
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
    world: &mut World,
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
fn join_evidence(world: &mut World, a: Option<Ty>, b: Option<Ty>) -> Option<Ty> {
    match (a, b) {
        (None, x) | (x, None) => x,
        (Some(a), Some(b)) if a == b => Some(a),
        (Some(a), Some(b)) => Some(world.types_mut().union(a, b)),
    }
}

/// Analyze one entry reached as a plain branch (no delivered value).
#[allow(clippy::too_many_arguments)]
fn analyze_branch(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
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
        tel,
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
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
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
            tel,
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
                calls.push(reached_but_unresolved(activation, *callsite));
                return Ok(None);
            };
            let (emission, return_ty) =
                resolve_direct_call(world, tel, activation, *callsite, *callee, arg_types, reads, waits)?;
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
                tel,
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
                calls.push(reached_but_unresolved(activation, *callsite));
                return Ok(None);
            };
            let (emission, return_ty) =
                resolve_closure_call(world, tel, activation, *callsite, callee_ty, arg_types, reads, waits)?;
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
                tel,
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
                tel,
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
                tel,
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
            let reachability = calculate_dispatch_reachability(world.types_mut(), &dispatch.plan, &input_tys);
            let mut merged = None;
            for (outcome, refined_inputs) in reachability.outcome_inputs {
                let body_id = dispatch
                    .plan
                    .outcomes
                    .iter()
                    .find(|candidate| candidate.outcome == outcome)
                    .expect("reachable dispatch outcome should have an arm")
                    .body_id;
                let arm_entry = *dispatch
                    .arm_entries
                    .get(body_id as usize)
                    .unwrap_or_else(|| panic!("compiler2 local dispatch arm {} is out of bounds", body_id));
                let mut refined_values = values.clone();
                for (input, ty) in inputs.iter().copied().zip(refined_inputs) {
                    refined_values.insert(input, ty);
                }
                let arm_ty = analyze_branch(
                    world,
                    tel,
                    entries,
                    arm_entry,
                    &refined_values,
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
                tel,
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
                    tel,
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
                    tel,
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
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
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
        if std::env::var_os("FZ_WALK_FIX").is_some()
            && let ControlDestination::Deliver(entry_id) = dest
        {
            let scope = entry_scope(entries, *entry_id, values, None, &[]);
            analyze_entry(
                world, tel, entries, *entry_id, &scope, reachable_entries, value_types, calls, activation, reads,
                waits,
            )?;
        }
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
                tel,
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

/// The walk reached this callsite and could not even build its call: an
/// operand on the path has no evidence yet. The edge still publishes — that
/// is the law that lets an omitted edge mean "no longer reached".
fn reached_but_unresolved(activation: &ActivationKey, callsite: CallSiteId) -> CallEmission {
    CallEmission {
        key: CallSiteKey {
            activation: activation.clone(),
            callsite,
        },
        resolution: CallSiteResolution::Unresolved,
        latent_executables: Vec::new(),
    }
}

fn resolve_direct_call(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    caller: &ActivationKey,
    callsite: CallSiteId,
    function: FunctionId,
    arg_types: Vec<Ty>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<(Option<CallEmission>, Option<Ty>), FatalError> {
    // A proven-empty argument type is a real fact: no value can reach this
    // call, the path is dead. (Absence cannot arrive here — an unresolved
    // upstream call already short-circuited the path.) A call that never
    // happens is no edge, so it publishes nothing: that is the one thing the
    // fact's absence still says (fz-kdt.69.2).
    if arg_types.iter().any(|arg| world.types().is_empty(arg)) {
        return Ok((None, Some(none_ty(world))));
    }

    let (resolution, return_ty) =
        resolve_function_call(world, tel, caller, function, arg_types, callsite.span(), reads, waits)?;
    Ok((
        Some(CallEmission {
            key: CallSiteKey {
                activation: caller.clone(),
                callsite,
            },
            resolution,
            latent_executables: Vec::new(),
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
fn merge_value_types(world: &mut World, merged: &mut ValueTypes, observed: &SemanticValues) {
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
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
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

    let mut pre_coalesce: HashMap<CallSiteKey, HashSet<(ActivationKey, Vec<Ty>)>> = HashMap::new();
    if std::env::var_os("FZ_PROBE").is_some() {
        for (key, grouped) in &grouped {
            if let Some(summary) = grouped.call.resolution.resolved() {
                for (a, i) in summary.demanded_activations() {
                    pre_coalesce.entry(key.clone()).or_default().insert((a.clone(), i.to_vec()));
                }
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
            tel,
            caller,
            grouped.call,
            reads,
            waits,
        )?);
    }
    if std::env::var_os("FZ_PROBE").is_some() {
        for call in &coalesced {
            let after: HashSet<(ActivationKey, Vec<Ty>)> = call
                .resolution
                .resolved()
                .map(|s| s.demanded_activations().map(|(a, i)| (a.clone(), i.to_vec())).collect())
                .unwrap_or_default();
            let before = pre_coalesce.remove(&call.key).unwrap_or_default();
            let lost_keys: HashSet<_> = before
                .iter()
                .map(|(a, _)| a.clone())
                .filter(|a| !after.iter().any(|(b, _)| b == a))
                .collect();
            let lost_rows = before.difference(&after).count();
            if !lost_keys.is_empty() {
                eprintln!("FZPROBE coalesce-lost-keys n={}", lost_keys.len());
            }
            if lost_rows > 0 {
                eprintln!("FZPROBE coalesce-lost-rows n={lost_rows}");
            }
        }
    }
    Ok(coalesced)
}

/// One callsite reached down several rows or arms is ONE edge. The
/// resolutions join on the same lattice the store uses: `Unresolved` is
/// bottom, so an arm that resolved nothing never erases an arm that did.
fn merge_call_emission(
    world: &mut World,
    current: &mut CallEmission,
    observed: CallEmission,
) -> Result<(), FatalError> {
    match (&mut current.resolution, observed.resolution) {
        (CallSiteResolution::Resolved(current_summary), CallSiteResolution::Resolved(observed_summary)) => {
            merge_call_targets(world, &mut current_summary.targets, observed_summary.targets)?;
            current_summary.return_ty = join_evidence(world, current_summary.return_ty, observed_summary.return_ty);
        }
        (CallSiteResolution::Unresolved, observed @ CallSiteResolution::Resolved(_)) => {
            current.resolution = observed;
        }
        (_, CallSiteResolution::Unresolved) => {}
    }
    current.latent_executables.extend(observed.latent_executables);
    Ok(())
}

fn rebuild_coalesced_call_emission(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    caller: &ActivationKey,
    call: CallEmission,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<CallEmission, FatalError> {
    let CallSiteResolution::Resolved(summary) = &call.resolution else {
        return Ok(call);
    };
    let mut rebuilt_targets = Vec::new();
    let mut rebuilt_return = None;
    let mut rebuilt_latent = Vec::new();

    for target in &summary.targets {
        match target.callee.clone() {
            SelectedCallee::Function(function) => {
                // `surface_inputs` is the declared call surface only -- a
                // closure target's real activation carries a leading
                // capture-environment prefix that `surface_inputs` never
                // names. Rebuilding from `surface_inputs` alone silently
                // drops that prefix and hands `call_emission_for_function`
                // an under-arity input vector, which mints a truncated
                // activation. The prefix is EVIDENCE, and the target already
                // recorded its full evidence vector in `activation_inputs` --
                // the kept activation's KEY is not a substitute, because a
                // convergence-collapsed key names a capture slot by an
                // address var, and rebuilding from the key would publish
                // key-language vars as activation-input evidence (fz-6gb).
                // Every `Function` target records its evidence vector when it
                // is built; a target without one has nothing to rebuild FROM,
                // so keep the settled emission rather than minting an
                // under-arity activation from surface inputs alone.
                let Some(mut input_types) = target.activation_inputs.clone() else {
                    return Ok(call);
                };
                let captures_len = input_types.len().saturating_sub(target.surface_inputs.len());
                input_types.truncate(captures_len);
                input_types.extend(target.surface_inputs.iter().copied());
                let Some(rebuilt) = call_emission_for_function(
                    world,
                    tel,
                    caller,
                    call.key.clone(),
                    function,
                    input_types,
                    reads,
                    waits,
                )?
                else {
                    return Ok(call);
                };
                let CallSiteResolution::Resolved(rebuilt_summary) = rebuilt.resolution else {
                    return Ok(call);
                };
                for mut rebuilt_target in rebuilt_summary.targets {
                    if captures_len > 0 {
                        rebuilt_target.surface_inputs.drain(..captures_len);
                    }
                    rebuilt_return = join_evidence(world, rebuilt_return, rebuilt_target.return_ty);
                    merge_call_targets(world, &mut rebuilt_targets, vec![rebuilt_target])?;
                }
                rebuilt_latent.extend(rebuilt.latent_executables);
            }
            SelectedCallee::ProviderBoundary(_) => {
                rebuilt_return = join_evidence(world, rebuilt_return, target.return_ty);
                rebuilt_targets.push(target.clone());
            }
        }
    }

    rebuilt_latent.extend(call.latent_executables);
    Ok(CallEmission {
        key: call.key,
        resolution: CallSiteResolution::Resolved(CallSiteSummary {
            targets: rebuilt_targets,
            return_ty: rebuilt_return,
        }),
        latent_executables: rebuilt_latent,
    })
}

fn call_emission_for_function(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    caller: &ActivationKey,
    key: CallSiteKey,
    function: FunctionId,
    input_types: Vec<Ty>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<Option<CallEmission>, FatalError> {
    let Some((input_types, contract_return_ty)) =
        refine_function_call_surface(world, tel, function, input_types, key.callsite.span(), reads, waits)?
    else {
        return Ok(None);
    };
    if world.function_is_provider_boundary(function) {
        // The earned dynamic edge: a boundary with no contract is `any`.
        let return_ty = Some(contract_return_ty.unwrap_or_else(|| any_ty(world)));
        return Ok(Some(CallEmission {
            key,
            resolution: CallSiteResolution::Resolved(CallSiteSummary {
                targets: vec![CallTargetSummary {
                    callee: SelectedCallee::ProviderBoundary(function),
                    surface_inputs: input_types,
                    activation: None,
                    activation_inputs: None,
                    return_ty,
                }],
                return_ty,
            }),
            latent_executables: Vec::new(),
        }));
    }
    let Some((activation, return_ty)) = prepare_function_call(world, caller, function, &input_types, reads, waits)
    else {
        return Ok(None);
    };
    let return_ty = refine_call_return(world, return_ty, contract_return_ty);
    Ok(Some(CallEmission {
        key,
        resolution: CallSiteResolution::Resolved(CallSiteSummary {
            targets: vec![CallTargetSummary {
                callee: SelectedCallee::Function(function),
                surface_inputs: input_types.clone(),
                activation: Some(activation),
                activation_inputs: Some(input_types),
                return_ty,
            }],
            return_ty,
        }),
        latent_executables: Vec::new(),
    }))
}

fn resolve_function_call(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
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
            tel,
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
        return Ok((CallSiteResolution::Unresolved, None));
    }
    let Some((input_types, contract_return_ty)) =
        refine_function_call_surface(world, tel, function, input_types, call_span, reads, waits)?
    else {
        return Ok((CallSiteResolution::Unresolved, None));
    };
    if world.function_is_provider_boundary(function) {
        // The provider boundary is the public dynamic edge: `any` is earned
        // here (and only here and at unresolvable callable values).
        let return_ty = contract_return_ty.unwrap_or_else(|| any_ty(world));
        return Ok((
            CallSiteResolution::Resolved(CallSiteSummary {
                targets: vec![call_target_summary(
                    SelectedCallee::ProviderBoundary(function),
                    input_types,
                    None,
                    None,
                    Some(return_ty),
                )],
                return_ty: Some(return_ty),
            }),
            Some(return_ty),
        ));
    }
    let Some((activation, return_evidence)) =
        prepare_function_call(world, caller, function, &input_types, reads, waits)
    else {
        return Ok((CallSiteResolution::Unresolved, None));
    };
    let return_ty = refine_call_return(world, return_evidence, contract_return_ty);
    Ok((
        CallSiteResolution::Resolved(CallSiteSummary {
            targets: vec![CallTargetSummary {
                callee: SelectedCallee::Function(function),
                surface_inputs: input_types.clone(),
                activation: Some(activation),
                activation_inputs: Some(input_types),
                return_ty,
            }],
            return_ty,
        }),
        return_ty,
    ))
}

fn resolve_protocol_call(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
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
        wait_for_protocol_module(world, tel, protocol, waits);
        return Ok((CallSiteResolution::Unresolved, None));
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
        return Ok((CallSiteResolution::Unresolved, None));
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
        return Ok((CallSiteResolution::Unresolved, None));
    }

    let matches = merge_protocol_matches_by_function(world, matches);
    let mut targets = Vec::new();
    let mut return_ty = None;
    for (selected, overlap) in matches {
        // VERDICT (fz-rh2.17.5.9): the old ModuleDefined(owner_module) wait
        // here was over-waiting — holding a ProtocolCallbackImpl proves the
        // impl fragment already published its function, and re-serializing
        // every protocol call behind whole-module scoping is readiness the
        // call does not require. Gate per FUNCTION, exactly as the
        // direct-call path does.
        if wait_for_unresolved_function_module(world, selected.function, waits) {
            return Ok((CallSiteResolution::Unresolved, None));
        }

        let refined_inputs = refine_protocol_target_inputs(world, &input_types, receiver_ty, overlap);
        let Some((refined_inputs, contract_return_ty)) =
            refine_function_call_surface(world, tel, selected.function, refined_inputs, call_span, reads, waits)?
        else {
            return Ok((CallSiteResolution::Unresolved, None));
        };
        let Some((activation, observed_return)) =
            prepare_function_call(world, caller, selected.function, &refined_inputs, reads, waits)
        else {
            return Ok((CallSiteResolution::Unresolved, None));
        };
        let target_return = refine_call_return(world, observed_return, contract_return_ty);
        return_ty = join_evidence(world, return_ty, target_return);
        targets.push(call_target_summary(
            SelectedCallee::Function(selected.function),
            refined_inputs.clone(),
            Some(activation),
            Some(refined_inputs),
            target_return,
        ));
    }
    Ok((
        CallSiteResolution::Resolved(CallSiteSummary { targets, return_ty }),
        return_ty,
    ))
}

fn protocol_receiver_target_overlaps(world: &mut World, receiver_ty: Ty, target_ty: Ty) -> bool {
    let receiver = world.types().runtime_type_predicate(&receiver_ty);
    let target = world.types().runtime_type_predicate(&target_ty);
    receiver.overlaps(&target) && {
        let overlap = world.types_mut().intersect(receiver_ty, target_ty);
        !world.types().is_empty(&overlap)
    }
}

fn merge_protocol_matches_by_function(
    world: &mut World,
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

/// Can any runtime value arrive in this callee slot at all?
///
/// Two shapes say no, for one reason: nothing inhabits them. The proven-empty
/// type has no members by definition. A *value template* — a bare type variable
/// — has no runtime representation, so an activation keyed with one at a callee
/// slot is a specialization for an argument no caller can ever supply
/// (fz-hwn.23). Either way the call cannot happen, and the Kleene reading of a
/// call that never happens is the empty type: evidence, not absence.
///
/// The distinction from [`callee_is_a_dynamic_edge`] is inhabitation, not
/// groundness. A callable that merely *carries* variables — `(int) -> a` — is a
/// perfectly representable value (a pointer); its analysis is simply pending,
/// which is absence. Only a bare variable is uninhabitable (fz-f98.18).
fn callee_has_no_inhabitants(types: &Types, callee_ty: Ty) -> bool {
    types.is_empty(&callee_ty) || types.is_value_template(&callee_ty)
}

/// Is an unresolved callee a genuine dynamic edge — the one place a closure
/// call may EARN `any`?
///
/// Only when its type is GROUND. A ground callable the engine cannot resolve to
/// closure targets really could be anything at runtime, exactly as at a provider
/// boundary. A callee whose type still carries type VARIABLES is a different
/// thing entirely: the slot has not been instantiated yet, so the call has no
/// evidence, precisely like a named target whose analysis is still pending.
///
/// The distinction is load-bearing because the value-type join is cumulative.
/// `any` unioned in from a not-yet-instantiated slot is never retracted once the
/// slot grounds, so the callsite ends up holding two disagreeing facts — a
/// precisely-resolved `CallSiteSummary` and an `any` value type (fz-f98.17).
fn callee_is_a_dynamic_edge(world: &World, callee_ty: Ty) -> bool {
    !world.types().has_vars(&callee_ty)
}

fn resolve_closure_call(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    caller: &ActivationKey,
    callsite: CallSiteId,
    callee_ty: Ty,
    arg_types: Vec<Ty>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<(Option<CallEmission>, Option<Ty>), FatalError> {
    let key = CallSiteKey {
        activation: caller.clone(),
        callsite,
    };
    if callee_has_no_inhabitants(world.types(), callee_ty) || arg_types.iter().any(|arg| world.types().is_empty(arg)) {
        // Uninhabitable callee or proven-empty argument: the call site is dead.
        // This is evidence (the empty type), not absence — absence
        // short-circuits upstream before any argument reaches a call. A call
        // that never happens is no edge, so it publishes nothing: that is the
        // one thing the fact's absence still says (fz-kdt.69.2).
        return Ok((None, Some(none_ty(world))));
    }
    let unresolved = |return_ty| {
        Ok((
            Some(CallEmission {
                key: key.clone(),
                resolution: CallSiteResolution::Unresolved,
                latent_executables: Vec::new(),
            }),
            return_ty,
        ))
    };
    let Some(clauses) = world.types_mut().callable_value_clauses(&callee_ty) else {
        if !callee_is_a_dynamic_edge(world, callee_ty) {
            return unresolved(None);
        }
        return unresolved(Some(any_ty(world)));
    };
    let mut selected_targets = Vec::new();
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
        let (resolution, observed_return) =
            resolve_function_call(world, tel, caller, function, inputs, callsite.span(), reads, waits)?;

        if let CallSiteResolution::Resolved(summary) = resolution {
            for target in summary.targets {
                let target_return = refine_call_return(world, target.return_ty, Some(clause.ret));
                return_ty = join_evidence(world, return_ty, target_return);
                let rebuilt_target = call_target_summary(
                    target.callee,
                    refined_args.clone(),
                    target.activation,
                    target.activation_inputs,
                    target_return,
                );
                if !selected_targets.contains(&rebuilt_target) {
                    selected_targets.push(rebuilt_target);
                }
            }
        } else {
            let clause_return = refine_call_return(world, observed_return, Some(clause.ret));
            return_ty = join_evidence(world, return_ty, clause_return);
        }
    }

    if selected_targets.is_empty() {
        // Two ways to reach here without a target, and both are absence of
        // evidence: a matching closure clause named a concrete target whose
        // analysis is still pending, or the callee is not known yet at all.
        // Report the evidence gathered so far and let the `reads`/`waits`
        // registered above re-wake this call; only a genuine dynamic edge
        // earns `any`.
        if named_concrete_target || !callee_is_a_dynamic_edge(world, callee_ty) {
            return unresolved(return_ty);
        }
        return unresolved(Some(any_ty(world)));
    };
    Ok((
        Some(CallEmission {
            key,
            resolution: CallSiteResolution::Resolved(CallSiteSummary {
                targets: selected_targets,
                return_ty,
            }),
            latent_executables,
        }),
        return_ty,
    ))
}

fn refine_function_call_surface(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
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
        tel,
        function,
        &contract,
        input_types,
        violation_span,
    )?))
}

fn apply_function_contract(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
    contract: &FunctionContract,
    input_types: Vec<Ty>,
    violation_span: Span,
) -> Result<(Vec<Ty>, Option<Ty>), FatalError> {
    let application = contract.apply(world.types_mut(), &input_types);
    if !application.enforceable_satisfied
        && function_contract_is_enforced(world, function, violation_span)
        && spec_violation_is_actionable(world, &input_types)
    {
        return Err(emit_spec_violation(tel, world, function, &input_types, violation_span));
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

/// A spec violation is enforced (fatal) only at USER callsites. Calls written
/// inside library code are validated for refinement but never diagnosed:
/// shared library bodies currently carry JOINED activation evidence — one
/// evidence row unioned across uncorrelated users — so a callsite there can
/// observe a phantom argument combination no runtime call makes (one user's
/// callable paired with another user's element type). The matcher verdict on
/// that row is correct, but as a diagnostic it is false, and its span points
/// into library source where the user can act on nothing. The gate retires
/// when activation evidence becomes correlation-sound. The violation span is
/// the callsite, so its source identifies the calling side.
fn function_contract_is_enforced(world: &World, function: FunctionId, violation_span: Span) -> bool {
    let (_source, surface) = world.function_definition(function);
    surface.extern_abi.is_none() && !world.is_bootstrap(super::super::CodeId::from_source(violation_span.code_id))
}

fn spec_violation_is_actionable(world: &mut World, input_types: &[Ty]) -> bool {
    let any = world.types_mut().any();
    input_types
        .iter()
        .all(|ty| !world.types().has_vars(ty) && !world.types().is_equivalent(ty, &any))
}

fn activation_contract_return(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
    input_types: &[Ty],
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
) -> Result<Option<Ty>, FatalError> {
    let violation_span = world.function_surface(function).span;
    let Some((_, contract_return_ty)) =
        refine_function_call_surface(world, tel, function, input_types.to_vec(), violation_span, reads, waits)?
    else {
        return Ok(None);
    };
    Ok(contract_return_ty)
}

fn emit_spec_violation(
    tel: &impl crate::telemetry::Telemetry,
    world: &World,
    function: FunctionId,
    input_types: &[Ty],
    span: Span,
) -> FatalError {
    let function_ref = world.function_ref(function);
    let observed = input_types
        .iter()
        .map(|ty| world.types().display_for_diag(ty))
        .collect::<Vec<_>>()
        .join(", ");
    emit_through(
        tel,
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

fn refine_contract_inputs<'a>(world: &mut World, observed: Vec<Ty>, arrows: impl Iterator<Item = &'a [Ty]>) -> Vec<Ty> {
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

fn refine_call_return(world: &mut World, observed: Option<Ty>, contract: Option<Ty>) -> Option<Ty> {
    let Some(observed) = observed else {
        // No body evidence yet: a contract bounds the eventual value but
        // does not witness that the call returns at all. Nothing is
        // manufactured from absence.
        return None;
    };
    Some(refine_observed_return(world, observed, contract))
}

fn refine_observed_return(world: &mut World, observed: Ty, contract: Option<Ty>) -> Ty {
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
    world: &mut World,
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
fn wait_for_protocol_module(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    protocol: ModuleId,
    waits: &mut HashSet<FactKey>,
) {
    if let Some(code_id) = super::super::drive::ExecutionContext::new(world, tel).ensure_runtime_module(protocol) {
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
fn wait_for_unresolved_function_module(world: &mut World, function: FunctionId, waits: &mut HashSet<FactKey>) -> bool {
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
    world: &mut World,
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
            merge_optional_summary_input_vec(
                world,
                &mut current_target.activation_inputs,
                observed_target.activation_inputs.as_deref(),
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
    _world: &mut World,
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
fn merge_summary_input_vec(world: &mut World, current: &mut Vec<Ty>, observed: &[Ty]) {
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

fn merge_optional_summary_input_vec(world: &mut World, current: &mut Option<Vec<Ty>>, observed: Option<&[Ty]>) {
    match (current, observed) {
        (Some(current), Some(observed)) => merge_summary_input_vec(world, current, observed),
        (current @ None, Some(observed)) => *current = Some(observed.to_vec()),
        _ => {}
    }
}

fn refine_protocol_target_inputs(world: &mut World, input_types: &[Ty], receiver_ty: Ty, target_ty: Ty) -> Vec<Ty> {
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
    activation_inputs: Option<Vec<Ty>>,
    return_ty: Option<Ty>,
) -> CallTargetSummary {
    CallTargetSummary {
        callee,
        surface_inputs,
        activation,
        activation_inputs,
        return_ty,
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

fn literal_ty(world: &mut World, literal: &GroundValue) -> Ty {
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

fn list_ty(world: &mut World, values: &SemanticValues, items: &[ValueId], tail: Option<ValueId>) -> Option<Ty> {
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

fn map_ty(world: &mut World, values: &SemanticValues, entries: &[(LoweredMapKey, ValueId)]) -> Option<Ty> {
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
    world: &mut World,
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
    world: &mut World,
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

fn map_key_from_ty(world: &World, ty: Ty) -> Option<super::super::types::MapKey> {
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

fn bitfield_value_ty(world: &mut World, spec: &super::super::body::LoweredBitFieldSpec) -> Ty {
    match spec.ty {
        crate::ast::BitType::Integer
        | crate::ast::BitType::Utf8
        | crate::ast::BitType::Utf16
        | crate::ast::BitType::Utf32 => world.types_mut().int(),
        crate::ast::BitType::Float => world.types_mut().float(),
        crate::ast::BitType::Binary | crate::ast::BitType::Bits => world.types_mut().str_t(),
    }
}

fn lowered_binop_ty(world: &mut World, op: BinOp, _left: Ty, _right: Ty) -> Ty {
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

fn lowered_unop_ty(world: &mut World, op: UnOp, input: Ty) -> Ty {
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

fn any_ty(world: &mut World) -> Ty {
    world.types_mut().any()
}

fn none_ty(world: &mut World) -> Ty {
    world.types_mut().none()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The three answers a closure callee can give, and why they are three and
    /// not two.
    ///
    /// A call is dead when nothing can arrive in its callee slot. The empty type
    /// has no members; a bare type variable has no runtime representation, so an
    /// activation keyed with one there is a specialization for an argument no
    /// caller can ever supply. Both are *evidence* — the call never happens, so
    /// its result is the empty type.
    ///
    /// A callable that merely carries a variable is the third answer and must
    /// stay distinct: `(int) -> a` is a perfectly representable value whose
    /// analysis is simply pending. Widening the death test to "has variables"
    /// would declare live calls dead. Widening it the other way — back to `any`
    /// — is the fz-f98.17 defect (fz-f98.18).
    #[test]
    fn only_an_uninhabitable_callee_makes_a_call_dead() {
        let mut types = Types::new();
        let never = types.none();
        let int = types.int();
        let alpha = types.param_alpha(0);
        let carries_a_var = types.arrow(&[int], alpha);

        assert!(
            callee_has_no_inhabitants(&types, never),
            "no value inhabits the empty type, so the call never happens",
        );
        assert!(
            callee_has_no_inhabitants(&types, alpha),
            "a bare type variable has no runtime representation, so nothing can be passed in that slot",
        );
        assert!(
            !callee_has_no_inhabitants(&types, carries_a_var),
            "a callable carrying an un-instantiated result is still a real pointer: absence of \
             analysis, not absence of values",
        );
    }
}
