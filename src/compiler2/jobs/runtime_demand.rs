use std::collections::{HashMap, HashSet};

use super::super::body::{
    CallArg, CallSiteId, ControlDestination, ControlEntryId, LoweredBody, LoweredEntry, LoweredStep, LoweredTail,
    ValueId,
};
use super::super::drive::{FactKey, Job};
use super::super::identity::{ExecutableKey, ExecutableNeed, FunctionId, function_id_of_closure_target};
use super::super::scheduler::FatalError;
use super::super::semantic::{
    ActivationAnalysis, CallSiteKey, CallSiteSummary, CallableDemand, CallableMaterialization, ExecutableRuntimeDemand,
    RuntimeDemand,
};
use super::super::types::Ty;
use super::super::world::World;
use super::semantic::executable_callsite_needs;

#[derive(Clone)]
struct ExecutableFacts {
    analysis: ActivationAnalysis,
    body: LoweredBody,
    entry_dispatch_inputs: HashSet<usize>,
    callsites: HashMap<CallSiteId, CallSiteSummary>,
    callsite_needs: HashMap<CallSiteId, ExecutableNeed>,
}

pub(super) struct RuntimeDemandClosure {
    pub demands: HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    pub latent_executables: HashSet<ExecutableKey>,
}

struct DerivedExecutableDemand {
    demand: ExecutableRuntimeDemand,
    call_return_demands: HashMap<CallSiteId, RuntimeDemand>,
}

pub(super) fn settle_runtime_demands(
    world: &mut World<'_>,
    entry: &ExecutableKey,
    executables: &HashSet<ExecutableKey>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<Option<RuntimeDemandClosure>, FatalError> {
    let facts = collect_executable_facts(world, executables);
    let locally_called = locally_called_executables(&facts);
    let mut demands = executables
        .iter()
        .map(|executable| {
            (
                executable.clone(),
                ExecutableRuntimeDemand {
                    return_demand: base_return_demand(executable, entry, &locally_called),
                    input_demands: vec![RuntimeDemand::Ignore; executable.activation.input.len()],
                    ..ExecutableRuntimeDemand::default()
                },
            )
        })
        .collect::<HashMap<_, _>>();

    loop {
        let mut next = HashMap::new();
        let mut observed_call_returns = HashMap::new();
        for executable in executables {
            let facts = facts
                .get(executable)
                .expect("runtime demand closure should have facts for every executable");
            let derived = derive_executable_runtime_demand(world, executable, facts, &demands);
            next.insert(executable.clone(), derived.demand);
            observed_call_returns.insert(executable.clone(), derived.call_return_demands);
        }
        propagate_call_return_demands(&facts, &observed_call_returns, &mut next);
        let changed = executables
            .iter()
            .any(|executable| demands.get(executable) != next.get(executable));
        demands = next;
        if !changed {
            break;
        }
    }

    let latent_executables =
        demanded_callable_executables(world, executables, &facts, &demands, reads, waits, follow_up)?;
    if !waits.is_empty() {
        return Ok(None);
    }

    Ok(Some(RuntimeDemandClosure {
        demands,
        latent_executables,
    }))
}

fn collect_executable_facts(
    world: &mut World<'_>,
    executables: &HashSet<ExecutableKey>,
) -> HashMap<ExecutableKey, ExecutableFacts> {
    executables
        .iter()
        .map(|executable| {
            let analysis = world
                .activation_analysis(&executable.activation)
                .cloned()
                .expect("settled semantic closure should have analysis for every executable");
            let body = world.lowered_body(executable.activation.function);
            let entry_dispatch_inputs = executable_dispatch_input_ordinals(
                world,
                executable.activation.function,
                analysis.reachable_clauses.clone(),
            );
            let callsites = analysis
                .callsites
                .iter()
                .filter_map(|callsite| {
                    world
                        .callsite_summary(&CallSiteKey {
                            activation: executable.activation.clone(),
                            callsite: *callsite,
                        })
                        .cloned()
                        .map(|summary| (*callsite, summary))
                })
                .collect::<HashMap<_, _>>();
            let callsite_needs = executable_callsite_needs(&body, &analysis.reachable_clauses, executable.need);
            (
                executable.clone(),
                ExecutableFacts {
                    analysis,
                    body,
                    entry_dispatch_inputs,
                    callsites,
                    callsite_needs,
                },
            )
        })
        .collect()
}

fn locally_called_executables(facts: &HashMap<ExecutableKey, ExecutableFacts>) -> HashSet<ExecutableKey> {
    let mut called = HashSet::new();
    for caller in facts.values() {
        for (callsite, summary) in &caller.callsites {
            let need = caller
                .callsite_needs
                .get(callsite)
                .copied()
                .unwrap_or(ExecutableNeed::Value);
            called.extend(local_call_targets(summary, need));
        }
    }
    called
}

fn base_return_demand(
    executable: &ExecutableKey,
    entry: &ExecutableKey,
    locally_called: &HashSet<ExecutableKey>,
) -> RuntimeDemand {
    if executable == entry || !locally_called.contains(executable) {
        runtime_demand_for_executable_need(executable.need)
    } else {
        RuntimeDemand::Ignore
    }
}

fn local_call_targets(summary: &CallSiteSummary, need: ExecutableNeed) -> Vec<ExecutableKey> {
    summary
        .targets
        .iter()
        .filter_map(|target| {
            target
                .activation
                .clone()
                .map(|activation| ExecutableKey { activation, need })
        })
        .collect()
}

fn executable_dispatch_input_ordinals(
    world: &World<'_>,
    function: FunctionId,
    reachable_clauses: Vec<u32>,
) -> HashSet<usize> {
    match world.lowered_body(function) {
        LoweredBody::Extern { .. } => HashSet::new(),
        LoweredBody::Clauses { .. } => {
            let dispatch =
                crate::compiler2::artifact::ExecutableDispatch::new(world.entry_dispatch(function), reachable_clauses);
            dispatch.required_input_ordinals()
        }
    }
}

fn propagate_call_return_demands(
    facts: &HashMap<ExecutableKey, ExecutableFacts>,
    observed_call_returns: &HashMap<ExecutableKey, HashMap<CallSiteId, RuntimeDemand>>,
    demands: &mut HashMap<ExecutableKey, ExecutableRuntimeDemand>,
) {
    for (caller_key, caller) in facts {
        let Some(observed_returns) = observed_call_returns.get(caller_key) else {
            continue;
        };
        for (callsite, observed) in observed_returns {
            if observed.is_ignore() {
                continue;
            }
            let need = caller
                .callsite_needs
                .get(callsite)
                .copied()
                .unwrap_or(ExecutableNeed::Value);
            let Some(summary) = caller.callsites.get(callsite) else {
                continue;
            };
            for target in local_call_targets(summary, need) {
                if let Some(callee) = demands.get_mut(&target) {
                    callee.return_demand.join_assign(observed);
                }
            }
        }
    }
}

fn derive_executable_runtime_demand(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
) -> DerivedExecutableDemand {
    let mut out = ExecutableRuntimeDemand {
        return_demand: demands
            .get(executable)
            .map(|demand| demand.return_demand.clone())
            .unwrap_or_default(),
        input_demands: vec![RuntimeDemand::Ignore; executable.activation.input.len()],
        ..ExecutableRuntimeDemand::default()
    };
    let mut call_return_demands = HashMap::new();

    let LoweredBody::Clauses { clauses, entries, .. } = &facts.body else {
        out.input_demands = executable
            .activation
            .input
            .iter()
            .copied()
            .map(|ty| boundary_runtime_demand(world, ty))
            .collect();
        return DerivedExecutableDemand {
            demand: out,
            call_return_demands,
        };
    };

    for clause_id in &facts.analysis.reachable_clauses {
        let clause = &clauses[*clause_id as usize];
        let mut live = collect_entry_live_demands(
            world,
            executable,
            entries.as_slice(),
            clause.entry,
            out.return_demand.clone(),
            facts,
            demands,
            &mut out,
            &mut call_return_demands,
        );
        propagate_steps_reverse(
            world,
            executable,
            clause.projections.as_slice(),
            &mut live,
            facts,
            demands,
            &mut out,
        );
        note_clause_matcher_demands(world, facts, clause.projections.as_slice(), &mut live, &mut out);
        for (index, param) in clause.params.iter().enumerate() {
            if let Some(demand) = live.remove(param) {
                out.input_demands[index].join_assign(&demand);
            }
        }
    }

    for &semantic_index in &facts.entry_dispatch_inputs {
        let Some(&ty) = executable.activation.input.get(semantic_index) else {
            continue;
        };
        let demand = boundary_runtime_demand(world, ty);
        out.input_demands[semantic_index].join_assign(&demand);
    }

    derive_callable_materializations(world, facts, &mut out);
    DerivedExecutableDemand {
        demand: out,
        call_return_demands,
    }
}

fn collect_entry_external_demands(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    entries: &[LoweredEntry],
    entry_id: ControlEntryId,
    outgoing_demand: RuntimeDemand,
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    out: &mut ExecutableRuntimeDemand,
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
) -> HashMap<ValueId, RuntimeDemand> {
    let entry = &entries[entry_id.as_u32() as usize];
    let mut live = collect_entry_live_demands(
        world,
        executable,
        entries,
        entry_id,
        outgoing_demand,
        facts,
        demands,
        out,
        call_return_demands,
    );
    let mut external = HashMap::new();
    if let Some(value) = entry.origin.input_value()
        && let Some(demand) = live.remove(&value)
    {
        external.insert(value, demand);
    }
    for capture in &entry.captures {
        if let Some(demand) = live.remove(capture) {
            join_map_demand(&mut external, *capture, demand);
        }
    }
    for param in &entry.params {
        live.remove(param);
    }
    merge_live_demands(&mut external, live);
    external
}

fn collect_entry_live_demands(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    entries: &[LoweredEntry],
    entry_id: ControlEntryId,
    outgoing_demand: RuntimeDemand,
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    out: &mut ExecutableRuntimeDemand,
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
) -> HashMap<ValueId, RuntimeDemand> {
    let entry = &entries[entry_id.as_u32() as usize];
    let mut live = HashMap::new();
    match &entry.tail {
        LoweredTail::Value { value, dest } => {
            let boundary_demand = demand_for_destination(
                world,
                executable,
                entries,
                dest,
                outgoing_demand,
                facts,
                demands,
                out,
                call_return_demands,
            );
            let demand = boundary_value_demand(world, facts, *value, boundary_demand);
            note_live_demand(world, out, &mut live, *value, demand);
        }
        LoweredTail::DirectCall {
            value,
            callsite,
            args,
            dest,
            ..
        } => {
            let boundary_demand = demand_for_destination(
                world,
                executable,
                entries,
                dest,
                outgoing_demand,
                facts,
                demands,
                out,
                call_return_demands,
            );
            let demand = boundary_value_demand(world, facts, *value, boundary_demand);
            note_live_demand(world, out, &mut live, *value, demand.clone());
            record_call_return_demand(call_return_demands, *callsite, demand);
            let arg_demands = direct_call_arg_demands(world, executable, *callsite, args.as_slice(), facts, demands);
            record_call_arg_demands(out, *callsite, arg_demands.as_slice());
            for (arg, demand) in args.iter().zip(arg_demands) {
                note_live_demand(world, out, &mut live, arg.value, demand);
            }
        }
        LoweredTail::ClosureCall {
            value,
            callsite,
            callee,
            args,
            dest,
            ..
        } => {
            let boundary_demand = demand_for_destination(
                world,
                executable,
                entries,
                dest,
                outgoing_demand,
                facts,
                demands,
                out,
                call_return_demands,
            );
            let demand = boundary_value_demand(world, facts, *value, boundary_demand);
            note_live_demand(world, out, &mut live, *value, demand.clone());
            record_call_return_demand(call_return_demands, *callsite, demand);
            note_live_demand(
                world,
                out,
                &mut live,
                *callee,
                RuntimeDemand::callable(closure_callee_demand(facts.callsites.get(callsite))),
            );
            let arg_demands = closure_call_arg_demands(world, executable, *callsite, args.as_slice(), facts, demands);
            record_call_arg_demands(out, *callsite, arg_demands.as_slice());
            for (arg, demand) in args.iter().zip(arg_demands) {
                note_live_demand(world, out, &mut live, arg.value, demand);
            }
        }
        LoweredTail::If {
            cond,
            then_entry,
            else_entry,
        } => {
            note_live_demand(world, out, &mut live, *cond, RuntimeDemand::Value);
            merge_live_demands(
                &mut live,
                collect_entry_external_demands(
                    world,
                    executable,
                    entries,
                    *then_entry,
                    outgoing_demand.clone(),
                    facts,
                    demands,
                    out,
                    call_return_demands,
                ),
            );
            merge_live_demands(
                &mut live,
                collect_entry_external_demands(
                    world,
                    executable,
                    entries,
                    *else_entry,
                    outgoing_demand,
                    facts,
                    demands,
                    out,
                    call_return_demands,
                ),
            );
        }
        LoweredTail::Dispatch {
            inputs,
            bindings,
            dispatch,
        } => {
            for input in inputs {
                note_live_demand(world, out, &mut live, *input, RuntimeDemand::Value);
            }
            for value in bindings.pinned.iter().chain(bindings.prepared.iter()) {
                note_live_demand(world, out, &mut live, *value, RuntimeDemand::Value);
            }
            for arm_entry in &dispatch.arm_entries {
                merge_live_demands(
                    &mut live,
                    collect_entry_external_demands(
                        world,
                        executable,
                        entries,
                        *arm_entry,
                        outgoing_demand.clone(),
                        facts,
                        demands,
                        out,
                        call_return_demands,
                    ),
                );
            }
            merge_live_demands(
                &mut live,
                collect_entry_external_demands(
                    world,
                    executable,
                    entries,
                    dispatch.miss_entry,
                    outgoing_demand,
                    facts,
                    demands,
                    out,
                    call_return_demands,
                ),
            );
        }
        LoweredTail::Receive(receive) => {
            for value in receive.bindings.pinned.iter().chain(receive.bindings.prepared.iter()) {
                note_live_demand(world, out, &mut live, *value, RuntimeDemand::Value);
            }
            for clause in &receive.clauses {
                merge_live_demands(
                    &mut live,
                    collect_entry_external_demands(
                        world,
                        executable,
                        entries,
                        clause.entry,
                        outgoing_demand.clone(),
                        facts,
                        demands,
                        out,
                        call_return_demands,
                    ),
                );
            }
            if let Some(after) = &receive.after {
                note_live_demand(world, out, &mut live, after.timeout, RuntimeDemand::Value);
                merge_live_demands(
                    &mut live,
                    collect_entry_external_demands(
                        world,
                        executable,
                        entries,
                        after.entry,
                        outgoing_demand,
                        facts,
                        demands,
                        out,
                        call_return_demands,
                    ),
                );
            }
        }
        LoweredTail::Halt { .. } => {}
    }

    propagate_steps_reverse(
        world,
        executable,
        entry.steps.as_slice(),
        &mut live,
        facts,
        demands,
        out,
    );
    live
}

fn demand_for_destination(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    entries: &[LoweredEntry],
    dest: &ControlDestination,
    outgoing_demand: RuntimeDemand,
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    out: &mut ExecutableRuntimeDemand,
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
) -> RuntimeDemand {
    match dest {
        ControlDestination::Return => outgoing_demand,
        ControlDestination::Deliver(entry_id) => {
            let delivered = entries[entry_id.as_u32() as usize]
                .origin
                .input_value()
                .expect("delivered control edges should target a resume entry");
            collect_entry_external_demands(
                world,
                executable,
                entries,
                *entry_id,
                outgoing_demand,
                facts,
                demands,
                out,
                call_return_demands,
            )
            .remove(&delivered)
            .unwrap_or(RuntimeDemand::Ignore)
        }
    }
}

fn propagate_steps_reverse(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    steps: &[LoweredStep],
    live: &mut HashMap<ValueId, RuntimeDemand>,
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    out: &mut ExecutableRuntimeDemand,
) {
    for step in steps.iter().rev() {
        match step {
            LoweredStep::Const { .. } | LoweredStep::FunctionRef { .. } => {}
            LoweredStep::Tuple { value, items } => {
                let demand = take_live_demand(live, *value);
                match demand {
                    RuntimeDemand::Ignore => {}
                    RuntimeDemand::TupleFields(fields) if fields.len() == items.len() => {
                        for (item, demand) in items.iter().zip(fields) {
                            let demand = boundary_value_demand(world, facts, *item, demand);
                            note_live_demand(world, out, live, *item, demand);
                        }
                    }
                    _ => {
                        for item in items {
                            let demand = boundary_value_demand(world, facts, *item, RuntimeDemand::Value);
                            note_live_demand(world, out, live, *item, demand);
                        }
                    }
                }
            }
            LoweredStep::List { value, items, tail } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for item in items {
                        let demand = boundary_value_demand(world, facts, *item, RuntimeDemand::Value);
                        note_live_demand(world, out, live, *item, demand);
                    }
                    if let Some(tail) = tail {
                        let demand = boundary_value_demand(world, facts, *tail, RuntimeDemand::Value);
                        note_live_demand(world, out, live, *tail, demand);
                    }
                }
            }
            LoweredStep::Map { value, entries } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for (key, field) in entries {
                        let key_demand = boundary_value_demand(world, facts, key.value, RuntimeDemand::Value);
                        let field_demand = boundary_value_demand(world, facts, *field, RuntimeDemand::Value);
                        note_live_demand(world, out, live, key.value, key_demand);
                        note_live_demand(world, out, live, *field, field_demand);
                    }
                }
            }
            LoweredStep::MapUpdate { value, base, entries } => {
                if !take_live_demand(live, *value).is_ignore() {
                    let base_demand = boundary_value_demand(world, facts, *base, RuntimeDemand::Value);
                    note_live_demand(world, out, live, *base, base_demand);
                    for (key, field) in entries {
                        let key_demand = boundary_value_demand(world, facts, key.value, RuntimeDemand::Value);
                        let field_demand = boundary_value_demand(world, facts, *field, RuntimeDemand::Value);
                        note_live_demand(world, out, live, key.value, key_demand);
                        note_live_demand(world, out, live, *field, field_demand);
                    }
                }
            }
            LoweredStep::Struct { value, fields, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for (_, field) in fields {
                        let demand = boundary_value_demand(world, facts, *field, RuntimeDemand::Value);
                        note_live_demand(world, out, live, *field, demand);
                    }
                }
            }
            LoweredStep::Bitstring { value, fields } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for field in fields {
                        note_live_demand(world, out, live, field.value, RuntimeDemand::Value);
                        if let Some(super::super::body::LoweredBitSize::Value(size)) = &field.spec.size {
                            note_live_demand(world, out, live, *size, RuntimeDemand::Value);
                        }
                    }
                }
            }
            LoweredStep::Lambda {
                value,
                function,
                captures,
            } => {
                let demand = take_live_demand(live, *value);
                if !demand.is_ignore() {
                    propagate_lambda_capture_demands(
                        world,
                        executable,
                        *function,
                        captures.as_slice(),
                        demand,
                        facts,
                        demands,
                        live,
                        out,
                    );
                }
            }
            LoweredStep::BinaryOp { value, left, right, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(world, out, live, *left, RuntimeDemand::Value);
                    note_live_demand(world, out, live, *right, RuntimeDemand::Value);
                }
            }
            LoweredStep::UnaryOp { value, input, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(world, out, live, *input, RuntimeDemand::Value);
                }
            }
            LoweredStep::MapIndex { value, base, key } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(world, out, live, *base, RuntimeDemand::Value);
                    note_live_demand(world, out, live, key.value, RuntimeDemand::Value);
                }
            }
            LoweredStep::FieldAccess { value, base, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(world, out, live, *base, RuntimeDemand::Value);
                }
            }
            LoweredStep::AssertLiteral { source, .. } => {
                note_live_demand(world, out, live, *source, RuntimeDemand::Value);
            }
            LoweredStep::AssertStruct { source, .. } => {
                note_live_demand(world, out, live, *source, RuntimeDemand::Value);
            }
            LoweredStep::RequireMapValue { value, source, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(world, out, live, *source, RuntimeDemand::Value);
                }
            }
            LoweredStep::AssertTuple { source, arity } => {
                note_live_demand(
                    world,
                    out,
                    live,
                    *source,
                    RuntimeDemand::tuple_fields(vec![RuntimeDemand::Ignore; *arity]),
                );
            }
            LoweredStep::TupleField { value, source, index } => {
                let demand = take_live_demand(live, *value);
                if !demand.is_ignore() {
                    let mut fields = vec![RuntimeDemand::Ignore; index + 1];
                    fields[*index] = demand;
                    note_live_demand(world, out, live, *source, RuntimeDemand::tuple_fields(fields));
                }
            }
            LoweredStep::AssertEmptyList { source } => {
                note_live_demand(world, out, live, *source, RuntimeDemand::Value);
            }
            LoweredStep::AssertSame { source, value } => {
                note_live_demand(world, out, live, *source, RuntimeDemand::Value);
                note_live_demand(world, out, live, *value, RuntimeDemand::Value);
            }
            LoweredStep::SplitList { source, head, tail } => {
                let head_demand = take_live_demand(live, *head);
                let tail_demand = take_live_demand(live, *tail);
                if !head_demand.is_ignore() || !tail_demand.is_ignore() {
                    note_live_demand(world, out, live, *source, RuntimeDemand::Value);
                }
            }
            LoweredStep::BitstringInit { reader, source } => {
                if !take_live_demand(live, *reader).is_ignore() {
                    note_live_demand(world, out, live, *source, RuntimeDemand::Value);
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
                let ok_demand = take_live_demand(live, *ok);
                let value_demand = take_live_demand(live, *value);
                let next_reader_demand = take_live_demand(live, *next_reader);
                if !ok_demand.is_ignore() || !value_demand.is_ignore() || !next_reader_demand.is_ignore() {
                    note_live_demand(world, out, live, *reader, RuntimeDemand::Value);
                    if let Some(super::super::body::LoweredBitSize::Value(size)) = &spec.size {
                        note_live_demand(world, out, live, *size, RuntimeDemand::Value);
                    }
                }
            }
            LoweredStep::AssertBitstringDone { reader } => {
                note_live_demand(world, out, live, *reader, RuntimeDemand::Value);
            }
        }
    }
}

fn note_clause_matcher_demands(
    world: &mut World<'_>,
    facts: &ExecutableFacts,
    steps: &[LoweredStep],
    live: &mut HashMap<ValueId, RuntimeDemand>,
    out: &mut ExecutableRuntimeDemand,
) {
    for step in steps {
        match step {
            LoweredStep::AssertLiteral { source, .. }
            | LoweredStep::AssertStruct { source, .. }
            | LoweredStep::AssertTuple { source, .. }
            | LoweredStep::AssertEmptyList { source }
            | LoweredStep::BitstringInit { source, .. } => {
                let demand = boundary_value_demand(world, facts, *source, RuntimeDemand::Value);
                note_live_demand(world, out, live, *source, demand);
            }
            LoweredStep::RequireMapValue { source, .. } => {
                let source_demand = boundary_value_demand(world, facts, *source, RuntimeDemand::Value);
                note_live_demand(world, out, live, *source, source_demand);
            }
            LoweredStep::AssertSame { source, value } => {
                let source_demand = boundary_value_demand(world, facts, *source, RuntimeDemand::Value);
                note_live_demand(world, out, live, *source, source_demand);
                let value_demand = boundary_value_demand(world, facts, *value, RuntimeDemand::Value);
                note_live_demand(world, out, live, *value, value_demand);
            }
            LoweredStep::SplitList { source, .. } => {
                let demand = boundary_value_demand(world, facts, *source, RuntimeDemand::Value);
                note_live_demand(world, out, live, *source, demand);
            }
            LoweredStep::BitstringRead { reader, spec, .. } => {
                let demand = boundary_value_demand(world, facts, *reader, RuntimeDemand::Value);
                note_live_demand(world, out, live, *reader, demand);
                if let Some(super::super::body::LoweredBitSize::Value(size)) = &spec.size {
                    note_live_demand(world, out, live, *size, RuntimeDemand::Value);
                }
            }
            LoweredStep::AssertBitstringDone { reader } => {
                let demand = boundary_value_demand(world, facts, *reader, RuntimeDemand::Value);
                note_live_demand(world, out, live, *reader, demand);
            }
            LoweredStep::Const { .. }
            | LoweredStep::Tuple { .. }
            | LoweredStep::List { .. }
            | LoweredStep::Map { .. }
            | LoweredStep::MapUpdate { .. }
            | LoweredStep::Struct { .. }
            | LoweredStep::Bitstring { .. }
            | LoweredStep::FunctionRef { .. }
            | LoweredStep::Lambda { .. }
            | LoweredStep::BinaryOp { .. }
            | LoweredStep::UnaryOp { .. }
            | LoweredStep::MapIndex { .. }
            | LoweredStep::FieldAccess { .. }
            | LoweredStep::TupleField { .. } => {}
        }
    }
}

fn propagate_lambda_capture_demands(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    function: FunctionId,
    captures: &[ValueId],
    demand: RuntimeDemand,
    facts: &ExecutableFacts,
    all_demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    live: &mut HashMap<ValueId, RuntimeDemand>,
    out: &mut ExecutableRuntimeDemand,
) {
    let capture_types = captures
        .iter()
        .map(|capture| facts.analysis.value_types.get(capture).copied())
        .collect::<Option<Vec<_>>>();
    let RuntimeDemand::Callable(callable) = demand else {
        for capture in captures {
            note_live_demand(world, out, live, *capture, RuntimeDemand::Value);
        }
        return;
    };
    if callable.opaque || callable.escape || capture_types.is_none() || callable.resolved.is_empty() {
        for capture in captures {
            note_live_demand(world, out, live, *capture, RuntimeDemand::Value);
        }
        return;
    }
    let capture_types = capture_types.expect("checked above");
    let mut matched = false;
    for surface in &callable.resolved {
        for (callee, callee_demand) in all_demands {
            if callee.activation.root != executable.activation.root || callee.activation.function != function {
                continue;
            }
            if callee.activation.input.len() != capture_types.len() + surface.inputs.len() {
                continue;
            }
            if &callee.activation.input[..capture_types.len()] != capture_types.as_slice() {
                continue;
            }
            if &callee.activation.input[capture_types.len()..] != surface.inputs.as_slice() {
                continue;
            }
            matched = true;
            for (capture, demand) in captures.iter().zip(callee_demand.input_demands.iter()) {
                note_live_demand(world, out, live, *capture, demand.clone());
            }
        }
    }
    if !matched {
        for capture in captures {
            note_live_demand(world, out, live, *capture, RuntimeDemand::Value);
        }
    }
}

fn direct_call_arg_demands(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    callsite: CallSiteId,
    args: &[CallArg],
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
) -> Vec<RuntimeDemand> {
    arg_demands_for_summary(world, executable, callsite, args.len(), 0, facts, demands)
}

fn closure_call_arg_demands(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    callsite: CallSiteId,
    args: &[CallArg],
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
) -> Vec<RuntimeDemand> {
    arg_demands_for_summary(world, executable, callsite, args.len(), 0, facts, demands)
}

fn arg_demands_for_summary(
    world: &mut World<'_>,
    _executable: &ExecutableKey,
    callsite: CallSiteId,
    arity: usize,
    default_offset: usize,
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
) -> Vec<RuntimeDemand> {
    let mut out = vec![RuntimeDemand::Ignore; arity];
    let Some(summary) = facts.callsites.get(&callsite) else {
        return vec![RuntimeDemand::Value; arity];
    };
    let need = facts
        .callsite_needs
        .get(&callsite)
        .copied()
        .unwrap_or(ExecutableNeed::Value);
    for target in &summary.targets {
        let target_demands = local_target_input_demands(world, target, need, demands);
        let offset = target
            .activation
            .as_ref()
            .map(|activation| activation.input.len().saturating_sub(target.surface_inputs.len()))
            .unwrap_or(default_offset);
        for (index, slot) in out.iter_mut().enumerate().take(arity) {
            let fallback_ty = target
                .surface_inputs
                .get(index)
                .copied()
                .unwrap_or_else(|| world.types_mut().any());
            let observed = target_demands
                .get(offset + index)
                .cloned()
                .unwrap_or_else(|| boundary_runtime_demand(world, fallback_ty));
            slot.join_assign(&observed);
        }
    }
    out
}

fn local_target_input_demands(
    world: &mut World<'_>,
    target: &super::super::semantic::CallTargetSummary,
    need: ExecutableNeed,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
) -> Vec<RuntimeDemand> {
    match target.callee {
        super::super::semantic::SelectedCallee::ProviderBoundary(_) => target
            .surface_inputs
            .iter()
            .copied()
            .map(|ty| boundary_runtime_demand(world, ty))
            .collect(),
        super::super::semantic::SelectedCallee::Function(function) => {
            if matches!(world.lowered_body(function), LoweredBody::Extern { .. }) {
                return target
                    .surface_inputs
                    .iter()
                    .copied()
                    .map(|ty| boundary_runtime_demand(world, ty))
                    .collect();
            }
            let Some(activation) = target.activation.clone() else {
                return target
                    .surface_inputs
                    .iter()
                    .copied()
                    .map(|ty| boundary_runtime_demand(world, ty))
                    .collect();
            };
            demands
                .get(&ExecutableKey { activation, need })
                .map(|demand| demand.input_demands.clone())
                .unwrap_or_else(|| vec![RuntimeDemand::Ignore; target.activation.as_ref().map_or(0, |a| a.input.len())])
        }
    }
}

fn boundary_runtime_demand(world: &mut World<'_>, ty: Ty) -> RuntimeDemand {
    if world.types_mut().callable_clauses(&ty).is_some() {
        RuntimeDemand::callable(CallableDemand {
            resolved: Default::default(),
            opaque: true,
            escape: true,
        })
    } else {
        RuntimeDemand::Value
    }
}

fn boundary_value_demand(
    world: &mut World<'_>,
    facts: &ExecutableFacts,
    value: ValueId,
    demand: RuntimeDemand,
) -> RuntimeDemand {
    if !matches!(demand, RuntimeDemand::Value) {
        return demand;
    }
    let Some(&ty) = facts.analysis.value_types.get(&value) else {
        return RuntimeDemand::Value;
    };
    if world.types_mut().callable_clauses(&ty).is_some() {
        RuntimeDemand::callable(CallableDemand::escaped())
    } else {
        RuntimeDemand::Value
    }
}

fn closure_callee_demand(summary: Option<&CallSiteSummary>) -> CallableDemand {
    let Some(summary) = summary else {
        return CallableDemand {
            resolved: Default::default(),
            opaque: true,
            escape: false,
        };
    };
    let mut demand = CallableDemand::default();
    for target in &summary.targets {
        demand.join_assign(&CallableDemand::resolved(target.surface_inputs.clone()));
    }
    demand
}

fn runtime_demand_for_executable_need(need: ExecutableNeed) -> RuntimeDemand {
    match need {
        ExecutableNeed::Value => RuntimeDemand::Value,
        ExecutableNeed::TupleFields(arity) => RuntimeDemand::tuple_fields(vec![RuntimeDemand::Value; arity]),
    }
}

fn demanded_callable_executables(
    world: &mut World<'_>,
    executables: &HashSet<ExecutableKey>,
    facts: &HashMap<ExecutableKey, ExecutableFacts>,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<HashSet<ExecutableKey>, FatalError> {
    let mut latent = HashSet::new();
    for executable in executables {
        let facts = facts
            .get(executable)
            .expect("runtime demand closure should have facts for every executable");
        let producer_values = local_callable_producer_values(&facts.body);
        let demand = demands
            .get(executable)
            .expect("runtime demand closure should produce a plan for every executable");
        for (value, materialization) in &demand.callable_materializations {
            if !matches!(materialization, CallableMaterialization::FirstClass { .. }) {
                continue;
            }
            if !producer_values.contains(value) {
                continue;
            }
            let Some(&ty) = facts.analysis.value_types.get(value) else {
                continue;
            };
            for callee in callable_executables_from_type(world, executable, ty, reads, waits, follow_up) {
                latent.insert(callee);
            }
        }
    }
    Ok(latent)
}

fn local_callable_producer_values(body: &LoweredBody) -> HashSet<ValueId> {
    let mut values = HashSet::new();
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return values;
    };
    for clause in clauses {
        for step in &clause.projections {
            if let Some(value) = step_local_callable_value(step) {
                values.insert(value);
            }
        }
    }
    for entry in entries {
        for step in &entry.steps {
            if let Some(value) = step_local_callable_value(step) {
                values.insert(value);
            }
        }
    }
    values
}

fn step_local_callable_value(step: &LoweredStep) -> Option<ValueId> {
    match step {
        LoweredStep::FunctionRef { value, .. } | LoweredStep::Lambda { value, .. } => Some(*value),
        _ => None,
    }
}

fn callable_executables_from_type(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    callable_ty: Ty,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Vec<ExecutableKey> {
    let Some(clauses) = world.types_mut().callable_value_clauses(&callable_ty) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for clause in clauses {
        let Some(closure) = clause.closure else {
            continue;
        };
        let function = function_id_of_closure_target(closure.target);
        if !world.require_activation_key_facts(function, reads, waits, follow_up) {
            continue;
        }
        let mut inputs = closure.captures;
        inputs.extend(clause.args);
        out.push(ExecutableKey {
            activation: world.activation_key(executable.activation.root, function, &inputs),
            need: ExecutableNeed::Value,
        });
    }
    out
}

fn derive_callable_materializations(world: &mut World<'_>, facts: &ExecutableFacts, out: &mut ExecutableRuntimeDemand) {
    out.callable_materializations.clear();
    for (value, demand) in &out.value_demands {
        let RuntimeDemand::Callable(callable) = demand else {
            continue;
        };
        let Some(&ty) = facts.analysis.value_types.get(value) else {
            continue;
        };
        if world.types_mut().callable_clauses(&ty).is_none() {
            continue;
        }
        let materialization = if callable.opaque || callable.escape {
            CallableMaterialization::FirstClass {
                surfaces: callable.resolved.clone(),
            }
        } else if callable.resolved.is_empty() {
            continue;
        } else {
            CallableMaterialization::DirectOnly {
                surfaces: callable.resolved.clone(),
            }
        };
        out.callable_materializations.insert(*value, materialization);
    }
}

fn note_live_demand(
    _world: &mut World<'_>,
    out: &mut ExecutableRuntimeDemand,
    live: &mut HashMap<ValueId, RuntimeDemand>,
    value: ValueId,
    demand: RuntimeDemand,
) {
    if demand.is_ignore() {
        return;
    }
    join_map_demand(live, value, demand.clone());
    join_map_demand(&mut out.value_demands, value, demand);
}

fn merge_live_demands(target: &mut HashMap<ValueId, RuntimeDemand>, observed: HashMap<ValueId, RuntimeDemand>) {
    for (value, demand) in observed {
        join_map_demand(target, value, demand);
    }
}

fn join_map_demand(target: &mut HashMap<ValueId, RuntimeDemand>, value: ValueId, demand: RuntimeDemand) {
    target
        .entry(value)
        .and_modify(|existing| existing.join_assign(&demand))
        .or_insert(demand);
}

fn record_call_arg_demands(out: &mut ExecutableRuntimeDemand, callsite: CallSiteId, observed: &[RuntimeDemand]) {
    let slot = out
        .call_arg_demands
        .entry(callsite)
        .or_insert_with(|| vec![RuntimeDemand::Ignore; observed.len()]);
    if slot.len() < observed.len() {
        slot.resize(observed.len(), RuntimeDemand::Ignore);
    }
    for (existing, observed) in slot.iter_mut().zip(observed.iter()) {
        existing.join_assign(observed);
    }
}

fn record_call_return_demand(
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
    callsite: CallSiteId,
    observed: RuntimeDemand,
) {
    if observed.is_ignore() {
        return;
    }
    call_return_demands
        .entry(callsite)
        .and_modify(|existing| existing.join_assign(&observed))
        .or_insert(observed);
}

fn take_live_demand(live: &mut HashMap<ValueId, RuntimeDemand>, value: ValueId) -> RuntimeDemand {
    live.remove(&value).unwrap_or(RuntimeDemand::Ignore)
}
