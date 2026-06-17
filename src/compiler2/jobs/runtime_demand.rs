use std::collections::{BTreeSet, HashMap, HashSet};

use super::super::body::{
    CallArg, CallSiteId, ControlDestination, ControlEntryId, DeliveredValueJoin, DeliveredValueSource, LoweredBody,
    LoweredEntry, LoweredStep, LoweredTail, ValueId, delivered_value_joins,
};
use super::super::drive::{FactKey, Job};
use super::super::identity::{ExecutableKey, ExecutableNeed, FunctionId};
use super::super::scheduler::FatalError;
use super::super::semantic::{
    ActivationAnalysis, CallSiteKey, CallSiteSummary, CallableDemand, CallableFlowFact, CallableSurface,
    ExecutableRuntimeDemand, RuntimeDemand, ShapeDemand,
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
    delivered_value_joins: HashMap<ControlEntryId, DeliveredValueJoin>,
    local_callable_producers: HashMap<ValueId, LocalCallableProducer>,
}

pub(super) struct RuntimeDemandClosure {
    pub demands: HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    pub latent_executables: HashSet<ExecutableKey>,
}

struct DerivedExecutableDemand {
    demand: ExecutableRuntimeDemand,
    call_return_demands: HashMap<CallSiteId, RuntimeDemand>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct LocalCallableProducer {
    function: FunctionId,
    captures: Box<[ValueId]>,
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
                    return_demand: base_return_demand(world, executable, entry, &locally_called),
                    input_demands: vec![RuntimeDemand::ignore(); executable.activation.input.len()],
                    ..ExecutableRuntimeDemand::default()
                },
            )
        })
        .collect::<HashMap<_, _>>();

    loop {
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

        derive_callable_flow_facts(
            world,
            executables,
            &locally_called,
            &facts,
            &mut demands,
            reads,
            waits,
            follow_up,
        )?;
        if !waits.is_empty() {
            return Ok(None);
        }
        if !apply_callable_boundary_return_demands(world, &mut demands) {
            break;
        }
    }

    let latent_executables = demanded_callable_executables(executables, &demands);

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
            let delivered_value_joins = delivered_value_joins(&body);
            let local_callable_producers = local_callable_producers(&body);
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
                    delivered_value_joins,
                    local_callable_producers,
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
    world: &mut World<'_>,
    executable: &ExecutableKey,
    entry: &ExecutableKey,
    locally_called: &HashSet<ExecutableKey>,
) -> RuntimeDemand {
    if executable == entry {
        runtime_demand_for_executable_need(executable.need)
    } else if !locally_called.contains(executable) {
        let return_ty = world
            .activation_return(&executable.activation)
            .unwrap_or_else(|| world.types_mut().none());
        boundary_runtime_demand(world, return_ty)
    } else {
        RuntimeDemand::ignore()
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
            let need = caller
                .callsite_needs
                .get(callsite)
                .copied()
                .unwrap_or(ExecutableNeed::Value);
            // A tuple-field callsite delivers exactly the field shape its need
            // names: that is the executable's ABI contract, fixed by the planner
            // when it keyed the callee. The observed value demand only refines a
            // plain value return, where an ignored result may stay unmaterialized.
            let delivered = match need {
                ExecutableNeed::TupleFields(_) => runtime_demand_for_executable_need(need),
                ExecutableNeed::Value => {
                    if observed.is_ignore() {
                        continue;
                    }
                    observed.clone()
                }
            };
            let Some(summary) = caller.callsites.get(callsite) else {
                continue;
            };
            for target in local_call_targets(summary, need) {
                if let Some(callee) = demands.get_mut(&target) {
                    callee.return_demand.join_assign(&delivered);
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
        input_demands: vec![RuntimeDemand::ignore(); executable.activation.input.len()],
        ..ExecutableRuntimeDemand::default()
    };
    let mut call_return_demands = HashMap::new();

    let LoweredBody::Clauses { clauses, entries, .. } = &facts.body else {
        out.input_demands = match &facts.body {
            LoweredBody::Extern { signature } => executable
                .activation
                .input
                .iter()
                .enumerate()
                .map(|(index, ty)| {
                    signature
                        .params
                        .get(index)
                        .map(|_| RuntimeDemand::whole())
                        .unwrap_or_else(|| boundary_runtime_demand(world, *ty))
                })
                .collect(),
            LoweredBody::Clauses { .. } => unreachable!(),
        };
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
        let demand = upgrade_joined_delivered_callable_value_demand(facts, entry_id, value, demand);
        join_map_demand(&mut out.value_demands, value, demand.clone());
        external.insert(value, demand);
    }
    let capture_demands = entry
        .captures
        .iter()
        .map(|capture| live.remove(capture).unwrap_or(RuntimeDemand::ignore()))
        .collect::<Vec<_>>();
    record_entry_capture_demands(out, entry_id, &capture_demands);
    for (capture, demand) in entry.captures.iter().zip(capture_demands) {
        if !demand.is_ignore() {
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
            let (boundary_demand, external_demands) = destination_demands(
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
            merge_live_demands(&mut live, external_demands);
        }
        LoweredTail::DirectCall {
            value,
            callsite,
            args,
            dest,
            ..
        } => {
            let (boundary_demand, external_demands) = destination_demands(
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
            merge_live_demands(&mut live, external_demands);
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
            let (boundary_demand, external_demands) = destination_demands(
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
            merge_live_demands(&mut live, external_demands);
            let callee_demand = RuntimeDemand::callable(closure_callee_demand(
                world,
                facts,
                args.as_slice(),
                facts.callsites.get(callsite),
            ));
            note_live_demand(world, out, &mut live, *callee, callee_demand);
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
            note_live_demand(world, out, &mut live, *cond, RuntimeDemand::whole());
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
                note_live_demand(world, out, &mut live, *input, RuntimeDemand::whole());
            }
            for value in bindings.pinned.iter().chain(bindings.prepared.iter()) {
                note_live_demand(world, out, &mut live, *value, RuntimeDemand::whole());
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
                note_live_demand(world, out, &mut live, *value, RuntimeDemand::whole());
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
                note_live_demand(world, out, &mut live, after.timeout, RuntimeDemand::whole());
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

fn destination_demands(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    entries: &[LoweredEntry],
    dest: &ControlDestination,
    outgoing_demand: RuntimeDemand,
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    out: &mut ExecutableRuntimeDemand,
    call_return_demands: &mut HashMap<CallSiteId, RuntimeDemand>,
) -> (RuntimeDemand, HashMap<ValueId, RuntimeDemand>) {
    match dest {
        ControlDestination::Return => (outgoing_demand, HashMap::new()),
        ControlDestination::Deliver(entry_id) => {
            let delivered = entries[entry_id.as_u32() as usize]
                .origin
                .input_value()
                .expect("delivered control edges should target a resume entry");
            let mut external_demands = collect_entry_external_demands(
                world,
                executable,
                entries,
                *entry_id,
                outgoing_demand,
                facts,
                demands,
                out,
                call_return_demands,
            );
            let delivered_demand = external_demands.remove(&delivered).unwrap_or(RuntimeDemand::ignore());
            (delivered_demand, external_demands)
        }
    }
}

fn upgrade_joined_delivered_callable_value_demand(
    facts: &ExecutableFacts,
    entry: ControlEntryId,
    value: ValueId,
    mut demand: RuntimeDemand,
) -> RuntimeDemand {
    if demand.is_callable() && delivered_join_has_distinct_callable_producers(facts, entry, value) {
        demand.callable.escape = true;
    }
    demand
}

fn delivered_join_has_distinct_callable_producers(
    facts: &ExecutableFacts,
    entry: ControlEntryId,
    delivered: ValueId,
) -> bool {
    let Some(join) = facts.delivered_value_joins.get(&entry) else {
        return false;
    };
    if join.value != delivered {
        return false;
    }
    let producers = join
        .sources
        .iter()
        .filter_map(|join_source| match join_source {
            DeliveredValueSource::LocalValue(value) => facts.local_callable_producers.get(value),
            DeliveredValueSource::CallsiteReturn(_) => None,
        })
        .collect::<HashSet<_>>();
    producers.len() > 1
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
    let asserted_tuple_arities = step_asserted_tuple_arities(steps);
    for step in steps.iter().rev() {
        match step {
            LoweredStep::Const { .. } | LoweredStep::FunctionRef { .. } => {}
            LoweredStep::Tuple { value, items } => {
                let demand = take_live_demand(live, *value);
                if !demand.is_callable() {
                    match demand.shape {
                        ShapeDemand::Ignore => {}
                        ShapeDemand::TupleFields(fields) if fields.len() == items.len() => {
                            for (item, demand) in items.iter().zip(fields) {
                                let demand = boundary_value_demand(world, facts, *item, demand);
                                note_live_demand(world, out, live, *item, demand);
                            }
                        }
                        _ => {
                            for item in items {
                                let demand = boundary_value_demand(world, facts, *item, RuntimeDemand::whole());
                                note_live_demand(world, out, live, *item, demand);
                            }
                        }
                    }
                } else {
                    for item in items {
                        let demand = boundary_value_demand(world, facts, *item, RuntimeDemand::whole());
                        note_live_demand(world, out, live, *item, demand);
                    }
                }
            }
            LoweredStep::List { value, items, tail } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for item in items {
                        let demand = boundary_value_demand(world, facts, *item, RuntimeDemand::whole());
                        note_live_demand(world, out, live, *item, demand);
                    }
                    if let Some(tail) = tail {
                        let demand = boundary_value_demand(world, facts, *tail, RuntimeDemand::whole());
                        note_live_demand(world, out, live, *tail, demand);
                    }
                }
            }
            LoweredStep::Map { value, entries } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for (key, field) in entries {
                        let key_demand = boundary_value_demand(world, facts, key.value, RuntimeDemand::whole());
                        let field_demand = boundary_value_demand(world, facts, *field, RuntimeDemand::whole());
                        note_live_demand(world, out, live, key.value, key_demand);
                        note_live_demand(world, out, live, *field, field_demand);
                    }
                }
            }
            LoweredStep::MapUpdate { value, base, entries } => {
                if !take_live_demand(live, *value).is_ignore() {
                    let base_demand = boundary_value_demand(world, facts, *base, RuntimeDemand::whole());
                    note_live_demand(world, out, live, *base, base_demand);
                    for (key, field) in entries {
                        let key_demand = boundary_value_demand(world, facts, key.value, RuntimeDemand::whole());
                        let field_demand = boundary_value_demand(world, facts, *field, RuntimeDemand::whole());
                        note_live_demand(world, out, live, key.value, key_demand);
                        note_live_demand(world, out, live, *field, field_demand);
                    }
                }
            }
            LoweredStep::Struct { value, fields, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for (_, field) in fields {
                        let demand = boundary_value_demand(world, facts, *field, RuntimeDemand::whole());
                        note_live_demand(world, out, live, *field, demand);
                    }
                }
            }
            LoweredStep::Bitstring { value, fields } => {
                if !take_live_demand(live, *value).is_ignore() {
                    for field in fields {
                        note_live_demand(world, out, live, field.value, RuntimeDemand::whole());
                        if let Some(super::super::body::LoweredBitSize::Value(size)) = &field.spec.size {
                            note_live_demand(world, out, live, *size, RuntimeDemand::whole());
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
                    note_live_demand(world, out, live, *left, RuntimeDemand::whole());
                    note_live_demand(world, out, live, *right, RuntimeDemand::whole());
                }
            }
            LoweredStep::UnaryOp { value, input, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(world, out, live, *input, RuntimeDemand::whole());
                }
            }
            LoweredStep::MapIndex { value, base, key } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(world, out, live, *base, RuntimeDemand::whole());
                    note_live_demand(world, out, live, key.value, RuntimeDemand::whole());
                }
            }
            LoweredStep::FieldAccess { value, base, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(world, out, live, *base, RuntimeDemand::whole());
                }
            }
            LoweredStep::AssertLiteral { source, .. } => {
                note_live_demand(world, out, live, *source, RuntimeDemand::whole());
            }
            LoweredStep::AssertStruct { source, .. } => {
                note_live_demand(world, out, live, *source, RuntimeDemand::whole());
            }
            LoweredStep::RequireMapValue { value, source, .. } => {
                if !take_live_demand(live, *value).is_ignore() {
                    note_live_demand(world, out, live, *source, RuntimeDemand::whole());
                }
            }
            LoweredStep::AssertTuple { source, arity } => {
                if !live.contains_key(source) || asserted_tuple_arities.get(source).copied() != Some(*arity) {
                    note_live_demand(world, out, live, *source, RuntimeDemand::whole());
                }
            }
            LoweredStep::TupleField { value, source, index } => {
                let demand = take_live_demand(live, *value);
                if !demand.is_ignore() {
                    let arity = asserted_tuple_arities.get(source).copied().unwrap_or(index + 1);
                    let mut fields = vec![RuntimeDemand::ignore(); arity];
                    fields[*index] = demand;
                    note_live_demand(world, out, live, *source, RuntimeDemand::tuple_fields(fields));
                }
            }
            LoweredStep::AssertEmptyList { source } => {
                note_live_demand(world, out, live, *source, RuntimeDemand::whole());
            }
            LoweredStep::AssertSame { source, value } => {
                note_live_demand(world, out, live, *source, RuntimeDemand::whole());
                note_live_demand(world, out, live, *value, RuntimeDemand::whole());
            }
            LoweredStep::SplitList { source, head, tail } => {
                let head_demand = take_live_demand(live, *head);
                let tail_demand = take_live_demand(live, *tail);
                if !head_demand.is_ignore() || !tail_demand.is_ignore() {
                    note_live_demand(world, out, live, *source, RuntimeDemand::whole());
                }
            }
            LoweredStep::BitstringInit { reader, source } => {
                if !take_live_demand(live, *reader).is_ignore() {
                    note_live_demand(world, out, live, *source, RuntimeDemand::whole());
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
                    note_live_demand(world, out, live, *reader, RuntimeDemand::whole());
                    if let Some(super::super::body::LoweredBitSize::Value(size)) = &spec.size {
                        note_live_demand(world, out, live, *size, RuntimeDemand::whole());
                    }
                }
            }
            LoweredStep::AssertBitstringDone { reader } => {
                note_live_demand(world, out, live, *reader, RuntimeDemand::whole());
            }
        }
    }
}

fn step_asserted_tuple_arities(steps: &[LoweredStep]) -> HashMap<ValueId, usize> {
    let mut arities = HashMap::new();
    for step in steps {
        if let LoweredStep::AssertTuple { source, arity } = step {
            arities.insert(*source, *arity);
        }
    }
    arities
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
                let demand = boundary_value_demand(world, facts, *source, RuntimeDemand::whole());
                note_live_demand(world, out, live, *source, demand);
            }
            LoweredStep::RequireMapValue { source, .. } => {
                let source_demand = boundary_value_demand(world, facts, *source, RuntimeDemand::whole());
                note_live_demand(world, out, live, *source, source_demand);
            }
            LoweredStep::AssertSame { source, value } => {
                let source_demand = boundary_value_demand(world, facts, *source, RuntimeDemand::whole());
                note_live_demand(world, out, live, *source, source_demand);
                let value_demand = boundary_value_demand(world, facts, *value, RuntimeDemand::whole());
                note_live_demand(world, out, live, *value, value_demand);
            }
            LoweredStep::SplitList { source, .. } => {
                let demand = boundary_value_demand(world, facts, *source, RuntimeDemand::whole());
                note_live_demand(world, out, live, *source, demand);
            }
            LoweredStep::BitstringRead { reader, spec, .. } => {
                let demand = boundary_value_demand(world, facts, *reader, RuntimeDemand::whole());
                note_live_demand(world, out, live, *reader, demand);
                if let Some(super::super::body::LoweredBitSize::Value(size)) = &spec.size {
                    note_live_demand(world, out, live, *size, RuntimeDemand::whole());
                }
            }
            LoweredStep::AssertBitstringDone { reader } => {
                let demand = boundary_value_demand(world, facts, *reader, RuntimeDemand::whole());
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
    if !demand.is_callable() {
        for capture in captures {
            note_live_demand(world, out, live, *capture, RuntimeDemand::whole());
        }
        return;
    }
    let callable = demand.callable;
    let capture_types = captures
        .iter()
        .map(|capture| facts.analysis.value_types.get(capture).copied())
        .collect::<Option<Vec<_>>>();
    let Some(capture_types) = capture_types else {
        for capture in captures {
            let demand = closure_capture_boundary_demand(world, facts, *capture, RuntimeDemand::whole(), &callable);
            note_live_demand(world, out, live, *capture, demand);
        }
        return;
    };
    // The captured values' demands live in the producer's own executable, in the
    // input-demand prefix that precedes its parameters. The closure's call
    // surfaces only select *which* specialization to read: a directly-called
    // closure restricts to the invoked surfaces, but an escaped closure — one
    // returned or stored rather than called here — carries no direct surface
    // (`resolved` is empty) even though its body still proves how it invokes each
    // capture (e.g. a returned `fn () -> f.(1) end` calls `f` at `(int)`). Reading
    // the producer executable by capture-type prefix recovers that proven surface;
    // gating on a non-empty `resolved` would discard it and let `f` reach
    // transport as a surface-less first-class demand.
    let mut matched = false;
    for (callee, callee_demand) in all_demands {
        if callee.activation.root != executable.activation.root || callee.activation.function != function {
            continue;
        }
        if callee.activation.input.len() < capture_types.len() {
            continue;
        }
        if &callee.activation.input[..capture_types.len()] != capture_types.as_slice() {
            continue;
        }
        let own_params = &callee.activation.input[capture_types.len()..];
        if !callable.resolved.is_empty()
            && !callable
                .resolved
                .iter()
                .any(|surface| surface.inputs.as_slice() == own_params)
        {
            continue;
        }
        matched = true;
        for (capture, demand) in captures.iter().zip(callee_demand.input_demands.iter()) {
            let demand = closure_capture_boundary_demand(world, facts, *capture, demand.clone(), &callable);
            note_live_demand(world, out, live, *capture, demand);
        }
    }
    if !matched {
        for capture in captures {
            let demand = closure_capture_boundary_demand(world, facts, *capture, RuntimeDemand::whole(), &callable);
            note_live_demand(world, out, live, *capture, demand);
        }
    }
}

fn closure_capture_boundary_demand(
    world: &mut World<'_>,
    facts: &ExecutableFacts,
    capture: ValueId,
    demand: RuntimeDemand,
    closure: &CallableDemand,
) -> RuntimeDemand {
    let mut upgraded = boundary_value_demand(world, facts, capture, demand);
    if upgraded.is_callable() {
        upgraded.callable.opaque |= closure.opaque;
        upgraded.callable.escape |= closure.escape;
    }
    upgraded
}

fn direct_call_arg_demands(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    callsite: CallSiteId,
    args: &[CallArg],
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
) -> Vec<RuntimeDemand> {
    arg_demands_for_summary(world, executable, callsite, args, 0, facts, demands)
}

fn closure_call_arg_demands(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    callsite: CallSiteId,
    args: &[CallArg],
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
) -> Vec<RuntimeDemand> {
    arg_demands_for_summary(world, executable, callsite, args, 0, facts, demands)
}

fn arg_demands_for_summary(
    world: &mut World<'_>,
    _executable: &ExecutableKey,
    callsite: CallSiteId,
    args: &[CallArg],
    default_offset: usize,
    facts: &ExecutableFacts,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
) -> Vec<RuntimeDemand> {
    let arity = args.len();
    let mut out = vec![RuntimeDemand::ignore(); arity];
    let Some(summary) = facts.callsites.get(&callsite) else {
        return args
            .iter()
            .map(|arg| opaque_call_arg_demand(world, facts, arg.value))
            .collect();
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
        for (index, (arg, slot)) in args.iter().zip(out.iter_mut()).enumerate().take(arity) {
            let fallback_ty = target
                .surface_inputs
                .get(index)
                .copied()
                .unwrap_or_else(|| world.types_mut().any());
            let observed = target_demands
                .get(offset + index)
                .cloned()
                .unwrap_or_else(|| boundary_runtime_demand(world, fallback_ty));
            let mut observed = boundary_value_demand(world, facts, arg.value, observed);
            ground_escaped_callable_surface(world, &mut observed, fallback_ty);
            slot.join_assign(&observed);
        }
    }
    out
}

/// Seed an escaping callable argument's surface from the boundary it crosses.
///
/// `boundary_value_demand` raises first-class `escape` on the callable axis but
/// records no `resolved` surface — the axis is type-blind by construction. The
/// surface the callee actually invokes the argument at is the boundary's settled
/// parameter type (`boundary_ty`), which pins free callable type variables to
/// their grounded instantiation. Unioning that surface onto an escaping callable
/// keys the escaping body at the grounded lane instead of its own polymorphic
/// template.
///
/// This is a *type seed*, not a re-grounding: it only ever adds a surface
/// derived from the static boundary type, gated solely on the monotone `escape`
/// bit. It never inspects (and so never depends on) the evolving callable axis,
/// so the union is unconditional — a callable that is both directly called and
/// escapes keeps both its call surface and its escape surface, and the demand
/// can only ascend across fixpoint rounds.
fn ground_escaped_callable_surface(world: &mut World<'_>, demand: &mut RuntimeDemand, boundary_ty: Ty) {
    if !demand.callable.escape {
        return;
    }
    let Some(clauses) = world.types_mut().callable_clauses(&boundary_ty) else {
        return;
    };
    demand
        .callable
        .resolved
        .extend(clauses.into_iter().map(|clause| CallableSurface::new(clause.args)));
}

fn local_target_input_demands(
    world: &mut World<'_>,
    target: &super::super::semantic::CallTargetSummary,
    need: ExecutableNeed,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
) -> Vec<RuntimeDemand> {
    match target.callee {
        super::super::semantic::SelectedCallee::ProviderBoundary(_function) => {
            // A provider boundary is interface-only by construction: it has no
            // defined function and no module body (`function_is_provider_boundary`),
            // so there is no lowered body to consult. Every argument crosses the
            // seam at its boundary demand; marshalling is the boundary fact's job.
            target
                .surface_inputs
                .iter()
                .copied()
                .map(|ty| boundary_runtime_demand(world, ty))
                .collect()
        }
        super::super::semantic::SelectedCallee::Function(function) => {
            if let LoweredBody::Extern { signature } = world.lowered_body(function) {
                return target
                    .surface_inputs
                    .iter()
                    .enumerate()
                    .map(|(index, ty)| {
                        signature
                            .params
                            .get(index)
                            .map(|_| RuntimeDemand::whole())
                            .unwrap_or_else(|| boundary_runtime_demand(world, *ty))
                    })
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
                .unwrap_or_else(|| {
                    vec![RuntimeDemand::ignore(); target.activation.as_ref().map_or(0, |a| a.input.len())]
                })
        }
    }
}

fn boundary_runtime_demand(world: &mut World<'_>, ty: Ty) -> RuntimeDemand {
    let Some(clauses) = world.types_mut().callable_clauses(&ty) else {
        if let Some(fields) = exact_tuple_field_tys(world, ty) {
            return RuntimeDemand::tuple_fields(
                fields
                    .into_iter()
                    .map(|field_ty| boundary_runtime_demand(world, field_ty))
                    .collect(),
            );
        }
        return RuntimeDemand::whole();
    };
    // A callable crossing a boundary escapes as a first-class value. Carry the
    // boundary's settled surface so callable-flow derivation keys the escaping
    // body at those exact argument lanes.
    let resolved = clauses
        .into_iter()
        .map(|clause| CallableSurface::new(clause.args))
        .collect::<BTreeSet<_>>();
    RuntimeDemand::callable(CallableDemand {
        resolved,
        opaque: false,
        escape: true,
    })
}

fn exact_tuple_field_tys(world: &mut World<'_>, ty: Ty) -> Option<Vec<Ty>> {
    let predicate = world.types().runtime_type_predicate(&ty);
    if predicate.tuple_arities.cofinite || predicate.tuple_arities.values.len() != 1 {
        return None;
    }
    let arity = *predicate.tuple_arities.values.iter().next()?;
    Some(tuple_field_tys(world, ty, arity))
}

fn tuple_field_tys(world: &mut World<'_>, ty: Ty, arity: usize) -> Vec<Ty> {
    let any = world.types_mut().any();
    let mut fields = world.types_mut().tuple_projections(&ty, arity);
    if fields.len() < arity {
        fields.resize(arity, any);
    } else if fields.len() > arity {
        fields.truncate(arity);
    }
    fields
}

fn value_is_callable(world: &mut World<'_>, facts: &ExecutableFacts, value: ValueId) -> bool {
    facts
        .analysis
        .value_types
        .get(&value)
        .copied()
        .is_some_and(|ty| world.types_mut().callable_clauses(&ty).is_some())
}

/// The runtime demand on an argument passed to an *opaque* closure call.
///
/// The callee is unresolved, so we cannot know which surface it invokes the
/// argument at. A callable argument therefore escapes first-class; other
/// arguments carry their ordinary whole-value boundary demand. The escape is
/// raised by `boundary_value_demand`, which is the single chokepoint for
/// first-class escape.
fn opaque_call_arg_demand(world: &mut World<'_>, facts: &ExecutableFacts, value: ValueId) -> RuntimeDemand {
    boundary_value_demand(world, facts, value, RuntimeDemand::whole())
}

/// The runtime demand on a value delivered to a destination boundary (a return
/// or call result). A callable delivered under a plain value demand escapes
/// ungrounded — no callee contract applies. A richer incoming demand (a
/// downstream surface, tuple fields) is honored as-is.
/// The runtime demand on `value` given the representation demand a consumer
/// places on it — the single chokepoint for first-class callable escape.
///
/// A callable consumed for its whole representation, with no resolved call
/// contract, escapes first-class. That is recorded by joining `escape` onto the
/// value's callable axis: a monotone raise that preserves the shape axis,
/// preserves any accumulated `resolved` surfaces, and never clears `opaque`.
/// Non-callable values, and callables that already carry a call contract, pass
/// through unchanged. There is no re-grounding from the value's type: the
/// callable axis is never erased by a shape join, so nothing needs recovering.
fn boundary_value_demand(
    world: &mut World<'_>,
    facts: &ExecutableFacts,
    value: ValueId,
    mut demand: RuntimeDemand,
) -> RuntimeDemand {
    if demand.shape == ShapeDemand::Whole && !demand.is_callable() && value_is_callable(world, facts, value) {
        demand.callable.join_assign(&CallableDemand::escaped());
    }
    demand
}

fn closure_callee_demand(
    world: &mut World<'_>,
    facts: &ExecutableFacts,
    args: &[CallArg],
    summary: Option<&CallSiteSummary>,
) -> CallableDemand {
    let Some(summary) = summary else {
        let mut demand = CallableDemand {
            resolved: Default::default(),
            opaque: true,
            escape: false,
        };
        demand.resolved.insert(CallableSurface::new(
            args.iter()
                .map(|arg| {
                    facts
                        .analysis
                        .value_types
                        .get(&arg.value)
                        .copied()
                        .unwrap_or_else(|| world.types_mut().any())
                })
                .collect(),
        ));
        return demand;
    };
    let mut demand = CallableDemand::default();
    for target in &summary.targets {
        demand.join_assign(&CallableDemand::resolved(target.surface_inputs.clone()));
    }
    let exact_local_target = matches!(
        summary.targets.as_slice(),
        [target]
            if matches!(target.callee, super::super::semantic::SelectedCallee::Function(_))
                && target.activation.is_some()
    );
    if !exact_local_target {
        demand.opaque = true;
    }
    demand
}

fn runtime_demand_for_executable_need(need: ExecutableNeed) -> RuntimeDemand {
    match need {
        ExecutableNeed::Value => RuntimeDemand::whole(),
        ExecutableNeed::TupleFields(arity) => RuntimeDemand::tuple_fields(vec![RuntimeDemand::whole(); arity]),
    }
}

fn demanded_callable_executables(
    executables: &HashSet<ExecutableKey>,
    demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
) -> HashSet<ExecutableKey> {
    let mut latent = HashSet::new();
    for executable in executables {
        let demand = demands
            .get(executable)
            .expect("runtime demand closure should produce a plan for every executable");
        for flow in demand.callable_flows.values() {
            if !flow.escape && !flow.opaque {
                continue;
            }
            latent.extend(flow.resolutions.iter().cloned());
        }
    }
    latent
}

fn apply_callable_boundary_return_demands(
    world: &mut World<'_>,
    demands: &mut HashMap<ExecutableKey, ExecutableRuntimeDemand>,
) -> bool {
    let mut required = Vec::new();
    for demand in demands.values() {
        for flow in demand.callable_flows.values() {
            if flow.first_class_surfaces.is_empty() {
                continue;
            }
            for surface in &flow.first_class_surfaces {
                for resolution in &flow.resolutions {
                    if resolution.activation.function != flow.function
                        || resolution.activation.input.len() < surface.inputs.len()
                    {
                        continue;
                    }
                    let offset = resolution.activation.input.len() - surface.inputs.len();
                    if resolution.activation.input[offset..] != surface.inputs {
                        continue;
                    }
                    let return_ty = world
                        .activation_return(&resolution.activation)
                        .unwrap_or_else(|| world.types_mut().none());
                    required.push((resolution.clone(), boundary_runtime_demand(world, return_ty)));
                }
            }
        }
    }

    let mut changed = false;
    for (executable, demand) in required {
        let Some(target) = demands.get_mut(&executable) else {
            continue;
        };
        let before = target.return_demand.clone();
        target.return_demand.join_assign(&demand);
        changed |= target.return_demand != before;
    }
    changed
}

fn derive_callable_flow_facts(
    world: &mut World<'_>,
    executables: &HashSet<ExecutableKey>,
    locally_called: &HashSet<ExecutableKey>,
    facts: &HashMap<ExecutableKey, ExecutableFacts>,
    demands: &mut HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Result<(), FatalError> {
    for executable in executables {
        let facts = facts
            .get(executable)
            .expect("runtime demand closure should have facts for every executable");
        let demand = demands
            .get_mut(executable)
            .expect("runtime demand closure should produce a plan for every executable");
        demand.callable_flows.clear();
        for (value, producer) in facts.local_callable_producers.clone() {
            let Some(value_demand) = demand.value_demands.get(&value) else {
                continue;
            };
            if !value_demand.is_callable() {
                continue;
            }
            let callable = &value_demand.callable;
            let closed = closed_callable_resolutions(world, locally_called, executables, facts, &producer);
            // `resolved` carries every observed surface. When the callable is
            // first-class (escaped/opaque), those surfaces are first-class
            // obligations, not direct calls — the genuinely-direct surfaces are
            // exactly the locally-called resolutions (`closed`). Only when the
            // callable is never first-class does `resolved` describe direct use.
            let mut direct_surfaces = if callable.is_first_class() {
                BTreeSet::new()
            } else {
                callable.resolved.clone()
            };
            direct_surfaces.extend(closed.iter().map(|(_, surface)| surface.clone()));
            let first_class_surfaces = first_class_surfaces_for_flow(world, facts, value, callable);
            let mut resolutions = closed.into_iter().map(|(resolution, _)| resolution).collect::<Vec<_>>();
            extend_unique(
                &mut resolutions,
                callable_flow_resolutions(
                    world,
                    executable,
                    facts,
                    &producer,
                    &first_class_surfaces,
                    reads,
                    waits,
                    follow_up,
                ),
            );
            demand.callable_flows.insert(
                value,
                CallableFlowFact {
                    function: producer.function,
                    captures: producer.captures,
                    direct_surfaces,
                    first_class_surfaces,
                    opaque: callable.opaque,
                    escape: callable.escape,
                    resolutions,
                },
            );
        }
    }
    Ok(())
}

fn first_class_surfaces_for_flow(
    world: &mut World<'_>,
    facts: &ExecutableFacts,
    value: ValueId,
    callable: &CallableDemand,
) -> BTreeSet<CallableSurface> {
    if !callable.opaque && !callable.escape {
        return BTreeSet::new();
    }
    let mut surfaces = callable.resolved.clone();
    if !surfaces.is_empty() {
        return surfaces;
    }
    let Some(&ty) = facts.analysis.value_types.get(&value) else {
        return surfaces;
    };
    let Some(clauses) = world.types_mut().callable_value_clauses(&ty) else {
        return surfaces;
    };
    surfaces.extend(clauses.into_iter().map(|clause| CallableSurface::new(clause.args)));
    surfaces
}

fn closed_callable_resolutions(
    world: &mut World<'_>,
    locally_called: &HashSet<ExecutableKey>,
    executables: &HashSet<ExecutableKey>,
    facts: &ExecutableFacts,
    producer: &LocalCallableProducer,
) -> Vec<(ExecutableKey, CallableSurface)> {
    let Some(capture_tys) = producer
        .captures
        .iter()
        .copied()
        .map(|capture| facts.analysis.value_types.get(&capture).copied())
        .collect::<Option<Vec<_>>>()
    else {
        return Vec::new();
    };
    let mut out = executables
        .iter()
        .filter(|candidate| {
            locally_called.contains(candidate)
                && candidate.need == ExecutableNeed::Value
                && candidate.activation.function == producer.function
                && candidate.activation.input.starts_with(capture_tys.as_slice())
                && candidate.activation.input.len() >= capture_tys.len()
        })
        .map(|candidate| {
            let inputs = candidate.activation.input[capture_tys.len()..]
                .iter()
                .copied()
                .map(|ty| world.types_mut().alpha_normalize_vars(&ty))
                .collect();
            (candidate.clone(), CallableSurface::new(inputs))
        })
        .collect::<Vec<_>>();
    out.sort_by_key(|(key, _)| executable_sort_key(key));
    out.dedup_by(|(left_key, _), (right_key, _)| left_key == right_key);
    out
}

fn callable_flow_resolutions(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    facts: &ExecutableFacts,
    producer: &LocalCallableProducer,
    surfaces: &BTreeSet<CallableSurface>,
    reads: &mut Vec<FactKey>,
    waits: &mut HashSet<FactKey>,
    follow_up: &mut HashSet<Job>,
) -> Vec<ExecutableKey> {
    if surfaces.is_empty() {
        return Vec::new();
    }
    if !world.require_activation_key_facts(producer.function, reads, waits, follow_up) {
        return Vec::new();
    }
    let Some(capture_tys) = producer
        .captures
        .iter()
        .copied()
        .map(|capture| facts.analysis.value_types.get(&capture).copied())
        .collect::<Option<Vec<_>>>()
    else {
        return Vec::new();
    };
    surfaces
        .iter()
        .map(|surface| {
            let mut inputs = capture_tys.clone();
            inputs.extend(surface.inputs.iter().copied());
            ExecutableKey {
                activation: world.activation_key(executable.activation.root, producer.function, &inputs),
                need: ExecutableNeed::Value,
            }
        })
        .collect()
}

fn executable_sort_key(executable: &ExecutableKey) -> (u32, Vec<Ty>, u8, usize) {
    let need = match executable.need {
        ExecutableNeed::Value => (0, 0),
        ExecutableNeed::TupleFields(arity) => (1, arity),
    };
    (
        executable.activation.function.as_u32(),
        executable.activation.input.clone(),
        need.0,
        need.1,
    )
}

fn extend_unique<T: PartialEq>(target: &mut Vec<T>, values: Vec<T>) {
    for value in values {
        if !target.contains(&value) {
            target.push(value);
        }
    }
}

fn local_callable_producers(body: &LoweredBody) -> HashMap<ValueId, LocalCallableProducer> {
    let mut producers = HashMap::new();
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return producers;
    };
    for clause in clauses {
        for step in &clause.projections {
            if let Some((value, producer)) = step_local_callable_producer(step) {
                producers.insert(value, producer);
            }
        }
    }
    for entry in entries {
        for step in &entry.steps {
            if let Some((value, producer)) = step_local_callable_producer(step) {
                producers.insert(value, producer);
            }
        }
    }
    producers
}

fn step_local_callable_producer(step: &LoweredStep) -> Option<(ValueId, LocalCallableProducer)> {
    match step {
        LoweredStep::FunctionRef { value, function } => Some((
            *value,
            LocalCallableProducer {
                function: *function,
                captures: Box::default(),
            },
        )),
        LoweredStep::Lambda {
            value,
            function,
            captures,
        } => Some((
            *value,
            LocalCallableProducer {
                function: *function,
                captures: captures.clone().into_boxed_slice(),
            },
        )),
        _ => None,
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
        .or_insert_with(|| vec![RuntimeDemand::ignore(); observed.len()]);
    if slot.len() < observed.len() {
        slot.resize(observed.len(), RuntimeDemand::ignore());
    }
    for (existing, observed) in slot.iter_mut().zip(observed.iter()) {
        existing.join_assign(observed);
    }
}

fn record_entry_capture_demands(
    out: &mut ExecutableRuntimeDemand,
    entry_id: ControlEntryId,
    observed: &[RuntimeDemand],
) {
    let slot = out
        .entry_capture_demands
        .entry(entry_id)
        .or_insert_with(|| vec![RuntimeDemand::ignore(); observed.len()]);
    if slot.len() < observed.len() {
        slot.resize(observed.len(), RuntimeDemand::ignore());
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
    live.remove(&value).unwrap_or(RuntimeDemand::ignore())
}
