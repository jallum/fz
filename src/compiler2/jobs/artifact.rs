//! Compiler2 artifact projection jobs.
//!
//! This module produces executable-scoped backend products on demand. Each
//! producer names the exact fact or product it needs instead of deriving a
//! root-wide projection stack.

use crate::compiler2::ValueMap;
use crate::fast_hash::{HashMap, HashSet};
use std::rc::Rc;

use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::extern_contract::extern_ty_from_name;
use crate::parser::lexer::Tok;
use crate::source::Span;

use super::super::artifact::{
    AbiReadyCallEdge, AbiReadyExecutable, AbiValueRepr, BackendReturnLayout, BackendSemanticInputLayout,
    BackendValueLayout, CallEdge, CallReturnFlow, CallTarget, ClosureCallEdge, DirectCallEdge, DispatchCallArm,
    DispatchCallEdge, EffectSummary, MaterializedCallEdge, MaterializedExecutable, MaterializedExecutableTransport,
    PositionedCallableConstructionOwner, TransportLayouts,
};
use super::super::body::{
    CallArg, CallSiteId, CaptureOwner, ControlDestination, ControlEntryId, ControlEntryOrigin, DirectCallee,
    LoweredBody, LoweredStep, LoweredTail, ValueId, ValueRole,
};
use super::super::callsite_dispatch::{CallDestinations, call_destinations};
use super::super::drive::{FactKey, emit_job_diagnostic};
use super::super::executable_facts::ExecutableFacts;
use super::super::identity::{ExecutableKey, ExecutableNeed, RootId};
use super::super::pull::{
    ProductKey, ProductReadContext, ProductValue, PullOutcome, PullWait, RecursiveProductRead, TransportLayout,
};
#[cfg(test)]
use super::super::semantic::CallSiteKey;
use super::super::semantic::ExecutableRuntimeDemand;
use super::super::semantic::{ActivationAnalysis, CallSiteSummary, CallTargetSummary, SelectedCallee};
#[cfg(test)]
use super::super::transport::ShapeDescr;
use super::super::transport::{ExecutableSymbol, PhysicalLaneSource, TransportPosition};
use super::super::types::{Ty, Types};
use super::super::world::World;
use super::transport::{ClosureCallForm, closure_call_form, whole_value_layout};
use fz_engine::FactUse;
use fz_engine::FatalError;
use fz_engine::SemanticOrd;

pub(crate) fn produce_materialized_executable_product(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    executable: &ExecutableKey,
) -> PullOutcome {
    let mut waits = Vec::new();
    let executable_facts = context.read_executable_facts(world, executable);
    if executable_facts.is_none() {
        waits.push(PullWait::Fact(FactUse::settled(FactKey::ExecutableFacts(
            executable.clone(),
        ))));
    }
    let return_fact = FactKey::ReturnType(executable.activation.clone());
    if !context.read_fact(world, FactUse::settled(return_fact.clone())) {
        waits.push(PullWait::Fact(FactUse::settled(return_fact)));
    }
    let runtime_demand = context.read_runtime_demand_fact(world, executable);
    if runtime_demand.is_none() {
        waits.push(PullWait::Fact(FactUse::settled(FactKey::RuntimeDemand(
            executable.clone(),
        ))));
    }
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }

    let executable_facts = executable_facts.expect("executable-facts wait should have been satisfied");
    let analysis = executable_facts.analysis();
    let return_ty = world
        .activation_return(&executable.activation)
        .unwrap_or_else(|| world.types_mut().none());
    let extern_wire = executable_facts.extern_wire().cloned();
    let pruned = executable_facts.pruned_body();
    let body = pruned.body.clone();
    let mut transport_positions = vec![TransportPosition::ExecutableReturn {
        executable: ExecutableSymbol::new(executable),
    }];
    transport_positions.extend(required_call_edge_transport_positions(
        executable,
        &executable_facts,
        &body,
    ));
    let position_layouts = match read_transport_layouts(world, context, transport_positions) {
        Ok(position_layouts) => position_layouts,
        Err(transport_waits) => {
            waits.extend(transport_waits);
            TransportLayouts::default()
        }
    };
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }
    let transport = materialized_executable_transport(position_layouts, executable);
    let transport_plan = &transport.position_layouts;
    // A call this program cannot lower has already said why through a
    // diagnostic; the root stops on that diagnostic rather than unwinding here.
    let Ok(call_edges) = materialize_call_edges(
        world,
        tel,
        context.session().root().expect("executable products are root-scoped"),
        transport_plan,
        executable,
        analysis,
        executable_facts.callsites(),
        executable_facts.callsite_needs(),
        &body,
        &pruned.original_entry_ids,
    ) else {
        return PullOutcome::Failed;
    };
    let call_edges = call_edges.expect("product materialization should have complete call edges after waits");
    let retained_values = super::body::retained_value_ids(&body);
    let value_types: ValueMap<Ty> = analysis
        .value_types
        .iter()
        .filter(|(value, _)| retained_values.contains(*value))
        .map(|(value, ty)| (value, *ty))
        .collect();
    let effects = local_effects(&body, extern_wire.as_ref(), &call_edges);
    let struct_modules = reachable_struct_modules(world.types(), executable, return_ty, &value_types, &call_edges);
    let materialized = Rc::new(MaterializedExecutable {
        entry_dispatch: executable_facts.entry_dispatch().cloned(),
        return_ty,
        runtime_demand: runtime_demand.expect("runtime-demand fact wait should have been satisfied"),
        transport,
        original_entry_ids: pruned.original_entry_ids.clone(),
        value_types,
        effects,
        struct_modules,
        body,
        extern_wire,
        call_edges,
    });
    PullOutcome::Produced(ProductValue::MaterializedExecutable(materialized))
}

fn reachable_struct_modules(
    types: &Types,
    executable: &ExecutableKey,
    return_ty: Ty,
    value_types: &ValueMap<Ty>,
    call_edges: &HashMap<CallSiteId, MaterializedCallEdge>,
) -> Box<[fz_runtime::module_name::ModuleName]> {
    let mut type_roots = Vec::with_capacity(2 + value_types.len() + call_edges.len() * 2);
    type_roots.extend([executable.activation.arrow, return_ty]);
    type_roots.extend(value_types.values().copied());
    for edge in call_edges.values() {
        type_roots.push(edge.return_ty());
        match edge.target() {
            CallEdge::Direct(direct) => {
                if let Some(callee) = direct.callee.local() {
                    type_roots.push(callee.activation.arrow);
                }
            }
            CallEdge::Dispatch(dispatch) => {
                for arm in &dispatch.arms {
                    if let Some(callee) = arm.callee.local() {
                        type_roots.push(callee.activation.arrow);
                    }
                }
            }
            CallEdge::Indirect(_) => {}
        }
    }
    types.struct_modules(type_roots).into_iter().collect()
}

pub(crate) fn produce_executable_effects_product<T: crate::telemetry::Telemetry>(
    tel: &T,
    context: &mut ProductReadContext<'_>,
    executable: &ExecutableKey,
    types: &Types,
) -> PullOutcome {
    let materialized_key = ProductKey::MaterializedExecutable(executable.clone());
    let materialized = match context.read_product(tel, &materialized_key, types) {
        Some(ProductValue::MaterializedExecutable(materialized)) => Rc::clone(materialized),
        Some(other) => panic!("materialized executable product produced unexpected value {other:?}"),
        None => return PullOutcome::wait_on_product(materialized_key),
    };
    let current = ProductKey::ExecutableEffects(executable.clone());
    let mut effects = materialized.effects;
    let mut waits = Vec::new();
    let mut recursive_group: Option<Vec<ProductKey>> = None;
    let mut callees = materialized
        .call_edges
        .values()
        .flat_map(|edge| edge.target().local_callees())
        .cloned()
        .collect::<Vec<_>>();
    callees.sort_by(|left, right| left.semantic_cmp(right, types));
    callees.dedup();
    for callee in callees {
        let key = ProductKey::ExecutableEffects(callee);
        match context.read_recursive_product(tel, &key, &current, types) {
            RecursiveProductRead::Ready(ProductValue::ExecutableEffects(callee_effects)) => {
                effects.union_with(*callee_effects);
            }
            RecursiveProductRead::Ready(other) => {
                panic!("executable effects product produced unexpected value {other:?}")
            }
            RecursiveProductRead::Waiting => waits.push(PullWait::Product(key)),
            RecursiveProductRead::Group(members) => {
                if let Some(previous) = &recursive_group {
                    assert!(
                        previous.iter().all(|member| members.contains(member)),
                        "recording another read cannot shrink a recursive group"
                    );
                }
                recursive_group = Some(members);
            }
        }
    }
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }
    let Some(members) = recursive_group else {
        return PullOutcome::Produced(ProductValue::ExecutableEffects(effects));
    };
    let mut external_waits = Vec::new();
    for (key, value) in context.recorded_recursive_group_inputs(&current, &members, types) {
        match (key.clone(), value) {
            (ProductKey::MaterializedExecutable(_), Some(ProductValue::MaterializedExecutable(materialized))) => {
                effects.union_with(materialized.effects);
            }
            (ProductKey::ExecutableEffects(_), Some(ProductValue::ExecutableEffects(callee_effects))) => {
                effects.union_with(callee_effects);
            }
            (ProductKey::ExecutableEffects(_), None) => external_waits.push(PullWait::Product(key)),
            (ProductKey::MaterializedExecutable(_), None) => {
                panic!("a recursive effect member must have its local materialized product")
            }
            (key, value) => panic!("an executable-effects group recorded unexpected input {key:?}: {value:?}"),
        }
    }
    if !external_waits.is_empty() {
        return PullOutcome::Waiting(external_waits);
    }
    let values = members
        .iter()
        .map(|_| ProductValue::ExecutableEffects(effects))
        .collect();
    PullOutcome::Produced(context.stage_recursive_group(&current, &members, values))
}

pub(crate) fn produce_abi_executable_product(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    executable: &ExecutableKey,
) -> PullOutcome {
    let mut waits = Vec::new();
    let materialized_key = ProductKey::MaterializedExecutable(executable.clone());
    let materialized = match context.read_product(tel, &materialized_key, world.types()) {
        Some(ProductValue::MaterializedExecutable(materialized)) => Some(Rc::clone(materialized)),
        Some(other) => panic!("materialized executable product produced unexpected value {other:?}"),
        None => {
            waits.push(PullWait::Product(materialized_key));
            None
        }
    };
    let effects_key = ProductKey::ExecutableEffects(executable.clone());
    let effects = match context.read_product(tel, &effects_key, world.types()) {
        Some(ProductValue::ExecutableEffects(effects)) => Some(*effects),
        Some(other) => panic!("executable effects product produced unexpected value {other:?}"),
        None => {
            waits.push(PullWait::Product(effects_key));
            None
        }
    };
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }

    let materialized = materialized.expect("materialized executable product wait should have been satisfied");
    let effects = effects.expect("executable effects product wait should have been satisfied");
    let mut transport_positions = materialized
        .transport
        .position_layouts
        .positions()
        .cloned()
        .collect::<Vec<_>>();
    transport_positions.extend(required_executable_transport_positions(executable, &materialized));
    let position_layouts = match read_transport_layouts(world, context, transport_positions) {
        Ok(position_layouts) => position_layouts,
        Err(transport_waits) => {
            waits.extend(transport_waits);
            TransportLayouts::default()
        }
    };
    let transport = waits
        .is_empty()
        .then(|| materialized_executable_transport(position_layouts, executable));
    let mut callable_owners = Vec::new();
    let owner_transport = transport.as_ref().unwrap_or(&materialized.transport);
    let facts = context
        .read_executable_facts(world, executable)
        .expect("materialized prerequisite has settled executable facts");
    for (position, layout) in owner_transport.position_layouts.iter() {
        if position.executable() != &owner_transport.executable {
            continue;
        }
        let local_flow =
            super::transport::local_callable_construction(&facts, &materialized.runtime_demand, position).is_some();
        if !local_flow && !world.shape_contains_callable(layout.structural) {
            continue;
        }
        let key = ProductKey::CallableConstruction(position.clone());
        match context.read_product(tel, &key, world.types()) {
            Some(ProductValue::CallableConstruction(owner)) => {
                callable_owners.push(PositionedCallableConstructionOwner {
                    position: position.clone(),
                    owner: Rc::clone(owner),
                })
            }
            Some(other) => panic!("callable construction product produced unexpected value {other:?}"),
            None => waits.push(PullWait::Product(key)),
        }
    }
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }
    let transport = transport.expect("complete transport reads must construct the ABI transport");
    let plan = build_executable_abi_plan(world, executable, &materialized, &transport);
    let abi = Rc::new(
        build_abi_executable(
            materialized,
            effects,
            transport,
            plan,
            callable_owners.into_boxed_slice(),
        )
        .expect("per-executable ABI derivation should not require root fan-in"),
    );
    PullOutcome::Produced(ProductValue::AbiExecutable(abi))
}

#[derive(Debug, Clone)]
struct ExecutableAbiPlan {
    param_reprs: Vec<AbiValueRepr>,
    semantic_inputs: Box<[BackendSemanticInputLayout]>,
    return_layout: BackendReturnLayout,
    return_endpoints: Box<[(TransportPosition, BackendReturnLayout)]>,
    value_layouts: ValueMap<BackendValueLayout>,
}

/// The pruned body an executable's positions are read from, with what names
/// them: the executable, the ids its entries had before pruning, and the
/// demand on its inputs.
struct LocalPositions<'a> {
    executable: &'a ExecutableKey,
    body: &'a LoweredBody,
    original_entry_ids: &'a [ControlEntryId],
    runtime_demand: &'a ExecutableRuntimeDemand,
}

impl<'a> LocalPositions<'a> {
    fn of_materialized(executable: &'a ExecutableKey, materialized: &'a MaterializedExecutable) -> Self {
        Self {
            executable,
            body: &materialized.body,
            original_entry_ids: &materialized.original_entry_ids,
            runtime_demand: &materialized.runtime_demand,
        }
    }

    /// The id transport positions use for the body's entry `entry`.
    fn original_entry_id(&self, entry: ControlEntryId) -> ControlEntryId {
        self.original_entry_ids
            .get(entry.as_u32() as usize)
            .copied()
            .unwrap_or(entry)
    }
}

/// Every position of `executable` read beside its inputs and its return: what
/// its call edges, entry captures, resumes and local backend need, and every
/// value its body retains -- the callable-construction owners of other
/// executables read the values their sources name. An executable's body fact
/// holds the layout at each.
pub(super) fn body_transport_positions(
    executable: &ExecutableKey,
    facts: &ExecutableFacts,
    runtime_demand: &ExecutableRuntimeDemand,
) -> Vec<TransportPosition> {
    let pruned = facts.pruned_body();
    let local = LocalPositions {
        executable,
        body: &pruned.body,
        original_entry_ids: &pruned.original_entry_ids,
        runtime_demand,
    };
    let symbol = ExecutableSymbol::new(executable);
    let mut positions = required_call_edge_transport_positions(executable, facts, &pruned.body);
    positions.extend(required_entry_capture_transport_positions(&local));
    positions.extend(required_resume_transport_positions(&local));
    positions.extend(required_local_backend_transport_positions(&local));
    positions.extend(
        super::body::retained_value_ids(&pruned.body)
            .iter()
            .map(|value| TransportPosition::Value {
                executable: symbol.clone(),
                value,
            }),
    );
    positions.retain(|position| {
        position.executable() == &symbol
            && !matches!(
                position,
                TransportPosition::ExecutableInput { .. } | TransportPosition::ExecutableReturn { .. }
            )
    });
    let mut seen = HashSet::default();
    positions.retain(|position| seen.insert(position.clone()));
    positions
}
fn materialized_executable_transport(
    position_layouts: TransportLayouts,
    executable: &ExecutableKey,
) -> MaterializedExecutableTransport {
    let symbol = ExecutableSymbol::new(executable);
    let mut input_positions = Vec::new();
    let mut return_position = None;
    let mut resume_positions = Vec::new();
    let mut return_payload_positions = Vec::new();
    let mut entry_capture_positions = Vec::new();
    let mut call_arg_positions = Vec::new();
    let mut value_positions = Vec::new();
    for position in position_layouts.positions() {
        if position.executable() != &symbol {
            continue;
        }
        match &position {
            TransportPosition::ExecutableInput { .. } => input_positions.push(position.clone()),
            TransportPosition::ExecutableReturn { .. } => return_position = Some(position.clone()),
            TransportPosition::ResumePayload { .. } => resume_positions.push(position.clone()),
            TransportPosition::ReturnPayload { .. } => return_payload_positions.push(position.clone()),
            TransportPosition::EntryCapture { .. } => entry_capture_positions.push(position.clone()),
            TransportPosition::CallArg { .. } => call_arg_positions.push(position.clone()),
            TransportPosition::Value { .. } => value_positions.push(position.clone()),
        }
    }
    MaterializedExecutableTransport {
        executable: symbol,
        position_layouts,
        input_positions,
        return_position: return_position.unwrap_or_else(|| {
            panic!("transport plan should publish one return position for materialized executable {executable:?}")
        }),
        resume_positions,
        return_payload_positions,
        entry_capture_positions,
        call_arg_positions,
        value_positions,
    }
}

fn required_entry_capture_transport_positions(local: &LocalPositions<'_>) -> Vec<TransportPosition> {
    let LoweredBody::Clauses { entries, .. } = local.body;
    let symbol = ExecutableSymbol::new(local.executable);
    let mut positions = Vec::new();
    for (entry_index, entry) in entries.iter().enumerate() {
        let entry_id = ControlEntryId::from_u32(entry_index as u32);
        let owned = entry
            .capture_owners
            .iter()
            .enumerate()
            .filter(|(capture_index, owner)| {
                **owner
                    == CaptureOwner {
                        entry: entry_id,
                        index: *capture_index,
                    }
            });
        for (capture_index, _) in owned {
            positions.push(TransportPosition::EntryCapture {
                executable: symbol.clone(),
                entry: local.original_entry_id(entry_id),
                capture_index,
            });
        }
    }
    positions
}

/// Every transport position an executable's ABI must have the layout of before
/// it can be lowered: its input, entry-capture, resume, and local-backend
/// positions (its return position is already read by the materialized
/// product). Their layouts are the exact positioned answers embedded in the
/// executable's ABI.
fn required_executable_transport_positions(
    executable: &ExecutableKey,
    materialized: &MaterializedExecutable,
) -> Vec<TransportPosition> {
    let local = LocalPositions::of_materialized(executable, materialized);
    let mut positions = Vec::new();
    positions.extend(required_executable_input_transport_positions(&local));
    positions.extend(required_entry_capture_transport_positions(&local));
    positions.extend(required_resume_transport_positions(&local));
    positions.extend(required_local_backend_transport_positions(&local));
    positions
}

fn required_executable_input_transport_positions(local: &LocalPositions<'_>) -> Vec<TransportPosition> {
    let symbol = ExecutableSymbol::new(local.executable);
    local
        .runtime_demand
        .input_demands
        .iter()
        .enumerate()
        .filter_map(|(semantic_index, demand)| {
            if demand.is_ignore() {
                return None;
            }
            let position = TransportPosition::ExecutableInput {
                executable: symbol.clone(),
                semantic_index,
            };
            Some(position)
        })
        .collect()
}

/// Each delivered resume an executable can reach has one payload position.
/// Its layout is the payload value's own: whoever delivers there -- one call,
/// several calls, local values, or a mix -- the value is their join.
fn required_resume_transport_positions(local: &LocalPositions<'_>) -> Vec<TransportPosition> {
    let LoweredBody::Clauses { entries, .. } = local.body;
    let symbol = ExecutableSymbol::new(local.executable);
    entries
        .iter()
        .enumerate()
        .filter(|(_, entry)| matches!(entry.origin, ControlEntryOrigin::DeliveredResume { .. }))
        // A resume nothing can reach has no payload to lay out; the backend
        // lowers it as a plain unreachable branch.
        .filter(|(_, entry)| !matches!(&entry.tail, LoweredTail::Unreachable))
        .map(|(entry_index, _)| TransportPosition::ResumePayload {
            executable: symbol.clone(),
            entry: local.original_entry_id(ControlEntryId::from_u32(entry_index as u32)),
        })
        .collect()
}

fn required_local_backend_transport_positions(local: &LocalPositions<'_>) -> Vec<TransportPosition> {
    let LoweredBody::Clauses { clauses, entries, .. } = local.body;
    let symbol = ExecutableSymbol::new(local.executable);
    let mut positions = Vec::new();
    positions.extend(
        local
            .runtime_demand
            .callable_flows
            .keys()
            .chain(
                local
                    .runtime_demand
                    .callable_flows
                    .values()
                    .flat_map(|flow| flow.captures.iter().copied()),
            )
            .map(|value| TransportPosition::Value {
                executable: symbol.clone(),
                value,
            }),
    );
    for value in entries
        .iter()
        .flat_map(|entry| entry.steps.iter())
        .flat_map(super::super::body::step_defined_values)
    {
        let position = TransportPosition::Value {
            executable: symbol.clone(),
            value,
        };
        positions.push(position);
    }
    positions.extend(
        entries
            .iter()
            .flat_map(|entry| entry.tail.dispatch_outcome_edges())
            .flat_map(|edge| edge.arguments.iter())
            .chain(clauses.iter().flat_map(|clause| clause.arguments.iter()))
            .filter(|argument| argument.role == ValueRole::Semantic)
            .map(|argument| TransportPosition::Value {
                executable: symbol.clone(),
                value: argument.parameter,
            }),
    );
    for entry in entries {
        let (callsite, args, value) = match &entry.tail {
            LoweredTail::DirectCall {
                value, callsite, args, ..
            }
            | LoweredTail::ClosureCall {
                value, callsite, args, ..
            } => (*callsite, args, *value),
            LoweredTail::Value { .. }
            | LoweredTail::If { .. }
            | LoweredTail::Dispatch { .. }
            | LoweredTail::Receive(_)
            | LoweredTail::Try { .. }
            | LoweredTail::Unreachable => continue,
        };
        let value_position = TransportPosition::Value {
            executable: symbol.clone(),
            value,
        };
        positions.push(value_position);
        for semantic_index in 0..args.len() {
            let position = TransportPosition::CallArg {
                executable: symbol.clone(),
                callsite,
                semantic_index,
            };
            positions.push(position);
        }
        let return_payload = TransportPosition::ReturnPayload {
            executable: symbol.clone(),
            callsite,
        };
        positions.push(return_payload);
    }
    positions
}

/// The layout at each of `positions`, read from the transport facts that hold
/// them, or the facts still to wait for.
fn read_transport_layouts(
    world: &World,
    context: &mut ProductReadContext<'_>,
    positions: impl IntoIterator<Item = TransportPosition>,
) -> Result<TransportLayouts, Vec<PullWait>> {
    let root = context.session().root().expect("transport reads are root-scoped");
    let mut positions = positions
        .into_iter()
        .collect::<HashSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    positions.sort_by(|left, right| left.semantic_cmp(right, world.types()));
    let mut layouts = Vec::with_capacity(positions.len());
    let mut waits: Vec<PullWait> = Vec::new();
    let mut settled: HashMap<FactKey, bool> = HashMap::default();
    for position in positions {
        let owner = super::transport::executable_key_for_transport_position(root, &position);
        let fact = super::transport_layouts::layout_fact(&owner, &position);
        let ready = *settled.entry(fact.clone()).or_insert_with_key(|fact| {
            let fact = FactUse::settled(fact.clone());
            let ready = context.read_fact(world, fact.clone());
            if !ready {
                waits.push(PullWait::Fact(fact));
            }
            ready
        });
        if !ready {
            continue;
        }
        let layout = super::transport_layouts::fact_layouts(world, &fact)
            .and_then(|held| held.layout_at(&position))
            .unwrap_or_else(|| panic!("the transport fact of {owner:?} publishes {position:?}"));
        layouts.push((position, layout));
    }
    if waits.is_empty() {
        Ok(layouts.into_iter().collect())
    } else {
        Err(waits)
    }
}

fn required_call_edge_transport_positions(
    executable: &ExecutableKey,
    facts: &ExecutableFacts,
    body: &LoweredBody,
) -> Vec<TransportPosition> {
    let LoweredBody::Clauses { entries, .. } = body;
    let caller_symbol = ExecutableSymbol::new(executable);
    let callsite_needs = facts.callsite_needs();
    let summaries = facts.callsites();
    let mut positions = HashSet::default();
    for entry in entries {
        match &entry.tail {
            LoweredTail::DirectCall { callsite, dest, .. } => {
                record_return_flow_transport_positions(
                    &mut positions,
                    &caller_symbol,
                    *callsite,
                    dest,
                    summaries.get(callsite).into_iter().flat_map(|summary| {
                        summary.targets.iter().filter_map(|target| {
                            target.runtime_executable(
                                callsite_needs.get(callsite).copied().unwrap_or(ExecutableNeed::Value),
                            )
                        })
                    }),
                );
            }
            LoweredTail::ClosureCall {
                callsite, callee, dest, ..
            } => {
                positions.insert(TransportPosition::Value {
                    executable: caller_symbol.clone(),
                    value: *callee,
                });
                for (semantic_index, _) in body.call_args(*callsite).into_iter().flatten().enumerate() {
                    positions.insert(TransportPosition::CallArg {
                        executable: caller_symbol.clone(),
                        callsite: *callsite,
                        semantic_index,
                    });
                }
                let callees = summaries
                    .get(callsite)
                    .into_iter()
                    .flat_map(|summary| {
                        summary.targets.iter().filter_map(|target| {
                            target.runtime_executable(
                                callsite_needs.get(callsite).copied().unwrap_or(ExecutableNeed::Value),
                            )
                        })
                    })
                    .collect::<Vec<_>>();
                record_return_flow_transport_positions(&mut positions, &caller_symbol, *callsite, dest, callees);
            }
            LoweredTail::Value { .. }
            | LoweredTail::If { .. }
            | LoweredTail::Dispatch { .. }
            | LoweredTail::Receive(_)
            | LoweredTail::Try { .. }
            | LoweredTail::Unreachable => {}
        }
    }
    positions.into_iter().collect()
}

fn record_return_flow_transport_positions(
    positions: &mut HashSet<TransportPosition>,
    caller_symbol: &ExecutableSymbol,
    callsite: CallSiteId,
    dest: &ControlDestination,
    callees: impl IntoIterator<Item = ExecutableKey>,
) {
    let callee_symbols = callees.into_iter().map(|callee| ExecutableSymbol::new(&callee));
    for position in return_flow_transport_positions(caller_symbol, callsite, dest, callee_symbols) {
        positions.insert(position);
    }
}

fn return_flow_transport_positions(
    caller: &ExecutableSymbol,
    callsite: CallSiteId,
    dest: &ControlDestination,
    callees: impl IntoIterator<Item = ExecutableSymbol>,
) -> Vec<TransportPosition> {
    let ControlDestination::Return = dest else {
        return Vec::new();
    };
    let mut positions = vec![
        TransportPosition::ExecutableReturn {
            executable: caller.clone(),
        },
        TransportPosition::ReturnPayload {
            executable: caller.clone(),
            callsite,
        },
    ];
    positions.extend(
        callees
            .into_iter()
            .map(|callee| TransportPosition::ExecutableReturn { executable: callee }),
    );
    positions
}

fn materialize_call_edges(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    transport_plan: &TransportLayouts,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    summaries: &HashMap<CallSiteId, CallSiteSummary>,
    callsite_needs: &HashMap<CallSiteId, ExecutableNeed>,
    body: &LoweredBody,
    original_entry_ids: &[ControlEntryId],
) -> Result<Option<HashMap<CallSiteId, MaterializedCallEdge>>, FatalError> {
    let mut call_edges = HashMap::default();
    let LoweredBody::Clauses { entries, .. } = body;
    for entry in entries {
        match &entry.tail {
            LoweredTail::DirectCall {
                callsite, callee, dest, ..
            } => {
                let Some(edge) = materialize_direct_call_edge(
                    world,
                    tel,
                    root_id,
                    transport_plan,
                    executable,
                    analysis,
                    summaries,
                    callsite_needs.get(callsite).copied().unwrap_or(ExecutableNeed::Value),
                    *callsite,
                    dest,
                    original_entry_ids,
                    body,
                )?
                else {
                    return Err(match callee {
                        DirectCallee::Function(callee) => call_reaches_no_target(world, tel, *callee),
                        DirectCallee::ModuleValue { .. } => incomplete_semantic_plan(
                            tel,
                            root_id,
                            "a call on a module value settled no function to call",
                        ),
                    });
                };
                call_edges.insert(*callsite, edge);
            }
            LoweredTail::ClosureCall {
                value,
                callsite,
                callee,
                dest,
                ..
            } => {
                let callee_position = TransportPosition::Value {
                    executable: ExecutableSymbol::new(executable),
                    value: *callee,
                };
                let callee_layout = require_transport_layout(tel, root_id, transport_plan, &callee_position)?;
                let edge = materialize_closure_call_edge(
                    world,
                    tel,
                    root_id,
                    transport_plan,
                    executable,
                    analysis,
                    summaries,
                    callee_layout,
                    callsite_needs.get(callsite).copied().unwrap_or(ExecutableNeed::Value),
                    *callsite,
                    *value,
                    dest,
                    original_entry_ids,
                    body,
                )?;
                call_edges.insert(*callsite, edge);
            }
            LoweredTail::Value { .. }
            | LoweredTail::If { .. }
            | LoweredTail::Dispatch { .. }
            | LoweredTail::Receive(_)
            | LoweredTail::Try { .. }
            | LoweredTail::Unreachable => {}
        }
    }
    Ok(Some(call_edges))
}

fn materialize_direct_call_edge(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    transport_plan: &TransportLayouts,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    summaries: &HashMap<CallSiteId, CallSiteSummary>,
    need: ExecutableNeed,
    callsite: CallSiteId,
    dest: &ControlDestination,
    original_entry_ids: &[ControlEntryId],
    body: &LoweredBody,
) -> Result<Option<MaterializedCallEdge>, FatalError> {
    // One door: a callsite that named no targets -- never reached, proven
    // dead, or reached and still unresolved -- materializes no edge.
    //
    // In TAIL position the caller treats that as fatal and names the callee
    // (`call_reaches_no_target`). That rests on the third case above --
    // "reached and still unresolved" -- not occurring by the time edges are
    // materialized. (The `has_fact` pre-test that used to stand here asked a
    // DIFFERENT question: the ledger's, where the store below is lowering's
    // authority and is never pruned. The two diverge only in the
    // ledger-withdrawn/store-stale state, so the store answers alone:
    // fz-kdt.69.2. fz-kdt.69.3 makes the ledger authoritative over exactly
    // this divergence; revisit then.)
    let Some(summary) = summaries.get(&callsite) else {
        return Ok(None);
    };
    // The callsite's DESTINATIONS, not its settled targets: a target the
    // runtime could never route to is no destination at all (fz-kdt.104), and
    // a callsite left with one of them is a direct call.
    let dispatch = match call_destinations(world.types_mut(), summary) {
        Ok(CallDestinations::None) => return Ok(None),
        Ok(CallDestinations::Direct(target)) => {
            let (direct, return_ty) = lower_materialized_call_target(
                world,
                tel,
                root_id,
                transport_plan,
                executable,
                analysis,
                need,
                callsite,
                dest,
                original_entry_ids,
                body,
                target,
            )?;
            return Ok(Some(MaterializedCallEdge::Named {
                target: CallEdge::Direct(direct),
                return_ty,
            }));
        }
        Ok(CallDestinations::Dispatch(dispatch)) => dispatch,
        Err(error) => {
            return Err(incomplete_semantic_plan(
                tel,
                root_id,
                format!(
                    "materialization could not build dispatch for multi-target direct callsite {}: {error:?}",
                    callsite.as_u32()
                ),
            ));
        }
    };
    let mut arms = Vec::with_capacity(dispatch.targets.len());
    for target in dispatch.targets {
        let (direct, _arm_return_ty) = lower_materialized_call_target(
            world,
            tel,
            root_id,
            transport_plan,
            executable,
            analysis,
            need,
            callsite,
            dest,
            original_entry_ids,
            body,
            target,
        )?;
        arms.push(DispatchCallArm {
            callee: direct.callee,
            return_flow: direct.return_flow,
            extern_marshals: direct.extern_marshals,
        });
    }
    let return_ty = summary.settled_return(world.types_mut());
    Ok(Some(MaterializedCallEdge::Named {
        target: CallEdge::Dispatch(Box::new(DispatchCallEdge::new(dispatch.plan, arms))),
        return_ty,
    }))
}

fn materialize_closure_call_edge(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    transport_plan: &TransportLayouts,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    summaries: &HashMap<CallSiteId, CallSiteSummary>,
    callee_layout: TransportLayout,
    need: ExecutableNeed,
    callsite: CallSiteId,
    result_value: ValueId,
    dest: &ControlDestination,
    original_entry_ids: &[ControlEntryId],
    body: &LoweredBody,
) -> Result<MaterializedCallEdge, FatalError> {
    let summary = summaries.get(&callsite);
    // One question decides the call, and `closure_call_form` is where it is
    // asked: can this caller supply the target's capture inputs out of what it
    // holds, and if not, is what it holds a word the seam can open? The form
    // travels with the edge, so native lowering, the interpreter and the
    // boxed-apply contract all emit what this one answer promised.
    match closure_call_form(world, callee_layout, summary, need) {
        // Nothing can be called here, so this call really never happens. Lower
        // it as the dead call it is — every `ClosureCall` tail needs a return
        // flow, and `NoReturn` is the name for one that never returns. Emitting
        // no edge at all instead leaves native lowering with a `Deliver`
        // destination and nothing to deliver (fz-f98.18). An `Unresolved` edge
        // (fz-kdt.69.2) reaches this same answer.
        ClosureCallForm::Dead => {
            let never = world.types_mut().none();
            Ok(MaterializedCallEdge::Closure {
                form: ClosureCallEdge::Dead,
                target: CallEdge::Indirect(CallReturnFlow::NoReturn { local_source: None }),
                return_ty: never,
            })
        }
        // A real callable value reaches this callsite at runtime and the
        // boxed-apply wrapper can call it, however little the analysis managed
        // to name. That is the standing state for a closure that arrived from
        // outside the analysed world — a mailbox message — where no target is
        // ever named and none ever will be: "no targets" there is UNKNOWN, not
        // `none` (fz-kdt.130). It is also where a lambda goes when the tuple
        // carrying it is used whole beside being taken apart.
        ClosureCallForm::Seam => {
            let return_ty =
                public_indirect_return_ty(world, tel, root_id, analysis, summary, callsite, result_value, body)?;
            let return_flow = if world.types().is_empty(&return_ty) {
                CallReturnFlow::NoReturn { local_source: None }
            } else {
                call_return_flow(
                    tel,
                    root_id,
                    transport_plan,
                    executable,
                    None,
                    callsite,
                    dest,
                    original_entry_ids,
                    true,
                )?
            };
            Ok(MaterializedCallEdge::Closure {
                form: ClosureCallEdge::Seam,
                target: CallEdge::Indirect(return_flow),
                return_ty,
            })
        }
        // The form came from the callsite's one owned target and carries that
        // summary row, so the direct edge is lowered against the row the
        // decision was made from.
        ClosureCallForm::Direct { edge, target } => {
            let (direct, return_ty) = lower_materialized_call_target(
                world,
                tel,
                root_id,
                transport_plan,
                executable,
                analysis,
                need,
                callsite,
                dest,
                original_entry_ids,
                body,
                target,
            )?;
            Ok(MaterializedCallEdge::Closure {
                form: edge,
                target: CallEdge::Direct(direct),
                return_ty,
            })
        }
    }
}

/// Whether every callable the callee can be is a closure of another arity than
/// the call's argument count. Such a call raises where it stands, so it settles
/// no result value, and its return is the empty type.
fn callee_takes_no_call_of_this_arity(
    world: &mut World,
    analysis: &ActivationAnalysis,
    body: &LoweredBody,
    callsite: CallSiteId,
) -> bool {
    let (Some(callee), Some(args)) = (body.closure_call_callee(callsite), body.call_args(callsite)) else {
        return false;
    };
    let Some(callee_ty) = analysis.value_types.get(&callee).copied() else {
        return false;
    };
    world
        .types_mut()
        .callable_value_clauses(&callee_ty)
        .is_some_and(|clauses| {
            !clauses.is_empty()
                && clauses
                    .iter()
                    .all(|clause| clause.closure.is_some() && clause.args.len() != args.len())
        })
}

fn public_indirect_return_ty(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    analysis: &ActivationAnalysis,
    summary: Option<&CallSiteSummary>,
    callsite: CallSiteId,
    result_value: ValueId,
    body: &LoweredBody,
) -> Result<Ty, FatalError> {
    let settled_return = summary.map(|summary| summary.settled_return(world.types_mut()));
    if let Some(return_ty) = settled_return.filter(|return_ty| world.types().is_empty(return_ty)) {
        return Ok(return_ty);
    }
    if callee_takes_no_call_of_this_arity(world, analysis, body, callsite) {
        return Ok(world.types_mut().none());
    }
    let result_ty = analysis.value_types.get(&result_value).copied().ok_or_else(|| {
        incomplete_semantic_plan(
            tel,
            root_id,
            format!(
                "missing semantic result type for public closure callsite {}",
                callsite.as_u32()
            ),
        )
    })?;
    if let Some(settled_return) =
        settled_return.filter(|settled_return| !world.types().is_equivalent(settled_return, &result_ty))
    {
        let settled = world.types().display(&settled_return);
        let semantic = world.types().display(&result_ty);
        return Err(incomplete_semantic_plan(
            tel,
            root_id,
            format!(
                "public closure callsite {} settled return `{settled}` disagrees with its semantic result type `{semantic}`",
                callsite.as_u32()
            ),
        ));
    }
    Ok(result_ty)
}

fn lower_materialized_call_target(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    transport_plan: &TransportLayouts,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    need: ExecutableNeed,
    callsite: CallSiteId,
    dest: &ControlDestination,
    original_entry_ids: &[ControlEntryId],
    body: &LoweredBody,
    target: CallTargetSummary,
) -> Result<(DirectCallEdge<ExecutableKey>, Ty), FatalError> {
    let return_ty = target.settled_return(world.types_mut());
    let (callee, extern_marshals) = match target.callee {
        SelectedCallee::Function(function) => {
            let activation = target.activation.clone().ok_or_else(|| {
                incomplete_semantic_plan(
                    tel,
                    root_id,
                    format!(
                        "function target {} at callsite {} is missing its settled activation",
                        function.as_u32(),
                        callsite.as_u32()
                    ),
                )
            })?;
            let callee = ExecutableKey { activation, need };
            let extern_marshals = if let Some(signature) = world.extern_wire(function) {
                let Some(args) = body.call_args(callsite) else {
                    return Err(incomplete_semantic_plan(
                        tel,
                        root_id,
                        format!(
                            "missing lowered call arguments for extern callsite {}",
                            callsite.as_u32()
                        ),
                    ));
                };
                Some(resolve_extern_marshals(
                    world,
                    tel,
                    root_id,
                    args,
                    &analysis.value_types,
                    &signature.params,
                    signature.variadic,
                )?)
            } else {
                None
            };
            (CallTarget::Local(callee), extern_marshals)
        }
        SelectedCallee::ProviderBoundary(function) => (CallTarget::ProviderBoundary(function), None),
        SelectedCallee::Undefined(undefined) => (CallTarget::Undefined(undefined), None),
    };
    let return_flow = if world.types().is_empty(&return_ty) {
        exact_no_return_flow(&callee)
    } else {
        call_return_flow(
            tel,
            root_id,
            transport_plan,
            executable,
            Some(&callee),
            callsite,
            dest,
            original_entry_ids,
            false,
        )?
    };
    Ok((
        DirectCallEdge {
            callee,
            return_flow,
            extern_marshals,
        },
        return_ty,
    ))
}

fn call_return_flow(
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    transport_plan: &TransportLayouts,
    executable: &ExecutableKey,
    callee: Option<&CallTarget<ExecutableKey>>,
    callsite: CallSiteId,
    dest: &ControlDestination,
    original_entry_ids: &[ControlEntryId],
    public_callable: bool,
) -> Result<CallReturnFlow, FatalError> {
    let caller_symbol = ExecutableSymbol::new(executable);
    match dest {
        ControlDestination::Deliver(entry) => {
            let transport_entry = original_entry_ids
                .get(entry.as_u32() as usize)
                .copied()
                .unwrap_or(*entry);
            let resume = TransportPosition::ResumePayload {
                executable: caller_symbol.clone(),
                entry: transport_entry,
            };
            let source = if public_callable {
                TransportPosition::ReturnPayload {
                    executable: caller_symbol,
                    callsite,
                }
            } else {
                match callee {
                    Some(CallTarget::Local(callee)) => TransportPosition::ExecutableReturn {
                        executable: ExecutableSymbol::new(callee),
                    },
                    Some(CallTarget::ProviderBoundary(_)) => resume.clone(),
                    Some(CallTarget::Undefined(_)) | None => {
                        return Err(incomplete_semantic_plan(
                            tel,
                            root_id,
                            "non-public call return flow has no callee that returns",
                        ));
                    }
                }
            };
            Ok(CallReturnFlow::Deliver {
                source,
                resume,
                entry: *entry,
            })
        }
        ControlDestination::Return => {
            let caller_return = TransportPosition::ExecutableReturn {
                executable: caller_symbol.clone(),
            };
            let payload = TransportPosition::ReturnPayload {
                executable: caller_symbol,
                callsite,
            };
            let source = if public_callable {
                payload.clone()
            } else if let Some(CallTarget::Local(callee)) = callee {
                TransportPosition::ExecutableReturn {
                    executable: ExecutableSymbol::new(callee),
                }
            } else {
                payload.clone()
            };
            let source_layout = require_transport_layout(tel, root_id, transport_plan, &source)?;
            let caller_layout = require_transport_layout(tel, root_id, transport_plan, &caller_return)?;
            let payload_layout = require_transport_layout(tel, root_id, transport_plan, &payload)?;
            if !public_callable && source_layout == caller_layout && source_layout == payload_layout {
                return Ok(CallReturnFlow::Tail {
                    source,
                    payload,
                    caller_return,
                });
            }
            Ok(CallReturnFlow::Continue {
                source,
                payload,
                caller_return,
            })
        }
    }
}

fn exact_no_return_flow(callee: &CallTarget<ExecutableKey>) -> CallReturnFlow {
    let local_source = callee.local().map(|callee| TransportPosition::ExecutableReturn {
        executable: ExecutableSymbol::new(callee),
    });
    CallReturnFlow::NoReturn { local_source }
}

fn require_transport_layout(
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    transport_plan: &TransportLayouts,
    position: &TransportPosition,
) -> Result<super::super::pull::TransportLayout, FatalError> {
    transport_plan.layout_at(position).ok_or_else(|| {
        incomplete_semantic_plan(
            tel,
            root_id,
            format!("missing transport layout for position {position:?}"),
        )
    })
}

fn resolve_extern_marshals(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    args: &[CallArg],
    value_types: &ValueMap<Ty>,
    fixed_params: &[crate::fz_ir::ExternTy],
    variadic: bool,
) -> Result<Vec<crate::fz_ir::ExternTy>, FatalError> {
    let fixed = fixed_params.len();
    let actual = args.len();
    if (!variadic && actual != fixed) || (variadic && actual < fixed) {
        return Err(incomplete_semantic_plan(
            tel,
            root_id,
            format!("extern call expected {} argument(s) but saw {}", fixed, actual),
        ));
    }

    let mut marshals = Vec::with_capacity(actual);
    for (index, arg) in args.iter().enumerate() {
        if index < fixed {
            let expected = fixed_params[index];
            if let Some(ascription) = &arg.ascription {
                let ascribed = parse_extern_ascription(world, tel, root_id, ascription)?;
                if ascribed != expected {
                    return Err(incomplete_semantic_plan(
                        tel,
                        root_id,
                        format!(
                            "extern fixed arg {} ascribed as {:?}, declared as {:?}",
                            index + 1,
                            ascribed,
                            expected
                        ),
                    ));
                }
            }
            marshals.push(expected);
            continue;
        }

        if let Some(ascription) = &arg.ascription {
            let ascribed = parse_extern_ascription(world, tel, root_id, ascription)?;
            if ascribed == crate::fz_ir::ExternTy::F64 {
                return Err(refuse_float_variadic_marshal(tel, root_id));
            }
            marshals.push(ascribed);
            continue;
        }

        let Some(arg_ty) = value_types.get(&arg.value).copied() else {
            return Err(incomplete_semantic_plan(
                tel,
                root_id,
                format!("missing settled type for extern argument value {}", arg.value.as_u32()),
            ));
        };
        marshals.push(resolve_auto_variadic_marshal(world, tel, root_id, arg_ty)?);
    }

    Ok(marshals)
}

fn parse_extern_ascription(
    _world: &World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    body: &crate::ast::TypeExprBody,
) -> Result<crate::fz_ir::ExternTy, FatalError> {
    let Some(tok) = body.0.first().map(|token| &token.tok) else {
        return Err(incomplete_semantic_plan(
            tel,
            root_id,
            "empty extern call-arg ascription",
        ));
    };
    let name = match tok {
        Tok::Ident(name) | Tok::Upper(name) => name.as_str(),
        Tok::Nil => "nil",
        _ => {
            return Err(incomplete_semantic_plan(
                tel,
                root_id,
                format!("unsupported extern call-arg ascription token {:?}", tok),
            ));
        }
    };
    extern_ty_from_name(name)
        .ok_or_else(|| incomplete_semantic_plan(tel, root_id, format!("unknown extern call-arg ascription `{name}`")))
}

fn resolve_auto_variadic_marshal(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    arg_ty: Ty,
) -> Result<crate::fz_ir::ExternTy, FatalError> {
    if world.types().is_integer(&arg_ty) {
        return Ok(crate::fz_ir::ExternTy::I64);
    }
    if world.types().is_floating(&arg_ty) {
        return Err(refuse_float_variadic_marshal(tel, root_id));
    }
    let str_ty = world.types_mut().bitstring();
    if world.types().is_subtype(&arg_ty, &str_ty) {
        return Err(incomplete_semantic_plan(
            tel,
            root_id,
            "binary values need an explicit extern variadic marshal ascription",
        ));
    }
    Err(incomplete_semantic_plan(
        tel,
        root_id,
        "no default extern variadic marshal class for this argument",
    ))
}

fn local_effects(
    body: &LoweredBody,
    extern_wire: Option<&super::super::body::LoweredExtern>,
    call_edges: &HashMap<CallSiteId, MaterializedCallEdge>,
) -> EffectSummary {
    if let Some(signature) = extern_wire {
        return EffectSummary {
            observable: true,
            halts: signature.ret == crate::fz_ir::ExternTy::Never,
            ..EffectSummary::default()
        };
    }
    let LoweredBody::Clauses { entries, .. } = body;
    let mut effects = EffectSummary::default();
    for entry in entries {
        effects.union_with(step_effects(&entry.steps, call_edges));
        effects.union_with(tail_effects(&entry.tail, call_edges));
    }
    effects
}

fn step_effects(steps: &[LoweredStep], _call_edges: &HashMap<CallSiteId, MaterializedCallEdge>) -> EffectSummary {
    let mut effects = EffectSummary::default();
    for step in steps {
        match step {
            LoweredStep::Tuple { .. }
            | LoweredStep::List { .. }
            | LoweredStep::Map { .. }
            | LoweredStep::MapUpdate { .. }
            | LoweredStep::Struct { .. }
            | LoweredStep::Bitstring { .. }
            | LoweredStep::Lambda { .. } => {
                effects.allocates = true;
            }
            _ => {}
        }
    }
    effects
}

fn tail_effects(tail: &LoweredTail, call_edges: &HashMap<CallSiteId, MaterializedCallEdge>) -> EffectSummary {
    let mut effects = EffectSummary::default();
    match tail {
        LoweredTail::ClosureCall { callsite, .. } => {
            // Missing entry ("not computed yet") and an explicit `Indirect`
            // edge (settled-ambiguous, 2+ producers) are both opaque calls
            // from the effects producer's point of view; only a settled
            // single/dispatch target is not.
            let opaque = match call_edges.get(callsite) {
                None => true,
                Some(edge) => matches!(edge.target(), CallEdge::Indirect { .. }),
            };
            if opaque {
                effects.calls_opaque = true;
            }
        }
        LoweredTail::DirectCall { callsite, .. } => {
            if call_edges.get(callsite).is_some_and(call_edge_calls_provider_boundary) {
                effects.calls_opaque = true;
            }
        }
        LoweredTail::Value { .. }
        | LoweredTail::If { .. }
        | LoweredTail::Dispatch { .. }
        | LoweredTail::Receive(_)
        | LoweredTail::Try { .. }
        | LoweredTail::Unreachable => {}
    }
    effects
}

fn call_edge_calls_provider_boundary(edge: &MaterializedCallEdge) -> bool {
    edge.target()
        .callees()
        .any(|callee| matches!(callee, CallTarget::ProviderBoundary(_)))
}

fn build_executable_abi_plan(
    world: &mut World,
    _key: &ExecutableKey,
    executable: &MaterializedExecutable,
    transport: &MaterializedExecutableTransport,
) -> ExecutableAbiPlan {
    let transport_plan = &transport.position_layouts;
    let semantic_inputs = transport
        .input_positions
        .iter()
        .filter_map(|position| {
            let TransportPosition::ExecutableInput { semantic_index, .. } = position else {
                return None;
            };
            let layout = transport_plan
                .layout_at(position)
                .unwrap_or_else(|| panic!("transport plan should publish materialized input position {position:?}"));
            let shape = layout.structural;
            let contract = abi_layout_contract(world, layout);
            Some(BackendSemanticInputLayout {
                semantic_index: *semantic_index,
                layout: BackendValueLayout {
                    structural: shape,
                    carrier: layout.carrier,
                    tys: contract.iter().map(|(ty, _)| *ty).collect(),
                    reprs: contract.iter().map(|(_, repr)| *repr).collect(),
                },
            })
        })
        .collect::<Vec<_>>()
        .into_boxed_slice();
    let param_reprs = semantic_inputs
        .iter()
        .flat_map(|input| input.layout.reprs.iter().copied())
        .collect::<Vec<_>>();
    let return_position = &transport.return_position;
    let return_layout = transport_plan
        .layout_at(return_position)
        .unwrap_or_else(|| panic!("transport plan should publish materialized return position {return_position:?}"));
    let return_contract = abi_layout_contract(world, return_layout);
    let mut value_layouts: ValueMap<BackendValueLayout> = transport
        .value_positions
        .iter()
        .filter_map(|position| {
            let TransportPosition::Value { value, .. } = position else {
                return None;
            };
            let layout = transport_plan
                .layout_at(position)
                .unwrap_or_else(|| panic!("transport plan should publish materialized value position {position:?}"));
            let contract = abi_layout_contract(world, layout);
            Some((
                *value,
                BackendValueLayout {
                    structural: layout.structural,
                    carrier: layout.carrier,
                    tys: contract.iter().map(|(ty, _)| *ty).collect(),
                    reprs: contract.iter().map(|(_, repr)| *repr).collect(),
                },
            ))
        })
        .collect();
    let LoweredBody::Clauses { clauses, entries, .. } = &executable.body;
    for param in entries.iter().flat_map(|entry| {
        let handed_whole = entry.origin.is_handed_parameters();
        entry
            .params
            .iter()
            .copied()
            .filter(move |param| handed_whole || entry.physical_params.contains(param))
    }) {
        let ty = executable
            .value_types
            .get(&param)
            .copied()
            .unwrap_or_else(|| world.types_mut().any());
        if !value_layouts.contains_key(&param) {
            let layout = whole_value_layout(world, ty);
            value_layouts.insert(param, backend_value_layout(world, layout));
        }
    }
    for clause in clauses {
        for (semantic_index, value) in clause.params.iter().copied().enumerate() {
            if let Some(input) = semantic_inputs
                .iter()
                .find(|input| input.semantic_index == semantic_index)
            {
                value_layouts.insert(value, input.layout.clone());
            }
        }
    }

    let return_endpoints = transport
        .return_payload_positions
        .iter()
        .chain(transport.resume_positions.iter())
        .chain(std::iter::once(return_position))
        .map(|position| {
            let layout = transport_plan
                .layout_at(position)
                .unwrap_or_else(|| panic!("transport plan should publish materialized return endpoint {position:?}"));
            let contract = abi_layout_contract(world, layout);
            (
                position.clone(),
                BackendReturnLayout {
                    layout: BackendValueLayout {
                        structural: layout.structural,
                        carrier: layout.carrier,
                        tys: contract.iter().map(|(ty, _)| *ty).collect(),
                        reprs: contract.iter().map(|(_, repr)| *repr).collect(),
                    },
                    diverges: world.types().is_empty(&executable.return_ty),
                },
            )
        })
        .collect::<Vec<_>>();
    ExecutableAbiPlan {
        param_reprs,
        semantic_inputs,
        return_layout: BackendReturnLayout {
            layout: BackendValueLayout {
                structural: return_layout.structural,
                carrier: return_layout.carrier,
                tys: return_contract.iter().map(|(ty, _)| *ty).collect(),
                reprs: return_contract.iter().map(|(_, repr)| *repr).collect(),
            },
            diverges: world.types().is_empty(&executable.return_ty),
        },
        return_endpoints: return_endpoints.into_boxed_slice(),
        value_layouts,
    }
}

fn build_abi_executable(
    materialized: Rc<MaterializedExecutable>,
    effects: EffectSummary,
    transport: MaterializedExecutableTransport,
    plan: ExecutableAbiPlan,
    callable_owners: Box<[PositionedCallableConstructionOwner]>,
) -> Result<AbiReadyExecutable, FatalError> {
    let call_edges = materialized
        .call_edges
        .iter()
        .map(|(callsite, edge)| {
            (
                *callsite,
                match edge {
                    MaterializedCallEdge::Named { target, return_ty } => AbiReadyCallEdge::Named {
                        target: target.clone(),
                        return_ty: *return_ty,
                    },
                    MaterializedCallEdge::Closure {
                        form,
                        target,
                        return_ty,
                    } => AbiReadyCallEdge::Closure {
                        form: form.clone(),
                        target: target.clone(),
                        return_ty: *return_ty,
                    },
                },
            )
        })
        .collect::<HashMap<_, _>>();
    Ok(AbiReadyExecutable {
        materialized,
        param_reprs: plan.param_reprs,
        semantic_inputs: plan.semantic_inputs,
        return_layout: plan.return_layout,
        return_endpoints: plan.return_endpoints,
        transport,
        value_layouts: plan.value_layouts,
        effects,
        call_edges,
        callable_owners,
    })
}

/// The typed lanes a layout occupies, and the physical form each travels in.
/// A carrier lane is always the one public word; a structural lane takes the
/// form its own type asks for.
fn backend_value_layout(world: &mut World, layout: TransportLayout) -> BackendValueLayout {
    let contract = abi_layout_contract(world, layout);
    BackendValueLayout {
        structural: layout.structural,
        carrier: layout.carrier,
        tys: contract.iter().map(|(ty, _)| *ty).collect(),
        reprs: contract.iter().map(|(_, repr)| *repr).collect(),
    }
}

pub(super) fn abi_layout_contract(world: &mut World, layout: TransportLayout) -> Vec<(Ty, AbiValueRepr)> {
    world
        .layout_physical_lanes(layout)
        .into_iter()
        .map(|physical| {
            let ty = world.lane(physical.lane).ty;
            (ty, physical_lane_repr(world, physical.source, ty))
        })
        .collect()
}

/// The form one physical lane travels in: a carrier is always the boxed word,
/// a structural lane takes the form its type gives.
pub(super) fn physical_lane_repr(world: &mut World, source: PhysicalLaneSource, ty: Ty) -> AbiValueRepr {
    match source {
        PhysicalLaneSource::Structural => AbiValueRepr::for_ty(world, ty),
        PhysicalLaneSource::Carrier => AbiValueRepr::ValueRef,
    }
}

/// A tail-position direct call whose callsite settled on no reachable target.
///
/// A protocol call whose receiver no implementation takes is not this: it is a
/// callsite that raises `Protocol.UndefinedError`. What reaches here is a call
/// whose receiver an implementation takes but that implementation does not
/// define the callback.
fn call_reaches_no_target(
    world: &World,
    tel: &impl crate::telemetry::Telemetry,
    callee: super::super::identity::FunctionId,
) -> FatalError {
    // The callee's REFERENCE, not its definition: a protocol function is
    // declared without a body, so it never reaches `Defined` and asking for its
    // definition panics -- which is how the first attempt at this diagnostic
    // traded one crash for another.
    let callee = world.function_ref(callee);
    let qualified = world.module_name(callee.module).map_or_else(
        || callee.display_name(),
        |module| format!("{module}.{}", callee.display_name()),
    );
    let diagnostic = Diagnostic::error(
        codes::ARTIFACT_INCOMPLETE_SEMANTIC_PLAN,
        format!(
            "`{qualified}/{}` has no implementation for the value it is called with; \
             the implementations that take its receiver do not define it",
            callee.arity
        ),
        Span::DUMMY,
    );
    emit_job_diagnostic(tel, diagnostic)
}

/// A variadic argument carries an integer or a pointer and nothing else.
///
/// The call a backend generates for a variadic function lists its variadic
/// values as ordinary integer parameters; a float would additionally need the
/// x86-64 vector-register count that such a call has no way to set.
fn refuse_float_variadic_marshal(tel: &impl crate::telemetry::Telemetry, root_id: RootId) -> FatalError {
    incomplete_semantic_plan(
        tel,
        root_id,
        "a variadic extern argument must be an integer or pointer value, not a float",
    )
}

fn incomplete_semantic_plan(
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    message: impl Into<String>,
) -> FatalError {
    let message = message.into();
    let diagnostic = Diagnostic::error(
        codes::ARTIFACT_INCOMPLETE_SEMANTIC_PLAN,
        format!("compiler2 materialization for root {}: {}", root_id.as_u32(), message),
        Span::DUMMY,
    );
    emit_job_diagnostic(tel, diagnostic)
}

#[cfg(test)]
#[path = "artifact_test.rs"]
mod artifact_test;
