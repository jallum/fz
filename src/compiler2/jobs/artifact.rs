//! Compiler2 artifact projection jobs.
//!
//! This module produces executable-scoped backend products on demand. Each
//! producer names the exact fact or product it needs instead of deriving a
//! root-wide projection stack.

use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::extern_contract::extern_ty_from_name;
use crate::parser::lexer::Tok;
use crate::source::Span;

use super::super::artifact::{
    AbiReadyCallEdge, AbiReadyExecutable, AbiValueRepr, BackendReturnLayout, BackendSemanticInputLayout,
    BackendValueLayout, CallEdge, CallReturnFlow, CallTarget, DirectCallEdge, DispatchCallArm, DispatchCallEdge,
    DispatchCallMiss, EffectSummary, MaterializedCallEdge, MaterializedExecutable, MaterializedExecutableTransport,
    PositionedCallableConstructionOwner,
};
use super::super::body::{
    CallArg, CallSiteId, ControlDestination, ControlEntryId, ControlEntryOrigin, LoweredBody, LoweredEntry,
    LoweredStep, LoweredTail, ValueId,
};
use super::super::callsite_dispatch::{CallDestinations, call_destinations};
use super::super::drive::FactKey;
use super::super::executable_facts::ExecutableFacts;
use super::super::facts::FactUse;
use super::super::identity::{ExecutableKey, ExecutableNeed, ModuleId, RootId};
use super::super::pull::{
    ProductKey, ProductReadContext, ProductValue, PullOutcome, PullWait, RecursiveProductRead, TransportCarrier,
    TransportLayout,
};
use super::super::scheduler::FatalError;
#[cfg(test)]
use super::super::semantic::CallSiteKey;
use super::super::semantic::SemanticOrd;
use super::super::semantic::{ActivationAnalysis, CallSiteSummary, CallTargetSummary, SelectedCallee, ShapeDemand};
#[cfg(test)]
use super::super::transport::ShapeDescr;
use super::super::transport::{
    ActivationSymbol, BoundaryId, CodegenLaneRepr, CodegenSeam, CodegenSeamFact, ExecutableSymbol, LaneId,
    PhysicalLaneSource, ShapeId, TransportPosition,
};
use super::super::types::{Ty, Types};
use super::super::world::World;

const UNREACHABLE_CONTROL_ATOM: &str = "compiler2_unreachable_control";

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
    let mut analysis = executable_facts.analysis().clone();
    let return_ty = world
        .activation_return(&executable.activation)
        .unwrap_or_else(|| world.types_mut().none());
    let lowered = executable_facts.body().clone();
    let (dispatch_outcomes, retained_entries) = match lowered {
        LoweredBody::Clauses { ref clauses, .. } => {
            let mut entries = analysis.reachable_entries.clone();
            entries.extend(
                analysis
                    .entry_reachability
                    .clauses()
                    .iter()
                    .map(|clause| clauses[*clause as usize].entry),
            );
            entries.sort_by_key(|entry| entry.as_u32());
            entries.dedup();
            (analysis.entry_reachability.clauses().to_vec(), entries)
        }
        LoweredBody::Extern { .. } => (
            analysis.entry_reachability.clauses().to_vec(),
            analysis.reachable_entries.clone(),
        ),
    };
    let pruned = prune_lowered_body(lowered, &dispatch_outcomes, &retained_entries);
    let body = pruned.body;
    let callsite_args = super::super::body::callsite_call_args(&body);
    let mut transport_positions = vec![TransportPosition::ExecutableReturn {
        executable: transport_executable_symbol(executable, world.types()),
    }];
    transport_positions.extend(required_call_edge_transport_positions(
        world,
        executable,
        &executable_facts,
        &body,
        &callsite_args,
    ));
    let position_layouts = match read_transport_layouts(tel, context, world.types(), transport_positions) {
        Ok(position_layouts) => position_layouts,
        Err(transport_waits) => {
            waits.extend(transport_waits);
            Vec::new()
        }
    };
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }
    let transport = materialized_executable_transport(position_layouts, executable, world.types());
    let codegen_seam_facts = Box::default();
    let transport_plan = transport_lookup(&transport.position_layouts, &codegen_seam_facts);
    let call_edges = materialize_call_edges(
        world,
        tel,
        context.session().root(),
        &transport_plan,
        executable,
        &analysis,
        executable_facts.callsites(),
        executable_facts.callsite_needs(),
        &body,
        &pruned.original_entry_ids,
        &callsite_args,
    )
    .expect("product materialization should use settled semantic facts")
    .expect("product materialization should have complete call edges after waits");
    let retained_values = super::body::retained_value_ids(&body);
    analysis.value_types.retain(|value, _| retained_values.contains(value));
    let effects = local_effects(&body, &call_edges);
    let struct_modules = reachable_struct_modules(
        world.types(),
        executable,
        &body,
        return_ty,
        &analysis.value_types,
        &call_edges,
    );
    let materialized = Rc::new(MaterializedExecutable {
        entry_dispatch: executable_facts.entry_dispatch().cloned(),
        return_ty,
        runtime_demand: runtime_demand.expect("runtime-demand fact wait should have been satisfied"),
        transport,
        original_entry_ids: pruned.original_entry_ids,
        value_types: analysis.value_types,
        effects,
        struct_modules,
        body,
        call_edges,
    });
    PullOutcome::Produced(ProductValue::MaterializedExecutable(materialized))
}

fn reachable_struct_modules(
    types: &Types,
    executable: &ExecutableKey,
    body: &LoweredBody,
    return_ty: Ty,
    value_types: &HashMap<ValueId, Ty>,
    call_edges: &HashMap<CallSiteId, MaterializedCallEdge>,
) -> Box<[ModuleId]> {
    let mut modules = BTreeSet::new();
    if let LoweredBody::Clauses { clauses, entries, .. } = body {
        for steps in clauses
            .iter()
            .map(|clause| clause.projections.as_slice())
            .chain(entries.iter().map(|entry| entry.steps.as_slice()))
        {
            for step in steps {
                match step {
                    LoweredStep::Struct { module, .. } | LoweredStep::AssertStruct { module, .. } => {
                        modules.insert(*module);
                    }
                    _ => {}
                }
            }
        }
    }

    let mut type_roots = Vec::with_capacity(2 + value_types.len() + call_edges.len() * 2);
    type_roots.extend([executable.activation.arrow, return_ty]);
    type_roots.extend(value_types.values().copied());
    for edge in call_edges.values() {
        type_roots.push(edge.return_ty);
        match &edge.target {
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
    modules.extend(types.struct_modules(type_roots));
    modules.into_iter().collect()
}

pub(crate) fn produce_executable_effects_product<T: crate::telemetry::Telemetry>(
    tel: &T,
    context: &mut ProductReadContext<'_>,
    executable: &ExecutableKey,
    types: &Types,
) -> PullOutcome {
    let materialized_key = ProductKey::MaterializedExecutable(executable.clone());
    let materialized = match context.read_product(tel, materialized_key.clone(), types) {
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
        .flat_map(|edge| edge.target.local_callees())
        .cloned()
        .collect::<Vec<_>>();
    callees.sort_by(|left, right| left.semantic_cmp(right, types));
    callees.dedup();
    for callee in callees {
        let key = ProductKey::ExecutableEffects(callee);
        match context.read_recursive_product(tel, key.clone(), &current, types) {
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
    let materialized = match context.read_product(tel, materialized_key.clone(), world.types()) {
        Some(ProductValue::MaterializedExecutable(materialized)) => Some(Rc::clone(materialized)),
        Some(other) => panic!("materialized executable product produced unexpected value {other:?}"),
        None => {
            waits.push(PullWait::Product(materialized_key));
            None
        }
    };
    let effects_key = ProductKey::ExecutableEffects(executable.clone());
    let effects = match context.read_product(tel, effects_key.clone(), world.types()) {
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
        .iter()
        .map(|(position, _)| position.clone())
        .collect::<Vec<_>>();
    transport_positions.extend(required_executable_transport_positions(
        world,
        executable,
        &materialized,
    ));
    let position_layouts = match read_transport_layouts(tel, context, world.types(), transport_positions) {
        Ok(position_layouts) => position_layouts,
        Err(transport_waits) => {
            waits.extend(transport_waits);
            Vec::new()
        }
    };
    let transport = waits
        .is_empty()
        .then(|| materialized_executable_transport(position_layouts, executable, world.types()));
    let mut callable_owners = Vec::new();
    let owner_transport = transport.as_ref().unwrap_or(&materialized.transport);
    for position in executable_transport_positions(owner_transport) {
        let key = ProductKey::CallableConstruction(position.clone());
        match context.read_product(tel, key.clone(), world.types()) {
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
    let codegen_seam_facts = Box::default();
    let transport_plan = transport_lookup(&transport.position_layouts, &codegen_seam_facts);
    let plan = build_executable_abi_plan(world, executable, &materialized, &transport, &transport_plan);
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

pub(crate) fn executable_transport_positions(
    transport: &MaterializedExecutableTransport,
) -> impl Iterator<Item = &TransportPosition> {
    transport
        .input_positions
        .iter()
        .chain(std::iter::once(&transport.return_position))
        .chain(&transport.resume_positions)
        .chain(&transport.return_payload_positions)
        .chain(&transport.entry_capture_positions)
        .chain(&transport.call_arg_positions)
        .chain(&transport.value_positions)
}

#[derive(Debug, Clone)]
struct ExecutableAbiPlan {
    param_reprs: Vec<AbiValueRepr>,
    semantic_inputs: Box<[BackendSemanticInputLayout]>,
    return_layout: BackendReturnLayout,
    return_endpoints: Box<[(TransportPosition, BackendReturnLayout)]>,
    value_layouts: HashMap<ValueId, BackendValueLayout>,
}

struct PrunedLoweredBody {
    body: LoweredBody,
    original_entry_ids: Vec<ControlEntryId>,
}

fn materialized_executable_transport(
    mut position_layouts: Vec<(TransportPosition, TransportLayout)>,
    executable: &ExecutableKey,
    types: &Types,
) -> MaterializedExecutableTransport {
    let symbol = transport_executable_symbol(executable, types);
    position_layouts.sort_by(|(left, _), (right, _)| left.semantic_cmp(right, types));
    position_layouts.dedup_by(|left, right| {
        if left.0 != right.0 {
            return false;
        }
        assert_eq!(left.1, right.1, "one transport position must have one settled layout");
        true
    });
    let mut input_positions = Vec::new();
    let mut return_position = None;
    let mut resume_positions = Vec::new();
    let mut return_payload_positions = Vec::new();
    let mut entry_capture_positions = Vec::new();
    let mut call_arg_positions = Vec::new();
    let mut value_positions = Vec::new();
    for (position, _) in &position_layouts {
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
    sort_transport_positions(&mut input_positions, types);
    sort_transport_positions(&mut resume_positions, types);
    sort_transport_positions(&mut return_payload_positions, types);
    sort_transport_positions(&mut entry_capture_positions, types);
    sort_transport_positions(&mut call_arg_positions, types);
    sort_transport_positions(&mut value_positions, types);
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

struct ArtifactTransportLookup<'a> {
    positions: &'a [(TransportPosition, TransportLayout)],
    codegen_seam_facts: &'a [CodegenSeamFact],
}

fn transport_lookup<'a>(
    positions: &'a [(TransportPosition, TransportLayout)],
    codegen_seam_facts: &'a [CodegenSeamFact],
) -> ArtifactTransportLookup<'a> {
    ArtifactTransportLookup {
        positions,
        codegen_seam_facts,
    }
}

impl ArtifactTransportLookup<'_> {
    fn layout_at(&self, position: &TransportPosition) -> Option<TransportLayout> {
        self.positions
            .iter()
            .find_map(|(candidate, layout)| (candidate == position).then_some(*layout))
    }
}

/// Canonical packaging order for the codegen-seam facts of one root: seam kind,
/// then the owner the seam hangs off, then the seam's own structural
/// discriminants, then the lane it names.
pub(crate) fn compare_codegen_seam_facts(left: &CodegenSeamFact, right: &CodegenSeamFact, types: &Types) -> Ordering {
    let (left_kind, left_owner, left_second, left_third) = codegen_seam_parts(&left.seam);
    let (right_kind, right_owner, right_second, right_third) = codegen_seam_parts(&right.seam);
    left_kind
        .cmp(&right_kind)
        .then_with(|| compare_codegen_seam_owners(&left_owner, &right_owner, types))
        .then_with(|| left_second.cmp(&right_second))
        .then_with(|| left_third.cmp(&right_third))
        .then_with(|| shape_rank(left.shape).cmp(&shape_rank(right.shape)))
        .then_with(|| left.lane.as_u32().cmp(&right.lane.as_u32()))
        .then_with(|| codegen_lane_repr_rank(left.repr).cmp(&codegen_lane_repr_rank(right.repr)))
}

/// What a codegen seam hangs off. Executable-owned seams lead; the seam KIND
/// already separates the two, so this only ever compares like with like.
enum CodegenSeamOwner<'a> {
    Executable(&'a ExecutableSymbol),
    Boundary(BoundaryId),
}

fn compare_codegen_seam_owners(left: &CodegenSeamOwner<'_>, right: &CodegenSeamOwner<'_>, types: &Types) -> Ordering {
    match (left, right) {
        (CodegenSeamOwner::Executable(left), CodegenSeamOwner::Executable(right)) => left.semantic_cmp(right, types),
        (CodegenSeamOwner::Executable(_), CodegenSeamOwner::Boundary(_)) => Ordering::Less,
        (CodegenSeamOwner::Boundary(_), CodegenSeamOwner::Executable(_)) => Ordering::Greater,
        (CodegenSeamOwner::Boundary(left), CodegenSeamOwner::Boundary(right)) => left.as_u32().cmp(&right.as_u32()),
    }
}

/// A seam's kind rank, its owner, and the two structural discriminants that
/// separate seams of one kind on one owner.
fn codegen_seam_parts(seam: &CodegenSeam) -> (u8, CodegenSeamOwner<'_>, u32, u32) {
    use CodegenSeamOwner::{Boundary, Executable};
    match seam {
        CodegenSeam::FunctionEntry {
            executable,
            semantic_index,
        } => (0, Executable(executable), *semantic_index as u32, 0),
        CodegenSeam::BlockParam { executable, entry } => (1, Executable(executable), entry.as_u32(), 0),
        CodegenSeam::EntryCapture {
            executable,
            entry,
            capture_index,
        } => (2, Executable(executable), entry.as_u32(), *capture_index as u32),
        CodegenSeam::ReturnDelivery { executable } => (3, Executable(executable), 0, 0),
        CodegenSeam::ContinuationEntry {
            executable,
            callsite,
            entry,
        } => (4, Executable(executable), callsite.as_u32(), entry.as_u32()),
        CodegenSeam::ReturnContinuation { executable, callsite } => (5, Executable(executable), callsite.as_u32(), 0),
        CodegenSeam::TailCall { executable, callsite } => (6, Executable(executable), callsite.as_u32(), 0),
        CodegenSeam::CallableBoundary { boundary, slot } => (7, Boundary(*boundary), *slot as u32, 0),
        CodegenSeam::ExternBoundary { executable } => (8, Executable(executable), 0, 0),
        CodegenSeam::FirstClassPublication { boundary } => (9, Boundary(*boundary), 0, 0),
    }
}

/// A seam without a shape sorts after every seam that has one.
fn shape_rank(shape: Option<ShapeId>) -> u32 {
    shape.map(ShapeId::as_u32).unwrap_or(u32::MAX)
}

fn codegen_lane_repr_rank(repr: CodegenLaneRepr) -> u8 {
    match repr {
        CodegenLaneRepr::ValueRef => 0,
        CodegenLaneRepr::RawInt => 1,
        CodegenLaneRepr::RawF64 => 2,
        CodegenLaneRepr::RawAtom => 3,
    }
}

fn required_entry_capture_transport_positions(
    world: &World,
    executable: &ExecutableKey,
    materialized: &MaterializedExecutable,
) -> Vec<TransportPosition> {
    let LoweredBody::Clauses { entries, .. } = &materialized.body else {
        return Vec::new();
    };
    let symbol = transport_executable_symbol(executable, world.types());
    let mut positions = Vec::new();
    for (entry_index, entry) in entries.iter().enumerate() {
        let entry_id = materialized
            .original_entry_ids
            .get(entry_index)
            .copied()
            .unwrap_or_else(|| ControlEntryId::from_u32(entry_index as u32));
        for capture_index in 0..entry.captures.len() {
            let position = TransportPosition::EntryCapture {
                executable: symbol.clone(),
                entry: entry_id,
                capture_index,
            };
            positions.push(position);
        }
    }
    positions
}

/// Every transport-shape product an executable's ABI must have settled before it
/// can be lowered: its input, entry-capture, resume, and local-backend positions
/// (its return position is already driven by the materialized product). Pulling
/// these `TransportShape` products supplies the exact positioned answers embedded
/// in the executable's ABI. The ABI product drives them before building the ABI
/// value.
fn required_executable_transport_positions(
    world: &World,
    executable: &ExecutableKey,
    materialized: &MaterializedExecutable,
) -> Vec<TransportPosition> {
    let mut positions = Vec::new();
    positions.extend(required_executable_input_transport_positions(
        world,
        executable,
        materialized,
    ));
    positions.extend(required_entry_capture_transport_positions(
        world,
        executable,
        materialized,
    ));
    positions.extend(required_resume_transport_positions(world, executable, materialized));
    positions.extend(required_local_backend_transport_positions(
        world,
        executable,
        materialized,
    ));
    positions
}

fn required_executable_input_transport_positions(
    world: &World,
    executable: &ExecutableKey,
    materialized: &MaterializedExecutable,
) -> Vec<TransportPosition> {
    let symbol = transport_executable_symbol(executable, world.types());
    let callable_carriers = callable_carrier_values(&materialized.body);
    let input_callable_carrier_indexes = input_indexes_for_values(&materialized.body, &callable_carriers);
    materialized
        .runtime_demand
        .input_demands
        .iter()
        .enumerate()
        .filter_map(|(semantic_index, demand)| {
            if matches!(demand.shape, ShapeDemand::Ignore) && !input_callable_carrier_indexes.contains(&semantic_index)
            {
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

fn callable_carrier_values(body: &LoweredBody) -> HashSet<ValueId> {
    let LoweredBody::Clauses { entries, .. } = body else {
        return HashSet::new();
    };
    let mut values = HashSet::new();
    for entry in entries {
        for step in &entry.steps {
            if let LoweredStep::Lambda { captures, .. } = step {
                values.extend(captures.iter().copied());
            }
        }
        match &entry.tail {
            LoweredTail::DirectCall { args, .. } => {
                values.extend(args.iter().map(|arg| arg.value));
            }
            LoweredTail::ClosureCall { callee, args, .. } => {
                values.insert(*callee);
                values.extend(args.iter().map(|arg| arg.value));
            }
            LoweredTail::Value { .. }
            | LoweredTail::If { .. }
            | LoweredTail::Dispatch { .. }
            | LoweredTail::Receive(_)
            | LoweredTail::Halt { .. } => {}
        }
    }
    values
}

fn input_indexes_for_values(body: &LoweredBody, values: &HashSet<ValueId>) -> HashSet<usize> {
    let LoweredBody::Clauses { clauses, .. } = body else {
        return HashSet::new();
    };
    clauses
        .iter()
        .flat_map(|clause| {
            clause
                .params
                .iter()
                .enumerate()
                .filter_map(|(index, value)| values.contains(value).then_some(index))
        })
        .collect()
}

fn required_resume_transport_positions(
    world: &World,
    executable: &ExecutableKey,
    materialized: &MaterializedExecutable,
) -> Vec<TransportPosition> {
    let LoweredBody::Clauses { entries, .. } = &materialized.body else {
        return Vec::new();
    };
    let symbol = transport_executable_symbol(executable, world.types());
    let mut positions = Vec::new();
    let mut deliver_callsites = HashMap::new();
    for entry in entries {
        let Some((callsite, ControlDestination::Deliver(entry_id))) = (match &entry.tail {
            LoweredTail::DirectCall { callsite, dest, .. } | LoweredTail::ClosureCall { callsite, dest, .. } => {
                Some((*callsite, dest))
            }
            LoweredTail::Value { .. }
            | LoweredTail::If { .. }
            | LoweredTail::Dispatch { .. }
            | LoweredTail::Receive(_)
            | LoweredTail::Halt { .. } => None,
        }) else {
            continue;
        };
        let entry_id = materialized
            .original_entry_ids
            .get(entry_id.as_u32() as usize)
            .copied()
            .unwrap_or(*entry_id);
        deliver_callsites.insert(entry_id, callsite);
    }
    for (entry_index, entry) in entries.iter().enumerate() {
        let ControlEntryOrigin::DeliveredResume { .. } = entry.origin else {
            continue;
        };
        let entry_id = materialized
            .original_entry_ids
            .get(entry_index)
            .copied()
            .unwrap_or_else(|| ControlEntryId::from_u32(entry_index as u32));
        let position = TransportPosition::ResumePayload {
            executable: symbol.clone(),
            callsite: deliver_callsites.get(&entry_id).copied(),
            entry: entry_id,
        };
        positions.push(position);
    }
    positions
}

fn required_local_backend_transport_positions(
    world: &World,
    executable: &ExecutableKey,
    materialized: &MaterializedExecutable,
) -> Vec<TransportPosition> {
    let LoweredBody::Clauses { clauses, entries, .. } = &materialized.body else {
        return Vec::new();
    };
    let symbol = transport_executable_symbol(executable, world.types());
    let mut positions = Vec::new();
    positions.extend(
        materialized
            .runtime_demand
            .callable_flows
            .keys()
            .map(|value| TransportPosition::Value {
                executable: symbol.clone(),
                value: *value,
            }),
    );
    for value in clauses
        .iter()
        .flat_map(|clause| clause.projections.iter())
        .chain(entries.iter().flat_map(|entry| entry.steps.iter()))
        .flat_map(step_result_values)
    {
        let position = TransportPosition::Value {
            executable: symbol.clone(),
            value,
        };
        positions.push(position);
    }
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
            | LoweredTail::Halt { .. } => continue,
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

fn read_transport_layouts(
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    types: &Types,
    positions: impl IntoIterator<Item = TransportPosition>,
) -> Result<Vec<(TransportPosition, TransportLayout)>, Vec<PullWait>> {
    let mut positions = positions
        .into_iter()
        .collect::<HashSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    positions.sort_by(|left, right| left.semantic_cmp(right, types));
    let mut layouts = Vec::with_capacity(positions.len());
    let mut waits = Vec::new();
    for position in positions {
        let key = ProductKey::TransportShape(position.clone());
        match context.read_product(tel, key.clone(), types) {
            Some(ProductValue::TransportShape(super::super::pull::TransportShapeFact::Layout(layout))) => {
                layouts.push((position, *layout));
            }
            Some(value) => panic!("transport shape produced unexpected value {value:?}"),
            None => waits.push(PullWait::Product(key)),
        }
    }
    if waits.is_empty() { Ok(layouts) } else { Err(waits) }
}

pub(crate) fn step_result_values(step: &LoweredStep) -> Vec<super::super::body::ValueId> {
    match step {
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
        | LoweredStep::TupleField { value, .. } => vec![*value],
        LoweredStep::SplitList { head, tail, .. } => vec![*head, *tail],
        LoweredStep::BitstringInit { reader, .. } => vec![*reader],
        LoweredStep::BitstringRead {
            ok, value, next_reader, ..
        } => vec![*ok, *value, *next_reader],
        LoweredStep::AssertLiteral { .. }
        | LoweredStep::AssertStruct { .. }
        | LoweredStep::AssertTuple { .. }
        | LoweredStep::AssertEmptyList { .. }
        | LoweredStep::AssertSame { .. }
        | LoweredStep::AssertBitstringDone { .. } => Vec::new(),
    }
}

fn required_call_edge_transport_positions(
    world: &mut World,
    executable: &ExecutableKey,
    facts: &ExecutableFacts,
    body: &LoweredBody,
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
) -> Vec<TransportPosition> {
    let LoweredBody::Clauses { entries, .. } = body else {
        return Vec::new();
    };
    let caller_symbol = transport_executable_symbol(executable, world.types());
    let callsite_needs = facts.callsite_needs();
    let summaries = facts.callsites();
    let mut positions = HashSet::new();
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
                    world.types(),
                );
            }
            LoweredTail::ClosureCall {
                callsite, callee, dest, ..
            } => {
                positions.insert(TransportPosition::Value {
                    executable: caller_symbol.clone(),
                    value: *callee,
                });
                for (semantic_index, _) in callsite_args.get(callsite).into_iter().flatten().enumerate() {
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
                record_return_flow_transport_positions(
                    &mut positions,
                    &caller_symbol,
                    *callsite,
                    dest,
                    callees,
                    world.types(),
                );
            }
            LoweredTail::Value { .. }
            | LoweredTail::If { .. }
            | LoweredTail::Dispatch { .. }
            | LoweredTail::Receive(_)
            | LoweredTail::Halt { .. } => {}
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
    types: &Types,
) {
    let callee_symbols = callees
        .into_iter()
        .map(|callee| transport_executable_symbol(&callee, types));
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

fn transport_executable_symbol(executable: &ExecutableKey, types: &Types) -> ExecutableSymbol {
    ExecutableSymbol {
        activation: ActivationSymbol {
            function: executable.activation.function,
            arrow: executable.activation.arrow,
            input: executable.activation.inputs(types).into_boxed_slice(),
        },
        need: executable.need,
    }
}

fn sort_transport_positions(positions: &mut [TransportPosition], types: &Types) {
    positions.sort_by(|left, right| left.semantic_cmp(right, types));
}

fn materialize_call_edges(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    transport_plan: &ArtifactTransportLookup<'_>,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    summaries: &HashMap<CallSiteId, CallSiteSummary>,
    callsite_needs: &HashMap<CallSiteId, ExecutableNeed>,
    body: &LoweredBody,
    original_entry_ids: &[ControlEntryId],
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
) -> Result<Option<HashMap<CallSiteId, MaterializedCallEdge>>, FatalError> {
    let mut call_edges = HashMap::new();
    let LoweredBody::Clauses { entries, .. } = body else {
        return Ok(Some(call_edges));
    };
    for entry in entries {
        match &entry.tail {
            LoweredTail::DirectCall { callsite, dest, .. } => {
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
                    callsite_args,
                )?
                else {
                    return Ok(None);
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
                    executable: transport_executable_symbol(executable, world.types()),
                    value: *callee,
                };
                let callee_layout = require_transport_layout(tel, root_id, transport_plan, &callee_position)?;
                if let Some(edge) = materialize_closure_call_edge(
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
                    callsite_args,
                )? {
                    call_edges.insert(*callsite, edge);
                }
            }
            LoweredTail::Value { .. }
            | LoweredTail::If { .. }
            | LoweredTail::Dispatch { .. }
            | LoweredTail::Receive(_)
            | LoweredTail::Halt { .. } => {}
        }
    }
    Ok(Some(call_edges))
}

fn materialize_direct_call_edge(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    transport_plan: &ArtifactTransportLookup<'_>,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    summaries: &HashMap<CallSiteId, CallSiteSummary>,
    need: ExecutableNeed,
    callsite: CallSiteId,
    dest: &ControlDestination,
    original_entry_ids: &[ControlEntryId],
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
) -> Result<Option<MaterializedCallEdge>, FatalError> {
    // One door: a callsite that named no targets -- never reached, proven
    // dead, or reached and still unresolved -- materializes no edge. (The
    // `has_fact` pre-test that used to stand here asked a DIFFERENT question:
    // the ledger's, where the store below is lowering's authority and is
    // never pruned. The two diverge only in the ledger-withdrawn/store-stale
    // state, measured to occur zero times across the 574-fixture corpus, lib,
    // and matrix -- so the store answers alone: fz-kdt.69.2. fz-kdt.69.3
    // makes the ledger authoritative over exactly this divergence; revisit
    // then.)
    let Some(summary) = summaries.get(&callsite).cloned() else {
        return Ok(None);
    };
    // The callsite's DESTINATIONS, not its settled targets: a target the
    // runtime could never route to is no destination at all (fz-kdt.104), and
    // a callsite left with one of them is a direct call.
    let dispatch = match call_destinations(world.types_mut(), &summary) {
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
                callsite_args,
                target,
            )?;
            return Ok(Some(MaterializedCallEdge {
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
    let mut arms = Vec::new();
    for (body_id, target) in dispatch.arm_body_ids.into_iter().zip(dispatch.targets) {
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
            callsite_args,
            target,
        )?;
        arms.push(DispatchCallArm {
            body_id,
            callee: direct.callee,
            return_flow: direct.return_flow,
            extern_marshals: direct.extern_marshals,
        });
    }
    let return_ty = summary.settled_return(world.types_mut());
    Ok(Some(MaterializedCallEdge {
        target: CallEdge::Dispatch(Box::new(DispatchCallEdge {
            plan: dispatch.plan,
            arms,
            miss: DispatchCallMiss::Unreachable,
        })),
        return_ty,
    }))
}

fn materialize_closure_call_edge(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    transport_plan: &ArtifactTransportLookup<'_>,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    summaries: &HashMap<CallSiteId, CallSiteSummary>,
    callee_layout: TransportLayout,
    need: ExecutableNeed,
    callsite: CallSiteId,
    result_value: ValueId,
    dest: &ControlDestination,
    original_entry_ids: &[ControlEntryId],
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
) -> Result<Option<MaterializedCallEdge>, FatalError> {
    let summary = summaries.get(&callsite).cloned();
    let target = summary.as_ref().and_then(|summary| summary.single_target().cloned());
    // The callee's CARRIER decides whether this call happens, not the static
    // target evidence standing behind it. A `ValueRef` carrier means a real
    // callable value reaches this callsite at runtime and the boxed-apply
    // wrapper can call it, however little the analysis managed to name. That is
    // the standing state for a closure that arrived from outside the analysed
    // world — a mailbox message — where no target is ever named and none ever
    // will be: "no targets" there is UNKNOWN, not `none` (fz-kdt.130).
    let public_callable = matches!(callee_layout.carrier, TransportCarrier::ValueRef(_));
    if public_callable {
        let return_ty =
            public_indirect_return_ty(world, tel, root_id, analysis, summary.as_ref(), callsite, result_value)?;
        let return_flow = if world.types().is_empty(&return_ty) {
            CallReturnFlow::NoReturn { local_source: None }
        } else {
            call_return_flow(
                world,
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
        return Ok(Some(MaterializedCallEdge {
            target: CallEdge::Indirect(return_flow),
            return_ty,
        }));
    }
    let Some(target) = target else {
        if summary.is_some() {
            return Err(incomplete_semantic_plan(
                tel,
                root_id,
                format!(
                    "closure callsite {} has no runtime callable carrier or single direct target",
                    callsite.as_u32()
                ),
            ));
        }
        // No callable carrier AND no evidence at all: nothing can be called
        // here, so this call really never happens. Lower it as the dead call it
        // is — every `ClosureCall` tail needs a return flow, and `NoReturn` is
        // the name for one that never returns. Emitting no edge at all instead
        // leaves native lowering with a `Deliver` destination and nothing to
        // deliver (fz-f98.18). An `Unresolved` edge (fz-kdt.69.2) reaches this
        // same answer.
        let never = world.types_mut().none();
        return Ok(Some(MaterializedCallEdge {
            target: CallEdge::Indirect(CallReturnFlow::NoReturn { local_source: None }),
            return_ty: never,
        }));
    };
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
        callsite_args,
        target,
    )?;
    Ok(Some(MaterializedCallEdge {
        target: CallEdge::Direct(direct),
        return_ty,
    }))
}

fn public_indirect_return_ty(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    analysis: &ActivationAnalysis,
    summary: Option<&CallSiteSummary>,
    callsite: CallSiteId,
    result_value: ValueId,
) -> Result<Ty, FatalError> {
    let settled_return = summary.map(|summary| summary.settled_return(world.types_mut()));
    if let Some(return_ty) = settled_return.filter(|return_ty| world.types().is_empty(return_ty)) {
        return Ok(return_ty);
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
    transport_plan: &ArtifactTransportLookup<'_>,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    need: ExecutableNeed,
    callsite: CallSiteId,
    dest: &ControlDestination,
    original_entry_ids: &[ControlEntryId],
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
    target: CallTargetSummary,
) -> Result<(DirectCallEdge<ExecutableKey>, Ty), FatalError> {
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
            let extern_marshals = if let LoweredBody::Extern { signature } = world.lowered_body(function) {
                let Some(args) = callsite_args.get(&callsite) else {
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
    };
    let return_ty = target.settled_return(world.types_mut());
    let return_flow = if world.types().is_empty(&return_ty) {
        exact_no_return_flow(world, &callee)
    } else {
        call_return_flow(
            world,
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
    world: &World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    transport_plan: &ArtifactTransportLookup<'_>,
    executable: &ExecutableKey,
    callee: Option<&CallTarget<ExecutableKey>>,
    callsite: CallSiteId,
    dest: &ControlDestination,
    original_entry_ids: &[ControlEntryId],
    public_callable: bool,
) -> Result<CallReturnFlow, FatalError> {
    let caller_symbol = transport_executable_symbol(executable, world.types());
    match dest {
        ControlDestination::Deliver(entry) => {
            let transport_entry = original_entry_ids
                .get(entry.as_u32() as usize)
                .copied()
                .unwrap_or(*entry);
            let resume = TransportPosition::ResumePayload {
                executable: caller_symbol.clone(),
                callsite: Some(callsite),
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
                        executable: transport_executable_symbol(callee, world.types()),
                    },
                    Some(CallTarget::ProviderBoundary(_)) => resume.clone(),
                    None => {
                        return Err(incomplete_semantic_plan(
                            tel,
                            root_id,
                            "non-public call return flow has no callee",
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
                    executable: transport_executable_symbol(callee, world.types()),
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

fn exact_no_return_flow(world: &World, callee: &CallTarget<ExecutableKey>) -> CallReturnFlow {
    let local_source = callee.local().map(|callee| TransportPosition::ExecutableReturn {
        executable: transport_executable_symbol(callee, world.types()),
    });
    CallReturnFlow::NoReturn { local_source }
}

fn require_transport_layout(
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    transport_plan: &ArtifactTransportLookup<'_>,
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

fn prune_lowered_body(
    body: LoweredBody,
    reachable_clauses: &[u32],
    reachable_entries: &[ControlEntryId],
) -> PrunedLoweredBody {
    match body {
        LoweredBody::Extern { .. } => PrunedLoweredBody {
            body,
            original_entry_ids: Vec::new(),
        },
        LoweredBody::Clauses {
            clauses,
            entries,
            generated,
        } => {
            let reachable_entries = reachable_entries.iter().copied().collect::<HashSet<_>>();
            let mut clauses = reachable_clauses
                .iter()
                .map(|clause_id| clauses[*clause_id as usize].clone())
                .collect::<Vec<_>>();
            let mut needed = HashMap::new();
            let mut kept_ids = Vec::new();
            for clause in &clauses {
                collect_reachable_entries(&entries, clause.entry, &reachable_entries, &mut kept_ids, &mut needed);
            }
            let mut kept = kept_ids
                .iter()
                .map(|entry_id| {
                    specialize_entry(
                        entries[entry_id.as_u32() as usize].clone(),
                        reachable_entries.contains(entry_id),
                    )
                })
                .collect::<Vec<_>>();
            reindex_entries(&mut clauses, &mut kept, &needed);
            PrunedLoweredBody {
                body: LoweredBody::Clauses {
                    clauses,
                    entries: kept,
                    generated,
                },
                original_entry_ids: kept_ids,
            }
        }
    }
}

fn collect_reachable_entries(
    entries: &[LoweredEntry],
    entry_id: super::super::body::ControlEntryId,
    reachable_entries: &HashSet<super::super::body::ControlEntryId>,
    order: &mut Vec<super::super::body::ControlEntryId>,
    out: &mut HashMap<super::super::body::ControlEntryId, super::super::body::ControlEntryId>,
) {
    if out.contains_key(&entry_id) {
        return;
    }
    let next_id = super::super::body::ControlEntryId::from_u32(order.len() as u32);
    order.push(entry_id);
    out.insert(entry_id, next_id);
    if !reachable_entries.contains(&entry_id) {
        return;
    }
    let entry = &entries[entry_id.as_u32() as usize];
    match &entry.tail {
        LoweredTail::Value { dest, .. }
        | LoweredTail::DirectCall { dest, .. }
        | LoweredTail::ClosureCall { dest, .. } => {
            if let super::super::body::ControlDestination::Deliver(target) = dest {
                collect_reachable_entries(entries, *target, reachable_entries, order, out);
            }
        }
        LoweredTail::If {
            then_entry, else_entry, ..
        } => {
            collect_reachable_entries(entries, *then_entry, reachable_entries, order, out);
            collect_reachable_entries(entries, *else_entry, reachable_entries, order, out);
        }
        LoweredTail::Dispatch { dispatch, .. } => {
            for arm_entry in &dispatch.arm_entries {
                collect_reachable_entries(entries, *arm_entry, reachable_entries, order, out);
            }
            collect_reachable_entries(entries, dispatch.miss_entry, reachable_entries, order, out);
        }
        LoweredTail::Receive(receive) => {
            if let super::super::body::ControlDestination::Deliver(target) = &receive.dest {
                collect_reachable_entries(entries, *target, reachable_entries, order, out);
            }
            for clause in &receive.clauses {
                collect_reachable_entries(entries, clause.entry, reachable_entries, order, out);
            }
            if let Some(after) = &receive.after {
                collect_reachable_entries(entries, after.entry, reachable_entries, order, out);
            }
        }
        LoweredTail::Halt { .. } => {}
    }
}

fn specialize_entry(mut entry: LoweredEntry, is_reachable: bool) -> LoweredEntry {
    if is_reachable {
        return entry;
    }
    entry.steps.clear();
    entry.tail = LoweredTail::Halt {
        atom: UNREACHABLE_CONTROL_ATOM.to_string(),
    };
    entry
}

fn reindex_entries(
    clauses: &mut [super::super::body::LoweredClause],
    entries: &mut [LoweredEntry],
    ids: &HashMap<super::super::body::ControlEntryId, super::super::body::ControlEntryId>,
) {
    for clause in clauses {
        clause.entry = ids[&clause.entry];
    }
    for entry in entries {
        match &mut entry.tail {
            LoweredTail::Value { dest, .. }
            | LoweredTail::DirectCall { dest, .. }
            | LoweredTail::ClosureCall { dest, .. } => {
                if let super::super::body::ControlDestination::Deliver(target) = dest {
                    *target = ids[target];
                }
            }
            LoweredTail::If {
                then_entry, else_entry, ..
            } => {
                *then_entry = ids[then_entry];
                *else_entry = ids[else_entry];
            }
            LoweredTail::Dispatch { dispatch, .. } => {
                for arm_entry in &mut dispatch.arm_entries {
                    *arm_entry = ids[arm_entry];
                }
                dispatch.miss_entry = ids[&dispatch.miss_entry];
            }
            LoweredTail::Receive(receive) => {
                if let super::super::body::ControlDestination::Deliver(target) = &mut receive.dest {
                    *target = ids[target];
                }
                for clause in &mut receive.clauses {
                    clause.entry = ids[&clause.entry];
                }
                if let Some(after) = &mut receive.after {
                    after.entry = ids[&after.entry];
                }
            }
            LoweredTail::Halt { .. } => {}
        }
    }
}

fn resolve_extern_marshals(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    args: &[CallArg],
    value_types: &HashMap<super::super::body::ValueId, Ty>,
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
            marshals.push(parse_extern_ascription(world, tel, root_id, ascription)?);
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
        return Ok(crate::fz_ir::ExternTy::F64);
    }
    let str_ty = world.types_mut().str_t();
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

fn local_effects(body: &LoweredBody, call_edges: &HashMap<CallSiteId, MaterializedCallEdge>) -> EffectSummary {
    match body {
        LoweredBody::Extern { signature } => EffectSummary {
            reads_allocation_stats: signature.symbol == "fz_process_heap_alloc_stats",
            scheduler_visible: matches!(signature.symbol.as_str(), "fz_send" | "fz_spawn" | "fz_spawn_opt"),
            observable: true,
            halts: signature.ret == crate::fz_ir::ExternTy::Never,
            ..EffectSummary::default()
        },
        LoweredBody::Clauses { clauses, entries, .. } => {
            let mut effects = EffectSummary::default();
            for clause in clauses {
                effects.union_with(step_effects(&clause.projections, call_edges));
            }
            for entry in entries {
                effects.union_with(step_effects(&entry.steps, call_edges));
                effects.union_with(tail_effects(&entry.tail, call_edges));
            }
            effects
        }
    }
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
                Some(edge) => matches!(edge.target, CallEdge::Indirect { .. }),
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
        | LoweredTail::Halt { .. } => {}
    }
    effects
}

fn call_edge_calls_provider_boundary(edge: &MaterializedCallEdge) -> bool {
    match &edge.target {
        CallEdge::Direct(direct) => matches!(direct.callee, CallTarget::ProviderBoundary(_)),
        CallEdge::Dispatch(dispatch) => dispatch
            .arms
            .iter()
            .any(|arm| matches!(arm.callee, CallTarget::ProviderBoundary(_))),
        CallEdge::Indirect { .. } => false,
    }
}

fn build_executable_abi_plan(
    world: &mut World,
    _key: &ExecutableKey,
    executable: &MaterializedExecutable,
    transport: &MaterializedExecutableTransport,
    transport_plan: &ArtifactTransportLookup<'_>,
) -> ExecutableAbiPlan {
    let semantic_inputs = transport
        .input_positions
        .iter()
        .filter_map(|position| {
            let TransportPosition::ExecutableInput {
                executable: symbol,
                semantic_index,
            } = position
            else {
                return None;
            };
            let layout = transport_plan
                .layout_at(position)
                .unwrap_or_else(|| panic!("transport plan should publish materialized input position {position:?}"));
            let shape = layout.structural;
            let demand = executable.runtime_demand.input_demands.get(*semantic_index);
            let contract =
                if layout.carrier == TransportCarrier::Absent && demand.is_some_and(|demand| demand.is_ignore()) {
                    Vec::new()
                } else {
                    physical_layout_contract(world, layout, |world, leaf_shape, lane| {
                        seam_repr_for_lane_or_default(
                            world,
                            transport_plan.codegen_seam_facts,
                            |seam| {
                                matches!(
                                    seam,
                                    CodegenSeam::FunctionEntry {
                                        executable,
                                        semantic_index: index
                                    } if executable == symbol && index == semantic_index
                                )
                            },
                            Some(leaf_shape),
                            lane,
                        )
                    })
                };
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
    let return_contract = physical_layout_contract(world, return_layout, |world, leaf_shape, lane| {
        seam_repr_for_lane_or_default(
            world,
            transport_plan.codegen_seam_facts,
            |seam| {
                matches!(
                    seam,
                    CodegenSeam::ReturnDelivery { executable: symbol }
                        if symbol == &transport.executable
                )
            },
            Some(leaf_shape),
            lane,
        )
    });
    let mut value_layouts: HashMap<ValueId, BackendValueLayout> = transport
        .value_positions
        .iter()
        .filter_map(|position| {
            let TransportPosition::Value { value, .. } = position else {
                return None;
            };
            let layout = transport_plan
                .layout_at(position)
                .unwrap_or_else(|| panic!("transport plan should publish materialized value position {position:?}"));
            let contract = physical_layout_contract(world, layout, |world, _, lane| {
                let ty = world.lane(lane).ty;
                abi_value_repr(world, ty)
            });
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
    if let LoweredBody::Clauses { clauses, .. } = &executable.body {
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
            let contract = physical_layout_contract(world, layout, |world, leaf_shape, lane| {
                endpoint_seam_repr(world, transport_plan.codegen_seam_facts, position, leaf_shape, lane)
            });
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
                AbiReadyCallEdge {
                    target: edge.target.clone(),
                    return_ty: edge.return_ty,
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

fn endpoint_seam_repr(
    world: &mut World,
    facts: &[super::super::transport::CodegenSeamFact],
    position: &TransportPosition,
    shape: ShapeId,
    lane: super::super::transport::LaneId,
) -> AbiValueRepr {
    seam_repr_for_lane_or_default(
        world,
        facts,
        |seam| match (position, seam) {
            (
                TransportPosition::ExecutableReturn { executable },
                CodegenSeam::ReturnDelivery { executable: candidate },
            ) => executable == candidate,
            (
                TransportPosition::ReturnPayload { executable, callsite },
                CodegenSeam::ReturnContinuation {
                    executable: candidate,
                    callsite: candidate_callsite,
                },
            ) => executable == candidate && callsite == candidate_callsite,
            (
                TransportPosition::ResumePayload {
                    executable,
                    callsite: Some(callsite),
                    entry,
                },
                CodegenSeam::ContinuationEntry {
                    executable: candidate,
                    callsite: candidate_callsite,
                    entry: candidate_entry,
                },
            ) => executable == candidate && callsite == candidate_callsite && entry == candidate_entry,
            (
                TransportPosition::ResumePayload {
                    executable,
                    callsite: None,
                    entry,
                },
                CodegenSeam::BlockParam {
                    executable: candidate,
                    entry: candidate_entry,
                },
            ) => executable == candidate && entry == candidate_entry,
            _ => false,
        },
        Some(shape),
        lane,
    )
}

pub(super) fn physical_layout_contract(
    world: &mut World,
    layout: TransportLayout,
    mut structural_repr: impl FnMut(&mut World, ShapeId, LaneId) -> AbiValueRepr,
) -> Vec<(Ty, AbiValueRepr)> {
    world
        .layout_physical_lanes(layout)
        .into_iter()
        .map(|physical| {
            let ty = world.lane(physical.lane).ty;
            let repr = match physical.source {
                PhysicalLaneSource::Structural => structural_repr(world, physical.structural, physical.lane),
                PhysicalLaneSource::Carrier => AbiValueRepr::ValueRef,
            };
            (ty, repr)
        })
        .collect()
}

fn seam_repr_for_lane_or_default(
    world: &mut World,
    facts: &[super::super::transport::CodegenSeamFact],
    seam_matches: impl Fn(&CodegenSeam) -> bool,
    shape: Option<ShapeId>,
    lane: LaneId,
) -> AbiValueRepr {
    facts
        .iter()
        .find(|fact| seam_matches(&fact.seam) && fact.shape == shape && fact.lane == lane)
        .map(|fact| abi_repr_from_codegen(fact.repr))
        .unwrap_or_else(|| {
            let ty = world.lane(lane).ty;
            abi_value_repr(world, ty)
        })
}

fn abi_repr_from_codegen(repr: CodegenLaneRepr) -> AbiValueRepr {
    match repr {
        CodegenLaneRepr::ValueRef => AbiValueRepr::ValueRef,
        CodegenLaneRepr::RawInt => AbiValueRepr::RawInt,
        CodegenLaneRepr::RawF64 => AbiValueRepr::RawF64,
        CodegenLaneRepr::RawAtom => AbiValueRepr::RawAtom,
    }
}

fn abi_value_repr(world: &mut World, ty: Ty) -> AbiValueRepr {
    if world.types().is_floating(&ty) {
        return AbiValueRepr::RawF64;
    }
    if world.types().is_integer(&ty) {
        return AbiValueRepr::RawInt;
    }
    let atom = world.types_mut().atom();
    if world.types().is_subtype(&ty, &atom) {
        AbiValueRepr::RawAtom
    } else {
        AbiValueRepr::ValueRef
    }
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
    emit_through(tel, std::slice::from_ref(&diagnostic));
    FatalError
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler2::semantic::{
        CallSiteResolution, CallSiteSummary, CallTargetSummary, EntryReachability, SelectedCallee,
    };
    use crate::compiler2::{ActivationKey, FunctionId};
    use crate::telemetry::ConfiguredTelemetry;

    #[test]
    fn carrier_provenance_forces_value_ref_for_a_raw_capable_lane() {
        let mut world = World::new();
        let int = world.types_mut().int();
        let lane = world.intern_lane(super::super::super::transport::LaneDescr {
            ty: int,
            class: super::super::super::transport::TransportClass::Value,
        });
        let shape = world.intern_shape(ShapeDescr::Lane(lane));
        let structural = physical_layout_contract(&mut world, TransportLayout::structural(shape), |world, _, lane| {
            abi_value_repr(world, world.lane(lane).ty)
        });
        let carrier = physical_layout_contract(
            &mut world,
            TransportLayout {
                structural: shape,
                carrier: TransportCarrier::ValueRef(lane),
            },
            |world, _, lane| abi_value_repr(world, world.lane(lane).ty),
        );

        assert_eq!(structural, vec![(int, AbiValueRepr::RawInt)]);
        assert_eq!(carrier, vec![(int, AbiValueRepr::ValueRef)]);
    }

    #[test]
    fn sort_transport_positions_orders_one_partition_by_structural_discriminants() {
        // Each MaterializedExecutableTransport field vector holds ONE variant
        // of ONE executable by construction (positions are gathered from the
        // per-symbol index and partitioned by variant), so packaging order is
        // decided purely by the variant-local structural discriminants --
        // here CallArg's (callsite, semantic_index) -- independent of
        // arrival order and of any interned-type identity.
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        world.submit_code(None, "fn main(x), do: x".to_string());
        let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
        let function = world.root_entry(root).function;
        let int = world.types_mut().int();
        let symbol = ExecutableSymbol {
            activation: ActivationSymbol {
                function,
                arrow: int,
                input: vec![int].into_boxed_slice(),
            },
            need: ExecutableNeed::Value,
        };
        let call_arg = |callsite: u32, semantic_index: usize| TransportPosition::CallArg {
            executable: symbol.clone(),
            callsite: CallSiteId::from_u32(callsite),
            semantic_index,
        };

        let mut positions = vec![call_arg(1, 1), call_arg(1, 0), call_arg(0, 1)];
        sort_transport_positions(&mut positions, world.types());

        assert_eq!(positions, vec![call_arg(0, 1), call_arg(1, 0), call_arg(1, 1)]);
    }

    fn fake_call_executable(world: &mut World, root: u32, function: u32, inputs: &[Ty]) -> ExecutableKey {
        let activation = ActivationKey::from_inputs(
            RootId::for_test(root),
            FunctionId::for_test(function),
            inputs,
            world.types_mut(),
        );
        ExecutableKey {
            activation,
            need: ExecutableNeed::Value,
        }
    }

    #[test]
    fn return_payload_is_owned_only_by_its_caller() {
        let mut world = World::new();
        let caller = fake_call_executable(&mut world, 10, 11, &[]);
        let callee = fake_call_executable(&mut world, 10, 12, &[]);
        let caller_symbol = transport_executable_symbol(&caller, world.types());
        let callee_symbol = transport_executable_symbol(&callee, world.types());
        let callsite = CallSiteId::from_u32(7);

        let positions = return_flow_transport_positions(
            &caller_symbol,
            callsite,
            &ControlDestination::Return,
            [callee_symbol.clone()],
        );

        assert!(positions.contains(&TransportPosition::ReturnPayload {
            executable: caller_symbol,
            callsite,
        }));
        assert!(positions.contains(&TransportPosition::ExecutableReturn {
            executable: callee_symbol.clone(),
        }));
        assert!(!positions.contains(&TransportPosition::ReturnPayload {
            executable: callee_symbol,
            callsite,
        }));
    }

    #[test]
    fn local_no_return_flow_carries_exact_return_endpoint() {
        let mut world = World::new();
        let callee = fake_call_executable(&mut world, 100, 102, &[]);
        let target = CallTarget::Local(callee.clone());
        let flow = exact_no_return_flow(&world, &target);

        assert_eq!(
            flow,
            CallReturnFlow::NoReturn {
                local_source: Some(TransportPosition::ExecutableReturn {
                    executable: transport_executable_symbol(&callee, world.types()),
                }),
            }
        );
    }

    /// What static target evidence stands behind the closure callsite under
    /// test -- the axis that decides how the edge is lowered.
    #[derive(Clone, Copy)]
    enum ClosureCallEvidence {
        /// Two settled targets, each with a return type.
        AmbiguousReturning,
        /// Two settled targets, none of which returns.
        AmbiguousNonReturning,
        /// No summary at all. This is the standing state for a callable that
        /// arrived from outside the analysed world -- a mailbox message -- and
        /// no later evidence will ever name a target for it (fz-kdt.130).
        Unnamed,
    }

    impl ClosureCallEvidence {
        fn summary_targets_return(self) -> bool {
            matches!(self, Self::AmbiguousReturning)
        }

        /// Whether the callsite's semantic result carries a value. An unnamed
        /// callee still produces one: only its *targets* are unknown.
        fn call_returns(self) -> bool {
            !matches!(self, Self::AmbiguousNonReturning)
        }
    }

    fn try_materialize_closure_edge(
        evidence: ClosureCallEvidence,
        carrier: TransportCarrier,
    ) -> (World, Result<Option<MaterializedCallEdge>, FatalError>) {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let caller = fake_call_executable(&mut world, 300, 301, &[]);
        let callsite = CallSiteId::from_u32(7);
        let key = CallSiteKey {
            activation: caller.activation.clone(),
            callsite,
        };
        let targets_return = evidence.summary_targets_return();
        if !matches!(evidence, ClosureCallEvidence::Unnamed) {
            world.define_callsite_summary(
                key,
                CallSiteResolution::Resolved(CallSiteSummary {
                    targets: [302, 303]
                        .into_iter()
                        .map(|function| CallTargetSummary {
                            callee: SelectedCallee::Function(FunctionId::for_test(function)),
                            surface_inputs: vec![int],
                            activation: None,
                            activation_inputs: None,
                            extern_params: None,
                            return_ty: targets_return.then_some(int),
                        })
                        .collect(),
                    return_ty: targets_return.then_some(int),
                }),
            );
        }
        let call_returns = evidence.call_returns();
        let result_value = ValueId::from_u32(2);
        let analysis = ActivationAnalysis {
            input_rows: Vec::new(),
            entry_reachability: EntryReachability::new(Vec::new(), false),
            reachable_entries: Vec::new(),
            callsites: Vec::new(),
            latent_executables: Vec::new(),
            value_types: call_returns.then_some((result_value, int)).into_iter().collect(),
        };
        let positions = if call_returns {
            let caller_symbol = transport_executable_symbol(&caller, world.types());
            let caller_return = TransportPosition::ExecutableReturn {
                executable: caller_symbol.clone(),
            };
            let payload = TransportPosition::ReturnPayload {
                executable: caller_symbol,
                callsite,
            };
            let shape = world.intern_shape(ShapeDescr::Nothing);
            vec![
                (caller_return, TransportLayout::structural(shape)),
                (
                    payload,
                    TransportLayout {
                        structural: shape,
                        carrier: TransportCarrier::ValueRef(LaneId::for_test(0)),
                    },
                ),
            ]
        } else {
            Vec::new()
        };
        let codegen_seam_facts = Vec::new();
        let transport_plan = ArtifactTransportLookup {
            positions: &positions,
            codegen_seam_facts: &codegen_seam_facts,
        };
        let callee_layout = TransportLayout {
            structural: world.intern_shape(ShapeDescr::Nothing),
            carrier,
        };
        let summaries = world
            .callsite_summary(&CallSiteKey {
                activation: caller.activation.clone(),
                callsite,
            })
            .cloned()
            .map(|summary| HashMap::from([(callsite, summary)]))
            .unwrap_or_default();
        let edge = materialize_closure_call_edge(
            &mut world,
            &tel,
            RootId::for_test(300),
            &transport_plan,
            &caller,
            &analysis,
            &summaries,
            callee_layout,
            ExecutableNeed::Value,
            callsite,
            result_value,
            &ControlDestination::Return,
            &[],
            &HashMap::new(),
        );
        (world, edge)
    }

    fn materialize_closure_edge(evidence: ClosureCallEvidence) -> (World, MaterializedCallEdge) {
        let (world, edge) = try_materialize_closure_edge(evidence, TransportCarrier::ValueRef(LaneId::for_test(0)));
        let edge = edge
            .expect("materialization should not fail")
            .expect("a closure call over a runtime callable should produce an edge");
        (world, edge)
    }

    #[test]
    fn materialize_closure_call_edge_routes_ambiguous_multi_target_through_indirect() {
        let (_world, edge) = materialize_closure_edge(ClosureCallEvidence::AmbiguousReturning);
        let CallEdge::Indirect(CallReturnFlow::Continue {
            source,
            payload,
            caller_return,
        }) = edge.target
        else {
            panic!("returning multi-target closure call should carry indirect return flow")
        };
        assert_eq!(source, payload);
        assert_ne!(source, caller_return);
    }

    #[test]
    fn materialize_closure_call_edge_routes_settled_empty_multi_target_without_a_result_value() {
        let (world, edge) = materialize_closure_edge(ClosureCallEvidence::AmbiguousNonReturning);
        assert!(world.types().is_empty(&edge.return_ty));
        assert_eq!(
            edge.target,
            CallEdge::Indirect(CallReturnFlow::NoReturn { local_source: None })
        );
    }

    #[test]
    fn materialize_closure_call_edge_rejects_absent_multi_target_carrier() {
        let (_world, edge) =
            try_materialize_closure_edge(ClosureCallEvidence::AmbiguousReturning, TransportCarrier::Absent);
        assert!(edge.is_err());
    }

    /// fz-kdt.130. A callable that arrived through the mailbox names no target
    /// and never will, but it is a real value the boxed-apply wrapper can call.
    /// Reading "no targets" as the empty type made this a `NoReturn` edge, and
    /// native lowering turns `NoReturn` into a tail call -- which silently drops
    /// everything the caller meant to do after the call. The carrier decides.
    #[test]
    fn materialize_closure_call_edge_calls_an_unnamed_callable_and_comes_back() {
        let (world, edge) = materialize_closure_edge(ClosureCallEvidence::Unnamed);
        assert!(!world.types().is_empty(&edge.return_ty));
        assert!(
            matches!(edge.target, CallEdge::Indirect(CallReturnFlow::Continue { .. })),
            "an unnamed callable behind a runtime carrier must return to its caller, got {:?}",
            edge.target
        );
    }

    /// The other side of that line: with no carrier AND no evidence there is
    /// nothing to call, so the dead-call lowering still stands (fz-f98.18).
    #[test]
    fn materialize_closure_call_edge_keeps_the_dead_call_when_nothing_can_be_called() {
        let (world, edge) = try_materialize_closure_edge(ClosureCallEvidence::Unnamed, TransportCarrier::Absent);
        let edge = edge
            .expect("materialization should not fail")
            .expect("a dead closure call still needs an edge to carry its return flow");
        assert!(world.types().is_empty(&edge.return_ty));
        assert_eq!(
            edge.target,
            CallEdge::Indirect(CallReturnFlow::NoReturn { local_source: None })
        );
    }
}
