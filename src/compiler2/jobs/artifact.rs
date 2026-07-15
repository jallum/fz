//! Compiler2 artifact projection jobs.
//!
//! This module produces executable-scoped backend products on demand. Each
//! producer names the exact fact or product it needs instead of deriving a
//! root-wide projection stack.

use std::collections::{HashMap, HashSet};

use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::extern_contract::extern_ty_from_name;
use crate::parser::lexer::Tok;
use crate::source::Span;

use super::super::artifact::{
    AbiReadyCallEdge, AbiReadyExecutable, AbiValueRepr, BackendReturnLayout, BackendSemanticInputLayout,
    BackendValueLayout, CallEdge, CallReturnFlow, CallTarget, DirectCallEdge, DispatchCallArm, DispatchCallEdge,
    DispatchCallMiss, EffectSummary, ExecutableDispatch, MaterializedCallEdge, MaterializedExecutable,
    MaterializedExecutableTransport,
};
use super::super::body::{
    CallArg, CallSiteId, ControlDestination, ControlEntryId, ControlEntryOrigin, LoweredBody, LoweredEntry,
    LoweredStep, LoweredTail, ValueId,
};
use super::super::drive::FactKey;
use super::super::facts::FactUse;
use super::super::identity::{ActivationKey, ExecutableKey, ExecutableNeed, RootId};
use super::super::pull::{
    ProductKey, ProductValue, PullOutcome, PullSession, PullWait, TransportCarrier, TransportLayout,
};
use super::super::scheduler::FatalError;
use super::super::semantic::{
    ActivationAnalysis, CallSiteKey, CallSiteSummary, CallTargetSummary, SelectedCallee, ShapeDemand,
};
use super::super::transport::{
    ActivationSymbol, BoundaryFacts, BoundaryId, CallableFacts, CallableId, CodegenLaneRepr, CodegenSeam,
    CodegenSeamFact, ExecutableSymbol, LaneId, ShapeDescr, ShapeId, TransportPosition,
};
use super::super::types::{Ty, Types};
use super::super::world::World;
use super::semantic::executable_callsite_needs;

const UNREACHABLE_CONTROL_ATOM: &str = "compiler2_unreachable_control";

pub(crate) fn produce_materialized_executable_product(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    session: &mut PullSession,
    executable: &ExecutableKey,
) -> PullOutcome {
    let revisions = world.executable_artifact_revisions(executable);
    if let Some(materialized) = session.materialized_executable(executable).cloned() {
        if session.materialized_executable_is_fresh(executable, revisions) {
            return PullOutcome::Produced(ProductValue::MaterializedExecutable(Box::new(materialized)));
        }
        session.invalidate_artifact_products_for(executable);
    }
    let mut waits = Vec::new();
    let activation_fact = FactKey::ActivationAnalyzed(executable.activation.clone());
    if !world.fact_is_settled(&activation_fact) {
        waits.push(PullWait::Fact(FactUse::settled(activation_fact)));
    }
    let return_fact = FactKey::ReturnType(executable.activation.clone());
    if !world.fact_is_settled(&return_fact) {
        waits.push(PullWait::Fact(FactUse::settled(return_fact)));
    }
    if session.memo().runtime_demand(executable).is_none() {
        waits.push(PullWait::Product(ProductKey::RuntimeDemand(executable.clone())));
    }
    if session
        .memo()
        .get(&ProductKey::OutgoingInputEdges(executable.clone()))
        .is_none()
    {
        waits.push(PullWait::Product(ProductKey::OutgoingInputEdges(executable.clone())));
    }
    if let Some(analysis) = world.activation_analysis(&executable.activation) {
        for callsite in &analysis.callsites {
            let fact = FactKey::CallSiteSummary(CallSiteKey {
                activation: executable.activation.clone(),
                callsite: *callsite,
            });
            if !world.fact_is_settled(&fact) {
                waits.push(PullWait::Fact(FactUse::settled(fact)));
            }
        }
    }
    let return_position = TransportPosition::ExecutableReturn {
        executable: transport_executable_symbol(executable, world.types()),
    };
    if transport_shape_product_pending(session, &return_position) {
        waits.push(PullWait::Product(ProductKey::TransportShape(return_position)));
    }
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }

    let analysis = world
        .activation_analysis(&executable.activation)
        .cloned()
        .expect("settled activation analysis should be readable for materialized product");
    let return_ty = world
        .activation_return(&executable.activation)
        .unwrap_or_else(|| world.types_mut().none());
    let lowered = world.lowered_body(executable.activation.function);
    let (dispatch_outcomes, retained_entries) = match lowered {
        LoweredBody::Clauses { ref clauses, .. } => {
            let mut entries = analysis.reachable_entries.clone();
            entries.extend(
                analysis
                    .reachable_clauses
                    .iter()
                    .map(|clause| clauses[*clause as usize].entry),
            );
            entries.sort_by_key(|entry| entry.as_u32());
            entries.dedup();
            (analysis.reachable_clauses.clone(), entries)
        }
        LoweredBody::Extern { .. } => (analysis.reachable_clauses.clone(), analysis.reachable_entries.clone()),
    };
    let pruned = prune_lowered_body(lowered, &dispatch_outcomes, &retained_entries);
    let body = pruned.body;
    let callsite_args = super::super::body::callsite_call_args(&body);
    waits.extend(required_call_edge_transport_waits(
        world,
        session,
        executable,
        &analysis,
        &body,
        &callsite_args,
    ));
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }
    if session.memo().codegen_seam_facts(session.root()).is_none() {
        return PullOutcome::Waiting(vec![PullWait::Product(ProductKey::CodegenSeamFacts(session.root()))]);
    }
    let codegen_seam_facts = session
        .memo()
        .codegen_seam_facts(session.root())
        .expect("codegen seam facts product wait should have been satisfied");
    let transport_plan = session_transport_lookup(session, codegen_seam_facts);
    let call_edges = materialize_call_edges(
        world,
        tel,
        session.root(),
        &transport_plan,
        executable,
        &analysis,
        &body,
        &pruned.original_entry_ids,
        &callsite_args,
    )
    .expect("product materialization should use settled semantic facts")
    .expect("product materialization should have complete call edges after waits");
    let effects = local_effects(&body, &call_edges);
    let materialized = MaterializedExecutable {
        entry_dispatch: materialize_entry_dispatch(world, executable, &analysis),
        return_ty,
        runtime_demand: session
            .memo()
            .runtime_demand(executable)
            .cloned()
            .expect("runtime-demand product wait should have been satisfied"),
        transport: session_materialized_executable_transport(session, executable, world.types()),
        original_entry_ids: pruned.original_entry_ids,
        value_types: analysis.value_types,
        effects,
        body,
        call_edges,
    };
    session.record_materialized_executable(executable.clone(), materialized.clone());
    session.record_materialized_executable_revisions(executable.clone(), revisions);
    PullOutcome::Produced(ProductValue::MaterializedExecutable(Box::new(materialized)))
}

pub(crate) fn produce_executable_effects_product(
    _world: &mut World,
    _tel: &impl crate::telemetry::Telemetry,
    session: &mut PullSession,
    executable: &ExecutableKey,
) -> PullOutcome {
    if let Some(effects) = session.executable_effects(executable) {
        return PullOutcome::Produced(ProductValue::ExecutableEffects(effects));
    }
    let graph = match collect_effect_cone(session, executable) {
        Ok(graph) => graph,
        Err(waits) => return PullOutcome::Waiting(waits),
    };
    let scc = effect_scc_containing(executable, &graph.edges);
    let waits = effect_scc_external_waits(session, &scc, &graph.edges);
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }
    let settled = settle_effect_scc(session, &scc, &graph);
    for (key, effects) in &settled {
        session.record_executable_effects(key.clone(), *effects);
    }
    let effects = settled
        .get(executable)
        .copied()
        .expect("requested executable should belong to its effects SCC");
    PullOutcome::Produced(ProductValue::ExecutableEffects(effects))
}

struct EffectGraph {
    local: HashMap<ExecutableKey, EffectSummary>,
    edges: HashMap<ExecutableKey, Vec<ExecutableKey>>,
}

fn collect_effect_cone(session: &PullSession, executable: &ExecutableKey) -> Result<EffectGraph, Vec<PullWait>> {
    let mut local = HashMap::new();
    let mut edges = HashMap::new();
    let mut seen = HashSet::new();
    let mut stack = vec![executable.clone()];
    let mut waits = Vec::new();
    while let Some(current) = stack.pop() {
        if !seen.insert(current.clone()) {
            continue;
        }
        let Some(materialized) = session.materialized_executable(&current) else {
            waits.push(PullWait::Product(ProductKey::MaterializedExecutable(current)));
            continue;
        };
        local.insert(
            current.clone(),
            local_effects(&materialized.body, &materialized.call_edges),
        );
        let callees = materialized
            .call_edges
            .values()
            .flat_map(|edge| edge.target.local_callees())
            .cloned()
            .collect::<Vec<_>>();
        for callee in &callees {
            if session.executable_effects(callee).is_none() {
                stack.push(callee.clone());
            }
        }
        edges.insert(current, callees);
    }
    if waits.is_empty() {
        Ok(EffectGraph { local, edges })
    } else {
        Err(waits)
    }
}

fn effect_scc_containing(
    executable: &ExecutableKey,
    edges: &HashMap<ExecutableKey, Vec<ExecutableKey>>,
) -> HashSet<ExecutableKey> {
    let mut forward = HashSet::new();
    collect_effect_reachable(executable, edges, &mut forward);
    forward
        .iter()
        .filter(|candidate| {
            let mut reaches_entry = HashSet::new();
            collect_effect_reachable(candidate, edges, &mut reaches_entry);
            reaches_entry.contains(executable)
        })
        .cloned()
        .collect()
}

fn collect_effect_reachable(
    executable: &ExecutableKey,
    edges: &HashMap<ExecutableKey, Vec<ExecutableKey>>,
    out: &mut HashSet<ExecutableKey>,
) {
    if !out.insert(executable.clone()) {
        return;
    }
    for callee in edges.get(executable).into_iter().flatten() {
        collect_effect_reachable(callee, edges, out);
    }
}

fn effect_scc_external_waits(
    session: &PullSession,
    scc: &HashSet<ExecutableKey>,
    edges: &HashMap<ExecutableKey, Vec<ExecutableKey>>,
) -> Vec<PullWait> {
    let mut waits = Vec::new();
    for executable in scc {
        for callee in edges.get(executable).into_iter().flatten() {
            if scc.contains(callee) || session.executable_effects(callee).is_some() {
                continue;
            }
            let key = ProductKey::ExecutableEffects(callee.clone());
            if !session.product_is_in_progress(&key) {
                waits.push(PullWait::Product(key));
            }
        }
    }
    waits
}

fn settle_effect_scc(
    session: &PullSession,
    scc: &HashSet<ExecutableKey>,
    graph: &EffectGraph,
) -> HashMap<ExecutableKey, EffectSummary> {
    let mut settled = scc
        .iter()
        .map(|key| (*key).clone())
        .map(|key| {
            let effects = graph.local.get(&key).copied().unwrap_or_default();
            (key, effects)
        })
        .collect::<HashMap<_, _>>();
    loop {
        let snapshot = settled.clone();
        let mut changed = false;
        for key in scc {
            let mut effects = graph.local.get(key).copied().unwrap_or_default();
            for callee in graph.edges.get(key).into_iter().flatten() {
                if let Some(callee_effects) = snapshot
                    .get(callee)
                    .copied()
                    .or_else(|| session.executable_effects(callee))
                {
                    effects.union_with(callee_effects);
                }
            }
            if settled.get(key).copied() != Some(effects) {
                settled.insert(key.clone(), effects);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    settled
}

pub(crate) fn produce_abi_executable_product(
    world: &mut World,
    _tel: &impl crate::telemetry::Telemetry,
    session: &mut PullSession,
    executable: &ExecutableKey,
) -> PullOutcome {
    if let Some(abi) = session.abi_executable(executable).cloned() {
        return PullOutcome::Produced(ProductValue::AbiExecutable(Box::new(abi)));
    }
    let mut waits = Vec::new();
    if session.materialized_executable(executable).is_none() {
        waits.push(PullWait::Product(ProductKey::MaterializedExecutable(
            executable.clone(),
        )));
    }
    if session.executable_effects(executable).is_none() {
        waits.push(PullWait::Product(ProductKey::ExecutableEffects(executable.clone())));
    }
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }

    let mut materialized = session
        .materialized_executable(executable)
        .cloned()
        .expect("materialized executable product wait should have been satisfied");
    if let Some(effects) = session.executable_effects(executable) {
        materialized.effects = effects;
    }
    materialized.transport = session_materialized_executable_transport(session, executable, world.types());
    waits.extend(required_executable_transport_facts_waits(
        session,
        executable,
        &materialized,
        world.types(),
    ));
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }
    // `required_executable_transport_facts_waits` only reads `session`, so the
    // transport recorded above is still current: nothing settled in between
    // that would change it, and recomputing it here would just repeat the same
    // per-production scan for an identical answer.
    if session.memo().codegen_seam_facts(session.root()).is_none() {
        return PullOutcome::Waiting(vec![PullWait::Product(ProductKey::CodegenSeamFacts(session.root()))]);
    }
    let codegen_seam_facts = session
        .memo()
        .codegen_seam_facts(session.root())
        .expect("codegen seam facts product wait should have been satisfied");
    let transport_plan = session_transport_lookup(session, codegen_seam_facts);
    let plan = build_executable_abi_plan(world, executable, &materialized, &transport_plan);
    let abi = build_abi_executable(&materialized, &plan)
        .expect("per-executable ABI derivation should not require root fan-in");
    session.record_abi_executable(executable.clone(), abi.clone());
    PullOutcome::Produced(ProductValue::AbiExecutable(Box::new(abi)))
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
    positions: impl Iterator<Item = TransportPosition>,
    executable: &ExecutableKey,
    types: &Types,
) -> MaterializedExecutableTransport {
    let symbol = transport_executable_symbol(executable, types);
    let mut input_positions = Vec::new();
    let mut return_position = None;
    let mut resume_positions = Vec::new();
    let mut return_payload_positions = Vec::new();
    let mut entry_capture_positions = Vec::new();
    let mut call_arg_positions = Vec::new();
    let mut value_positions = Vec::new();
    for position in positions {
        match &position {
            TransportPosition::ExecutableInput { .. } => input_positions.push(position),
            TransportPosition::ExecutableReturn { .. } => return_position = Some(position),
            TransportPosition::ResumePayload { .. } => resume_positions.push(position),
            TransportPosition::ReturnPayload { .. } => return_payload_positions.push(position),
            TransportPosition::EntryCapture { .. } => entry_capture_positions.push(position),
            TransportPosition::CallArg { .. } => call_arg_positions.push(position),
            TransportPosition::Value { .. } => value_positions.push(position),
        }
    }
    sort_transport_positions(&mut input_positions);
    sort_transport_positions(&mut resume_positions);
    sort_transport_positions(&mut return_payload_positions);
    sort_transport_positions(&mut entry_capture_positions);
    sort_transport_positions(&mut call_arg_positions);
    sort_transport_positions(&mut value_positions);
    MaterializedExecutableTransport {
        executable: symbol,
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

fn session_materialized_executable_transport(
    session: &PullSession,
    executable: &ExecutableKey,
    types: &Types,
) -> MaterializedExecutableTransport {
    let symbol = transport_executable_symbol(executable, types);
    let mut positions = session
        .transport_shape_positions_for(&symbol)
        .cloned()
        .collect::<HashSet<_>>();
    positions.extend(session.demanded_capture_resume_positions_for(&symbol).cloned());
    materialized_executable_transport(positions.into_iter(), executable, types)
}

/// A per-production view onto the session's already-settled transport facts,
/// borrowed straight from `PullSession` instead of cloned. Every consumer in
/// this file does single-key lookups or a linear scan of `codegen_seam_facts`,
/// so this lookup carries only what materialized/ABI production actually
/// reads (contrast `MaterializedTransportPlan`, the root-scoped product built
/// once per root in `jobs/backend.rs`, which carries the fuller shape).
struct ArtifactTransportLookup<'a> {
    positions: &'a HashMap<TransportPosition, TransportLayout>,
    callables: &'a HashMap<CallableId, CallableFacts>,
    boundaries: &'a HashMap<BoundaryId, BoundaryFacts>,
    codegen_seam_facts: &'a [CodegenSeamFact],
}

fn session_transport_lookup<'a>(
    session: &'a PullSession,
    codegen_seam_facts: &'a [CodegenSeamFact],
) -> ArtifactTransportLookup<'a> {
    ArtifactTransportLookup {
        positions: session.transport_layouts(),
        callables: session.callable_facts_inventory(),
        boundaries: session.boundary_facts_inventory(),
        codegen_seam_facts,
    }
}

/// Produces `ProductKey::CodegenSeamFacts(root)`: the session-wide codegen
/// seam-fact set, computed once per root per invalidation epoch and read
/// (never recomputed) by both `produce_materialized_executable_product` and
/// `produce_abi_executable_product`. This has no waits of its own -- like
/// `produce_callable_facts`/`produce_boundary_facts`, it always succeeds
/// immediately over whatever `BoundaryFacts` the session has recorded so far
/// -- so its callers are responsible for having already waited on the
/// specific boundaries/transport shapes THEY need before pulling this
/// product (`required_call_edge_transport_waits` and
/// `required_executable_transport_facts_waits` already do this). Staleness
/// is instead prevented on the write side: `PullSession::record_boundary_facts`
/// invalidates this product's memo entry whenever a boundary's recorded
/// facts actually change, so a later pull that observes a newer boundary
/// re-derives the set instead of serving a snapshot that predates it.
pub(crate) fn produce_codegen_seam_facts_product(
    world: &mut World,
    _tel: &impl crate::telemetry::Telemetry,
    session: &mut PullSession,
    root: RootId,
) -> PullOutcome {
    debug_assert_eq!(
        root,
        session.root(),
        "codegen seam facts are keyed by the session's own root"
    );
    let facts = session_codegen_publication_seam_facts(world, session);
    PullOutcome::Produced(ProductValue::CodegenSeamFacts(facts))
}

fn session_codegen_publication_seam_facts(world: &World, session: &PullSession) -> Box<[CodegenSeamFact]> {
    let mut out = Vec::new();
    for boundary in session.boundary_facts_inventory().keys().copied() {
        let descr = world.boundary(boundary);
        for lane in descr
            .published_capture_lanes
            .iter()
            .chain(descr.published_arg_lanes.iter())
            .chain(descr.published_return_lanes.iter())
            .copied()
        {
            out.push(CodegenSeamFact {
                seam: CodegenSeam::CallableBoundary { boundary },
                shape: None,
                lane,
                repr: codegen_repr_for_lane(world, lane),
            });
        }
        let Some(facts) = session.boundary_facts(boundary) else {
            continue;
        };
        if facts.publications.is_empty() {
            continue;
        }
        out.push(CodegenSeamFact {
            seam: CodegenSeam::FirstClassPublication { boundary },
            shape: None,
            lane: descr.published_value_lane,
            repr: CodegenLaneRepr::ValueRef,
        });
        for publication in facts.publications.iter() {
            push_session_publication_codegen_seam(publication, descr.published_value_lane, &mut out);
        }
    }
    // A structural key, not a `format!("{fact:?}")` comparator: the fields
    // already carry stable numeric/interned identity, so comparing them
    // directly gives the same deterministic order without formatting (and
    // allocating a `String` for) every fact on every production. Cached
    // because the key still allocates its owner `Vec<Ty>` per element.
    out.sort_by_cached_key(codegen_seam_fact_sort_key);
    out.into_boxed_slice()
}

pub(crate) type CodegenSeamOwnerKey = (u8, u32, Option<Ty>, Vec<Ty>, u8, usize, u32);
pub(crate) type CodegenSeamSortKey = (u8, CodegenSeamOwnerKey, u32, u32, u32, u32, u8);

pub(crate) fn codegen_seam_fact_sort_key(fact: &CodegenSeamFact) -> CodegenSeamSortKey {
    let (kind, owner, secondary, tertiary) = codegen_seam_kind_key(&fact.seam);
    (
        kind,
        owner,
        secondary,
        tertiary,
        fact.shape.map(ShapeId::as_u32).unwrap_or(u32::MAX),
        fact.lane.as_u32(),
        codegen_lane_repr_rank(fact.repr),
    )
}

fn executable_owner_key(executable: &ExecutableSymbol) -> CodegenSeamOwnerKey {
    let (function, arrow, inputs, need0, need1) = transport_executable_sort_key(executable);
    (0, function, Some(arrow), inputs, need0, need1, 0)
}

fn boundary_owner_key(boundary: BoundaryId) -> CodegenSeamOwnerKey {
    (1, 0, None, Vec::new(), 0, 0, boundary.as_u32())
}

fn codegen_seam_kind_key(seam: &CodegenSeam) -> (u8, CodegenSeamOwnerKey, u32, u32) {
    match seam {
        CodegenSeam::FunctionEntry {
            executable,
            semantic_index,
        } => (0, executable_owner_key(executable), *semantic_index as u32, 0),
        CodegenSeam::BlockParam { executable, entry } => (1, executable_owner_key(executable), entry.as_u32(), 0),
        CodegenSeam::EntryCapture {
            executable,
            entry,
            capture_index,
        } => (
            2,
            executable_owner_key(executable),
            entry.as_u32(),
            *capture_index as u32,
        ),
        CodegenSeam::ReturnDelivery { executable } => (3, executable_owner_key(executable), 0, 0),
        CodegenSeam::ContinuationEntry {
            executable,
            callsite,
            entry,
        } => (4, executable_owner_key(executable), callsite.as_u32(), entry.as_u32()),
        CodegenSeam::ReturnContinuation { executable, callsite } => {
            (5, executable_owner_key(executable), callsite.as_u32(), 0)
        }
        CodegenSeam::TailCall { executable, callsite } => (6, executable_owner_key(executable), callsite.as_u32(), 0),
        CodegenSeam::CallableBoundary { boundary } => (7, boundary_owner_key(*boundary), 0, 0),
        CodegenSeam::ExternBoundary { executable } => (8, executable_owner_key(executable), 0, 0),
        CodegenSeam::FirstClassPublication { boundary } => (9, boundary_owner_key(*boundary), 0, 0),
    }
}

fn codegen_lane_repr_rank(repr: CodegenLaneRepr) -> u8 {
    match repr {
        CodegenLaneRepr::ValueRef => 0,
        CodegenLaneRepr::RawInt => 1,
        CodegenLaneRepr::RawF64 => 2,
        CodegenLaneRepr::RawAtom => 3,
    }
}

fn push_session_publication_codegen_seam(
    publication: &TransportPosition,
    lane: LaneId,
    out: &mut Vec<CodegenSeamFact>,
) {
    let repr = CodegenLaneRepr::ValueRef;
    match publication {
        TransportPosition::ExecutableInput {
            executable,
            semantic_index,
        } => out.push(CodegenSeamFact {
            seam: CodegenSeam::FunctionEntry {
                executable: executable.clone(),
                semantic_index: *semantic_index,
            },
            shape: None,
            lane,
            repr,
        }),
        TransportPosition::ExecutableReturn { executable } => out.push(CodegenSeamFact {
            seam: CodegenSeam::ReturnDelivery {
                executable: executable.clone(),
            },
            shape: None,
            lane,
            repr,
        }),
        TransportPosition::ReturnPayload { executable, callsite } => out.push(CodegenSeamFact {
            seam: CodegenSeam::ReturnContinuation {
                executable: executable.clone(),
                callsite: *callsite,
            },
            shape: None,
            lane,
            repr,
        }),
        TransportPosition::ResumePayload {
            executable,
            callsite: Some(callsite),
            entry,
        } => out.push(CodegenSeamFact {
            seam: CodegenSeam::ContinuationEntry {
                executable: executable.clone(),
                callsite: *callsite,
                entry: *entry,
            },
            shape: None,
            lane,
            repr,
        }),
        TransportPosition::ResumePayload {
            executable,
            callsite: None,
            entry,
        } => out.push(CodegenSeamFact {
            seam: CodegenSeam::BlockParam {
                executable: executable.clone(),
                entry: *entry,
            },
            shape: None,
            lane,
            repr,
        }),
        TransportPosition::EntryCapture {
            executable,
            entry,
            capture_index,
        } => {
            out.push(CodegenSeamFact {
                seam: CodegenSeam::EntryCapture {
                    executable: executable.clone(),
                    entry: *entry,
                    capture_index: *capture_index,
                },
                shape: None,
                lane,
                repr,
            });
        }
        TransportPosition::CallArg { .. } | TransportPosition::Value { .. } => {}
    }
}

fn required_entry_capture_transport_waits(
    session: &PullSession,
    executable: &ExecutableKey,
    materialized: &MaterializedExecutable,
    types: &Types,
) -> Vec<PullWait> {
    let LoweredBody::Clauses { entries, .. } = &materialized.body else {
        return Vec::new();
    };
    let symbol = transport_executable_symbol(executable, types);
    let mut waits = Vec::new();
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
            if transport_shape_product_pending(session, &position) {
                waits.push(PullWait::Product(ProductKey::TransportShape(position)));
            }
        }
    }
    waits
}

/// Every transport-shape product an executable's ABI must have settled before it
/// can be lowered: its input, entry-capture, resume, and local-backend positions
/// (its return position is already driven by the materialized product). Pulling
/// these `TransportShape` products records the executable's shapes and, through
/// the transport component projection, publishes the callable/boundary facts and
/// grows the demand closure. The ABI product drives them before building the ABI
/// struct; the transport-facts-only path drives them without building anything.
pub(crate) fn required_executable_transport_facts_waits(
    session: &PullSession,
    executable: &ExecutableKey,
    materialized: &MaterializedExecutable,
    types: &Types,
) -> Vec<PullWait> {
    let mut waits = Vec::new();
    waits.extend(required_executable_input_transport_waits(
        session,
        executable,
        materialized,
        types,
    ));
    waits.extend(required_entry_capture_transport_waits(
        session,
        executable,
        materialized,
        types,
    ));
    waits.extend(required_resume_transport_waits(
        session,
        executable,
        materialized,
        types,
    ));
    waits.extend(required_local_backend_transport_waits(
        session,
        executable,
        materialized,
        types,
    ));
    waits
}

fn required_executable_input_transport_waits(
    session: &PullSession,
    executable: &ExecutableKey,
    materialized: &MaterializedExecutable,
    types: &Types,
) -> Vec<PullWait> {
    let symbol = transport_executable_symbol(executable, types);
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
            transport_shape_product_pending(session, &position)
                .then_some(PullWait::Product(ProductKey::TransportShape(position)))
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

fn required_resume_transport_waits(
    session: &PullSession,
    executable: &ExecutableKey,
    materialized: &MaterializedExecutable,
    types: &Types,
) -> Vec<PullWait> {
    let LoweredBody::Clauses { entries, .. } = &materialized.body else {
        return Vec::new();
    };
    let symbol = transport_executable_symbol(executable, types);
    let mut waits = Vec::new();
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
        if transport_shape_product_pending(session, &position) {
            waits.push(PullWait::Product(ProductKey::TransportShape(position)));
        }
    }
    waits
}

fn required_local_backend_transport_waits(
    session: &PullSession,
    executable: &ExecutableKey,
    materialized: &MaterializedExecutable,
    types: &Types,
) -> Vec<PullWait> {
    let LoweredBody::Clauses { clauses, entries, .. } = &materialized.body else {
        return Vec::new();
    };
    let symbol = transport_executable_symbol(executable, types);
    let mut waits = Vec::new();
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
        if transport_shape_product_pending(session, &position) {
            waits.push(PullWait::Product(ProductKey::TransportShape(position)));
        }
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
        if transport_shape_product_pending(session, &value_position) {
            waits.push(PullWait::Product(ProductKey::TransportShape(value_position)));
        }
        for semantic_index in 0..args.len() {
            let position = TransportPosition::CallArg {
                executable: symbol.clone(),
                callsite,
                semantic_index,
            };
            if transport_shape_product_pending(session, &position) {
                waits.push(PullWait::Product(ProductKey::TransportShape(position)));
            }
        }
        let return_payload = TransportPosition::ReturnPayload {
            executable: symbol.clone(),
            callsite,
        };
        if transport_shape_product_pending(session, &return_payload) {
            waits.push(PullWait::Product(ProductKey::TransportShape(return_payload)));
        }
    }
    waits
}

fn transport_shape_product_pending(session: &PullSession, position: &TransportPosition) -> bool {
    session.transport_shape_fact(position).is_none()
        && session
            .memo()
            .get(&ProductKey::TransportShape(position.clone()))
            .is_none()
}

fn step_result_values(step: &LoweredStep) -> Vec<super::super::body::ValueId> {
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

fn required_call_edge_transport_waits(
    world: &mut World,
    session: &PullSession,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    body: &LoweredBody,
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
) -> Vec<PullWait> {
    let LoweredBody::Clauses { entries, .. } = body else {
        return Vec::new();
    };
    let caller_symbol = transport_executable_symbol(executable, world.types());
    let callsite_needs = callsite_needs_for_body(body, executable.need);
    let summaries = analysis
        .callsites
        .iter()
        .filter_map(|callsite| {
            let key = CallSiteKey {
                activation: executable.activation.clone(),
                callsite: *callsite,
            };
            world
                .callsite_summary(&key)
                .cloned()
                .map(|summary| (*callsite, summary))
        })
        .collect::<HashMap<_, _>>();
    let mut waits = HashSet::new();
    for entry in entries {
        match &entry.tail {
            LoweredTail::DirectCall { callsite, dest, .. } => {
                record_return_flow_transport_waits(
                    session,
                    &mut waits,
                    &caller_symbol,
                    *callsite,
                    dest,
                    summaries.get(callsite).into_iter().flat_map(|summary| {
                        summary.targets.iter().filter_map(|target| {
                            target.activation.clone().map(|activation| ExecutableKey {
                                activation,
                                need: callsite_needs.get(callsite).copied().unwrap_or(ExecutableNeed::Value),
                            })
                        })
                    }),
                    world.types(),
                );
            }
            LoweredTail::ClosureCall {
                callsite, callee, dest, ..
            } => {
                let has_callable_flow = session
                    .memo()
                    .runtime_demand(executable)
                    .is_some_and(|demand| demand.callable_flows.contains_key(callee));
                if has_callable_flow {
                    push_optional_transport_shape_wait(
                        session,
                        &mut waits,
                        TransportPosition::Value {
                            executable: caller_symbol.clone(),
                            value: *callee,
                        },
                    );
                    for (semantic_index, _) in callsite_args.get(callsite).into_iter().flatten().enumerate() {
                        push_optional_transport_shape_wait(
                            session,
                            &mut waits,
                            TransportPosition::CallArg {
                                executable: caller_symbol.clone(),
                                callsite: *callsite,
                                semantic_index,
                            },
                        );
                    }
                }
                let mut callees = summaries
                    .get(callsite)
                    .into_iter()
                    .flat_map(|summary| {
                        summary.targets.iter().filter_map(|target| {
                            target.activation.clone().map(|activation| ExecutableKey {
                                activation,
                                need: callsite_needs.get(callsite).copied().unwrap_or(ExecutableNeed::Value),
                            })
                        })
                    })
                    .collect::<Vec<_>>();
                if let Some(shape) = session.transport_shape(&TransportPosition::Value {
                    executable: caller_symbol.clone(),
                    value: *callee,
                }) && let ShapeDescr::Callable(callable) = world.shape(shape)
                    && let Some(facts) = session.callable_facts(*callable)
                {
                    for edge in &facts.direct_edges {
                        callees.push(ExecutableKey {
                            activation: world.activation_key(
                                session.root(),
                                edge.resolution.activation.function,
                                edge.resolution.activation.input.as_ref(),
                            ),
                            need: edge.resolution.need,
                        });
                    }
                }
                record_return_flow_transport_waits(
                    session,
                    &mut waits,
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
    waits.into_iter().collect()
}

fn record_return_flow_transport_waits(
    session: &PullSession,
    waits: &mut HashSet<PullWait>,
    caller_symbol: &ExecutableSymbol,
    callsite: CallSiteId,
    dest: &ControlDestination,
    callees: impl IntoIterator<Item = ExecutableKey>,
    types: &Types,
) {
    let ControlDestination::Return = dest else {
        return;
    };
    push_transport_shape_wait(
        session,
        waits,
        TransportPosition::ExecutableReturn {
            executable: caller_symbol.clone(),
        },
    );
    push_transport_shape_wait(
        session,
        waits,
        TransportPosition::ReturnPayload {
            executable: caller_symbol.clone(),
            callsite,
        },
    );
    for callee in callees {
        let callee_symbol = transport_executable_symbol(&callee, types);
        push_transport_shape_wait(
            session,
            waits,
            TransportPosition::ExecutableReturn {
                executable: callee_symbol.clone(),
            },
        );
        push_optional_transport_shape_wait(
            session,
            waits,
            TransportPosition::ReturnPayload {
                executable: callee_symbol,
                callsite,
            },
        );
    }
}

fn push_transport_shape_wait(session: &PullSession, waits: &mut HashSet<PullWait>, position: TransportPosition) {
    if transport_shape_product_pending(session, &position) {
        waits.insert(PullWait::Product(ProductKey::TransportShape(position)));
    }
}

fn push_optional_transport_shape_wait(
    session: &PullSession,
    waits: &mut HashSet<PullWait>,
    position: TransportPosition,
) {
    if transport_shape_product_pending(session, &position) {
        waits.insert(PullWait::Product(ProductKey::TransportShape(position)));
    }
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

/// Canonical packaging order for one MaterializedExecutableTransport field
/// vector. Every call site sorts a single-variant, single-executable
/// partition (the six category vectors `materialized_executable_transport`
/// builds), so the key carries only the variant-local STRUCTURAL
/// discriminants -- semantic indexes, callsites, entries -- and no
/// executable component (constant within the vector) and no interned types.
fn sort_transport_positions(positions: &mut [TransportPosition]) {
    positions.sort_by_key(transport_position_local_sort_key);
}

pub(crate) type TransportPositionLocalSortKey = (u32, u32, usize);
pub(crate) type TransportExecutableSortKey = (u32, Ty, Vec<Ty>, u8, usize);

fn transport_position_local_sort_key(position: &TransportPosition) -> TransportPositionLocalSortKey {
    match position {
        TransportPosition::ExecutableInput { semantic_index, .. } => (0, 0, *semantic_index),
        TransportPosition::ExecutableReturn { .. } => (0, 0, 0),
        TransportPosition::ResumePayload { callsite, entry, .. } => (
            callsite.map(|callsite| callsite.as_u32()).unwrap_or(u32::MAX),
            entry.as_u32(),
            0,
        ),
        TransportPosition::ReturnPayload { callsite, .. } => (callsite.as_u32(), 0, 0),
        TransportPosition::EntryCapture {
            entry, capture_index, ..
        } => (0, entry.as_u32(), *capture_index),
        TransportPosition::CallArg {
            callsite,
            semantic_index,
            ..
        } => (callsite.as_u32(), 0, *semantic_index),
        TransportPosition::Value { value, .. } => (value.as_u32(), 0, 0),
    }
}

fn transport_executable_sort_key(executable: &ExecutableSymbol) -> TransportExecutableSortKey {
    let need = match executable.need {
        ExecutableNeed::Value => (0, 0),
        ExecutableNeed::TupleFields(arity) => (1, arity),
    };
    (
        executable.activation.function.as_u32(),
        executable.activation.arrow,
        executable.activation.input.to_vec(),
        need.0,
        need.1,
    )
}

pub(crate) type TransportPositionGlobalSortKey = (TransportExecutableSortKey, u8, TransportPositionLocalSortKey);

/// Canonical packaging order for a GLOBAL (cross-executable) set of
/// `TransportPosition`s: the owning executable's structural key, then the
/// variant discriminant, then the variant-local discriminants. Structural on
/// interned ids, so PER-PROCESS deterministic -- the same guarantee the old
/// `format!("{position:?}")` keys gave (Debug prints those same interned ids)
/// without formatting every position on every comparison.
pub(crate) fn transport_position_global_sort_key(position: &TransportPosition) -> TransportPositionGlobalSortKey {
    let variant = match position {
        TransportPosition::ExecutableInput { .. } => 0,
        TransportPosition::ExecutableReturn { .. } => 1,
        TransportPosition::ResumePayload { .. } => 2,
        TransportPosition::ReturnPayload { .. } => 3,
        TransportPosition::CallArg { .. } => 4,
        TransportPosition::EntryCapture { .. } => 5,
        TransportPosition::Value { .. } => 6,
    };
    (
        transport_executable_sort_key(position.executable()),
        variant,
        transport_position_local_sort_key(position),
    )
}

fn materialize_call_edges(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    transport_plan: &ArtifactTransportLookup<'_>,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    body: &LoweredBody,
    original_entry_ids: &[ControlEntryId],
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
) -> Result<Option<HashMap<CallSiteId, MaterializedCallEdge>>, FatalError> {
    let mut call_edges = HashMap::new();
    let callsite_needs = callsite_needs_for_body(body, executable.need);
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
                if let Some(edge) = materialize_closure_call_edge(
                    world,
                    tel,
                    root_id,
                    transport_plan,
                    executable,
                    analysis,
                    callsite_needs.get(callsite).copied().unwrap_or(ExecutableNeed::Value),
                    *callsite,
                    *callee,
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
    need: ExecutableNeed,
    callsite: CallSiteId,
    dest: &ControlDestination,
    original_entry_ids: &[ControlEntryId],
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
) -> Result<Option<MaterializedCallEdge>, FatalError> {
    let key = CallSiteKey {
        activation: executable.activation.clone(),
        callsite,
    };
    if !world.has_fact(&FactKey::CallSiteSummary(key.clone())) {
        return Ok(None);
    }
    let Some(summary) = world.callsite_summary(&key).cloned() else {
        return Ok(None);
    };
    if let Some(target) = summary.single_target().cloned() {
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
    let dispatch = super::super::callsite_dispatch::dispatch_from_callsite_summary(world.types_mut(), &summary);
    let Some(dispatch) = dispatch.map_err(|error| {
        incomplete_semantic_plan(
            tel,
            root_id,
            format!(
                "materialization could not build dispatch for multi-target direct callsite {}: {error:?}",
                callsite.as_u32()
            ),
        )
    })?
    else {
        return Ok(None);
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
    if arms.is_empty() {
        return Err(incomplete_semantic_plan(
            tel,
            root_id,
            format!(
                "multi-target direct callsite {} has no dispatch arms",
                callsite.as_u32()
            ),
        ));
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
    need: ExecutableNeed,
    callsite: CallSiteId,
    callee_value: ValueId,
    result_value: ValueId,
    dest: &ControlDestination,
    original_entry_ids: &[ControlEntryId],
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
) -> Result<Option<MaterializedCallEdge>, FatalError> {
    match materialize_transport_closure_call_edge(
        world,
        tel,
        root_id,
        transport_plan,
        executable,
        analysis,
        callsite,
        callee_value,
        result_value,
        dest,
        original_entry_ids,
        callsite_args,
    )? {
        TransportClosureCallEdge::Direct { edge, return_ty } => {
            return Ok(Some(MaterializedCallEdge {
                target: CallEdge::Direct(edge),
                return_ty,
            }));
        }
        TransportClosureCallEdge::PublicIndirect { return_flow, return_ty } => {
            return Ok(Some(MaterializedCallEdge {
                target: CallEdge::Indirect(return_flow),
                return_ty,
            }));
        }
        TransportClosureCallEdge::Absent => {}
    }
    let key = CallSiteKey {
        activation: executable.activation.clone(),
        callsite,
    };
    let Some(summary) = world.callsite_summary(&key).cloned() else {
        return Ok(None);
    };
    let Some(target) = summary.single_target().cloned() else {
        if summary.targets.len() >= 2 {
            let return_ty =
                public_indirect_return_ty(world, tel, root_id, analysis, Some(&summary), callsite, result_value)?;
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
        return Ok(None);
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

enum TransportClosureCallEdge {
    Direct {
        edge: DirectCallEdge<ExecutableKey>,
        return_ty: Ty,
    },
    PublicIndirect {
        return_flow: CallReturnFlow,
        return_ty: Ty,
    },
    Absent,
}

fn materialize_transport_closure_call_edge(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    transport_plan: &ArtifactTransportLookup<'_>,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    callsite: CallSiteId,
    callee_value: ValueId,
    result_value: ValueId,
    dest: &ControlDestination,
    original_entry_ids: &[ControlEntryId],
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
) -> Result<TransportClosureCallEdge, FatalError> {
    let caller_symbol = transport_executable_symbol(executable, world.types());
    let callee_position = TransportPosition::Value {
        executable: caller_symbol.clone(),
        value: callee_value,
    };
    let Some(callee_shape) = transport_plan
        .positions
        .get(&callee_position)
        .map(|layout| layout.structural)
    else {
        return Ok(TransportClosureCallEdge::Absent);
    };
    let ShapeDescr::Callable(callable) = world.shape(callee_shape) else {
        return Ok(TransportClosureCallEdge::Absent);
    };
    let callable = *callable;
    let Some(facts) = transport_plan.callables.get(&callable) else {
        return Ok(TransportClosureCallEdge::Absent);
    };
    let args = callsite_args.get(&callsite).ok_or_else(|| {
        incomplete_semantic_plan(
            tel,
            root_id,
            format!(
                "missing lowered call arguments for closure callsite {}",
                callsite.as_u32()
            ),
        )
    })?;
    let mut resolutions = boundary_resolutions_for_closure_call(
        world,
        transport_plan,
        &caller_symbol,
        callsite,
        args,
        &facts.boundary_ids,
    );
    let public_callable = !facts.boundary_ids.is_empty();
    if resolutions.is_empty() {
        if facts.direct_edges.is_empty() {
            return materialize_public_indirect_closure_call_edge(
                world,
                tel,
                root_id,
                transport_plan,
                executable,
                analysis,
                callsite,
                result_value,
                dest,
                original_entry_ids,
                public_callable,
            );
        }
        let direct_edges = facts.direct_edges.to_vec();
        let surface_inputs = args
            .iter()
            .map(|arg| analysis.value_types.get(&arg.value).copied())
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| {
                incomplete_semantic_plan(
                    tel,
                    root_id,
                    format!(
                        "missing semantic argument types for closure callsite {} direct edge selection",
                        callsite.as_u32()
                    ),
                )
            })?;
        let surface_inputs = world.types_mut().address_inputs(&surface_inputs);
        resolutions = direct_edge_resolutions_for_surface(world, &direct_edges, &surface_inputs);
    }
    // Materialization needs ONE distinct resolution; several sources may name
    // it several times. All-equal-to-first is the keyed-set read of that
    // requirement — no sort-for-dedup (sorting is a barrier).
    let Some((resolution, rest)) = resolutions.split_first() else {
        return Ok(TransportClosureCallEdge::Absent);
    };
    if rest.iter().any(|candidate| candidate != resolution) {
        return materialize_public_indirect_closure_call_edge(
            world,
            tel,
            root_id,
            transport_plan,
            executable,
            analysis,
            callsite,
            result_value,
            dest,
            original_entry_ids,
            public_callable,
        );
    }
    let activation = ActivationKey {
        root: root_id,
        function: resolution.activation.function,
        arrow: resolution.activation.arrow,
    };
    let target = ExecutableKey {
        activation,
        need: resolution.need,
    };
    let callee = CallTarget::Local(target.clone());
    let return_ty = world
        .activation_return(&target.activation)
        .unwrap_or_else(|| world.types_mut().none());
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
            public_callable,
        )?
    };
    Ok(TransportClosureCallEdge::Direct {
        edge: DirectCallEdge {
            callee,
            return_flow,
            extern_marshals: None,
        },
        return_ty,
    })
}

fn materialize_public_indirect_closure_call_edge(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    transport_plan: &ArtifactTransportLookup<'_>,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    callsite: CallSiteId,
    result_value: ValueId,
    dest: &ControlDestination,
    original_entry_ids: &[ControlEntryId],
    public_callable: bool,
) -> Result<TransportClosureCallEdge, FatalError> {
    if !public_callable {
        return Ok(TransportClosureCallEdge::Absent);
    }
    let key = CallSiteKey {
        activation: executable.activation.clone(),
        callsite,
    };
    let summary = world.callsite_summary(&key).cloned();
    let return_ty = public_indirect_return_ty(world, tel, root_id, analysis, summary.as_ref(), callsite, result_value)?;
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
    Ok(TransportClosureCallEdge::PublicIndirect { return_flow, return_ty })
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
    if settled_return.is_some_and(|settled_return| !world.types().is_equivalent(&settled_return, &result_ty)) {
        return Err(incomplete_semantic_plan(
            tel,
            root_id,
            format!(
                "public closure callsite {} settled return disagrees with its semantic result type",
                callsite.as_u32()
            ),
        ));
    }
    Ok(result_ty)
}

fn boundary_resolutions_for_closure_call(
    world: &World,
    transport_plan: &ArtifactTransportLookup<'_>,
    caller_symbol: &ExecutableSymbol,
    callsite: CallSiteId,
    args: &[CallArg],
    boundary_ids: &[super::super::transport::BoundaryId],
) -> Vec<ExecutableSymbol> {
    let Some(arg_shapes) = args
        .iter()
        .enumerate()
        .map(|(semantic_index, _)| {
            let position = TransportPosition::CallArg {
                executable: caller_symbol.clone(),
                callsite,
                semantic_index,
            };
            transport_plan.positions.get(&position).map(|layout| layout.structural)
        })
        .collect::<Option<Vec<_>>>()
    else {
        return Vec::new();
    };
    let mut resolutions = Vec::new();
    for boundary in boundary_ids.iter().copied() {
        let boundary_descr = world.boundary(boundary);
        if boundary_descr.surface_arg_shapes.as_ref() != arg_shapes.as_slice() {
            continue;
        }
        if let Some(boundary_facts) = transport_plan.boundaries.get(&boundary) {
            for resolution in boundary_facts.resolutions.iter().cloned() {
                if !resolutions.contains(&resolution) {
                    resolutions.push(resolution);
                }
            }
        }
    }
    resolutions
}

fn direct_edge_resolutions_for_surface(
    _world: &mut World,
    edges: &[super::super::transport::CallableDirectEdge],
    surface_inputs: &[Ty],
) -> Vec<ExecutableSymbol> {
    edges
        .iter()
        .filter(|edge| edge.surface_inputs.as_ref() == surface_inputs)
        .map(|edge| edge.resolution.clone())
        .collect()
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
                executable: caller_symbol,
                callsite: Some(callsite),
                entry: transport_entry,
            };
            let source = if public_callable {
                resume.clone()
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
    transport_plan.positions.get(position).copied().ok_or_else(|| {
        incomplete_semantic_plan(
            tel,
            root_id,
            format!("missing transport layout for return-flow position {position:?}"),
        )
    })
}

fn callsite_needs_for_body(body: &LoweredBody, need: ExecutableNeed) -> HashMap<CallSiteId, ExecutableNeed> {
    match body {
        LoweredBody::Extern { .. } => HashMap::new(),
        LoweredBody::Clauses { clauses, .. } => {
            let clause_ids = (0..clauses.len() as u32).collect::<Vec<_>>();
            executable_callsite_needs(body, &clause_ids, need)
        }
    }
}

fn materialize_entry_dispatch(
    world: &World,
    executable: &ExecutableKey,
    _analysis: &ActivationAnalysis,
) -> Option<ExecutableDispatch> {
    match world.lowered_body(executable.activation.function) {
        LoweredBody::Extern { .. } => None,
        LoweredBody::Clauses { .. } => Some(ExecutableDispatch::new(
            world.entry_dispatch(executable.activation.function),
            _analysis.reachable_clauses.clone(),
        )),
    }
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
    transport_plan: &ArtifactTransportLookup<'_>,
) -> ExecutableAbiPlan {
    let semantic_inputs = executable
        .transport
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
            let layout = *transport_plan
                .positions
                .get(position)
                .unwrap_or_else(|| panic!("transport plan should publish materialized input position {position:?}"));
            if matches!(layout.carrier, TransportCarrier::ValueRef) {
                return Some(BackendSemanticInputLayout {
                    semantic_index: *semantic_index,
                    layout: BackendValueLayout {
                        structural: layout.structural,
                        carrier: layout.carrier,
                        tys: Box::new([world.types_mut().any()]),
                        reprs: Box::new([AbiValueRepr::ValueRef]),
                    },
                });
            }
            let publication_contract =
                function_entry_publication_contract(world, transport_plan.codegen_seam_facts, symbol, *semantic_index);
            if !publication_contract.is_empty() {
                return Some(BackendSemanticInputLayout {
                    semantic_index: *semantic_index,
                    layout: BackendValueLayout {
                        structural: layout.structural,
                        carrier: layout.carrier,
                        tys: publication_contract.iter().map(|(ty, _)| *ty).collect(),
                        reprs: publication_contract.iter().map(|(_, repr)| *repr).collect(),
                    },
                });
            }
            let shape = layout.structural;
            let demand = executable.runtime_demand.input_demands.get(*semantic_index);
            let contract = if demand.is_some_and(|demand| demand.is_ignore()) {
                Vec::new()
            } else {
                shape_leaf_lanes_for_artifact(world, shape)
                    .into_iter()
                    .map(|(leaf_shape, lane)| {
                        (
                            world.lane(lane).ty,
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
                            ),
                        )
                    })
                    .collect::<Vec<_>>()
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
    let return_position = &executable.transport.return_position;
    let return_layout = *transport_plan
        .positions
        .get(return_position)
        .unwrap_or_else(|| panic!("transport plan should publish materialized return position {return_position:?}"));
    let return_contract = if matches!(return_layout.carrier, TransportCarrier::ValueRef) {
        vec![(world.types_mut().any(), AbiValueRepr::ValueRef)]
    } else {
        shape_leaf_lanes_for_artifact(world, return_layout.structural)
            .into_iter()
            .map(|(leaf_shape, lane)| {
                (
                    world.lane(lane).ty,
                    seam_repr_for_lane_or_default(
                        world,
                        transport_plan.codegen_seam_facts,
                        |seam| {
                            matches!(
                                seam,
                                CodegenSeam::ReturnDelivery { executable: symbol }
                                    if symbol == &executable.transport.executable
                            )
                        },
                        Some(leaf_shape),
                        lane,
                    ),
                )
            })
            .collect::<Vec<_>>()
    };
    let mut value_layouts: HashMap<ValueId, BackendValueLayout> = executable
        .transport
        .value_positions
        .iter()
        .filter_map(|position| {
            let TransportPosition::Value { value, .. } = position else {
                return None;
            };
            let layout = *transport_plan
                .positions
                .get(position)
                .unwrap_or_else(|| panic!("transport plan should publish materialized value position {position:?}"));
            let contract = if matches!(layout.carrier, TransportCarrier::ValueRef) {
                vec![(world.types_mut().any(), AbiValueRepr::ValueRef)]
            } else {
                shape_leaf_lanes_for_artifact(world, layout.structural)
                    .into_iter()
                    .map(|(_, lane)| {
                        let ty = world.lane(lane).ty;
                        (ty, abi_value_repr(world, ty))
                    })
                    .collect()
            };
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

    let return_endpoints = executable
        .transport
        .return_payload_positions
        .iter()
        .chain(executable.transport.resume_positions.iter())
        .chain(std::iter::once(return_position))
        .map(|position| {
            let layout = *transport_plan
                .positions
                .get(position)
                .unwrap_or_else(|| panic!("transport plan should publish materialized return endpoint {position:?}"));
            let contract = if matches!(layout.carrier, TransportCarrier::ValueRef) {
                vec![(world.types_mut().any(), AbiValueRepr::ValueRef)]
            } else {
                shape_leaf_lanes_for_artifact(world, layout.structural)
                    .into_iter()
                    .map(|(leaf_shape, lane)| {
                        (
                            world.lane(lane).ty,
                            endpoint_seam_repr(world, transport_plan.codegen_seam_facts, position, leaf_shape, lane),
                        )
                    })
                    .collect()
            };
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
    executable: &MaterializedExecutable,
    plan: &ExecutableAbiPlan,
) -> Result<AbiReadyExecutable, FatalError> {
    let call_edges = executable
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
        entry_dispatch: executable.entry_dispatch.clone(),
        return_ty: executable.return_ty,
        param_reprs: plan.param_reprs.clone(),
        semantic_inputs: plan.semantic_inputs.clone(),
        return_layout: plan.return_layout.clone(),
        return_endpoints: plan.return_endpoints.clone(),
        runtime_demand: executable.runtime_demand.clone(),
        transport: executable.transport.clone(),
        original_entry_ids: executable.original_entry_ids.clone(),
        value_types: executable.value_types.clone(),
        value_layouts: plan.value_layouts.clone(),
        effects: executable.effects,
        body: executable.body.clone(),
        call_edges,
    })
}

fn function_entry_publication_contract(
    world: &World,
    facts: &[super::super::transport::CodegenSeamFact],
    executable: &ExecutableSymbol,
    semantic_index: usize,
) -> Vec<(Ty, AbiValueRepr)> {
    let mut contract = Vec::new();
    let mut seen_lanes = HashSet::new();
    for fact in facts.iter().filter(|fact| {
        fact.shape.is_none()
            && matches!(
                &fact.seam,
                CodegenSeam::FunctionEntry {
                    executable: candidate,
                    semantic_index: candidate_index,
                } if candidate == executable && *candidate_index == semantic_index
            )
    }) {
        if seen_lanes.insert(fact.lane) {
            contract.push((world.lane(fact.lane).ty, abi_repr_from_codegen(fact.repr)));
        }
    }
    contract
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

fn shape_leaf_lanes_for_artifact(world: &World, shape: ShapeId) -> Vec<(ShapeId, LaneId)> {
    match world.shape(shape) {
        ShapeDescr::Nothing => Vec::new(),
        ShapeDescr::Lane(lane) => vec![(shape, *lane)],
        ShapeDescr::Tuple(items) => items
            .iter()
            .copied()
            .flat_map(|item| shape_leaf_lanes_for_artifact(world, item))
            .collect(),
        ShapeDescr::Callable(callable) => world
            .callable(*callable)
            .capture_lanes
            .iter()
            .copied()
            .map(|lane| (shape, lane))
            .collect(),
    }
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

fn codegen_repr_for_lane(world: &World, lane: LaneId) -> CodegenLaneRepr {
    let ty = world.lane(lane).ty;
    if world.types().is_floating(&ty) {
        CodegenLaneRepr::RawF64
    } else if world.types().is_integer(&ty) {
        CodegenLaneRepr::RawInt
    } else if world.types().is_atom_type(&ty) {
        CodegenLaneRepr::RawAtom
    } else {
        CodegenLaneRepr::ValueRef
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
    use crate::compiler2::semantic::{CallSiteSummary, CallTargetSummary, SelectedCallee};
    use crate::compiler2::transport::{CodegenSeamFact, LaneDescr, TransportClass};
    use crate::compiler2::{ActivationKey, FunctionId};
    use crate::telemetry::ConfiguredTelemetry;

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
        sort_transport_positions(&mut positions);

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

    fn materialize_ambiguous_closure_edge(returns: bool) -> (World, MaterializedCallEdge) {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let caller = fake_call_executable(&mut world, 300, 301, &[]);
        let callsite = CallSiteId::from_u32(7);
        let key = CallSiteKey {
            activation: caller.activation.clone(),
            callsite,
        };
        world.define_callsite_summary(
            key,
            CallSiteSummary {
                targets: [302, 303]
                    .into_iter()
                    .map(|function| CallTargetSummary {
                        callee: SelectedCallee::Function(FunctionId::for_test(function)),
                        surface_inputs: vec![int],
                        activation: None,
                        activation_inputs: None,
                        return_ty: returns.then_some(int),
                    })
                    .collect(),
                return_ty: returns.then_some(int),
            },
        );
        let result_value = ValueId::from_u32(2);
        let analysis = ActivationAnalysis {
            reachable_clauses: Vec::new(),
            reachable_entries: Vec::new(),
            callsites: Vec::new(),
            latent_executables: Vec::new(),
            value_types: returns.then_some((result_value, int)).into_iter().collect(),
        };
        let positions = if returns {
            let caller_symbol = transport_executable_symbol(&caller, world.types());
            let caller_return = TransportPosition::ExecutableReturn {
                executable: caller_symbol.clone(),
            };
            let payload = TransportPosition::ReturnPayload {
                executable: caller_symbol,
                callsite,
            };
            let shape = world.intern_shape(ShapeDescr::Nothing);
            HashMap::from([
                (caller_return, TransportLayout::structural(shape)),
                (
                    payload,
                    TransportLayout {
                        structural: shape,
                        carrier: TransportCarrier::ValueRef,
                    },
                ),
            ])
        } else {
            HashMap::new()
        };
        let callables = HashMap::new();
        let boundaries = HashMap::new();
        let codegen_seam_facts = Vec::new();
        let transport_plan = ArtifactTransportLookup {
            positions: &positions,
            callables: &callables,
            boundaries: &boundaries,
            codegen_seam_facts: &codegen_seam_facts,
        };
        let edge = materialize_closure_call_edge(
            &mut world,
            &tel,
            RootId::for_test(300),
            &transport_plan,
            &caller,
            &analysis,
            ExecutableNeed::Value,
            callsite,
            ValueId::from_u32(1),
            result_value,
            &ControlDestination::Return,
            &[],
            &HashMap::new(),
        )
        .expect("materialization should not fail")
        .expect("settled multi-target closure call should produce an edge");
        (world, edge)
    }

    #[test]
    fn materialize_closure_call_edge_routes_ambiguous_multi_target_through_indirect() {
        let (_world, edge) = materialize_ambiguous_closure_edge(true);
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
        let (world, edge) = materialize_ambiguous_closure_edge(false);
        assert!(world.types().is_empty(&edge.return_ty));
        assert_eq!(
            edge.target,
            CallEdge::Indirect(CallReturnFlow::NoReturn { local_source: None })
        );
    }

    #[test]
    fn function_entry_publication_contract_deduplicates_duplicate_lane_facts() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        world.submit_code(None, "fn main(x), do: x".to_string());
        let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
        let function = world.root_entry(root).function;
        let int = world.types_mut().int();
        let lane = world.intern_lane(LaneDescr {
            ty: int,
            class: TransportClass::Value,
        });
        let executable = ExecutableSymbol {
            activation: ActivationSymbol {
                function,
                arrow: int,
                input: vec![int].into_boxed_slice(),
            },
            need: ExecutableNeed::Value,
        };
        let fact = CodegenSeamFact {
            seam: CodegenSeam::FunctionEntry {
                executable: executable.clone(),
                semantic_index: 0,
            },
            shape: None,
            lane,
            repr: CodegenLaneRepr::ValueRef,
        };

        assert_eq!(
            function_entry_publication_contract(&world, &[fact.clone(), fact], &executable, 0),
            vec![(int, AbiValueRepr::ValueRef)],
            "duplicate publication facts for the same function-entry lane must not widen the executable ABI",
        );
    }
}
