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
    AbiReadyCallEdge, AbiReadyExecutable, AbiValueRepr, CallEdge, CallReturnFlow, CallTarget, DirectCallEdge,
    DispatchCallArm, DispatchCallEdge, DispatchCallMiss, EffectSummary, ExecutableDispatch, MaterializedCallEdge,
    MaterializedExecutable, MaterializedExecutableTransport,
};
use super::super::body::{
    CallArg, CallSiteId, ControlDestination, ControlEntryId, ControlEntryOrigin, Literal, LoweredBody, LoweredEntry,
    LoweredStep, LoweredTail, ValueId,
};
use super::super::drive::FactKey;
use super::super::facts::FactUse;
use super::super::identity::{ExecutableKey, ExecutableNeed, RootId};
use super::super::pull::{ProductKey, ProductValue, PullOutcome, PullSession, PullWait};
use super::super::scheduler::FatalError;
use super::super::semantic::{ActivationAnalysis, CallSiteKey, CallTargetSummary, SelectedCallee, ShapeDemand};
use super::super::transport::{
    ActivationSymbol, BoundaryFacts, BoundaryId, CallableFacts, CallableId, CodegenLaneRepr, CodegenSeam,
    CodegenSeamFact, ExecutableSymbol, LaneId, ShapeDescr, ShapeId, TransportPosition,
};
use super::super::types::{Ty, Types};
use super::super::world::World;
use super::semantic::executable_callsite_needs;

const UNREACHABLE_CONTROL_ATOM: &str = "compiler2_unreachable_control";

pub(crate) fn produce_materialized_executable_product(
    world: &mut World<'_>,
    session: &mut PullSession,
    executable: &ExecutableKey,
) -> PullOutcome {
    if let Some(materialized) = session.materialized_executable(executable).cloned() {
        return PullOutcome::Produced(ProductValue::MaterializedExecutable(Box::new(materialized)));
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
    let pruned = prune_lowered_body(
        world.lowered_body(executable.activation.function),
        &analysis.reachable_clauses,
        &analysis.reachable_entries,
    );
    let body = pruned.body;
    let callsite_args = collect_callsite_args(&body);
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
        session.root(),
        &transport_plan,
        executable,
        &analysis,
        &body,
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
    PullOutcome::Produced(ProductValue::MaterializedExecutable(Box::new(materialized)))
}

pub(crate) fn produce_executable_effects_product(
    _world: &mut World<'_>,
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
    world: &mut World<'_>,
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
    value_reprs: HashMap<ValueId, AbiValueRepr>,
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
    positions: &'a HashMap<TransportPosition, ShapeId>,
    callables: &'a HashMap<CallableId, CallableFacts>,
    boundaries: &'a HashMap<BoundaryId, BoundaryFacts>,
    codegen_seam_facts: &'a [CodegenSeamFact],
}

fn session_transport_lookup<'a>(
    session: &'a PullSession,
    codegen_seam_facts: &'a [CodegenSeamFact],
) -> ArtifactTransportLookup<'a> {
    ArtifactTransportLookup {
        positions: session.transport_shapes(),
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
    world: &mut World<'_>,
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

fn session_codegen_publication_seam_facts(world: &World<'_>, session: &PullSession) -> Box<[CodegenSeamFact]> {
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

pub(crate) type CodegenSeamOwnerKey = (u8, u32, Vec<Ty>, u8, usize, u32);
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
    let (function, inputs, need0, need1) = transport_executable_sort_key(executable);
    (0, function, inputs, need0, need1, 0)
}

fn boundary_owner_key(boundary: BoundaryId) -> CodegenSeamOwnerKey {
    (1, 0, Vec::new(), 0, 0, boundary.as_u32())
}

fn codegen_seam_kind_key(seam: &CodegenSeam) -> (u8, CodegenSeamOwnerKey, u32, u32) {
    match seam {
        CodegenSeam::FunctionEntry {
            executable,
            semantic_index,
        } => (0, executable_owner_key(executable), *semantic_index as u32, 0),
        CodegenSeam::BlockParam { executable, entry } => (1, executable_owner_key(executable), entry.as_u32(), 0),
        CodegenSeam::ReturnDelivery { executable } => (2, executable_owner_key(executable), 0, 0),
        CodegenSeam::ContinuationEntry {
            executable,
            callsite,
            entry,
        } => (3, executable_owner_key(executable), callsite.as_u32(), entry.as_u32()),
        CodegenSeam::ReturnContinuation { executable, callsite } => {
            (4, executable_owner_key(executable), callsite.as_u32(), 0)
        }
        CodegenSeam::TailCall { executable, callsite } => (5, executable_owner_key(executable), callsite.as_u32(), 0),
        CodegenSeam::CallableBoundary { boundary } => (6, boundary_owner_key(*boundary), 0, 0),
        CodegenSeam::ExternBoundary { executable } => (7, executable_owner_key(executable), 0, 0),
        CodegenSeam::FirstClassPublication { boundary } => (8, boundary_owner_key(*boundary), 0, 0),
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
        TransportPosition::EntryCapture { executable, entry, .. } => {
            out.push(CodegenSeamFact {
                seam: CodegenSeam::BlockParam {
                    executable: executable.clone(),
                    entry: *entry,
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
    world: &mut World<'_>,
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
pub(crate) type TransportExecutableSortKey = (u32, Vec<Ty>, u8, usize);

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
    world: &mut World<'_>,
    root_id: RootId,
    transport_plan: &ArtifactTransportLookup<'_>,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    body: &LoweredBody,
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
                    root_id,
                    transport_plan,
                    executable,
                    analysis,
                    callsite_needs.get(callsite).copied().unwrap_or(ExecutableNeed::Value),
                    *callsite,
                    dest,
                    callsite_args,
                )?
                else {
                    return Ok(None);
                };
                call_edges.insert(*callsite, edge);
            }
            LoweredTail::ClosureCall { callsite, dest, .. } => {
                let LoweredTail::ClosureCall { callee, .. } = &entry.tail else {
                    unreachable!("matched closure call above")
                };
                if let Some(edge) = materialize_closure_call_edge(
                    world,
                    root_id,
                    transport_plan,
                    executable,
                    analysis,
                    callsite_needs.get(callsite).copied().unwrap_or(ExecutableNeed::Value),
                    *callsite,
                    *callee,
                    dest,
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
    world: &mut World<'_>,
    root_id: RootId,
    transport_plan: &ArtifactTransportLookup<'_>,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    need: ExecutableNeed,
    callsite: CallSiteId,
    dest: &ControlDestination,
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
            root_id,
            transport_plan,
            executable,
            analysis,
            need,
            callsite,
            dest,
            callsite_args,
            target,
        )?;
        return Ok(Some(MaterializedCallEdge {
            target: CallEdge::Direct(direct),
            return_ty,
        }));
    }
    let Some(dispatch) =
        super::super::callsite_dispatch::dispatch_from_callsite_summary(&summary).map_err(|error| {
            incomplete_semantic_plan(
                world,
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
    for (body_id, target) in dispatch.targets.into_iter().enumerate() {
        let (direct, _arm_return_ty) = lower_materialized_call_target(
            world,
            root_id,
            transport_plan,
            executable,
            analysis,
            need,
            callsite,
            dest,
            callsite_args,
            target,
        )?;
        arms.push(DispatchCallArm {
            body_id: body_id as u32,
            callee: direct.callee,
            return_flow: direct.return_flow,
            extern_marshals: direct.extern_marshals,
        });
    }
    if arms.is_empty() {
        return Err(incomplete_semantic_plan(
            world,
            root_id,
            format!(
                "multi-target direct callsite {} has no dispatch arms",
                callsite.as_u32()
            ),
        ));
    }
    let return_ty = summary.settled_return(world.types_mut());
    Ok(Some(MaterializedCallEdge {
        target: CallEdge::Dispatch(DispatchCallEdge {
            plan: dispatch.plan,
            arms,
            miss: DispatchCallMiss::Unreachable,
        }),
        return_ty,
    }))
}

fn materialize_closure_call_edge(
    world: &mut World<'_>,
    root_id: RootId,
    transport_plan: &ArtifactTransportLookup<'_>,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    need: ExecutableNeed,
    callsite: CallSiteId,
    callee_value: ValueId,
    dest: &ControlDestination,
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
) -> Result<Option<MaterializedCallEdge>, FatalError> {
    if let Some((direct, return_ty)) = materialize_transport_closure_call_edge(
        world,
        root_id,
        transport_plan,
        executable,
        analysis,
        callsite,
        callee_value,
        dest,
        callsite_args,
    )? {
        return Ok(Some(MaterializedCallEdge {
            target: CallEdge::Direct(direct),
            return_ty,
        }));
    }
    let key = CallSiteKey {
        activation: executable.activation.clone(),
        callsite,
    };
    let Some(summary) = world.callsite_summary(&key).cloned() else {
        return Ok(None);
    };
    let Some(target) = summary.single_target().cloned() else {
        return Ok(None);
    };
    let (direct, return_ty) = lower_materialized_call_target(
        world,
        root_id,
        transport_plan,
        executable,
        analysis,
        need,
        callsite,
        dest,
        callsite_args,
        target,
    )?;
    Ok(Some(MaterializedCallEdge {
        target: CallEdge::Direct(direct),
        return_ty,
    }))
}

fn materialize_transport_closure_call_edge(
    world: &mut World<'_>,
    root_id: RootId,
    transport_plan: &ArtifactTransportLookup<'_>,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    callsite: CallSiteId,
    callee_value: ValueId,
    dest: &ControlDestination,
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
) -> Result<Option<(DirectCallEdge<ExecutableKey>, Ty)>, FatalError> {
    let caller_symbol = transport_executable_symbol(executable, world.types());
    let callee_position = TransportPosition::Value {
        executable: caller_symbol.clone(),
        value: callee_value,
    };
    let Some(callee_shape) = transport_plan.positions.get(&callee_position).copied() else {
        return Ok(None);
    };
    let ShapeDescr::Callable(callable) = world.shape(callee_shape) else {
        return Ok(None);
    };
    let callable = *callable;
    let Some(facts) = transport_plan.callables.get(&callable) else {
        return Ok(None);
    };
    let args = callsite_args.get(&callsite).ok_or_else(|| {
        incomplete_semantic_plan(
            world,
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
    if resolutions.is_empty() {
        if facts.direct_edges.is_empty() {
            return Ok(None);
        }
        let direct_edges = facts.direct_edges.to_vec();
        let surface_inputs = args
            .iter()
            .map(|arg| analysis.value_types.get(&arg.value).copied())
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| {
                incomplete_semantic_plan(
                    world,
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
        return Ok(None);
    };
    if rest.iter().any(|candidate| candidate != resolution) {
        return Ok(None);
    }
    let activation = world.activation_key(
        root_id,
        resolution.activation.function,
        resolution.activation.input.as_ref(),
    );
    let target = ExecutableKey {
        activation,
        need: resolution.need,
    };
    let callee = CallTarget::Local(target.clone());
    let return_flow = call_return_flow(world, root_id, transport_plan, executable, &callee, callsite, dest)?;
    let return_ty = world
        .activation_return(&target.activation)
        .unwrap_or_else(|| world.types_mut().none());
    Ok(Some((
        DirectCallEdge {
            callee,
            return_flow,
            extern_marshals: None,
        },
        return_ty,
    )))
}

fn boundary_resolutions_for_closure_call(
    world: &World<'_>,
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
            transport_plan.positions.get(&position).copied()
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
    _world: &mut World<'_>,
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
    world: &mut World<'_>,
    root_id: RootId,
    transport_plan: &ArtifactTransportLookup<'_>,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    need: ExecutableNeed,
    callsite: CallSiteId,
    dest: &ControlDestination,
    callsite_args: &HashMap<CallSiteId, Vec<CallArg>>,
    target: CallTargetSummary,
) -> Result<(DirectCallEdge<ExecutableKey>, Ty), FatalError> {
    let (callee, extern_marshals) = match target.callee {
        SelectedCallee::Function(function) => {
            let activation = target.activation.clone().ok_or_else(|| {
                incomplete_semantic_plan(
                    world,
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
                        world,
                        root_id,
                        format!(
                            "missing lowered call arguments for extern callsite {}",
                            callsite.as_u32()
                        ),
                    ));
                };
                Some(resolve_extern_marshals(
                    world,
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
    let return_flow = call_return_flow(world, root_id, transport_plan, executable, &callee, callsite, dest)?;
    Ok((
        DirectCallEdge {
            callee,
            return_flow,
            extern_marshals,
        },
        target.settled_return(world.types_mut()),
    ))
}

fn call_return_flow(
    world: &World<'_>,
    root_id: RootId,
    transport_plan: &ArtifactTransportLookup<'_>,
    executable: &ExecutableKey,
    callee: &CallTarget<ExecutableKey>,
    callsite: CallSiteId,
    dest: &ControlDestination,
) -> Result<CallReturnFlow, FatalError> {
    let caller_symbol = transport_executable_symbol(executable, world.types());
    match dest {
        ControlDestination::Deliver(entry) => {
            let resume = TransportPosition::ResumePayload {
                executable: caller_symbol,
                callsite: Some(callsite),
                entry: *entry,
            };
            let payload = match callee {
                CallTarget::Local(callee) => TransportPosition::ExecutableReturn {
                    executable: transport_executable_symbol(callee, world.types()),
                },
                CallTarget::ProviderBoundary(_) => resume.clone(),
            };
            Ok(CallReturnFlow::Deliver {
                payload,
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
            let caller_shape = require_transport_position(world, root_id, transport_plan, &caller_return)?;
            let payload_shape = require_transport_position(world, root_id, transport_plan, &payload)?;
            if let CallTarget::Local(callee) = callee {
                let callee_return = TransportPosition::ExecutableReturn {
                    executable: transport_executable_symbol(callee, world.types()),
                };
                let callee_shape = require_transport_position(world, root_id, transport_plan, &callee_return)?;
                if matches!(world.shape(callee_shape), ShapeDescr::Nothing)
                    || (caller_shape == callee_shape && payload_shape == callee_shape)
                {
                    return Ok(CallReturnFlow::Tail {
                        callee_return,
                        caller_return,
                    });
                }
            }
            Ok(CallReturnFlow::Continue { payload, caller_return })
        }
    }
}

fn require_transport_position(
    world: &World<'_>,
    root_id: RootId,
    transport_plan: &ArtifactTransportLookup<'_>,
    position: &TransportPosition,
) -> Result<ShapeId, FatalError> {
    transport_plan.positions.get(position).copied().ok_or_else(|| {
        incomplete_semantic_plan(
            world,
            root_id,
            format!("transport plan is missing required call return-flow position {position:?}"),
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
    world: &World<'_>,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
) -> Option<ExecutableDispatch> {
    match world.lowered_body(executable.activation.function) {
        LoweredBody::Extern { .. } => None,
        LoweredBody::Clauses { .. } => Some(ExecutableDispatch::new(
            world.entry_dispatch(executable.activation.function),
            analysis.reachable_clauses.clone(),
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

fn collect_callsite_args(body: &LoweredBody) -> HashMap<CallSiteId, Vec<CallArg>> {
    let mut out = HashMap::new();
    match body {
        LoweredBody::Extern { .. } => {}
        LoweredBody::Clauses { clauses, entries, .. } => {
            for clause in clauses {
                collect_step_call_args(&clause.projections, &mut out);
            }
            for entry in entries {
                collect_step_call_args(&entry.steps, &mut out);
                collect_tail_call_args(&entry.tail, &mut out);
            }
        }
    }
    out
}

fn collect_step_call_args(_steps: &[LoweredStep], _out: &mut HashMap<CallSiteId, Vec<CallArg>>) {}

fn collect_tail_call_args(tail: &LoweredTail, out: &mut HashMap<CallSiteId, Vec<CallArg>>) {
    match tail {
        LoweredTail::DirectCall { callsite, args, .. } | LoweredTail::ClosureCall { callsite, args, .. } => {
            out.insert(*callsite, args.clone());
        }
        LoweredTail::Value { .. }
        | LoweredTail::If { .. }
        | LoweredTail::Dispatch { .. }
        | LoweredTail::Receive(_)
        | LoweredTail::Halt { .. } => {}
    }
}

fn resolve_extern_marshals(
    world: &mut World<'_>,
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
            world,
            root_id,
            format!("extern call expected {} argument(s) but saw {}", fixed, actual),
        ));
    }

    let mut marshals = Vec::with_capacity(actual);
    for (index, arg) in args.iter().enumerate() {
        if index < fixed {
            let expected = fixed_params[index];
            if let Some(ascription) = &arg.ascription {
                let ascribed = parse_extern_ascription(world, root_id, ascription)?;
                if ascribed != expected {
                    return Err(incomplete_semantic_plan(
                        world,
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
            marshals.push(parse_extern_ascription(world, root_id, ascription)?);
            continue;
        }

        let Some(arg_ty) = value_types.get(&arg.value).copied() else {
            return Err(incomplete_semantic_plan(
                world,
                root_id,
                format!("missing settled type for extern argument value {}", arg.value.as_u32()),
            ));
        };
        marshals.push(resolve_auto_variadic_marshal(world, root_id, arg_ty)?);
    }

    Ok(marshals)
}

fn parse_extern_ascription(
    world: &World<'_>,
    root_id: RootId,
    body: &crate::ast::TypeExprBody,
) -> Result<crate::fz_ir::ExternTy, FatalError> {
    let Some(tok) = body.0.first().map(|token| &token.tok) else {
        return Err(incomplete_semantic_plan(
            world,
            root_id,
            "empty extern call-arg ascription",
        ));
    };
    let name = match tok {
        Tok::Ident(name) | Tok::Upper(name) => name.as_str(),
        Tok::Nil => "nil",
        _ => {
            return Err(incomplete_semantic_plan(
                world,
                root_id,
                format!("unsupported extern call-arg ascription token {:?}", tok),
            ));
        }
    };
    extern_ty_from_name(name)
        .ok_or_else(|| incomplete_semantic_plan(world, root_id, format!("unknown extern call-arg ascription `{name}`")))
}

fn resolve_auto_variadic_marshal(
    world: &mut World<'_>,
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
            world,
            root_id,
            "binary values need an explicit extern variadic marshal ascription",
        ));
    }
    Err(incomplete_semantic_plan(
        world,
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
        LoweredTail::ClosureCall { callsite, .. } if !call_edges.contains_key(callsite) => {
            effects.calls_opaque = true;
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
        LoweredTail::ClosureCall { .. } => {}
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
    }
}

fn build_executable_abi_plan(
    world: &mut World<'_>,
    _key: &ExecutableKey,
    executable: &MaterializedExecutable,
    transport_plan: &ArtifactTransportLookup<'_>,
) -> ExecutableAbiPlan {
    let param_reprs = executable
        .transport
        .input_positions
        .iter()
        .flat_map(|position| {
            let TransportPosition::ExecutableInput {
                executable: symbol,
                semantic_index,
            } = position
            else {
                return Vec::new();
            };
            let publication_reprs =
                function_entry_publication_reprs(transport_plan.codegen_seam_facts, symbol, *semantic_index);
            if !publication_reprs.is_empty() {
                return publication_reprs;
            }
            let shape = *transport_plan
                .positions
                .get(position)
                .unwrap_or_else(|| panic!("transport plan should publish materialized input position {position:?}"));
            shape_leaf_lanes_for_artifact(world, shape)
                .into_iter()
                .map(|(leaf_shape, lane)| {
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
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut value_reprs = HashMap::new();
    if let LoweredBody::Clauses { clauses, entries, .. } = &executable.body {
        for clause in clauses {
            for (index, value) in clause.params.iter().copied().enumerate() {
                let Some(position) = executable.transport.input_positions.iter().find(|position| {
                    matches!(
                        position,
                        TransportPosition::ExecutableInput {
                            semantic_index,
                            ..
                        } if *semantic_index == index
                    )
                }) else {
                    continue;
                };
                let shape = *transport_plan.positions.get(position).unwrap_or_else(|| {
                    panic!("transport plan should publish materialized input position {position:?}")
                });
                let leaf_lanes = shape_leaf_lanes_for_artifact(world, shape);
                if let [(leaf_shape, lane)] = leaf_lanes.as_slice() {
                    let TransportPosition::ExecutableInput {
                        executable: symbol,
                        semantic_index,
                    } = position
                    else {
                        continue;
                    };
                    let publication_reprs =
                        function_entry_publication_reprs(transport_plan.codegen_seam_facts, symbol, *semantic_index);
                    let repr = if let [repr] = publication_reprs.as_slice() {
                        *repr
                    } else {
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
                            Some(*leaf_shape),
                            *lane,
                        )
                    };
                    value_reprs.insert(value, repr);
                }
            }
        }
        for clause in clauses {
            record_step_reprs(world, executable, &clause.projections, &mut value_reprs);
        }
        for entry in entries {
            record_step_reprs(world, executable, &entry.steps, &mut value_reprs);
        }
    }

    ExecutableAbiPlan {
        param_reprs,
        value_reprs,
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
        runtime_demand: executable.runtime_demand.clone(),
        transport: executable.transport.clone(),
        original_entry_ids: executable.original_entry_ids.clone(),
        value_types: executable.value_types.clone(),
        value_reprs: plan.value_reprs.clone(),
        effects: executable.effects,
        body: executable.body.clone(),
        call_edges,
    })
}

fn function_entry_publication_reprs(
    facts: &[super::super::transport::CodegenSeamFact],
    executable: &ExecutableSymbol,
    semantic_index: usize,
) -> Vec<AbiValueRepr> {
    let mut reprs = Vec::new();
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
            reprs.push(abi_repr_from_codegen(fact.repr));
        }
    }
    reprs
}

fn shape_leaf_lanes_for_artifact(world: &World<'_>, shape: ShapeId) -> Vec<(ShapeId, LaneId)> {
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
    world: &mut World<'_>,
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

fn codegen_repr_for_lane(world: &World<'_>, lane: LaneId) -> CodegenLaneRepr {
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

fn record_step_reprs(
    world: &mut World<'_>,
    executable: &MaterializedExecutable,
    steps: &[LoweredStep],
    value_reprs: &mut HashMap<ValueId, AbiValueRepr>,
) {
    for step in steps {
        match step {
            LoweredStep::Const { value, literal } => {
                value_reprs.insert(*value, literal_repr(literal));
            }
            LoweredStep::Tuple { value, .. }
            | LoweredStep::List { value, .. }
            | LoweredStep::Map { value, .. }
            | LoweredStep::MapUpdate { value, .. }
            | LoweredStep::Struct { value, .. }
            | LoweredStep::Bitstring { value, .. }
            | LoweredStep::FunctionRef { value, .. }
            | LoweredStep::Lambda { value, .. }
            | LoweredStep::MapIndex { value, .. }
            | LoweredStep::FieldAccess { value, .. }
            | LoweredStep::RequireMapValue { value, .. }
            | LoweredStep::TupleField { value, .. }
            | LoweredStep::BitstringInit { reader: value, .. } => {
                value_reprs.insert(*value, AbiValueRepr::ValueRef);
            }
            LoweredStep::BinaryOp { value, .. } | LoweredStep::UnaryOp { value, .. } => {
                let ty = executable
                    .value_types
                    .get(value)
                    .copied()
                    .unwrap_or_else(|| world.types_mut().any());
                value_reprs.insert(*value, abi_value_repr(world, ty));
            }
            LoweredStep::SplitList { head, tail, .. } => {
                value_reprs.insert(*head, AbiValueRepr::ValueRef);
                value_reprs.insert(*tail, AbiValueRepr::ValueRef);
            }
            LoweredStep::BitstringRead {
                ok, value, next_reader, ..
            } => {
                value_reprs.insert(*ok, AbiValueRepr::ValueRef);
                value_reprs.insert(*value, AbiValueRepr::ValueRef);
                value_reprs.insert(*next_reader, AbiValueRepr::ValueRef);
            }
            LoweredStep::AssertLiteral { .. }
            | LoweredStep::AssertStruct { .. }
            | LoweredStep::AssertTuple { .. }
            | LoweredStep::AssertEmptyList { .. }
            | LoweredStep::AssertSame { .. }
            | LoweredStep::AssertBitstringDone { .. } => {}
        }
    }
}

fn literal_repr(literal: &Literal) -> AbiValueRepr {
    match literal {
        Literal::Int(_) => AbiValueRepr::RawInt,
        Literal::Float(_) => AbiValueRepr::RawF64,
        Literal::Atom(_) | Literal::Bool(_) | Literal::Nil => AbiValueRepr::RawAtom,
        Literal::Binary(_) => AbiValueRepr::ValueRef,
    }
}

fn abi_value_repr(world: &mut World<'_>, ty: Ty) -> AbiValueRepr {
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

fn incomplete_semantic_plan(world: &World<'_>, root_id: RootId, message: impl Into<String>) -> FatalError {
    let message = message.into();
    let diagnostic = Diagnostic::error(
        codes::ARTIFACT_INCOMPLETE_SEMANTIC_PLAN,
        format!("compiler2 materialization for root {}: {}", root_id.as_u32(), message),
        Span::DUMMY,
    );
    emit_through(world.tel(), std::slice::from_ref(&diagnostic));
    FatalError
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler2::transport::{CodegenSeamFact, LaneDescr, TransportClass};
    use crate::telemetry::ConfiguredTelemetry;

    #[test]
    fn sort_transport_positions_orders_one_partition_by_structural_discriminants() {
        // Each MaterializedExecutableTransport field vector holds ONE variant
        // of ONE executable by construction (positions are gathered from the
        // per-symbol index and partitioned by variant), so packaging order is
        // decided purely by the variant-local structural discriminants --
        // here CallArg's (callsite, semantic_index) -- independent of
        // arrival order and of any interned-type identity.
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        world.submit_code(None, "fn main(x), do: x".to_string());
        let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
        let function = world.root_entry(root).function;
        let int = world.types_mut().int();
        let symbol = ExecutableSymbol {
            activation: ActivationSymbol {
                function,
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

    #[test]
    fn function_entry_publication_reprs_deduplicates_duplicate_lane_facts() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
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
            function_entry_publication_reprs(&[fact.clone(), fact], &executable, 0),
            vec![AbiValueRepr::ValueRef],
            "duplicate publication facts for the same function-entry lane must not widen the executable ABI",
        );
    }
}
