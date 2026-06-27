//! Compiler2 backend-lowering jobs.
//!
//! This module turns one emission-ready closed root into one backend-owned
//! program. The result keeps function/clause structure, but every callsite now
//! points at settled executable inventory, every callable boundary carries its
//! required callable-entry inventory, and every extern callsite carries its
//! concrete wire classes.

use std::collections::HashSet;

use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch, PatternGuardExpr};
use crate::dispatch_matrix::{ComparisonValue, DispatchConst, DispatchNode, ProjectionKind, Region, SubjectSource};
use crate::source::Span;

use super::super::artifact::{
    AbiReadyExecutable, BackendBody, BackendCallArg, BackendCallableEntry, BackendClause, BackendEntry,
    BackendEntryOrigin, BackendExecutable, BackendProgram, BackendStep, BackendTail, CallEdge, CallTarget,
    DirectCallEdge, DispatchCallArm, EmissionReadyExecutable, MaterializedTransportPlan,
};
use super::super::body::{
    CallArg, CallSiteId, ControlEntryId, ControlEntryOrigin, LoweredBody, LoweredClause, LoweredEntry, LoweredStep,
    LoweredTail,
};
use super::super::drive::{FactKey, Job, JobEffects, settled_uses};
use super::super::facts::FactUse;
use super::super::identity::RootId;
use super::super::identity::{ActivationKey, ExecutableKey, ExecutableNeed};
use super::super::pull::{
    ProductKey, ProductValue, PullOutcome, PullSession, PullWait, SymbolicBackendBody, SymbolicBackendClause,
    SymbolicBackendEntry, SymbolicBackendExecutable, SymbolicBackendTail,
};
use super::super::scheduler::FatalError;
use super::super::transport::ShapeDescr;
use super::super::transport::{ActivationSymbol, ExecutableSymbol, TransportPosition};
use super::super::types::Ty;
use super::super::world::World;

const UNREACHABLE_CONTROL_ATOM: &str = "compiler2_unreachable_control";

/// Lowers one emission-ready closed root into the shared backend handoff.
///
/// The backend artifact consumes only `EmissionReadyProgram(root)` plus the
/// world-owned type store. It does not reopen semantic closure, planner state,
/// or backend-specific discovery.
pub(super) fn lower_backend_program(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let emission_ready_fact = FactKey::EmissionReadyProgram(root_id);
    let Some(emission_ready_revision) = world.fact_revision(&emission_ready_fact) else {
        return Ok(JobEffects::wait_on_settled(
            emission_ready_fact,
            [Job::DeriveEmissionReady(root_id)],
        ));
    };

    let emission_ready = world.emission_ready_program(root_id);
    let executables = {
        let mut lowerer = BackendLowerer::new(world, root_id, &emission_ready.transport);
        emission_ready
            .executables
            .iter()
            .map(|executable| lowerer.lower_executable(executable))
            .collect::<Result<Vec<_>, _>>()?
    };
    let callable_entries = emission_ready
        .callable_entries
        .iter()
        .map(|entry| BackendCallableEntry {
            boundary: entry.boundary,
            target: entry.target,
            capture_count: entry.capture_count,
            capture_reprs: entry.capture_reprs.clone(),
            arg_reprs: entry.arg_reprs.clone(),
            return_ty: entry.return_ty,
            return_shape: entry.return_shape,
            return_lanes: entry.return_lanes.clone(),
        })
        .collect();
    let program = BackendProgram {
        emission_ready_revision,
        transport_revision: emission_ready.transport_revision,
        entry: emission_ready.entry,
        transport: emission_ready.transport,
        atom_names: collect_backend_atom_names(world, &executables),
        struct_schemas: world.struct_schemas(),
        executables,
        callable_entries,
    };
    let backend_fact = FactKey::BackendProgram(root_id);
    let changed = world.define_backend_program(root_id, program);
    Ok(JobEffects {
        reads: settled_uses([emission_ready_fact]),
        outputs: vec![backend_fact.clone()],
        changed: changed.then_some(backend_fact).into_iter().collect(),
        // Native lowering is demand-only: the interp front door drives roots to
        // `BackendProgram` and never consumes native, while the JIT/AOT/dump
        // front doors transitively demand `LowerNativeProgram(root)` for the
        // whole-program root they compile. Pushing native here produced ~30
        // unconsumed native bodies on every interp run. No artifact above the
        // demanded product.
        ..JobEffects::default()
    })
}

pub(crate) fn produce_root_backend_product(
    world: &mut World<'_>,
    session: &mut PullSession,
    root: RootId,
) -> PullOutcome {
    let root_entry = world.root_entry(root);
    let keying_waits = [
        FactKey::RootEntry(root),
        FactKey::DispatchMask(root_entry.function),
        FactKey::Recursive(root_entry.function),
    ]
    .into_iter()
    .filter(|fact| !world.fact_is_settled(fact))
    .map(|fact| PullWait::Fact(FactUse::settled(fact)))
    .collect::<Vec<_>>();
    if !keying_waits.is_empty() {
        return PullOutcome::Waiting(keying_waits);
    }
    let entry = world.root_entry_executable(root);
    let mut reachable = HashSet::new();
    let mut stack = vec![entry.clone()];
    stack.extend(boundary_resolution_executables(world, root, session));
    let mut waits = Vec::new();
    while let Some(current) = stack.pop() {
        if !reachable.insert(current.clone()) {
            continue;
        }
        let Some(backend) = session.backend_executable(&current) else {
            waits.push(PullWait::Product(ProductKey::BackendExecutable(current)));
            continue;
        };
        for target in backend.call_edges.values() {
            for callee in symbolic_call_edge_callees(target) {
                stack.push(callee.clone());
            }
        }
    }
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }

    let mut executable_keys = reachable.into_iter().collect::<Vec<_>>();
    executable_keys.sort_by(|left, right| compare_executable_keys(left, right, world.types()));
    let executable_index = executable_keys
        .iter()
        .enumerate()
        .map(|(index, executable)| (executable.clone(), index))
        .collect::<std::collections::HashMap<_, _>>();
    for (executable, index) in &executable_index {
        session.assign_executable_index(executable.clone(), *index);
    }
    let executables = executable_keys
        .iter()
        .map(|executable| {
            let backend = session
                .backend_executable(executable)
                .expect("reachable backend executable should have been checked before packaging");
            package_symbolic_backend_executable(world, root, backend, &executable_index)
        })
        .collect::<Result<Vec<_>, _>>()
        .expect("root backend product should have complete symbolic executable inventory");
    let callable_entries = package_backend_callable_entries(world, root, session, &executable_index)
        .expect("root backend product should have complete callable-entry inventory");
    let transport = symbolic_materialized_transport_plan(session, &entry, world.types());
    let entry_index = executable_index
        .get(&entry)
        .copied()
        .expect("root entry should be in packaged executable inventory");
    let program = BackendProgram {
        emission_ready_revision: 0,
        transport_revision: 0,
        entry: entry_index,
        transport,
        atom_names: collect_backend_atom_names(world, &executables),
        struct_schemas: world.struct_schemas(),
        executables,
        callable_entries,
    };
    world.define_backend_program(root, program.clone());
    PullOutcome::Produced(ProductValue::RootBackendProduct(Box::new(program)))
}

pub(crate) fn produce_backend_executable_product(
    world: &mut World<'_>,
    session: &mut PullSession,
    executable: &ExecutableKey,
) -> PullOutcome {
    if let Some(backend) = session.backend_executable(executable).cloned() {
        return PullOutcome::Produced(ProductValue::BackendExecutable(Box::new(backend)));
    }
    let Some(abi) = session.abi_executable(executable).cloned() else {
        return PullOutcome::Waiting(vec![PullWait::Product(ProductKey::AbiExecutable(executable.clone()))]);
    };
    let transport = symbolic_materialized_transport_plan(session, executable, world.types());
    let mut lowerer = BackendLowerer::new(world, session.root(), &transport);
    let emission = symbolic_emission_ready_executable(executable.clone(), &abi);
    let lowered = lower_symbolic_body(&mut lowerer, &emission, &abi)
        .expect("symbolic backend lowering should be complete after ABI product exists");
    let call_edges = abi
        .call_edges
        .iter()
        .map(|(callsite, edge)| (*callsite, edge.target.clone()))
        .collect::<std::collections::HashMap<_, _>>();
    let backend = SymbolicBackendExecutable {
        key: executable.clone(),
        abi: Box::new(abi),
        body: lowered,
        call_edges,
    };
    session.record_backend_executable(executable.clone(), backend.clone());
    PullOutcome::Produced(ProductValue::BackendExecutable(Box::new(backend)))
}

fn symbolic_call_edge_callees(target: &CallEdge<ExecutableKey>) -> Vec<&ExecutableKey> {
    match target {
        CallEdge::Direct(direct) => direct.callee.local().into_iter().collect(),
        CallEdge::Dispatch(dispatch) => dispatch.arms.iter().filter_map(|arm| arm.callee.local()).collect(),
    }
}

fn boundary_resolution_executables(world: &mut World<'_>, root: RootId, session: &PullSession) -> Vec<ExecutableKey> {
    let mut out = Vec::new();
    for facts in session.boundary_facts_inventory().values() {
        for target in facts.resolutions.iter() {
            out.push(executable_key_for_symbol(root, target, world.types_mut()));
        }
    }
    out
}

fn executable_key_for_symbol(
    root: RootId,
    symbol: &ExecutableSymbol,
    types: &mut super::super::Types,
) -> ExecutableKey {
    ExecutableKey {
        activation: ActivationKey::from_inputs(root, symbol.activation.function, &symbol.activation.input, types),
        need: symbol.need,
    }
}

fn package_symbolic_backend_executable(
    world: &World<'_>,
    root: RootId,
    backend: &SymbolicBackendExecutable,
    executable_index: &std::collections::HashMap<ExecutableKey, usize>,
) -> Result<BackendExecutable, FatalError> {
    Ok(BackendExecutable {
        key: backend.key.clone(),
        entry_dispatch: backend.abi.entry_dispatch.clone(),
        return_ty: backend.abi.return_ty,
        param_reprs: backend.abi.param_reprs.clone(),
        runtime_demand: backend.abi.runtime_demand.clone(),
        transport: backend.abi.transport.clone(),
        value_types: backend.abi.value_types.clone(),
        value_reprs: backend.abi.value_reprs.clone(),
        effects: backend.abi.effects,
        body: package_symbolic_backend_body(world, root, &backend.key, &backend.body, executable_index)?,
    })
}

fn package_symbolic_backend_body(
    world: &World<'_>,
    root: RootId,
    caller: &ExecutableKey,
    body: &SymbolicBackendBody,
    executable_index: &std::collections::HashMap<ExecutableKey, usize>,
) -> Result<BackendBody, FatalError> {
    Ok(match body {
        SymbolicBackendBody::Extern { signature } => BackendBody::Extern {
            signature: signature.clone(),
        },
        SymbolicBackendBody::Clauses {
            clauses,
            entries,
            generated,
        } => BackendBody::Clauses {
            clauses: clauses
                .iter()
                .map(|clause| BackendClause {
                    span: clause.span,
                    params: clause.params.clone(),
                    projections: clause.projections.clone(),
                    entry: clause.entry,
                })
                .collect(),
            entries: entries
                .iter()
                .map(|entry| package_symbolic_backend_entry(world, root, caller, entry, executable_index))
                .collect::<Result<Vec<_>, _>>()?,
            generated: generated.clone(),
        },
    })
}

fn package_symbolic_backend_entry(
    world: &World<'_>,
    root: RootId,
    caller: &ExecutableKey,
    entry: &SymbolicBackendEntry,
    executable_index: &std::collections::HashMap<ExecutableKey, usize>,
) -> Result<BackendEntry, FatalError> {
    Ok(BackendEntry {
        span: entry.span,
        origin: entry.origin.clone(),
        params: entry.params.clone(),
        captures: entry.captures.clone(),
        capture_positions: entry.capture_positions.clone(),
        reusable_cons_captures: entry.reusable_cons_captures.clone(),
        steps: entry.steps.clone(),
        tail: package_symbolic_backend_tail(world, root, caller, &entry.tail, executable_index)?,
    })
}

fn package_symbolic_backend_tail(
    world: &World<'_>,
    root: RootId,
    caller: &ExecutableKey,
    tail: &SymbolicBackendTail,
    executable_index: &std::collections::HashMap<ExecutableKey, usize>,
) -> Result<BackendTail, FatalError> {
    Ok(match tail {
        SymbolicBackendTail::Value { value, dest } => BackendTail::Value {
            value: *value,
            dest: dest.clone(),
        },
        SymbolicBackendTail::DirectCall {
            value,
            callsite,
            target,
            args,
            dest,
        } => BackendTail::DirectCall {
            value: *value,
            callsite: *callsite,
            target: package_call_edge(world, root, caller, target, executable_index)?,
            args: args.clone(),
            dest: dest.clone(),
        },
        SymbolicBackendTail::ClosureCall {
            value,
            callsite,
            callee,
            target,
            args,
            dest,
            return_flow,
        } => BackendTail::ClosureCall {
            value: *value,
            callsite: *callsite,
            callee: *callee,
            target: target
                .as_ref()
                .map(|target| {
                    executable_index.get(target).copied().ok_or_else(|| {
                        incomplete_backend_program(
                            world,
                            root,
                            format!(
                                "symbolic closure target {:?} -> {:?} is missing from final inventory",
                                caller, target
                            ),
                        )
                    })
                })
                .transpose()?,
            args: args.clone(),
            dest: dest.clone(),
            return_flow: return_flow.clone(),
        },
        SymbolicBackendTail::If {
            cond,
            then_entry,
            else_entry,
        } => BackendTail::If {
            cond: *cond,
            then_entry: *then_entry,
            else_entry: *else_entry,
        },
        SymbolicBackendTail::Dispatch {
            inputs,
            bindings,
            dispatch,
        } => BackendTail::Dispatch {
            inputs: inputs.clone(),
            bindings: bindings.clone(),
            dispatch: dispatch.clone(),
        },
        SymbolicBackendTail::Receive(receive) => BackendTail::Receive(receive.clone()),
        SymbolicBackendTail::Halt { atom } => BackendTail::Halt { atom: atom.clone() },
    })
}

fn package_call_edge(
    world: &World<'_>,
    root: RootId,
    caller: &ExecutableKey,
    target: &CallEdge<ExecutableKey>,
    executable_index: &std::collections::HashMap<ExecutableKey, usize>,
) -> Result<CallEdge<usize>, FatalError> {
    Ok(match target {
        CallEdge::Direct(direct) => CallEdge::Direct(DirectCallEdge {
            callee: package_call_target(world, root, caller, &direct.callee, executable_index)?,
            return_flow: direct.return_flow.clone(),
            extern_marshals: direct.extern_marshals.clone(),
        }),
        CallEdge::Dispatch(dispatch) => CallEdge::Dispatch(super::super::artifact::DispatchCallEdge {
            plan: dispatch.plan.clone(),
            arms: dispatch
                .arms
                .iter()
                .map(|arm| {
                    Ok(DispatchCallArm {
                        body_id: arm.body_id,
                        callee: package_call_target(world, root, caller, &arm.callee, executable_index)?,
                        return_flow: arm.return_flow.clone(),
                        extern_marshals: arm.extern_marshals.clone(),
                    })
                })
                .collect::<Result<Vec<_>, _>>()?,
            miss: dispatch.miss,
        }),
    })
}

fn package_call_target(
    world: &World<'_>,
    root: RootId,
    caller: &ExecutableKey,
    target: &CallTarget<ExecutableKey>,
    executable_index: &std::collections::HashMap<ExecutableKey, usize>,
) -> Result<CallTarget<usize>, FatalError> {
    Ok(match target {
        CallTarget::Local(callee) => CallTarget::Local(executable_index.get(callee).copied().ok_or_else(|| {
            incomplete_backend_program(
                world,
                root,
                format!(
                    "symbolic backend call edge {:?} -> {:?} points outside final executable inventory",
                    caller, callee
                ),
            )
        })?),
        CallTarget::ProviderBoundary(function) => CallTarget::ProviderBoundary(*function),
    })
}

fn package_backend_callable_entries(
    world: &World<'_>,
    root: RootId,
    session: &PullSession,
    executable_index: &std::collections::HashMap<ExecutableKey, usize>,
) -> Result<Vec<BackendCallableEntry>, FatalError> {
    let mut entries = Vec::new();
    for (boundary, facts) in session.boundary_facts_inventory() {
        let boundary_descr = world.boundary(*boundary);
        for target_symbol in facts.resolutions.iter() {
            let Some(target) = executable_key_for_symbol_in_index(target_symbol, executable_index, world.types())
            else {
                return Err(incomplete_backend_program(
                    world,
                    root,
                    format!(
                        "boundary {:?} resolution {:?} is missing from final executable inventory",
                        boundary, target_symbol
                    ),
                ));
            };
            let Some(target_index) = executable_index.get(&target).copied() else {
                return Err(incomplete_backend_program(
                    world,
                    root,
                    format!(
                        "boundary {:?} target {:?} is missing from final executable inventory",
                        boundary, target
                    ),
                ));
            };
            let Some(target_backend) = session.backend_executable(&target) else {
                return Err(incomplete_backend_program(
                    world,
                    root,
                    format!(
                        "boundary {:?} target {:?} is missing from backend products",
                        boundary, target
                    ),
                ));
            };
            entries.push(BackendCallableEntry {
                boundary: *boundary,
                target: target_index,
                capture_count: boundary_descr.published_capture_lanes.len(),
                capture_reprs: boundary_descr
                    .published_capture_lanes
                    .iter()
                    .copied()
                    .map(|lane| abi_value_repr_for_lane(world, lane))
                    .collect(),
                arg_reprs: boundary_descr
                    .published_arg_lanes
                    .iter()
                    .copied()
                    .map(|lane| abi_value_repr_for_lane(world, lane))
                    .collect(),
                return_ty: target_backend.abi.return_ty,
                return_shape: boundary_descr.published_return_shape,
                return_lanes: boundary_descr.published_return_lanes.to_vec(),
            });
        }
    }
    entries.sort_by(compare_backend_callable_entries);
    entries.dedup();
    Ok(entries)
}

fn executable_key_for_symbol_in_index(
    symbol: &ExecutableSymbol,
    executable_index: &std::collections::HashMap<ExecutableKey, usize>,
    types: &super::super::Types,
) -> Option<ExecutableKey> {
    executable_index
        .keys()
        .find(|key| {
            key.need == symbol.need
                && key.activation.function == symbol.activation.function
                && key.activation.inputs(types).as_slice() == symbol.activation.input.as_ref()
        })
        .cloned()
}

fn compare_backend_callable_entries(left: &BackendCallableEntry, right: &BackendCallableEntry) -> std::cmp::Ordering {
    left.target
        .cmp(&right.target)
        .then_with(|| left.boundary.as_u32().cmp(&right.boundary.as_u32()))
        .then_with(|| left.capture_count.cmp(&right.capture_count))
}

fn compare_executable_keys(
    left: &ExecutableKey,
    right: &ExecutableKey,
    types: &super::super::Types,
) -> std::cmp::Ordering {
    left.activation
        .root
        .as_u32()
        .cmp(&right.activation.root.as_u32())
        .then_with(|| {
            left.activation
                .function
                .as_u32()
                .cmp(&right.activation.function.as_u32())
        })
        .then_with(|| left.activation.inputs(types).cmp(&right.activation.inputs(types)))
        .then_with(|| compare_executable_needs(left.need, right.need))
}

fn compare_executable_needs(left: ExecutableNeed, right: ExecutableNeed) -> std::cmp::Ordering {
    match (left, right) {
        (ExecutableNeed::Value, ExecutableNeed::Value) => std::cmp::Ordering::Equal,
        (ExecutableNeed::Value, ExecutableNeed::TupleFields(_)) => std::cmp::Ordering::Less,
        (ExecutableNeed::TupleFields(_), ExecutableNeed::Value) => std::cmp::Ordering::Greater,
        (ExecutableNeed::TupleFields(left), ExecutableNeed::TupleFields(right)) => left.cmp(&right),
    }
}

fn abi_value_repr_for_lane(
    world: &World<'_>,
    lane: super::super::transport::LaneId,
) -> super::super::artifact::AbiValueRepr {
    let ty = world.lane(lane).ty;
    if world.types().is_floating(&ty) {
        return super::super::artifact::AbiValueRepr::RawF64;
    }
    if world.types().is_integer(&ty) {
        return super::super::artifact::AbiValueRepr::RawInt;
    }
    if !world.types().atom_literals(&ty).is_empty() {
        super::super::artifact::AbiValueRepr::RawAtom
    } else {
        super::super::artifact::AbiValueRepr::ValueRef
    }
}

fn lower_symbolic_body(
    lowerer: &mut BackendLowerer<'_, '_, '_>,
    emission: &EmissionReadyExecutable,
    abi: &AbiReadyExecutable,
) -> Result<SymbolicBackendBody, FatalError> {
    match &abi.body {
        LoweredBody::Extern { signature } => Ok(SymbolicBackendBody::Extern {
            signature: signature.clone(),
        }),
        LoweredBody::Clauses {
            clauses,
            entries,
            generated,
        } => Ok(SymbolicBackendBody::Clauses {
            clauses: clauses
                .iter()
                .map(|clause| {
                    Ok(SymbolicBackendClause {
                        span: clause.span,
                        params: clause.params.clone(),
                        projections: clause
                            .projections
                            .iter()
                            .map(|step| lowerer.lower_step(emission, step))
                            .collect::<Result<Vec<_>, _>>()?,
                        entry: clause.entry,
                    })
                })
                .collect::<Result<Vec<_>, _>>()?,
            entries: entries
                .iter()
                .enumerate()
                .map(|(index, entry)| lower_symbolic_entry(lowerer, emission, abi, index, entry))
                .collect::<Result<Vec<_>, _>>()?,
            generated: generated.clone(),
        }),
    }
}

fn lower_symbolic_entry(
    lowerer: &mut BackendLowerer<'_, '_, '_>,
    emission: &EmissionReadyExecutable,
    abi: &AbiReadyExecutable,
    entry_index: usize,
    entry: &LoweredEntry,
) -> Result<SymbolicBackendEntry, FatalError> {
    let entry_id = original_entry_id(emission, entry_index);
    Ok(SymbolicBackendEntry {
        span: entry.span,
        origin: lower_entry_origin(emission, entry_index, entry),
        params: entry.params.clone(),
        captures: entry.captures.clone(),
        capture_positions: lowerer.capture_positions_for_entry(emission, entry_id, entry)?,
        reusable_cons_captures: entry
            .reusable_cons_captures
            .iter()
            .map(|capture| super::super::artifact::ReusableConsCapture {
                head: capture.head,
                source: capture.source,
            })
            .collect(),
        steps: entry
            .steps
            .iter()
            .map(|step| lowerer.lower_step(emission, step))
            .collect::<Result<Vec<_>, _>>()?,
        tail: lower_symbolic_tail(lowerer, emission, abi, &entry.tail).unwrap_or_else(|_| {
            panic!(
                "symbolic backend entry {entry_index} tail is incomplete: {:?}",
                entry.tail
            )
        }),
    })
}

fn lower_symbolic_tail(
    lowerer: &mut BackendLowerer<'_, '_, '_>,
    emission: &EmissionReadyExecutable,
    abi: &AbiReadyExecutable,
    tail: &LoweredTail,
) -> Result<SymbolicBackendTail, FatalError> {
    Ok(match tail {
        LoweredTail::Value { value, dest } => SymbolicBackendTail::Value {
            value: *value,
            dest: dest.clone(),
        },
        LoweredTail::DirectCall {
            value,
            callsite,
            args,
            dest,
            ..
        } => {
            let edge = abi.call_edges.get(callsite).ok_or_else(|| {
                incomplete_backend_program(
                    lowerer.world,
                    lowerer.root_id,
                    format!("missing symbolic direct-call edge for callsite {}", callsite.as_u32()),
                )
            })?;
            SymbolicBackendTail::DirectCall {
                value: *value,
                callsite: *callsite,
                target: edge.target.clone(),
                args: lowerer.lower_call_args(emission, *callsite, None, args)?,
                dest: dest.clone(),
            }
        }
        LoweredTail::ClosureCall {
            value,
            callsite,
            callee,
            args,
            dest,
        } => {
            let edge = abi.call_edges.get(callsite);
            SymbolicBackendTail::ClosureCall {
                value: *value,
                callsite: *callsite,
                callee: *callee,
                target: edge
                    .and_then(|edge| symbolic_direct_call_edge(&edge.target))
                    .and_then(|edge| edge.callee.local().cloned()),
                args: lowerer.lower_call_args(emission, *callsite, Some(*callee), args)?,
                dest: dest.clone(),
                return_flow: edge
                    .and_then(|edge| symbolic_direct_call_edge(&edge.target))
                    .map(|edge| edge.return_flow.clone()),
            }
        }
        LoweredTail::If {
            cond,
            then_entry,
            else_entry,
        } => SymbolicBackendTail::If {
            cond: *cond,
            then_entry: *then_entry,
            else_entry: *else_entry,
        },
        LoweredTail::Dispatch {
            inputs,
            bindings,
            dispatch,
        } => SymbolicBackendTail::Dispatch {
            inputs: inputs.clone(),
            bindings: bindings.clone(),
            dispatch: dispatch.clone(),
        },
        LoweredTail::Receive(receive) => {
            SymbolicBackendTail::Receive(Box::new(super::super::artifact::BackendReceive {
                bindings: receive.bindings.clone(),
                dispatch: receive.dispatch.clone(),
                clauses: receive.clauses.clone(),
                after: receive.after.clone(),
                dest: receive.dest.clone(),
            }))
        }
        LoweredTail::Halt { atom } => SymbolicBackendTail::Halt { atom: atom.clone() },
    })
}

fn symbolic_direct_call_edge(target: &CallEdge<ExecutableKey>) -> Option<&DirectCallEdge<ExecutableKey>> {
    match target {
        CallEdge::Direct(direct) => Some(direct),
        CallEdge::Dispatch(_) => None,
    }
}

fn symbolic_emission_ready_executable(key: ExecutableKey, abi: &AbiReadyExecutable) -> EmissionReadyExecutable {
    EmissionReadyExecutable {
        key,
        entry_dispatch: abi.entry_dispatch.clone(),
        return_ty: abi.return_ty,
        param_reprs: abi.param_reprs.clone(),
        runtime_demand: abi.runtime_demand.clone(),
        transport: abi.transport.clone(),
        original_entry_ids: abi.original_entry_ids.clone(),
        value_types: abi.value_types.clone(),
        value_reprs: abi.value_reprs.clone(),
        effects: abi.effects,
        body: abi.body.clone(),
        call_edges: Vec::new(),
    }
}

fn symbolic_materialized_transport_plan(
    session: &PullSession,
    executable: &ExecutableKey,
    types: &super::super::Types,
) -> MaterializedTransportPlan {
    let mut position_shapes = session
        .transport_shapes()
        .iter()
        .map(|(position, shape)| (position.clone(), *shape))
        .collect::<Vec<_>>();
    position_shapes.sort_by_key(|(position, _)| format!("{position:?}"));
    let mut publication_boundaries = session
        .boundary_facts_inventory()
        .iter()
        .flat_map(|(boundary, facts)| facts.publications.iter().cloned().map(|position| (position, *boundary)))
        .collect::<Vec<_>>();
    publication_boundaries.sort_by(|left, right| {
        format!("{:?}", left.0)
            .cmp(&format!("{:?}", right.0))
            .then_with(|| left.1.as_u32().cmp(&right.1.as_u32()))
    });
    MaterializedTransportPlan {
        entry: ExecutableSymbol {
            activation: ActivationSymbol {
                function: executable.activation.function,
                input: executable.activation.inputs(types).into_boxed_slice(),
            },
            need: executable.need,
        },
        executable_membership: Box::default(),
        position_shapes,
        callable_ids: session.demanded_callables().iter().copied().collect(),
        boundary_ids: session.demanded_boundaries().iter().copied().collect(),
        publication_boundaries,
        codegen_seam_facts: Box::default(),
    }
}

struct BackendLowerer<'a, 'plan, 'tel> {
    world: &'a mut World<'tel>,
    root_id: RootId,
    transport: &'plan MaterializedTransportPlan,
}

impl<'a, 'plan, 'tel> BackendLowerer<'a, 'plan, 'tel> {
    fn new(world: &'a mut World<'tel>, root_id: RootId, transport: &'plan MaterializedTransportPlan) -> Self {
        Self {
            world,
            root_id,
            transport,
        }
    }

    fn lower_executable(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
    ) -> Result<BackendExecutable, FatalError> {
        Ok(BackendExecutable {
            key: executable.key.clone(),
            entry_dispatch: executable.entry_dispatch.clone(),
            return_ty: executable.return_ty,
            param_reprs: executable.param_reprs.clone(),
            runtime_demand: executable.runtime_demand.clone(),
            transport: executable.transport.clone(),
            value_types: executable.value_types.clone(),
            value_reprs: executable.value_reprs.clone(),
            effects: executable.effects,
            body: self.lower_body(executable)?,
        })
    }

    fn lower_body(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
    ) -> Result<BackendBody, FatalError> {
        match &executable.body {
            LoweredBody::Extern { signature } => Ok(BackendBody::Extern {
                signature: signature.clone(),
            }),
            LoweredBody::Clauses {
                clauses,
                entries,
                generated,
            } => Ok(BackendBody::Clauses {
                clauses: clauses
                    .iter()
                    .map(|clause| self.lower_clause(executable, clause))
                    .collect::<Result<Vec<_>, _>>()?,
                entries: entries
                    .iter()
                    .enumerate()
                    .map(|(index, entry)| self.lower_entry(executable, index, entry))
                    .collect::<Result<Vec<_>, _>>()?,
                generated: generated.clone(),
            }),
        }
    }

    fn lower_clause(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
        clause: &LoweredClause,
    ) -> Result<BackendClause, FatalError> {
        Ok(BackendClause {
            span: clause.span,
            params: clause.params.clone(),
            projections: clause
                .projections
                .iter()
                .map(|step| self.lower_step(executable, step))
                .collect::<Result<Vec<_>, _>>()?,
            entry: clause.entry,
        })
    }

    fn lower_entry(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
        entry_index: usize,
        entry: &LoweredEntry,
    ) -> Result<BackendEntry, FatalError> {
        let entry_id = original_entry_id(executable, entry_index);
        let capture_positions = self.capture_positions_for_entry(executable, entry_id, entry)?;
        Ok(BackendEntry {
            span: entry.span,
            origin: lower_entry_origin(executable, entry_index, entry),
            params: entry.params.clone(),
            captures: entry.captures.clone(),
            capture_positions,
            reusable_cons_captures: entry
                .reusable_cons_captures
                .iter()
                .map(|capture| super::super::artifact::ReusableConsCapture {
                    head: capture.head,
                    source: capture.source,
                })
                .collect(),
            steps: entry
                .steps
                .iter()
                .map(|step| self.lower_step(executable, step))
                .collect::<Result<Vec<_>, _>>()?,
            tail: self.lower_tail(executable, &entry.tail)?,
        })
    }

    fn capture_positions_for_entry(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
        entry_id: ControlEntryId,
        entry: &LoweredEntry,
    ) -> Result<Vec<super::super::transport::TransportPosition>, FatalError> {
        let positions = executable
            .transport
            .entry_capture_positions
            .iter()
            .filter(|position| {
                matches!(
                    position,
                    super::super::transport::TransportPosition::EntryCapture {
                        entry: captured_entry,
                        ..
                    } if *captured_entry == entry_id
                )
            })
            .cloned()
            .collect::<Vec<_>>();
        if positions.len() != entry.captures.len() {
            return Err(incomplete_backend_program(
                self.world,
                self.root_id,
                format!(
                    "entry {} has {} captures but {} transport capture positions",
                    entry_id.as_u32(),
                    entry.captures.len(),
                    positions.len()
                ),
            ));
        }
        Ok(positions)
    }

    fn lower_step(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
        step: &LoweredStep,
    ) -> Result<BackendStep, FatalError> {
        Ok(match step {
            LoweredStep::Const { value, literal } => BackendStep::Const {
                value: *value,
                literal: literal.clone(),
            },
            LoweredStep::Tuple { value, items } => {
                if self.value_is_proven_runtime_absent(executable, *value) {
                    BackendStep::Omitted { value: *value }
                } else {
                    BackendStep::Tuple {
                        value: *value,
                        items: items.clone(),
                    }
                }
            }
            LoweredStep::List { value, items, tail } => {
                if self.value_is_proven_runtime_absent(executable, *value) {
                    BackendStep::Omitted { value: *value }
                } else {
                    BackendStep::List {
                        value: *value,
                        items: items.clone(),
                        tail: *tail,
                    }
                }
            }
            LoweredStep::Map { value, entries } => BackendStep::Map {
                value: *value,
                entries: entries.iter().map(|(key, value)| (key.value, *value)).collect(),
            },
            LoweredStep::MapUpdate { value, base, entries } => BackendStep::MapUpdate {
                value: *value,
                base: *base,
                entries: entries.iter().map(|(key, value)| (key.value, *value)).collect(),
            },
            LoweredStep::Struct { value, module, fields } => BackendStep::Struct {
                value: *value,
                module_name: self
                    .world
                    .module_name(*module)
                    .unwrap_or_else(|| panic!("struct module {} should have a name", module.as_u32()))
                    .to_string(),
                fields: fields.clone(),
            },
            LoweredStep::Bitstring { value, fields } => BackendStep::Bitstring {
                value: *value,
                fields: fields.clone(),
            },
            LoweredStep::FunctionRef { value, function } => BackendStep::FunctionRef {
                value: *value,
                function: *function,
            },
            LoweredStep::Lambda {
                value,
                function,
                captures,
            } => BackendStep::Lambda {
                value: *value,
                function: *function,
                captures: captures.clone(),
            },
            LoweredStep::BinaryOp { value, op, left, right } => BackendStep::BinaryOp {
                value: *value,
                op: *op,
                left: *left,
                right: *right,
            },
            LoweredStep::UnaryOp { value, op, input } => BackendStep::UnaryOp {
                value: *value,
                op: *op,
                input: *input,
            },
            LoweredStep::MapIndex { value, base, key } => BackendStep::MapIndex {
                value: *value,
                base: *base,
                key: key.value,
            },
            LoweredStep::FieldAccess { value, base, field } => BackendStep::FieldAccess {
                value: *value,
                base: *base,
                field: field.clone(),
            },
            LoweredStep::AssertLiteral { source, literal } => BackendStep::AssertLiteral {
                source: *source,
                literal: literal.clone(),
            },
            LoweredStep::AssertStruct { source, module } => BackendStep::AssertStruct {
                source: *source,
                module_name: self
                    .world
                    .module_name(*module)
                    .unwrap_or_else(|| panic!("struct module {} should have a name", module.as_u32()))
                    .to_string(),
            },
            LoweredStep::RequireMapValue { value, source, key } => BackendStep::RequireMapValue {
                value: *value,
                source: *source,
                key: key.clone(),
            },
            LoweredStep::AssertTuple { source, arity } => BackendStep::AssertTuple {
                source: *source,
                arity: *arity,
            },
            LoweredStep::TupleField { value, source, index } => BackendStep::TupleField {
                value: *value,
                source: *source,
                index: *index,
            },
            LoweredStep::AssertEmptyList { source } => BackendStep::AssertEmptyList { source: *source },
            LoweredStep::AssertSame { source, value } => BackendStep::AssertSame {
                source: *source,
                value: *value,
            },
            LoweredStep::SplitList { source, head, tail } => BackendStep::SplitList {
                source: *source,
                head: *head,
                tail: *tail,
            },
            LoweredStep::BitstringInit { reader, source } => BackendStep::BitstringInit {
                reader: *reader,
                source: *source,
            },
            LoweredStep::BitstringRead {
                ok,
                value,
                next_reader,
                reader,
                spec,
                is_last,
            } => BackendStep::BitstringRead {
                ok: *ok,
                value: *value,
                next_reader: *next_reader,
                reader: *reader,
                spec: spec.clone(),
                is_last: *is_last,
            },
            LoweredStep::AssertBitstringDone { reader } => BackendStep::AssertBitstringDone { reader: *reader },
        })
    }

    fn value_is_proven_runtime_absent(
        &self,
        executable: &super::super::artifact::EmissionReadyExecutable,
        value: super::super::body::ValueId,
    ) -> bool {
        self.transport
            .executable_value_shape(&executable.transport, value)
            .is_some_and(|shape| matches!(self.world.shape(shape), ShapeDescr::Nothing))
    }

    fn lower_tail(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
        tail: &LoweredTail,
    ) -> Result<BackendTail, FatalError> {
        Ok(match tail {
            LoweredTail::Value { value, dest } => BackendTail::Value {
                value: *value,
                dest: dest.clone(),
            },
            LoweredTail::DirectCall {
                value,
                callsite,
                args,
                dest,
                ..
            } => {
                let edge = call_edge(executable, *callsite).ok_or_else(|| {
                    incomplete_backend_program(
                        self.world,
                        self.root_id,
                        format!("missing settled direct-call edge for callsite {}", callsite.as_u32()),
                    )
                })?;
                BackendTail::DirectCall {
                    value: *value,
                    callsite: *callsite,
                    target: edge.target.clone(),
                    args: self.lower_call_args(executable, *callsite, None, args)?,
                    dest: dest.clone(),
                }
            }
            LoweredTail::ClosureCall {
                value,
                callsite,
                callee,
                args,
                dest,
            } => {
                let edge = call_edge(executable, *callsite);
                BackendTail::ClosureCall {
                    value: *value,
                    callsite: *callsite,
                    callee: *callee,
                    target: edge
                        .and_then(direct_call_edge)
                        .and_then(|edge| edge.callee.copied_local()),
                    args: self.lower_call_args(executable, *callsite, Some(*callee), args)?,
                    dest: dest.clone(),
                    return_flow: edge.and_then(direct_call_edge).map(|edge| edge.return_flow.clone()),
                }
            }
            LoweredTail::If {
                cond,
                then_entry,
                else_entry,
            } => BackendTail::If {
                cond: *cond,
                then_entry: *then_entry,
                else_entry: *else_entry,
            },
            LoweredTail::Dispatch {
                inputs,
                bindings,
                dispatch,
            } => BackendTail::Dispatch {
                inputs: inputs.clone(),
                bindings: bindings.clone(),
                dispatch: dispatch.clone(),
            },
            LoweredTail::Receive(receive) => BackendTail::Receive(Box::new(super::super::artifact::BackendReceive {
                bindings: receive.bindings.clone(),
                dispatch: receive.dispatch.clone(),
                clauses: receive.clauses.clone(),
                after: receive.after.clone(),
                dest: receive.dest.clone(),
            })),
            LoweredTail::Halt { atom } => BackendTail::Halt { atom: atom.clone() },
        })
    }

    fn lower_call_args(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
        callsite: CallSiteId,
        _closure_callee: Option<super::super::body::ValueId>,
        args: &[CallArg],
    ) -> Result<Vec<BackendCallArg>, FatalError> {
        let executable_symbol = ExecutableSymbol {
            activation: ActivationSymbol {
                function: executable.key.activation.function,
                input: executable.key.activation.inputs(self.world.types()).into_boxed_slice(),
            },
            need: executable.key.need,
        };
        args.iter()
            .enumerate()
            .map(|(semantic_index, arg)| {
                Ok(BackendCallArg {
                    value: arg.value,
                    position: TransportPosition::CallArg {
                        executable: executable_symbol.clone(),
                        callsite,
                        semantic_index,
                    },
                })
            })
            .collect()
    }
}

fn lower_entry_origin(
    executable: &super::super::artifact::EmissionReadyExecutable,
    entry_index: usize,
    entry: &LoweredEntry,
) -> BackendEntryOrigin {
    let entry_id = original_entry_id(executable, entry_index);
    if let ControlEntryOrigin::DeliveredResume { value } = entry.origin {
        if let Some(position) = executable
            .transport
            .resume_positions
            .iter()
            .find(|position| {
                matches!(
                    position,
                    super::super::transport::TransportPosition::ResumePayload {
                        entry: resume_entry,
                        ..
                    } if *resume_entry == entry_id
                )
            })
            .cloned()
        {
            return BackendEntryOrigin::DeliveredResume { value, position };
        }
        if matches!(&entry.tail, LoweredTail::Halt { atom } if atom == UNREACHABLE_CONTROL_ATOM) {
            return BackendEntryOrigin::Branch;
        }
        panic!("resume entry {entry_index} should have a settled transport position: {entry:?}");
    }
    if matches!(&entry.tail, LoweredTail::Halt { atom } if atom == UNREACHABLE_CONTROL_ATOM) {
        return BackendEntryOrigin::Branch;
    }
    match entry.origin {
        ControlEntryOrigin::Clause => BackendEntryOrigin::Clause,
        ControlEntryOrigin::Branch => BackendEntryOrigin::Branch,
        ControlEntryOrigin::ReceiveOutcome => BackendEntryOrigin::ReceiveOutcome,
        ControlEntryOrigin::DeliveredResume { .. } => unreachable!("delivered resumes return before branch fallback"),
    }
}

fn original_entry_id(
    executable: &super::super::artifact::EmissionReadyExecutable,
    entry_index: usize,
) -> ControlEntryId {
    executable
        .original_entry_ids
        .get(entry_index)
        .copied()
        .unwrap_or_else(|| ControlEntryId::from_u32(entry_index as u32))
}

fn call_edge(
    executable: &super::super::artifact::EmissionReadyExecutable,
    callsite: CallSiteId,
) -> Option<&super::super::artifact::EmissionReadyCallEdge> {
    executable.call_edges.iter().find(|edge| edge.callsite == callsite)
}

fn direct_call_edge(edge: &super::super::artifact::EmissionReadyCallEdge) -> Option<&DirectCallEdge<usize>> {
    match &edge.target {
        CallEdge::Direct(direct) => Some(direct),
        CallEdge::Dispatch(_) => None,
    }
}

fn collect_backend_atom_names(world: &mut World<'_>, executables: &[BackendExecutable]) -> Vec<String> {
    let mut seen = HashSet::new();
    let mut atoms = Vec::new();
    for name in ["nil", "true", "false"] {
        push_atom(&mut seen, &mut atoms, name);
    }
    for executable in executables {
        collect_executable_atoms(world, executable, &mut seen, &mut atoms);
    }
    atoms
}

fn collect_executable_atoms(
    world: &mut World<'_>,
    executable: &BackendExecutable,
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    match &executable.body {
        BackendBody::Extern { .. } => {}
        BackendBody::Clauses { clauses, entries, .. } => {
            if let Some(dispatch) = &executable.entry_dispatch {
                collect_dispatch_atoms(world, dispatch.plan(), seen, atoms);
            }
            for clause in clauses {
                collect_step_atoms(world, &clause.projections, seen, atoms);
            }
            for entry in entries {
                collect_entry_atoms(world, entry, seen, atoms);
            }
        }
    }
}

fn collect_entry_atoms(
    world: &mut World<'_>,
    entry: &BackendEntry,
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    collect_step_atoms(world, &entry.steps, seen, atoms);
    collect_tail_atoms(world, &entry.tail, seen, atoms);
}

fn collect_step_atoms(
    _world: &mut World<'_>,
    steps: &[BackendStep],
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    for step in steps {
        match step {
            BackendStep::Const { literal, .. } | BackendStep::AssertLiteral { literal, .. } => {
                collect_literal_atoms(literal, seen, atoms);
            }
            BackendStep::FieldAccess { field, .. } => {
                if seen.insert(field.clone()) {
                    atoms.push(field.clone());
                }
            }
            BackendStep::RequireMapValue { key, .. } => {
                collect_literal_atoms(key, seen, atoms);
            }
            BackendStep::Omitted { .. }
            | BackendStep::Tuple { .. }
            | BackendStep::List { .. }
            | BackendStep::Map { .. }
            | BackendStep::MapUpdate { .. }
            | BackendStep::Struct { .. }
            | BackendStep::Bitstring { .. }
            | BackendStep::FunctionRef { .. }
            | BackendStep::Lambda { .. }
            | BackendStep::BinaryOp { .. }
            | BackendStep::UnaryOp { .. }
            | BackendStep::MapIndex { .. }
            | BackendStep::AssertStruct { .. }
            | BackendStep::AssertTuple { .. }
            | BackendStep::TupleField { .. }
            | BackendStep::AssertEmptyList { .. }
            | BackendStep::AssertSame { .. }
            | BackendStep::SplitList { .. }
            | BackendStep::BitstringInit { .. }
            | BackendStep::BitstringRead { .. }
            | BackendStep::AssertBitstringDone { .. } => {}
        }
    }
}

fn collect_tail_atoms(world: &mut World<'_>, tail: &BackendTail, seen: &mut HashSet<String>, atoms: &mut Vec<String>) {
    match tail {
        BackendTail::DirectCall {
            target: CallEdge::Dispatch(dispatch),
            ..
        } => {
            collect_dispatch_atoms(world, &dispatch.plan, seen, atoms);
            push_atom(seen, atoms, UNREACHABLE_CONTROL_ATOM);
        }
        BackendTail::Dispatch { dispatch, .. } => collect_dispatch_atoms(world, &dispatch.plan, seen, atoms),
        BackendTail::Receive(receive) => collect_dispatch_atoms(world, &receive.dispatch, seen, atoms),
        BackendTail::Halt { atom } => push_atom(seen, atoms, atom),
        BackendTail::Value { .. }
        | BackendTail::DirectCall { .. }
        | BackendTail::ClosureCall { .. }
        | BackendTail::If { .. } => {}
    }
}

fn collect_literal_atoms(literal: &super::super::body::Literal, seen: &mut HashSet<String>, atoms: &mut Vec<String>) {
    if let super::super::body::Literal::Atom(name) = literal {
        push_atom(seen, atoms, name);
    }
}

fn collect_dispatch_atoms(
    world: &mut World<'_>,
    plan: &PatternDispatchPlan<Ty>,
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    for prepared in &plan.prepared_keys {
        collect_dispatch_const_atoms(prepared, seen, atoms);
    }
    for subject in &plan.matrix.subjects {
        match &subject.source {
            SubjectSource::Input { .. } => {}
            SubjectSource::Projection(projection) => {
                if let ProjectionKind::MapValue { key } = &projection.kind {
                    collect_dispatch_const_atoms(key, seen, atoms);
                }
            }
        }
    }
    for guard in &plan.guards {
        collect_guard_atoms(world, guard, seen, atoms);
    }
    collect_dispatch_graph_atoms(world, plan, plan.graph.root, seen, atoms);
}

fn collect_dispatch_graph_atoms(
    world: &mut World<'_>,
    plan: &PatternDispatchPlan<Ty>,
    node_id: crate::dispatch_matrix::GraphNodeId,
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    let Some(node) = plan.graph.node(node_id) else {
        return;
    };
    match node {
        DispatchNode::Fail | DispatchNode::Outcome { .. } => {}
        DispatchNode::Test {
            predicate,
            on_match,
            on_miss,
        } => {
            collect_region_atoms(world, &predicate.region, seen, atoms);
            collect_dispatch_graph_atoms(world, plan, on_match.target, seen, atoms);
            collect_dispatch_graph_atoms(world, plan, on_miss.target, seen, atoms);
        }
    }
}

fn collect_region_atoms(
    world: &mut World<'_>,
    region: &Region<Ty>,
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    match region {
        Region::Equal(ComparisonValue::Const(value)) | Region::MapKeyPresent { key: value } => {
            collect_dispatch_const_atoms(value, seen, atoms);
        }
        Region::Type(ty) => {
            for atom in world.types().atom_literals(ty) {
                push_atom(seen, atoms, &atom);
            }
        }
        Region::Equal(ComparisonValue::Pinned(_))
        | Region::TupleArity(_)
        | Region::List(_)
        | Region::MapKind
        | Region::Bitstring(_)
        | Region::Guard(_) => {}
    }
}

fn collect_guard_atoms(
    world: &mut World<'_>,
    expr: &PatternGuardExpr<Ty>,
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    match expr {
        PatternGuardExpr::Const(value) => collect_dispatch_const_atoms(value, seen, atoms),
        PatternGuardExpr::Unary { expr, .. } => collect_guard_atoms(world, expr, seen, atoms),
        PatternGuardExpr::Binary { lhs, rhs, .. } => {
            collect_guard_atoms(world, lhs, seen, atoms);
            collect_guard_atoms(world, rhs, seen, atoms);
        }
        PatternGuardExpr::Dispatch { inputs, dispatch } => {
            for input in inputs {
                collect_guard_atoms(world, input, seen, atoms);
            }
            collect_guard_dispatch_atoms(world, dispatch, seen, atoms);
        }
        PatternGuardExpr::Subject(_) | PatternGuardExpr::Pinned(_) => {}
    }
}

fn collect_guard_dispatch_atoms(
    world: &mut World<'_>,
    dispatch: &PatternGuardDispatch<Ty>,
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    collect_dispatch_atoms(world, &dispatch.plan, seen, atoms);
    for body in &dispatch.bodies {
        collect_guard_atoms(world, body, seen, atoms);
    }
}

fn collect_dispatch_const_atoms(value: &DispatchConst, seen: &mut HashSet<String>, atoms: &mut Vec<String>) {
    if let DispatchConst::AtomName(name) = value {
        push_atom(seen, atoms, name);
    }
}

fn push_atom(seen: &mut HashSet<String>, atoms: &mut Vec<String>, name: &str) {
    if seen.insert(name.to_string()) {
        atoms.push(name.to_string());
    }
}

fn incomplete_backend_program(world: &World<'_>, root_id: RootId, message: impl Into<String>) -> FatalError {
    let message = message.into();
    let diagnostic = Diagnostic::error(
        codes::ARTIFACT_INCOMPLETE_SEMANTIC_PLAN,
        format!("compiler2 backend lowering for root {}: {}", root_id.as_u32(), message),
        Span::DUMMY,
    );
    emit_through(world.tel(), std::slice::from_ref(&diagnostic));
    FatalError
}
