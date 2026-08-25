//! Compiler2 backend product packaging.
//!
//! This module packages product-keyed symbolic backend executables into the
//! backend-owned program consumed by the interpreter and native lowering.

use std::collections::{HashMap, HashSet};

use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch, PatternGuardExpr};
use crate::dispatch_matrix::{ComparisonValue, DispatchNode, ProjectionKind, Region, SubjectSource};
use crate::ground_value::GroundValue;
use crate::source::Span;

use super::super::artifact::{
    AbiReadyExecutable, AbiValueRepr, BackendBody, BackendCallArg, BackendClause, BackendConstructionCapture,
    BackendConstructionMemberAdapter, BackendConstructionWrapper, BackendEntry, BackendEntryCapture,
    BackendEntryOrigin, BackendExecutable, BackendProgram, BackendReturnFlow, BackendReturnLayout, BackendStep,
    BackendTail, CallEdge, CallReturnFlow, CallTarget, DirectCallEdge, DispatchCallArm, EmissionReadyExecutable,
    MaterializedTransportPlan, RootBackendProductAnswer,
};
use super::super::body::{
    CallArg, CallSiteId, ControlDestination, ControlEntryId, ControlEntryOrigin, LoweredBody, LoweredEntry,
    LoweredStep, LoweredTail, ValueId,
};
use super::super::drive::{FactKey, Job, JobEffects};
use super::super::facts::FactUse;
use super::super::identity::RootId;
use super::super::identity::{ActivationKey, ExecutableKey, ExecutableNeed};
use super::super::pull::{
    ProductKey, ProductReadContext, ProductValue, PullOutcome, PullWait, SymbolicBackendBody, SymbolicBackendClause,
    SymbolicBackendEntry, SymbolicBackendEntryOrigin, SymbolicBackendExecutable, SymbolicBackendTail, TransportLayout,
};
use super::super::scheduler::FatalError;
use super::super::transport::{
    ActivationSymbol, BoundaryFacts, BoundaryId, CallableFacts, CallableId, CodegenLaneRepr, CodegenSeam,
    CodegenSeamFact, ExecutableSymbol, LaneId, ShapeDescr, ShapeId, TransportPosition,
};
use super::super::types::Ty;
use super::super::world::World;
use super::artifact::{codegen_seam_fact_sort_key, transport_position_global_sort_key};

const UNREACHABLE_CONTROL_ATOM: &str = "compiler2_unreachable_control";

pub(crate) fn build_backend_product(
    world: &mut World,
    tel: &impl crate::telemetry::RawSpanTelemetry,
    root_id: RootId,
) -> Result<JobEffects, FatalError> {
    let backend_fact = FactKey::BackendProgram(root_id);
    let (_program, driver) =
        super::super::product_drive::drive_root_backend_product::<_, FatalError>(world, tel, root_id)?;
    driver.finish_session();
    Ok(JobEffects {
        outputs: vec![backend_fact.clone()],
        changed: vec![backend_fact],
        ..JobEffects::default()
    })
}

/// Reports `RootBackendProduct` pull-drive failures as `FatalError`,
/// emitting the diagnostic the fatal-error contract requires. The
/// `job_failed` hook forwards the job's own `FatalError` unchanged — a job
/// that fails through `jobs::run` has already emitted its own diagnostic, so
/// this boundary must not emit a second one for the same failure.
impl super::super::product_drive::ProductDriveError for FatalError {
    fn job_failed<T: crate::telemetry::Telemetry>(
        _world: &World,
        _tel: &T,
        _root: RootId,
        _fact: &FactUse<FactKey>,
        _job: &Job,
        source: FatalError,
    ) -> Self {
        source
    }

    fn no_ready_producer<T: crate::telemetry::Telemetry>(
        _world: &World,
        tel: &T,
        root: RootId,
        fact: &FactUse<FactKey>,
    ) -> Self {
        emit_backend_product_error(
            tel,
            Span::DUMMY,
            format!(
                "compiler2 backend product for root {} waited on {:?} with no ready producer",
                root.as_u32(),
                fact
            ),
        )
    }

    fn fact_wait_budget_exceeded<T: crate::telemetry::Telemetry>(
        _world: &World,
        tel: &T,
        root: RootId,
        fact: &FactUse<FactKey>,
    ) -> Self {
        emit_backend_product_error(
            tel,
            Span::DUMMY,
            format!(
                "compiler2 backend product for root {} exceeded fact-wait budget for {:?}",
                root.as_u32(),
                fact
            ),
        )
    }

    fn did_not_settle<T: crate::telemetry::Telemetry>(
        _world: &World,
        tel: &T,
        root: RootId,
        _last_wait: Option<(ProductKey, Vec<PullWait>)>,
    ) -> Self {
        emit_backend_product_error(
            tel,
            Span::DUMMY,
            format!("compiler2 backend product for root {} did not settle", root.as_u32()),
        )
    }
}

fn emit_backend_product_error(
    tel: &impl crate::telemetry::Telemetry,
    span: Span,
    message: impl Into<String>,
) -> FatalError {
    let diagnostic = Diagnostic::error(codes::ARTIFACT_INCOMPLETE_SEMANTIC_PLAN, message.into(), span);
    emit_through(tel, std::slice::from_ref(&diagnostic));
    FatalError
}

pub(crate) fn produce_root_backend_product(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    root: RootId,
) -> PullOutcome {
    let root_entry = world.root_entry(root);
    let keying_facts = [
        FactKey::RootEntry(root),
        FactKey::DispatchMask(root_entry.function),
        FactKey::Recursive(root_entry.function),
    ];
    let keying_waits = keying_facts
        .into_iter()
        .filter(|fact| !context.read_fact(world, FactUse::settled(fact.clone())))
        .map(|fact| PullWait::Fact(FactUse::settled(fact)))
        .collect::<Vec<_>>();
    if !keying_waits.is_empty() {
        return PullOutcome::Waiting(keying_waits);
    }
    let entry = world.root_entry_executable(root);
    let mut reachable = HashSet::new();
    let mut stack = vec![entry.clone()];
    let mut waits = Vec::new();
    let mut backends = HashMap::new();
    while let Some(current) = stack.pop() {
        if !reachable.insert(current.clone()) {
            continue;
        }
        let Some(value) = context.read_product(ProductKey::BackendExecutable(current.clone())) else {
            waits.push(PullWait::Product(ProductKey::BackendExecutable(current)));
            continue;
        };
        let ProductValue::BackendExecutable(backend) = value else {
            panic!("backend executable product produced unexpected value {value:?}");
        };
        let backend = backend.as_ref().clone();
        for target in backend.call_edges.values() {
            for callee in symbolic_call_edge_callees(target) {
                stack.push(callee.clone());
            }
        }
        for positioned in backend.abi.callable_owners.iter() {
            let owner = &positioned.owner;
            stack.extend(callable_resolution_executables(root, &owner.callable_facts));
            stack.extend(boundary_resolution_executables(root, &owner.boundary_facts));
        }
        backends.insert(current, backend);
    }
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }
    let owners = backends
        .values()
        .flat_map(|backend| {
            backend
                .abi
                .callable_owners
                .iter()
                .map(|positioned| positioned.owner.clone())
        })
        .collect::<Vec<_>>();
    let (produced_callables, produced_boundaries) = aggregate_callable_owners(&owners);
    let transport =
        symbolic_materialized_transport_plan(&backends, &entry, world, &produced_callables, &produced_boundaries);

    let mut executable_keys = reachable.into_iter().collect::<Vec<_>>();
    executable_keys.sort_by(|left, right| compare_executable_keys(left, right, world.types()));
    let executable_index = executable_keys
        .iter()
        .enumerate()
        .map(|(index, executable)| (executable.clone(), index))
        .collect::<std::collections::HashMap<_, _>>();
    let (construction_wrappers, construction_identities) =
        package_backend_construction_wrappers(world, tel, root, &backends, &transport, &executable_index)
            .expect("root backend product should have complete construction wrapper inventory");
    for (executable, index) in &executable_index {
        context
            .session_mut()
            .assign_executable_index(executable.clone(), *index);
    }
    let return_endpoints = executable_keys
        .iter()
        .flat_map(|key| {
            backends
                .get(key)
                .into_iter()
                .flat_map(|backend| backend.abi.return_endpoints.iter().cloned())
        })
        .collect::<HashMap<_, _>>();
    let executables = executable_keys
        .iter()
        .map(|executable| {
            let backend = backends
                .get(executable)
                .expect("reachable backend executable should have been checked before packaging");
            package_symbolic_backend_executable(
                world,
                tel,
                root,
                backend,
                &executable_index,
                &transport,
                &construction_identities,
                &return_endpoints,
            )
        })
        .collect::<Result<Vec<_>, _>>()
        .unwrap_or_else(|error| {
            panic!("root backend product should have complete symbolic executable inventory: {error:?}")
        });
    let entry_index = executable_index
        .get(&entry)
        .copied()
        .expect("root entry should be in packaged executable inventory");
    let program = BackendProgram {
        backend_revision: 0,
        entry: entry_index,
        atom_names: collect_backend_atom_names(world, &executables),
        struct_schemas: world.struct_def_schemas(),
        executables,
        construction_wrappers,
    };
    super::super::drive::ExecutionContext::new(world, tel).define_backend_program(root, program.clone());
    PullOutcome::Produced(ProductValue::RootBackendProduct(Box::new(RootBackendProductAnswer {
        program,
        transport,
    })))
}

pub(crate) fn aggregate_callable_owners(
    owners: &[super::super::transport::CallableConstructionOwner],
) -> (HashMap<CallableId, CallableFacts>, HashMap<BoundaryId, BoundaryFacts>) {
    let mut callables = HashMap::<CallableId, CallableFacts>::new();
    let mut boundaries = HashMap::<BoundaryId, BoundaryFacts>::new();
    for owner in owners {
        for (callable, facts) in &owner.callable_facts {
            let aggregate = callables.entry(*callable).or_insert_with(|| CallableFacts {
                resolutions: Box::default(),
                direct_surfaces: Box::default(),
                direct_edges: Box::default(),
                boundary_ids: Box::default(),
            });
            aggregate.resolutions = union_boxed(&aggregate.resolutions, &facts.resolutions);
            aggregate.direct_surfaces = union_boxed(&aggregate.direct_surfaces, &facts.direct_surfaces);
            aggregate.direct_edges = union_boxed(&aggregate.direct_edges, &facts.direct_edges);
            aggregate.boundary_ids = union_boxed(&aggregate.boundary_ids, &facts.boundary_ids);
        }
        for (boundary, facts) in &owner.boundary_facts {
            let aggregate = boundaries.entry(*boundary).or_insert_with(|| BoundaryFacts {
                publications: Box::default(),
                resolutions: Box::default(),
            });
            aggregate.publications = union_boxed(&aggregate.publications, &facts.publications);
            aggregate.resolutions = union_boxed(&aggregate.resolutions, &facts.resolutions);
        }
    }
    (callables, boundaries)
}

fn union_boxed<T: Clone + PartialEq>(left: &[T], right: &[T]) -> Box<[T]> {
    let mut values = left.to_vec();
    for value in right {
        if !values.contains(value) {
            values.push(value.clone());
        }
    }
    values.into_boxed_slice()
}

pub(crate) fn produce_backend_executable_product(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    executable: &ExecutableKey,
) -> PullOutcome {
    let Some(value) = context.read_product(ProductKey::AbiExecutable(executable.clone())) else {
        return PullOutcome::Waiting(vec![PullWait::Product(ProductKey::AbiExecutable(executable.clone()))]);
    };
    let ProductValue::AbiExecutable(abi) = value else {
        panic!("ABI executable product produced unexpected value {value:?}");
    };
    let abi = abi.as_ref().clone();
    let value_shapes = executable_value_shapes(&abi);
    let mut lowerer = BackendLowerer::new(world, tel, context.session().root(), value_shapes);
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
    context
        .session_mut()
        .record_backend_executable(executable.clone(), backend.clone());
    PullOutcome::Produced(ProductValue::BackendExecutable(Box::new(backend)))
}

fn executable_value_shapes(abi: &AbiReadyExecutable) -> HashMap<ValueId, ShapeId> {
    let mut shapes = HashMap::new();
    for position in abi.transport.value_positions.iter() {
        let TransportPosition::Value { value, .. } = position else {
            continue;
        };
        let shape = abi.transport.layout_at(position).map(|layout| layout.structural);
        let previous = shapes.insert(*value, shape);
        assert!(
            previous.is_none(),
            "transport should publish one local value position for {:?} in {:?}",
            value,
            abi.transport.executable
        );
    }
    shapes
        .into_iter()
        .filter_map(|(value, shape)| Some((value, shape?)))
        .collect()
}

fn symbolic_call_edge_callees(target: &CallEdge<ExecutableKey>) -> Vec<&ExecutableKey> {
    match target {
        CallEdge::Direct(direct) => direct.callee.local().into_iter().collect(),
        CallEdge::Dispatch(dispatch) => dispatch.arms.iter().filter_map(|arm| arm.callee.local()).collect(),
        CallEdge::Indirect { .. } => Vec::new(),
    }
}

fn boundary_resolution_executables(
    root: RootId,
    boundaries: &HashMap<BoundaryId, BoundaryFacts>,
) -> Vec<ExecutableKey> {
    let mut out = Vec::new();
    for facts in boundaries.values() {
        for target in facts.resolutions.iter() {
            out.push(executable_key_for_symbol(root, target));
        }
    }
    out
}

fn callable_resolution_executables(root: RootId, callables: &HashMap<CallableId, CallableFacts>) -> Vec<ExecutableKey> {
    callables
        .values()
        .flat_map(|facts| facts.resolutions.iter())
        .map(|target| executable_key_for_symbol(root, target))
        .collect()
}

pub(crate) fn executable_key_for_symbol(root: RootId, symbol: &ExecutableSymbol) -> ExecutableKey {
    ExecutableKey {
        activation: ActivationKey {
            root,
            function: symbol.activation.function,
            arrow: symbol.activation.arrow,
        },
        need: symbol.need,
    }
}

fn package_symbolic_backend_executable(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root: RootId,
    backend: &SymbolicBackendExecutable,
    executable_index: &std::collections::HashMap<ExecutableKey, usize>,
    transport: &MaterializedTransportPlan,
    construction_identities: &HashMap<TransportPosition, u32>,
    return_endpoints: &HashMap<TransportPosition, BackendReturnLayout>,
) -> Result<BackendExecutable, FatalError> {
    let resolved_entries =
        resolved_constructions_for_values(&backend.abi.transport.value_positions, construction_identities);
    Ok(BackendExecutable {
        key: backend.key.clone(),
        entry_dispatch: backend.abi.entry_dispatch.clone(),
        return_ty: backend.abi.return_ty,
        param_reprs: backend.abi.param_reprs.clone(),
        semantic_inputs: backend.abi.semantic_inputs.clone(),
        return_layout: backend.abi.return_layout.clone(),
        runtime_demand: backend.abi.runtime_demand.clone(),
        value_types: backend.abi.value_types.clone(),
        value_layouts: backend.abi.value_layouts.clone(),
        effects: backend.abi.effects,
        body: package_symbolic_backend_body(
            world,
            tel,
            root,
            &backend.key,
            &backend.body,
            executable_index,
            &resolved_entries,
            transport,
            return_endpoints,
        )?,
    })
}

fn package_symbolic_backend_body(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root: RootId,
    caller: &ExecutableKey,
    body: &SymbolicBackendBody,
    executable_index: &std::collections::HashMap<ExecutableKey, usize>,
    resolved_entries: &HashMap<ValueId, u32>,
    transport: &MaterializedTransportPlan,
    return_endpoints: &HashMap<TransportPosition, BackendReturnLayout>,
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
                    projections: package_backend_steps(&clause.projections, resolved_entries),
                    entry: clause.entry,
                })
                .collect(),
            entries: entries
                .iter()
                .map(|entry| {
                    package_symbolic_backend_entry(
                        world,
                        tel,
                        root,
                        caller,
                        entry,
                        executable_index,
                        resolved_entries,
                        transport,
                        return_endpoints,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?,
            generated: generated.clone(),
        },
    })
}

fn package_symbolic_backend_entry(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root: RootId,
    caller: &ExecutableKey,
    entry: &SymbolicBackendEntry,
    executable_index: &std::collections::HashMap<ExecutableKey, usize>,
    resolved_entries: &HashMap<ValueId, u32>,
    transport: &MaterializedTransportPlan,
    return_endpoints: &HashMap<TransportPosition, BackendReturnLayout>,
) -> Result<BackendEntry, FatalError> {
    Ok(BackendEntry {
        span: entry.span,
        origin: package_backend_entry_origin(&entry.origin, return_endpoints)?,
        params: entry.params.clone(),
        captures: package_backend_entry_captures(world, transport, entry)?,
        reusable_cons_captures: entry.reusable_cons_captures.clone(),
        steps: package_backend_steps(&entry.steps, resolved_entries),
        tail: package_symbolic_backend_tail(
            world,
            tel,
            root,
            caller,
            &entry.tail,
            executable_index,
            resolved_entries,
            return_endpoints,
        )?,
    })
}

fn package_backend_entry_origin(
    origin: &SymbolicBackendEntryOrigin,
    endpoints: &HashMap<TransportPosition, BackendReturnLayout>,
) -> Result<BackendEntryOrigin, FatalError> {
    Ok(match origin {
        SymbolicBackendEntryOrigin::Clause => BackendEntryOrigin::Clause,
        SymbolicBackendEntryOrigin::Branch => BackendEntryOrigin::Branch,
        SymbolicBackendEntryOrigin::ReceiveOutcome => BackendEntryOrigin::ReceiveOutcome,
        SymbolicBackendEntryOrigin::DeliveredResume { value, position } => BackendEntryOrigin::DeliveredResume {
            value: *value,
            layout: endpoints.get(position).cloned().ok_or(FatalError)?,
        },
    })
}

fn package_backend_entry_captures(
    world: &mut World,
    transport: &MaterializedTransportPlan,
    entry: &SymbolicBackendEntry,
) -> Result<Vec<BackendEntryCapture>, FatalError> {
    if entry.captures.len() != entry.capture_positions.len() {
        return Err(FatalError);
    }
    entry
        .captures
        .iter()
        .copied()
        .zip(entry.capture_positions.iter().cloned())
        .map(|(value, position)| {
            let layout = transport.layout_at(&position).ok_or(FatalError)?;
            let contract = backend_entry_capture_contract(world, transport, &position, layout.structural)?;
            Ok(BackendEntryCapture {
                value,
                layout: super::super::artifact::BackendValueLayout {
                    structural: layout.structural,
                    carrier: layout.carrier,
                    tys: contract.iter().map(|(ty, _)| *ty).collect(),
                    reprs: contract.iter().map(|(_, repr)| *repr).collect(),
                },
            })
        })
        .collect()
}

fn backend_entry_capture_contract(
    world: &mut World,
    transport: &MaterializedTransportPlan,
    position: &TransportPosition,
    shape: ShapeId,
) -> Result<Vec<(Ty, AbiValueRepr)>, FatalError> {
    if transport.carries_runtime_value(position) {
        return Ok(vec![(world.types_mut().any(), AbiValueRepr::ValueRef)]);
    }
    match world.shape(shape).clone() {
        ShapeDescr::Tuple(fields) => fields
            .iter()
            .copied()
            .map(|field| backend_entry_capture_contract(world, transport, position, field))
            .collect::<Result<Vec<_>, _>>()
            .map(|fields| fields.into_iter().flatten().collect()),
        ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Callable(_) => {
            backend_entry_capture_leaf_contracts(world, transport, position, shape)
        }
    }
}

fn backend_entry_capture_leaf_contracts(
    world: &mut World,
    transport: &MaterializedTransportPlan,
    position: &TransportPosition,
    shape: ShapeId,
) -> Result<Vec<(Ty, AbiValueRepr)>, FatalError> {
    Ok(world
        .shape_leaf_lanes(shape)
        .into_iter()
        .filter_map(|(leaf_shape, lane)| {
            transport
                .codegen_seam_facts
                .iter()
                .find(|fact| {
                    fact.shape == Some(leaf_shape)
                        && fact.lane == lane
                        && backend_entry_capture_seam_matches(position, &fact.seam)
                })
                .map(|fact| {
                    let repr = match fact.repr {
                        CodegenLaneRepr::ValueRef => AbiValueRepr::ValueRef,
                        CodegenLaneRepr::RawInt => AbiValueRepr::RawInt,
                        CodegenLaneRepr::RawF64 => AbiValueRepr::RawF64,
                        CodegenLaneRepr::RawAtom => AbiValueRepr::RawAtom,
                    };
                    (world.lane(lane).ty, repr)
                })
        })
        .collect())
}

fn backend_entry_capture_seam_matches(position: &TransportPosition, seam: &CodegenSeam) -> bool {
    let TransportPosition::EntryCapture {
        executable,
        entry,
        capture_index,
    } = position
    else {
        return false;
    };
    matches!(
        seam,
        CodegenSeam::EntryCapture {
            executable: seam_executable,
            entry: seam_entry,
            capture_index: seam_capture_index,
        } if seam_executable == executable && seam_entry == entry && seam_capture_index == capture_index
    )
}

fn resolved_constructions_for_values(
    positions: &[TransportPosition],
    identities: &HashMap<TransportPosition, u32>,
) -> HashMap<ValueId, u32> {
    let mut resolved = HashMap::new();
    for position in positions {
        let TransportPosition::Value { value, .. } = position else {
            continue;
        };
        if let Some(identity) = identities.get(position) {
            resolved.insert(*value, *identity);
        }
    }
    resolved
}

fn package_backend_steps(steps: &[BackendStep], resolved_entries: &HashMap<ValueId, u32>) -> Vec<BackendStep> {
    let resolved_entry_for = |value: &ValueId| resolved_entries.get(value).copied();
    steps
        .iter()
        .map(|step| match step {
            BackendStep::FunctionRef { value, function, .. } => BackendStep::FunctionRef {
                value: *value,
                function: *function,
                construction: resolved_entry_for(value),
            },
            BackendStep::Lambda {
                value,
                function,
                captures,
                ..
            } => BackendStep::Lambda {
                value: *value,
                function: *function,
                captures: captures.clone(),
                construction: resolved_entry_for(value),
            },
            _ => step.clone(),
        })
        .collect()
}

fn package_symbolic_backend_tail(
    world: &World,
    tel: &impl crate::telemetry::Telemetry,
    root: RootId,
    caller: &ExecutableKey,
    tail: &SymbolicBackendTail,
    executable_index: &std::collections::HashMap<ExecutableKey, usize>,
    _resolved_entries: &HashMap<ValueId, u32>,
    return_endpoints: &HashMap<TransportPosition, BackendReturnLayout>,
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
            target: package_call_edge(world, tel, root, caller, target, executable_index, return_endpoints)?,
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
                            tel,
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
            return_flow: return_flow
                .as_ref()
                .map(|flow| resolve_return_flow(flow, return_endpoints))
                .transpose()?,
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
    world: &World,
    tel: &impl crate::telemetry::Telemetry,
    root: RootId,
    caller: &ExecutableKey,
    target: &CallEdge<ExecutableKey>,
    executable_index: &std::collections::HashMap<ExecutableKey, usize>,
    return_endpoints: &HashMap<TransportPosition, BackendReturnLayout>,
) -> Result<CallEdge<usize, BackendReturnFlow>, FatalError> {
    Ok(match target {
        CallEdge::Direct(direct) => CallEdge::Direct(DirectCallEdge {
            callee: package_call_target(world, tel, root, caller, &direct.callee, executable_index)?,
            return_flow: resolve_return_flow(&direct.return_flow, return_endpoints)?,
            extern_marshals: direct.extern_marshals.clone(),
        }),
        CallEdge::Dispatch(dispatch) => CallEdge::Dispatch(Box::new(super::super::artifact::DispatchCallEdge {
            plan: dispatch.plan.clone(),
            arms: dispatch
                .arms
                .iter()
                .map(|arm| {
                    Ok(DispatchCallArm {
                        body_id: arm.body_id,
                        callee: package_call_target(world, tel, root, caller, &arm.callee, executable_index)?,
                        return_flow: resolve_return_flow(&arm.return_flow, return_endpoints)?,
                        extern_marshals: arm.extern_marshals.clone(),
                    })
                })
                .collect::<Result<Vec<_>, _>>()?,
            miss: dispatch.miss,
        })),
        CallEdge::Indirect(return_flow) => CallEdge::Indirect(resolve_return_flow(return_flow, return_endpoints)?),
    })
}

fn package_call_target(
    _world: &World,
    tel: &impl crate::telemetry::Telemetry,
    root: RootId,
    caller: &ExecutableKey,
    target: &CallTarget<ExecutableKey>,
    executable_index: &std::collections::HashMap<ExecutableKey, usize>,
) -> Result<CallTarget<usize>, FatalError> {
    Ok(match target {
        CallTarget::Local(callee) => CallTarget::Local(executable_index.get(callee).copied().ok_or_else(|| {
            incomplete_backend_program(
                tel,
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

fn resolve_return_flow(
    flow: &super::super::artifact::CallReturnFlow,
    endpoints: &HashMap<TransportPosition, BackendReturnLayout>,
) -> Result<BackendReturnFlow, FatalError> {
    let layout = |position: &TransportPosition| endpoints.get(position).ok_or(FatalError);
    Ok(match flow {
        CallReturnFlow::NoReturn { local_source } => {
            if let Some(local_source) = local_source
                && !layout(local_source)?.diverges
            {
                return Err(FatalError);
            }
            BackendReturnFlow::NoReturn
        }
        super::super::artifact::CallReturnFlow::Tail {
            source,
            payload,
            caller_return,
        } => {
            if layout(source)? == layout(payload)? && layout(source)? == layout(caller_return)? {
                BackendReturnFlow::Tail
            } else {
                BackendReturnFlow::Continue {
                    source: Box::new(layout(source)?.clone()),
                }
            }
        }
        super::super::artifact::CallReturnFlow::Continue { source, .. } => BackendReturnFlow::Continue {
            source: Box::new(layout(source)?.clone()),
        },
        super::super::artifact::CallReturnFlow::Deliver { source, entry, .. } => {
            let source = layout(source)?;
            if source.diverges {
                return Err(FatalError);
            }
            BackendReturnFlow::Deliver {
                source: Box::new(source.clone()),
                entry: *entry,
            }
        }
    })
}

fn package_backend_construction_wrappers(
    world: &World,
    tel: &impl crate::telemetry::Telemetry,
    root: RootId,
    backends: &HashMap<ExecutableKey, SymbolicBackendExecutable>,
    transport: &MaterializedTransportPlan,
    executable_index: &std::collections::HashMap<ExecutableKey, usize>,
) -> Result<(Vec<BackendConstructionWrapper>, HashMap<TransportPosition, u32>), FatalError> {
    let mut constructions = transport
        .callable_owners
        .iter()
        .filter_map(|positioned| {
            positioned
                .owner
                .construction
                .as_ref()
                .map(|construction| (positioned, construction))
        })
        .collect::<Vec<_>>();
    constructions.sort_by_cached_key(|(positioned, _)| transport_position_global_sort_key(&positioned.position));
    let identities = constructions
        .iter()
        .enumerate()
        .map(|(identity, (positioned, _))| (positioned.position.clone(), identity as u32))
        .collect();
    let wrappers = constructions
        .into_iter()
        .enumerate()
        .map(|(identity, (_, construction))| {
            let call_arity = construction
                .members
                .first()
                .expect("first-class construction authority must contain an executable member")
                .surface_inputs
                .len();
            if construction
                .members
                .iter()
                .any(|member| member.surface_inputs.len() != call_arity)
                || construction
                    .members
                    .iter()
                    .any(|member| world.boundary(member.boundary).surface_arg_shapes.len() != call_arity)
            {
                return Err(incomplete_backend_program(
                    tel,
                    root,
                    format!(
                        "callable construction {:?} has members with incompatible semantic call arities",
                        construction.producer
                    ),
                ));
            }
            let members = construction
                .members
                .iter()
                .map(|member| {
                    let target_key = executable_key_for_symbol_in_index(&member.resolution, executable_index);
                    let target = target_key
                        .as_ref()
                        .and_then(|key| executable_index.get(key).copied())
                        .ok_or_else(|| {
                            incomplete_backend_program(
                                tel,
                                root,
                                format!(
                                    "callable construction {:?} member {:?} is missing from final executable inventory",
                                    construction.producer, member.resolution
                                ),
                            )
                        })?;
                    let target_backend = backends
                        .get(
                            target_key
                                .as_ref()
                                .expect("resolved construction member should name an executable"),
                        )
                        .expect("resolved construction member should have backend ABI");
                    Ok(BackendConstructionMemberAdapter {
                        boundary: member.boundary,
                        surface_inputs: member.surface_inputs.clone(),
                        surface_arg_shapes: member.surface_arg_shapes.clone(),
                        target,
                        capture_semantic_inputs: member.capture_semantic_inputs.clone(),
                        surface_semantic_inputs: member.surface_semantic_inputs.clone(),
                        target_inputs: target_backend.abi.semantic_inputs.clone(),
                        target_return: target_backend.abi.return_layout.clone(),
                    })
                })
                .collect::<Result<Vec<_>, FatalError>>()?;
            let return_form = if members.iter().all(|member| member.target_return.diverges) {
                super::super::artifact::BackendCallableReturn::Diverges
            } else if members
                .iter()
                .filter(|member| !member.target_return.diverges)
                .map(|member| member.target_return.layout.reprs.is_empty())
                .collect::<std::collections::BTreeSet<_>>()
                == std::collections::BTreeSet::from([false])
            {
                super::super::artifact::BackendCallableReturn::ValueRef
            } else if members
                .iter()
                .filter(|member| !member.target_return.diverges)
                .all(|member| member.target_return.layout.reprs.is_empty())
            {
                super::super::artifact::BackendCallableReturn::Absent
            } else {
                return Err(incomplete_backend_program(
                    tel,
                    root,
                    format!(
                        "callable construction {:?} mixes absent and value member returns",
                        construction.producer
                    ),
                ));
            };
            let captures = construction
                .captures
                .iter()
                .map(|capture| {
                    let TransportPosition::Value { executable, value } = &capture.source else {
                        return Err(FatalError);
                    };
                    let layout = symbolic_backend_for_executable(backends, executable, world)
                        .and_then(|backend| backend.abi.value_layouts.get(value))
                        .cloned()
                        .ok_or(FatalError)?;
                    if layout.structural != capture.layout.structural || layout.carrier != capture.layout.carrier {
                        return Err(FatalError);
                    }
                    Ok(BackendConstructionCapture { layout })
                })
                .collect::<Result<Box<_>, FatalError>>()?;
            Ok(BackendConstructionWrapper {
                identity: identity as u32,
                callable: construction.callable,
                captures,
                call_arity,
                return_form,
                members: members.into_boxed_slice(),
                selection: construction.selection.clone(),
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((wrappers, identities))
}

fn executable_key_for_symbol_in_index(
    symbol: &ExecutableSymbol,
    executable_index: &std::collections::HashMap<ExecutableKey, usize>,
) -> Option<ExecutableKey> {
    executable_index
        .keys()
        .find(|key| {
            key.need == symbol.need
                && key.activation.function == symbol.activation.function
                && key.activation.arrow == symbol.activation.arrow
        })
        .cloned()
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

fn lower_symbolic_body(
    lowerer: &mut BackendLowerer<'_, '_, impl crate::telemetry::Telemetry>,
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
                            .map(|step| lowerer.lower_step(step))
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
    lowerer: &mut BackendLowerer<'_, '_, impl crate::telemetry::Telemetry>,
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
        reusable_cons_captures: entry.reusable_cons_captures.clone(),
        steps: entry
            .steps
            .iter()
            .map(|step| lowerer.lower_step(step))
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
    lowerer: &mut BackendLowerer<'_, '_, impl crate::telemetry::Telemetry>,
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
                    lowerer.telemetry,
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
                    .and_then(|edge| symbolic_call_edge_return_flow(&edge.target))
                    .cloned(),
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
        CallEdge::Dispatch(_) | CallEdge::Indirect(_) => None,
    }
}

fn symbolic_call_edge_return_flow(target: &CallEdge<ExecutableKey>) -> Option<&CallReturnFlow> {
    match target {
        CallEdge::Direct(direct) => Some(&direct.return_flow),
        CallEdge::Indirect(return_flow) => Some(return_flow),
        CallEdge::Dispatch(_) => None,
    }
}

fn symbolic_emission_ready_executable(key: ExecutableKey, abi: &AbiReadyExecutable) -> EmissionReadyExecutable {
    EmissionReadyExecutable {
        key,
        entry_dispatch: abi.entry_dispatch.clone(),
        return_ty: abi.return_ty,
        param_reprs: abi.param_reprs.clone(),
        semantic_inputs: abi.semantic_inputs.clone(),
        return_layout: abi.return_layout.clone(),
        runtime_demand: abi.runtime_demand.clone(),
        transport: abi.transport.clone(),
        original_entry_ids: abi.original_entry_ids.clone(),
        value_types: abi.value_types.clone(),
        value_layouts: abi.value_layouts.clone(),
        effects: abi.effects,
        body: abi.body.clone(),
        call_edges: Vec::new(),
    }
}

pub(crate) fn symbolic_materialized_transport_plan(
    backends: &HashMap<ExecutableKey, SymbolicBackendExecutable>,
    executable: &ExecutableKey,
    world: &World,
    callables: &HashMap<CallableId, CallableFacts>,
    boundaries: &HashMap<BoundaryId, BoundaryFacts>,
) -> MaterializedTransportPlan {
    let mut position_layouts = backends
        .values()
        .flat_map(|backend| {
            backend.abi.transport.position_layouts.iter().cloned().chain(
                backend
                    .abi
                    .callable_owners
                    .iter()
                    .map(|positioned| (positioned.position.clone(), positioned.owner.layout)),
            )
        })
        .collect::<Vec<_>>();
    // Structural keys, not `format!("{position:?}")` comparators: these are
    // final-packaging sorts over the GLOBAL position set, and Debug-string
    // keys recomputed per comparison were ~21% of the release compile. Cached
    // because the key allocates (interned input types).
    position_layouts.sort_by_cached_key(|(position, _)| transport_position_global_sort_key(position));
    position_layouts.dedup_by(|left, right| {
        if left.0 != right.0 {
            return false;
        }
        assert_eq!(left.1, right.1, "one transport position must have one settled layout");
        true
    });
    let mut publication_boundaries = boundaries
        .iter()
        .flat_map(|(boundary, facts)| facts.publications.iter().cloned().map(|position| (position, *boundary)))
        .collect::<Vec<_>>();
    publication_boundaries
        .sort_by_cached_key(|(position, boundary)| (transport_position_global_sort_key(position), boundary.as_u32()));
    let codegen_seam_facts = symbolic_codegen_seam_facts(backends, &position_layouts, world, boundaries);
    let mut callable_owners = backends
        .values()
        .flat_map(|backend| backend.abi.callable_owners.iter().cloned())
        .collect::<Vec<_>>();
    callable_owners.sort_by_cached_key(|positioned| transport_position_global_sort_key(&positioned.position));
    callable_owners.dedup_by(|left, right| {
        if left.position != right.position {
            return false;
        }
        assert_eq!(
            left.owner, right.owner,
            "one callable position must have one settled owner"
        );
        true
    });
    MaterializedTransportPlan {
        entry: ExecutableSymbol {
            activation: ActivationSymbol {
                function: executable.activation.function,
                arrow: executable.activation.arrow,
                input: executable.activation.inputs(world.types()).into_boxed_slice(),
            },
            need: executable.need,
        },
        executable_membership: Box::default(),
        position_layouts,
        callable_boundaries: {
            let mut rows = callables
                .iter()
                .map(|(callable, facts)| (*callable, facts.boundary_ids.clone()))
                .collect::<Vec<_>>();
            rows.sort_by_key(|(callable, _)| callable.as_u32());
            rows
        },
        boundary_ids: {
            let mut ids = boundaries.keys().copied().collect::<Vec<_>>();
            ids.sort_by_key(|boundary| boundary.as_u32());
            ids
        },
        publication_boundaries,
        codegen_seam_facts,
        callable_owners: callable_owners.into_boxed_slice(),
        callable_facts: callables.clone(),
        boundary_facts: boundaries.clone(),
    }
}

fn symbolic_codegen_seam_facts(
    backends: &HashMap<ExecutableKey, SymbolicBackendExecutable>,
    position_layouts: &[(TransportPosition, TransportLayout)],
    world: &World,
    boundaries: &HashMap<BoundaryId, BoundaryFacts>,
) -> Box<[CodegenSeamFact]> {
    let mut out = Vec::new();
    for (position, layout) in position_layouts {
        let shape = layout.structural;
        if symbolic_position_structural_lanes_are_ignored(backends, position, world) {
            continue;
        }
        for (leaf_shape, lane) in lanes_for_codegen_seam_shape(world, shape) {
            match position {
                TransportPosition::ExecutableInput {
                    executable,
                    semantic_index,
                } => {
                    let repr = codegen_repr_for_lane(world, lane);
                    out.push(CodegenSeamFact {
                        seam: CodegenSeam::FunctionEntry {
                            executable: executable.clone(),
                            semantic_index: *semantic_index,
                        },
                        shape: Some(leaf_shape),
                        lane,
                        repr,
                    });
                    if symbolic_backend_for_executable(backends, executable, world)
                        .is_some_and(|backend| matches!(backend.body, SymbolicBackendBody::Extern { .. }))
                    {
                        out.push(CodegenSeamFact {
                            seam: CodegenSeam::ExternBoundary {
                                executable: executable.clone(),
                            },
                            shape: Some(leaf_shape),
                            lane,
                            repr,
                        });
                    }
                }
                TransportPosition::ExecutableReturn { executable } => {
                    let repr = codegen_repr_for_lane(world, lane);
                    out.push(CodegenSeamFact {
                        seam: CodegenSeam::ReturnDelivery {
                            executable: executable.clone(),
                        },
                        shape: Some(leaf_shape),
                        lane,
                        repr,
                    });
                    if symbolic_backend_for_executable(backends, executable, world)
                        .is_some_and(|backend| matches!(backend.body, SymbolicBackendBody::Extern { .. }))
                    {
                        out.push(CodegenSeamFact {
                            seam: CodegenSeam::ExternBoundary {
                                executable: executable.clone(),
                            },
                            shape: Some(leaf_shape),
                            lane,
                            repr,
                        });
                    }
                }
                TransportPosition::ResumePayload {
                    executable,
                    callsite,
                    entry,
                } => {
                    let repr = block_param_codegen_repr_for_lane(world, lane);
                    out.push(CodegenSeamFact {
                        seam: CodegenSeam::BlockParam {
                            executable: executable.clone(),
                            entry: *entry,
                        },
                        shape: Some(leaf_shape),
                        lane,
                        repr,
                    });
                    if let Some(callsite) = callsite {
                        out.push(CodegenSeamFact {
                            seam: CodegenSeam::ContinuationEntry {
                                executable: executable.clone(),
                                callsite: *callsite,
                                entry: *entry,
                            },
                            shape: Some(leaf_shape),
                            lane,
                            repr,
                        });
                    }
                }
                TransportPosition::ReturnPayload { executable, callsite } => {
                    out.push(CodegenSeamFact {
                        seam: CodegenSeam::ReturnContinuation {
                            executable: executable.clone(),
                            callsite: *callsite,
                        },
                        shape: Some(leaf_shape),
                        lane,
                        repr: codegen_repr_for_lane(world, lane),
                    });
                }
                TransportPosition::EntryCapture {
                    executable,
                    entry,
                    capture_index,
                } => {
                    let repr = block_param_codegen_repr_for_lane(world, lane);
                    out.push(CodegenSeamFact {
                        seam: CodegenSeam::EntryCapture {
                            executable: executable.clone(),
                            entry: *entry,
                            capture_index: *capture_index,
                        },
                        shape: Some(leaf_shape),
                        lane,
                        repr,
                    });
                    if let Some(callsite) = symbolic_entry_capture_owner_callsite(backends, executable, position, world)
                    {
                        out.push(CodegenSeamFact {
                            seam: CodegenSeam::ContinuationEntry {
                                executable: executable.clone(),
                                callsite,
                                entry: *entry,
                            },
                            shape: Some(leaf_shape),
                            lane,
                            repr,
                        });
                    }
                }
                TransportPosition::CallArg {
                    executable, callsite, ..
                } => {
                    if symbolic_backend_for_executable(backends, executable, world)
                        .and_then(|backend| symbolic_callsite_dest(backend, *callsite))
                        .is_some_and(|dest| matches!(dest, ControlDestination::Return))
                    {
                        out.push(CodegenSeamFact {
                            seam: CodegenSeam::TailCall {
                                executable: executable.clone(),
                                callsite: *callsite,
                            },
                            shape: Some(leaf_shape),
                            lane,
                            repr: codegen_repr_for_lane(world, lane),
                        });
                    }
                }
                TransportPosition::Value { .. } => {}
            }
        }
    }
    for boundary in boundaries.keys().copied() {
        push_symbolic_boundary_codegen_seams(backends, world, boundary, &boundaries[&boundary], &mut out);
    }
    // Same structural key the session's codegen-seam-fact product uses
    // (`jobs/artifact.rs`), so the plan's facts and the session product share
    // one canonical order.
    out.sort_by_cached_key(codegen_seam_fact_sort_key);
    out.into_boxed_slice()
}

fn symbolic_position_structural_lanes_are_ignored(
    backends: &HashMap<ExecutableKey, SymbolicBackendExecutable>,
    position: &TransportPosition,
    world: &World,
) -> bool {
    match position {
        TransportPosition::ExecutableInput {
            executable,
            semantic_index,
        } => symbolic_backend_for_executable(backends, executable, world)
            .and_then(|backend| backend.abi.runtime_demand.input_demands.get(*semantic_index))
            .is_some_and(|demand| demand.is_ignore()),
        TransportPosition::EntryCapture {
            executable,
            entry,
            capture_index,
        } => symbolic_backend_for_executable(backends, executable, world)
            .and_then(|backend| backend.abi.runtime_demand.entry_capture_demands.get(entry))
            .and_then(|demands| demands.get(*capture_index))
            .is_some_and(|demand| demand.is_ignore()),
        TransportPosition::ExecutableReturn { .. }
        | TransportPosition::ResumePayload { .. }
        | TransportPosition::ReturnPayload { .. }
        | TransportPosition::CallArg { .. }
        | TransportPosition::Value { .. } => false,
    }
}

fn push_symbolic_boundary_codegen_seams(
    backends: &HashMap<ExecutableKey, SymbolicBackendExecutable>,
    world: &World,
    boundary: BoundaryId,
    facts: &BoundaryFacts,
    out: &mut Vec<CodegenSeamFact>,
) {
    let descr = world.boundary(boundary);
    for lane in descr
        .published_capture_lanes
        .iter()
        .chain(descr.published_arg_lanes.iter())
        .copied()
    {
        out.push(CodegenSeamFact {
            seam: CodegenSeam::CallableBoundary { boundary },
            shape: None,
            lane,
            repr: codegen_repr_for_lane(world, lane),
        });
    }
    if facts.publications.is_empty() {
        return;
    }
    out.push(CodegenSeamFact {
        seam: CodegenSeam::FirstClassPublication { boundary },
        shape: None,
        lane: descr.published_value_lane,
        repr: CodegenLaneRepr::ValueRef,
    });
    for publication in facts.publications.iter() {
        push_symbolic_publication_codegen_seam(backends, world, boundary, publication, descr.published_value_lane, out);
    }
}

fn push_symbolic_publication_codegen_seam(
    backends: &HashMap<ExecutableKey, SymbolicBackendExecutable>,
    world: &World,
    boundary: BoundaryId,
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
        TransportPosition::ReturnPayload { executable, callsite } => out.push(CodegenSeamFact {
            seam: CodegenSeam::ReturnContinuation {
                executable: executable.clone(),
                callsite: *callsite,
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
            if let Some(callsite) = symbolic_entry_capture_owner_callsite(backends, executable, publication, world) {
                out.push(CodegenSeamFact {
                    seam: CodegenSeam::ContinuationEntry {
                        executable: executable.clone(),
                        callsite,
                        entry: *entry,
                    },
                    shape: None,
                    lane,
                    repr,
                });
            }
        }
        TransportPosition::CallArg { .. } | TransportPosition::Value { .. } => {
            let _ = boundary;
        }
    }
}

fn symbolic_backend_for_executable<'a>(
    backends: &'a HashMap<ExecutableKey, SymbolicBackendExecutable>,
    executable: &ExecutableSymbol,
    world: &World,
) -> Option<&'a SymbolicBackendExecutable> {
    backends
        .values()
        .find(|backend| executable_symbol(&backend.key, world) == *executable)
}

fn executable_symbol(executable: &ExecutableKey, world: &World) -> ExecutableSymbol {
    ExecutableSymbol {
        activation: ActivationSymbol {
            function: executable.activation.function,
            arrow: executable.activation.arrow,
            input: executable.activation.inputs(world.types()).into_boxed_slice(),
        },
        need: executable.need,
    }
}

fn symbolic_entry_capture_owner_callsite(
    backends: &HashMap<ExecutableKey, SymbolicBackendExecutable>,
    executable: &ExecutableSymbol,
    position: &TransportPosition,
    world: &World,
) -> Option<CallSiteId> {
    let backend = symbolic_backend_for_executable(backends, executable, world)?;
    let SymbolicBackendBody::Clauses { entries, .. } = &backend.body else {
        return None;
    };
    entries
        .iter()
        .filter(|entry| entry.capture_positions.iter().any(|candidate| candidate == position))
        .find_map(|entry| match &entry.origin {
            SymbolicBackendEntryOrigin::DeliveredResume {
                position:
                    TransportPosition::ResumePayload {
                        callsite: Some(callsite),
                        ..
                    },
                ..
            } => Some(*callsite),
            _ => None,
        })
}

fn symbolic_callsite_dest(backend: &SymbolicBackendExecutable, callsite: CallSiteId) -> Option<&ControlDestination> {
    let SymbolicBackendBody::Clauses { entries, .. } = &backend.body else {
        return None;
    };
    entries.iter().find_map(|entry| match &entry.tail {
        SymbolicBackendTail::DirectCall {
            callsite: candidate,
            dest,
            ..
        }
        | SymbolicBackendTail::ClosureCall {
            callsite: candidate,
            dest,
            ..
        } if *candidate == callsite => Some(dest),
        _ => None,
    })
}

fn lanes_for_codegen_seam_shape(world: &World, shape: ShapeId) -> Vec<(ShapeId, LaneId)> {
    match world.shape(shape) {
        ShapeDescr::Nothing => Vec::new(),
        ShapeDescr::Lane(lane) => vec![(shape, *lane)],
        ShapeDescr::Callable(callable) => world
            .callable(*callable)
            .capture_lanes
            .iter()
            .copied()
            .map(|lane| (shape, lane))
            .collect(),
        ShapeDescr::Tuple(items) => items
            .iter()
            .copied()
            .flat_map(|item| lanes_for_codegen_seam_shape(world, item))
            .collect(),
    }
}

fn raw_codegen_repr_for_lane(world: &World, lane: LaneId) -> Option<CodegenLaneRepr> {
    let ty = world.lane(lane).ty;
    if world.types().is_floating(&ty) {
        Some(CodegenLaneRepr::RawF64)
    } else if world.types().is_integer(&ty) {
        Some(CodegenLaneRepr::RawInt)
    } else if world.types().is_atom_type(&ty) {
        Some(CodegenLaneRepr::RawAtom)
    } else {
        None
    }
}

fn codegen_repr_for_lane(world: &World, lane: LaneId) -> CodegenLaneRepr {
    raw_codegen_repr_for_lane(world, lane).unwrap_or(CodegenLaneRepr::ValueRef)
}

fn block_param_codegen_repr_for_lane(world: &World, lane: LaneId) -> CodegenLaneRepr {
    match raw_codegen_repr_for_lane(world, lane) {
        Some(repr @ (CodegenLaneRepr::RawInt | CodegenLaneRepr::RawAtom)) => repr,
        Some(CodegenLaneRepr::RawF64 | CodegenLaneRepr::ValueRef) | None => CodegenLaneRepr::ValueRef,
    }
}

struct BackendLowerer<'a, 'tel, T: crate::telemetry::Telemetry> {
    world: &'a mut World,
    telemetry: &'tel T,
    root_id: RootId,
    value_shapes: HashMap<ValueId, ShapeId>,
}

impl<'a, 'tel, T: crate::telemetry::Telemetry> BackendLowerer<'a, 'tel, T> {
    fn new(world: &'a mut World, telemetry: &'tel T, root_id: RootId, value_shapes: HashMap<ValueId, ShapeId>) -> Self {
        Self {
            world,
            telemetry,
            root_id,
            value_shapes,
        }
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
                self.telemetry,
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

    fn lower_step(&mut self, step: &LoweredStep) -> Result<BackendStep, FatalError> {
        Ok(match step {
            LoweredStep::Const { value, literal } => BackendStep::Const {
                value: *value,
                literal: literal.clone(),
            },
            LoweredStep::Tuple { value, items } => self.construction_step_or_omitted(
                *value,
                BackendStep::Tuple {
                    value: *value,
                    items: items.clone(),
                },
            ),
            LoweredStep::List { value, items, tail } => self.construction_step_or_omitted(
                *value,
                BackendStep::List {
                    value: *value,
                    items: items.clone(),
                    tail: *tail,
                },
            ),
            LoweredStep::Map { value, entries } => self.construction_step_or_omitted(
                *value,
                BackendStep::Map {
                    value: *value,
                    entries: entries.iter().map(|(key, value)| (key.value, *value)).collect(),
                },
            ),
            LoweredStep::MapUpdate { value, base, entries } => self.construction_step_or_omitted(
                *value,
                BackendStep::MapUpdate {
                    value: *value,
                    base: *base,
                    entries: entries.iter().map(|(key, value)| (key.value, *value)).collect(),
                },
            ),
            LoweredStep::Struct { value, module, fields } => self.construction_step_or_omitted(
                *value,
                BackendStep::Struct {
                    value: *value,
                    module_name: self
                        .world
                        .module_name(*module)
                        .unwrap_or_else(|| panic!("struct module {} should have a name", module.as_u32()))
                        .to_string(),
                    fields: fields.clone(),
                },
            ),
            LoweredStep::Bitstring { value, fields } => self.construction_step_or_omitted(
                *value,
                BackendStep::Bitstring {
                    value: *value,
                    fields: fields.clone(),
                },
            ),
            LoweredStep::FunctionRef { value, function } => BackendStep::FunctionRef {
                value: *value,
                function: *function,
                construction: None,
            },
            LoweredStep::Lambda {
                value,
                function,
                captures,
            } => BackendStep::Lambda {
                value: *value,
                function: *function,
                captures: captures.clone(),
                construction: None,
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

    fn value_is_proven_runtime_absent(&self, value: ValueId) -> bool {
        self.value_shapes
            .get(&value)
            .is_some_and(|shape| matches!(self.world.shape(*shape), ShapeDescr::Nothing))
    }

    /// Every fresh-construction step (Tuple/List/Map/MapUpdate/Struct/
    /// Bitstring) must respect the absence proof: when transport proves the
    /// constructed value runtime-absent, its operands were never demanded and
    /// may be unbound at runtime, so the step lowers as `Omitted` instead of
    /// executing a read of never-materialized values (fz-9in: a dead binding
    /// whose construction call survives because it allocates).
    fn construction_step_or_omitted(&self, value: ValueId, step: BackendStep) -> BackendStep {
        if self.value_is_proven_runtime_absent(value) {
            BackendStep::Omitted { value }
        } else {
            step
        }
    }

    fn lower_call_args(
        &mut self,
        _executable: &super::super::artifact::EmissionReadyExecutable,
        _callsite: CallSiteId,
        _closure_callee: Option<super::super::body::ValueId>,
        args: &[CallArg],
    ) -> Result<Vec<BackendCallArg>, FatalError> {
        args.iter().map(|arg| Ok(BackendCallArg { value: arg.value })).collect()
    }
}

fn lower_entry_origin(
    executable: &super::super::artifact::EmissionReadyExecutable,
    entry_index: usize,
    entry: &LoweredEntry,
) -> SymbolicBackendEntryOrigin {
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
            return SymbolicBackendEntryOrigin::DeliveredResume { value, position };
        }
        if matches!(&entry.tail, LoweredTail::Halt { atom } if atom == UNREACHABLE_CONTROL_ATOM) {
            return SymbolicBackendEntryOrigin::Branch;
        }
        panic!("resume entry {entry_index} should have a settled transport position: {entry:?}");
    }
    if matches!(&entry.tail, LoweredTail::Halt { atom } if atom == UNREACHABLE_CONTROL_ATOM) {
        return SymbolicBackendEntryOrigin::Branch;
    }
    match entry.origin {
        ControlEntryOrigin::Clause => SymbolicBackendEntryOrigin::Clause,
        ControlEntryOrigin::Branch => SymbolicBackendEntryOrigin::Branch,
        ControlEntryOrigin::ReceiveOutcome => SymbolicBackendEntryOrigin::ReceiveOutcome,
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

fn collect_backend_atom_names(world: &mut World, executables: &[BackendExecutable]) -> Vec<String> {
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
    world: &mut World,
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

fn collect_entry_atoms(world: &mut World, entry: &BackendEntry, seen: &mut HashSet<String>, atoms: &mut Vec<String>) {
    collect_step_atoms(world, &entry.steps, seen, atoms);
    collect_tail_atoms(world, &entry.tail, seen, atoms);
}

fn collect_step_atoms(_world: &mut World, steps: &[BackendStep], seen: &mut HashSet<String>, atoms: &mut Vec<String>) {
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

fn collect_tail_atoms(world: &mut World, tail: &BackendTail, seen: &mut HashSet<String>, atoms: &mut Vec<String>) {
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

fn collect_literal_atoms(literal: &GroundValue, seen: &mut HashSet<String>, atoms: &mut Vec<String>) {
    if let GroundValue::Atom(name) = literal {
        push_atom(seen, atoms, name);
    }
}

fn collect_dispatch_atoms(
    world: &mut World,
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
    world: &mut World,
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

fn collect_region_atoms(world: &mut World, region: &Region<Ty>, seen: &mut HashSet<String>, atoms: &mut Vec<String>) {
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
    world: &mut World,
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
    world: &mut World,
    dispatch: &PatternGuardDispatch<Ty>,
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    collect_dispatch_atoms(world, &dispatch.plan, seen, atoms);
    for body in &dispatch.bodies {
        collect_guard_atoms(world, body, seen, atoms);
    }
}

fn collect_dispatch_const_atoms(value: &GroundValue, seen: &mut HashSet<String>, atoms: &mut Vec<String>) {
    if let GroundValue::Atom(name) = value {
        push_atom(seen, atoms, name);
    }
}

fn push_atom(seen: &mut HashSet<String>, atoms: &mut Vec<String>, name: &str) {
    if seen.insert(name.to_string()) {
        atoms.push(name.to_string());
    }
}

fn incomplete_backend_program(
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    message: impl Into<String>,
) -> FatalError {
    let message = message.into();
    let diagnostic = Diagnostic::error(
        codes::ARTIFACT_INCOMPLETE_SEMANTIC_PLAN,
        format!("compiler2 backend lowering for root {}: {}", root_id.as_u32(), message),
        Span::DUMMY,
    );
    emit_through(tel, std::slice::from_ref(&diagnostic));
    FatalError
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler2::FunctionId;
    use crate::compiler2::artifact::BackendValueLayout;
    use crate::compiler2::pull::TransportCarrier;
    use crate::compiler2::transport::{ActivationSymbol, ExecutableSymbol};

    #[test]
    fn resolve_return_flow_rejects_divergence_contradictions() {
        let mut world = World::new();
        let ty = world.types_mut().int();
        let shape = world.intern_shape(ShapeDescr::Nothing);
        let position = TransportPosition::ExecutableReturn {
            executable: ExecutableSymbol {
                activation: ActivationSymbol {
                    function: FunctionId::for_test(1),
                    arrow: ty,
                    input: Box::default(),
                },
                need: ExecutableNeed::Value,
            },
        };
        let layout = |diverges| BackendReturnLayout {
            layout: BackendValueLayout {
                structural: shape,
                carrier: TransportCarrier::Absent,
                tys: Box::default(),
                reprs: Box::default(),
            },
            diverges,
        };

        let returning = HashMap::from([(position.clone(), layout(false))]);
        assert!(
            resolve_return_flow(
                &CallReturnFlow::NoReturn {
                    local_source: Some(position.clone()),
                },
                &returning,
            )
            .is_err()
        );

        let divergent = HashMap::from([(position.clone(), layout(true))]);
        assert!(
            resolve_return_flow(
                &CallReturnFlow::Deliver {
                    source: position.clone(),
                    resume: position,
                    entry: ControlEntryId::from_u32(0),
                },
                &divergent,
            )
            .is_err()
        );
    }
}
