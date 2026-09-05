//! Compiler2 backend product packaging.
//!
//! This module packages product-keyed symbolic backend executables into the
//! backend-owned program consumed by the interpreter and native lowering.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch, PatternGuardExpr};
use crate::dispatch_matrix::{ComparisonValue, DispatchNode, ProjectionKind, Region, SubjectSource};
use crate::ground_value::GroundValue;
use crate::source::Span;

use super::super::artifact::{
    AbiReadyExecutable, AbiValueRepr, BackendBody, BackendCallArg, BackendCallableReturn, BackendClause,
    BackendConstructionCapture, BackendConstructionMemberAdapter, BackendConstructionWrapper, BackendEntry,
    BackendEntryCapture, BackendEntryOrigin, BackendExecutable, BackendProgram, BackendReturnFlow, BackendReturnLayout,
    BackendStep, BackendTail, CallEdge, CallReturnFlow, DirectCallEdge, DispatchCallArm, MaterializedTransportPlan,
    RootBackendProductAnswer,
};
use super::super::body::{
    CallArg, CallSiteId, ControlDestination, ControlEntryId, ControlEntryOrigin, LoweredBody, LoweredEntry,
    LoweredStep, LoweredTail, ValueId,
};
use super::super::drive::{FactKey, Job};
use super::super::facts::FactUse;
use super::super::identity::RootId;
use super::super::identity::{ActivationKey, ExecutableKey};
use super::super::pull::{
    ProductKey, ProductReadContext, ProductValue, PullOutcome, PullWait, TransportCarrier, TransportLayout,
};
use super::super::scheduler::FatalError;
use super::super::semantic::SemanticOrd;
use super::super::transport::{
    ActivationSymbol, BoundaryFacts, BoundaryId, CallableFacts, CallableId, CodegenLaneRepr, CodegenSeam,
    CodegenSeamFact, ExecutableSymbol, LaneId, PhysicalLane, PhysicalLaneSource, ShapeDescr, ShapeId,
    TransportPosition,
};
use super::super::types::Ty;
use super::super::world::World;
use super::artifact::compare_codegen_seam_facts;

const UNREACHABLE_CONTROL_ATOM: &str = "compiler2_unreachable_control";

/// Reports `RootBackendProduct` pull-drive failures as `FatalError`,
/// emitting the diagnostic the fatal-error contract requires. The
/// `job_failed` hook forwards the job's own `FatalError` unchanged — a job
/// that fails through `jobs::run` has already emitted its own diagnostic, so
/// this boundary must not emit a second one for the same failure.
impl super::super::product_drive::ProductDriveError for FatalError {
    fn dependency_failed<T: crate::telemetry::Telemetry>(
        _world: &World,
        _tel: &T,
        _address: super::super::drive::ProductAddress,
        source: FatalError,
    ) -> Self {
        source
    }
    fn product_failed<T: crate::telemetry::Telemetry>(
        _world: &World,
        tel: &T,
        root: RootId,
        product: &ProductKey,
        _failure: super::super::pull::ProductFailure,
    ) -> Self {
        emit_backend_product_error(
            tel,
            Span::DUMMY,
            format!("compiler2 product {product:?} for root {} failed", root.as_u32()),
        )
    }

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
        FactKey::InputDemand(root_entry.function),
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
        let Some(value) = context.read_product(tel, ProductKey::BackendExecutable(current.clone()), world.types())
        else {
            waits.push(PullWait::Product(ProductKey::BackendExecutable(current)));
            continue;
        };
        let ProductValue::BackendExecutable(backend) = value else {
            panic!("backend executable product produced unexpected value {value:?}");
        };
        let backend = Rc::clone(backend);
        for edge in backend.abi.call_edges.values() {
            for callee in symbolic_call_edge_callees(&edge.target) {
                stack.push(callee.clone());
            }
        }
        for positioned in backend.abi.callable_owners.iter() {
            let owner = &positioned.owner;
            stack.extend(callable_fact_executables(root, &owner.callable_facts));
            stack.extend(boundary_resolution_executables(root, &owner.boundary_facts));
        }
        backends.insert(current, backend);
    }
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }
    let struct_modules = backends
        .values()
        .flat_map(|backend| backend.abi.materialized.struct_modules.iter().copied())
        .collect::<BTreeSet<_>>();
    let mut struct_schemas = BTreeMap::new();
    for module in struct_modules {
        let fact = FactKey::StructDefined(module);
        if !context.read_fact(world, FactUse::settled(fact.clone())) {
            waits.push(PullWait::Fact(FactUse::settled(fact)));
            continue;
        }
        let name = world
            .module_name(module)
            .expect("a reachable struct module must have a name")
            .to_string();
        let fields = world
            .struct_def_fields(module)
            .expect("a settled reachable struct fact must have a schema")
            .to_vec();
        struct_schemas.insert(name, fields);
    }
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }
    let owners = backends.values().flat_map(|backend| {
        backend
            .abi
            .callable_owners
            .iter()
            .map(|positioned| positioned.owner.as_ref())
    });
    let (produced_callables, produced_boundaries) = aggregate_callable_owners(owners);
    let transport =
        symbolic_materialized_transport_plan(&backends, &entry, world, &produced_callables, &produced_boundaries);

    let mut executable_keys = reachable.into_iter().collect::<Vec<_>>();
    executable_keys.sort_by(|left, right| left.semantic_cmp(right, world.types()));
    let executables = executable_keys
        .iter()
        .map(|key| Rc::clone(&backends[key]))
        .collect::<Vec<_>>();
    let mut construction_wrappers = executables
        .iter()
        .flat_map(|backend| backend.construction_wrappers.iter().cloned())
        .collect::<Vec<_>>();
    construction_wrappers.sort_by(|left, right| left.identity.semantic_cmp(&right.identity, world.types()));
    construction_wrappers.dedup_by(|left, right| {
        if left.identity != right.identity {
            return false;
        }
        assert_eq!(left, right, "one construction position has one complete wrapper");
        true
    });
    let program = Rc::new(BackendProgram::new(
        entry,
        collect_backend_atom_names(world, &executables),
        struct_schemas,
        executables,
        construction_wrappers,
    ));
    verify_boxed_apply_seam_return_convention(tel, root, &program)
        .expect("root backend product should compile one return convention across the boxed apply seam");
    PullOutcome::Produced(ProductValue::RootBackendProduct(RootBackendProductAnswer {
        program,
        transport: Rc::new(transport),
    }))
}

pub(crate) fn produce_root_backend_content(
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    root: RootId,
    types: &super::super::types::Types,
) -> PullOutcome {
    let key = ProductKey::RootBackendProduct(root);
    match context.read_product(tel, key.clone(), types) {
        Some(ProductValue::RootBackendProduct(answer)) => {
            PullOutcome::Produced(ProductValue::RootBackendContent(Rc::clone(&answer.program)))
        }
        Some(value) => panic!("root backend product produced unexpected value {value:?}"),
        None => PullOutcome::wait_on_product(key),
    }
}

pub(crate) fn aggregate_callable_owners<'a>(
    owners: impl IntoIterator<Item = &'a super::super::transport::CallableConstructionOwner>,
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
    let Some(value) = context.read_product(tel, ProductKey::AbiExecutable(executable.clone()), world.types()) else {
        return PullOutcome::Waiting(vec![PullWait::Product(ProductKey::AbiExecutable(executable.clone()))]);
    };
    let ProductValue::AbiExecutable(abi) = value else {
        panic!("ABI executable product produced unexpected value {value:?}");
    };
    let abi = Rc::clone(abi);
    let root = context.session().root();
    let mut dependencies = HashSet::new();
    for edge in abi.call_edges.values() {
        let flows = match &edge.target {
            CallEdge::Direct(edge) => vec![&edge.return_flow],
            CallEdge::Dispatch(dispatch) => dispatch.arms.iter().map(|arm| &arm.return_flow).collect(),
            CallEdge::Indirect(flow) => vec![flow],
        };
        for flow in flows {
            let source = match flow {
                CallReturnFlow::NoReturn { local_source } => local_source.as_ref(),
                CallReturnFlow::Tail { source, .. }
                | CallReturnFlow::Continue { source, .. }
                | CallReturnFlow::Deliver { source, .. } => Some(source),
            };
            if let Some(source) = source {
                dependencies.insert(executable_key_for_symbol(root, source.executable()));
            }
        }
    }
    for construction in abi
        .callable_owners
        .iter()
        .filter_map(|owner| owner.owner.construction.as_ref())
    {
        dependencies.extend(
            construction
                .members
                .iter()
                .map(|member| executable_key_for_symbol(root, &member.resolution)),
        );
        dependencies.extend(
            construction
                .captures
                .iter()
                .map(|capture| executable_key_for_symbol(root, capture.source.executable())),
        );
    }
    dependencies.remove(executable);
    let mut dependencies = dependencies.into_iter().collect::<Vec<_>>();
    dependencies.sort_by(|left, right| left.semantic_cmp(right, world.types()));
    let mut abis = HashMap::from([(executable.clone(), Rc::clone(&abi))]);
    let mut waits = Vec::new();
    for dependency in dependencies {
        let key = ProductKey::AbiExecutable(dependency.clone());
        match context.read_product(tel, key.clone(), world.types()) {
            Some(ProductValue::AbiExecutable(answer)) => {
                abis.insert(dependency, Rc::clone(answer));
            }
            Some(answer) => panic!("ABI prerequisite produced unexpected value {answer:?}"),
            None => waits.push(PullWait::Product(key)),
        }
    }
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }
    let return_endpoints = abis
        .values()
        .flat_map(|abi| abi.return_endpoints.iter().cloned())
        .collect();
    let construction_wrappers = package_backend_construction_wrappers(world, tel, root, &abis, &abi)
        .expect("local construction prerequisites must provide complete wrappers");
    let constructions = construction_wrappers
        .iter()
        .filter_map(|wrapper| {
            let TransportPosition::Value { value, .. } = &wrapper.identity else {
                return None;
            };
            Some((*value, wrapper.identity.clone()))
        })
        .collect();
    let value_shapes = executable_value_shapes(&abi);
    let mut lowerer = BackendLowerer::new(world, tel, root, value_shapes, return_endpoints, constructions);
    let lowered = lower_backend_body(&mut lowerer, &abi)
        .expect("symbolic backend lowering should be complete after ABI product exists");
    let backend = BackendExecutable {
        key: executable.clone(),
        abi,
        body: lowered,
        construction_wrappers,
    };
    let backend = Rc::new(backend);
    PullOutcome::Produced(ProductValue::BackendExecutable(backend))
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

fn callable_fact_executables(root: RootId, callables: &HashMap<CallableId, CallableFacts>) -> Vec<ExecutableKey> {
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

fn backend_call_edge(
    target: &CallEdge<ExecutableKey>,
    endpoints: &HashMap<TransportPosition, BackendReturnLayout>,
) -> Result<CallEdge<ExecutableKey, BackendReturnFlow>, FatalError> {
    Ok(match target {
        CallEdge::Direct(direct) => CallEdge::Direct(DirectCallEdge {
            callee: direct.callee.clone(),
            return_flow: resolve_return_flow(&direct.return_flow, endpoints)?,
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
                        callee: arm.callee.clone(),
                        return_flow: resolve_return_flow(&arm.return_flow, endpoints)?,
                        extern_marshals: arm.extern_marshals.clone(),
                    })
                })
                .collect::<Result<Vec<_>, FatalError>>()?,
            miss: dispatch.miss,
        })),
        CallEdge::Indirect(flow) => CallEdge::Indirect(resolve_return_flow(flow, endpoints)?),
    })
}

fn backend_entry_captures(
    world: &World,
    abi: &AbiReadyExecutable,
    values: &[ValueId],
    positions: &[TransportPosition],
) -> Result<Vec<BackendEntryCapture>, FatalError> {
    if values.len() != positions.len() {
        return Err(FatalError);
    }
    values
        .iter()
        .zip(positions)
        .map(|(value, position)| {
            let layout = abi.transport.layout_at(position).ok_or(FatalError)?;
            let TransportPosition::EntryCapture {
                entry, capture_index, ..
            } = position
            else {
                return Err(FatalError);
            };
            let ignored = abi
                .materialized
                .runtime_demand
                .entry_capture_demands
                .get(entry)
                .and_then(|demands| demands.get(*capture_index))
                .is_some_and(|demand| demand.is_ignore());
            let contract = world
                .layout_physical_lanes(layout)
                .into_iter()
                .filter(|physical| !ignored || physical.source == PhysicalLaneSource::Carrier)
                .map(|physical| {
                    let repr = match block_param_codegen_repr_for_physical_lane(world, physical) {
                        CodegenLaneRepr::ValueRef => AbiValueRepr::ValueRef,
                        CodegenLaneRepr::RawInt => AbiValueRepr::RawInt,
                        CodegenLaneRepr::RawF64 => AbiValueRepr::RawF64,
                        CodegenLaneRepr::RawAtom => AbiValueRepr::RawAtom,
                    };
                    (world.lane(physical.lane).ty, repr)
                })
                .collect::<Vec<_>>();
            Ok(BackendEntryCapture {
                value: *value,
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
    abis: &HashMap<ExecutableKey, Rc<AbiReadyExecutable>>,
    abi: &AbiReadyExecutable,
) -> Result<Box<[Rc<BackendConstructionWrapper>]>, FatalError> {
    let mut constructions = abi
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
    constructions.sort_by(|(left, _), (right, _)| left.position.semantic_cmp(&right.position, world.types()));
    constructions
        .into_iter()
        .map(|(positioned, construction)| {
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
                    .any(|member| world.boundary(member.boundary).surface_arg_layouts.len() != call_arity)
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
                    let target = executable_key_for_symbol(root, &member.resolution);
                    let target_abi = abis.get(&target).ok_or(FatalError)?;
                    Ok(BackendConstructionMemberAdapter {
                        boundary: member.boundary,
                        surface_inputs: member.surface_inputs.clone(),
                        surface_arg_shapes: member.surface_arg_shapes.clone(),
                        target,
                        capture_semantic_inputs: member.capture_semantic_inputs.clone(),
                        surface_semantic_inputs: member.surface_semantic_inputs.clone(),
                        target_inputs: target_abi.semantic_inputs.clone(),
                        target_return: target_abi.return_layout.clone(),
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
                    let layout = abis
                        .get(&executable_key_for_symbol(root, executable))
                        .and_then(|abi| abi.value_layouts.get(value))
                        .cloned()
                        .ok_or(FatalError)?;
                    if layout.structural != capture.layout.structural || layout.carrier != capture.layout.carrier {
                        return Err(FatalError);
                    }
                    Ok(BackendConstructionCapture { layout })
                })
                .collect::<Result<Box<_>, FatalError>>()?;
            Ok(Rc::new(BackendConstructionWrapper {
                identity: positioned.position.clone(),
                callable: construction.callable,
                captures,
                call_arity,
                return_form,
                members: members.into_boxed_slice(),
                selection: construction.selection.clone(),
            }))
        })
        .collect()
}

fn lower_backend_body(
    lowerer: &mut BackendLowerer<'_, '_, impl crate::telemetry::Telemetry>,
    abi: &AbiReadyExecutable,
) -> Result<BackendBody, FatalError> {
    match &abi.materialized.body {
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
                .map(|clause| {
                    Ok(BackendClause {
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
                .map(|(index, entry)| lower_backend_entry(lowerer, abi, index, entry))
                .collect::<Result<Vec<_>, _>>()?,
            generated: generated.clone(),
        }),
    }
}

fn lower_backend_entry(
    lowerer: &mut BackendLowerer<'_, '_, impl crate::telemetry::Telemetry>,
    abi: &AbiReadyExecutable,
    entry_index: usize,
    entry: &LoweredEntry,
) -> Result<BackendEntry, FatalError> {
    let entry_id = original_entry_id(abi, entry_index);
    let capture_positions = lowerer.capture_positions_for_entry(abi, entry_id, entry)?;
    Ok(BackendEntry {
        span: entry.span,
        origin: lower_entry_origin(abi, entry_index, entry),
        params: entry.params.clone(),
        captures: backend_entry_captures(lowerer.world, abi, &entry.captures, &capture_positions)?,
        reusable_cons_captures: entry.reusable_cons_captures.clone(),
        steps: entry
            .steps
            .iter()
            .map(|step| lowerer.lower_step(step))
            .collect::<Result<Vec<_>, _>>()?,
        tail: lower_backend_tail(lowerer, abi, &entry.tail).unwrap_or_else(|_| {
            panic!(
                "symbolic backend entry {entry_index} tail is incomplete: {:?}",
                entry.tail
            )
        }),
    })
}

fn lower_backend_tail(
    lowerer: &mut BackendLowerer<'_, '_, impl crate::telemetry::Telemetry>,
    abi: &AbiReadyExecutable,
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
            let edge = abi.call_edges.get(callsite).ok_or_else(|| {
                incomplete_backend_program(
                    lowerer.telemetry,
                    lowerer.root_id,
                    format!("missing symbolic direct-call edge for callsite {}", callsite.as_u32()),
                )
            })?;
            BackendTail::DirectCall {
                value: *value,
                callsite: *callsite,
                target: backend_call_edge(&edge.target, &lowerer.return_endpoints)?,
                args: lowerer.lower_call_args(abi, *callsite, None, args)?,
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
            BackendTail::ClosureCall {
                value: *value,
                callsite: *callsite,
                callee: *callee,
                target: edge
                    .and_then(|edge| symbolic_direct_call_edge(&edge.target))
                    .and_then(|edge| edge.callee.local().cloned()),
                args: lowerer.lower_call_args(abi, *callsite, Some(*callee), args)?,
                dest: dest.clone(),
                return_flow: edge
                    .and_then(|edge| symbolic_call_edge_return_flow(&edge.target))
                    .map(|flow| resolve_return_flow(flow, &lowerer.return_endpoints))
                    .transpose()?,
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

pub(crate) fn symbolic_materialized_transport_plan(
    backends: &HashMap<ExecutableKey, Rc<BackendExecutable>>,
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
    // Structural comparison, not `format!("{position:?}")`: these are
    // final-packaging sorts over the GLOBAL position set, and Debug-string
    // keys recomputed per comparison were ~21% of the release compile. Compared
    // in place rather than through a materialized key, so a comparison stops at
    // the first difference and the input-type vector is never cloned.
    position_layouts.sort_by(|(left, _), (right, _)| left.semantic_cmp(right, world.types()));
    position_layouts.dedup_by(|left, right| {
        if left.0 != right.0 {
            return false;
        }
        assert_eq!(left.1, right.1, "one transport position must have one settled layout");
        true
    });
    let codegen_seam_facts = symbolic_codegen_seam_facts(backends, &position_layouts, world, boundaries);
    let mut callable_owners = backends
        .values()
        .flat_map(|backend| backend.abi.callable_owners.iter().cloned())
        .collect::<Vec<_>>();
    callable_owners.sort_by(|left, right| left.position.semantic_cmp(&right.position, world.types()));
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
        codegen_seam_facts,
        callable_owners: callable_owners.into_boxed_slice(),
        callable_facts: callables.clone(),
        boundary_facts: boundaries.clone(),
    }
}

fn symbolic_codegen_seam_facts(
    backends: &HashMap<ExecutableKey, Rc<BackendExecutable>>,
    position_layouts: &[(TransportPosition, TransportLayout)],
    world: &World,
    boundaries: &HashMap<BoundaryId, BoundaryFacts>,
) -> Box<[CodegenSeamFact]> {
    let mut out = Vec::new();
    for (position, layout) in position_layouts {
        let ignore_structural = symbolic_position_structural_lanes_are_ignored(backends, position, world);
        for physical in world.layout_physical_lanes(*layout) {
            if ignore_structural && physical.source == PhysicalLaneSource::Structural {
                continue;
            }
            let leaf_shape = physical.structural;
            let lane = physical.lane;
            match position {
                TransportPosition::ExecutableInput {
                    executable,
                    semantic_index,
                } => {
                    let repr = codegen_repr_for_physical_lane(world, physical);
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
                        .is_some_and(|backend| matches!(backend.body, BackendBody::Extern { .. }))
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
                    let repr = codegen_repr_for_physical_lane(world, physical);
                    out.push(CodegenSeamFact {
                        seam: CodegenSeam::ReturnDelivery {
                            executable: executable.clone(),
                        },
                        shape: Some(leaf_shape),
                        lane,
                        repr,
                    });
                    if symbolic_backend_for_executable(backends, executable, world)
                        .is_some_and(|backend| matches!(backend.body, BackendBody::Extern { .. }))
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
                    let repr = block_param_codegen_repr_for_physical_lane(world, physical);
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
                        repr: codegen_repr_for_physical_lane(world, physical),
                    });
                }
                TransportPosition::EntryCapture {
                    executable,
                    entry,
                    capture_index,
                } => {
                    let repr = block_param_codegen_repr_for_physical_lane(world, physical);
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
                            repr: codegen_repr_for_physical_lane(world, physical),
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
    // Same comparator the session's codegen-seam-fact product uses
    // (`jobs/artifact.rs`), so the plan's facts and the session product share
    // one canonical order.
    out.sort_by(|left, right| compare_codegen_seam_facts(left, right, world.types()));
    out.into_boxed_slice()
}

fn symbolic_position_structural_lanes_are_ignored(
    backends: &HashMap<ExecutableKey, Rc<BackendExecutable>>,
    position: &TransportPosition,
    world: &World,
) -> bool {
    match position {
        TransportPosition::ExecutableInput {
            executable,
            semantic_index,
        } => symbolic_backend_for_executable(backends, executable, world)
            .and_then(|backend| {
                backend
                    .abi
                    .materialized
                    .runtime_demand
                    .input_demands
                    .get(*semantic_index)
            })
            .is_some_and(|demand| demand.is_ignore()),
        TransportPosition::EntryCapture {
            executable,
            entry,
            capture_index,
        } => symbolic_backend_for_executable(backends, executable, world)
            .and_then(|backend| backend.abi.materialized.runtime_demand.entry_capture_demands.get(entry))
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
    backends: &HashMap<ExecutableKey, Rc<BackendExecutable>>,
    world: &World,
    boundary: BoundaryId,
    facts: &BoundaryFacts,
    out: &mut Vec<CodegenSeamFact>,
) {
    let descr = world.boundary(boundary);
    let capture_layouts = &world.callable(descr.callable).capture_layouts;
    for (slot, physical) in capture_layouts
        .iter()
        .chain(descr.surface_arg_layouts.iter())
        .copied()
        .flat_map(|layout| world.layout_physical_lanes(layout))
        .enumerate()
    {
        out.push(CodegenSeamFact {
            seam: CodegenSeam::CallableBoundary { boundary, slot },
            shape: Some(physical.structural),
            lane: physical.lane,
            repr: codegen_repr_for_physical_lane(world, physical),
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
    backends: &HashMap<ExecutableKey, Rc<BackendExecutable>>,
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
    backends: &'a HashMap<ExecutableKey, Rc<BackendExecutable>>,
    executable: &ExecutableSymbol,
    world: &World,
) -> Option<&'a BackendExecutable> {
    backends
        .values()
        .find(|backend| executable_symbol(&backend.key, world) == *executable)
        .map(Rc::as_ref)
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
    backends: &HashMap<ExecutableKey, Rc<BackendExecutable>>,
    executable: &ExecutableSymbol,
    position: &TransportPosition,
    world: &World,
) -> Option<CallSiteId> {
    let backend = symbolic_backend_for_executable(backends, executable, world)?;
    let TransportPosition::EntryCapture { entry, .. } = position else {
        return None;
    };
    backend
        .abi
        .transport
        .resume_positions
        .iter()
        .find_map(|position| match position {
            TransportPosition::ResumePayload {
                entry: resumed,
                callsite,
                ..
            } if resumed == entry => *callsite,
            _ => None,
        })
}

fn symbolic_callsite_dest(backend: &BackendExecutable, callsite: CallSiteId) -> Option<&ControlDestination> {
    let BackendBody::Clauses { entries, .. } = &backend.body else {
        return None;
    };
    entries.iter().find_map(|entry| match &entry.tail {
        BackendTail::DirectCall {
            callsite: candidate,
            dest,
            ..
        }
        | BackendTail::ClosureCall {
            callsite: candidate,
            dest,
            ..
        } if *candidate == callsite => Some(dest),
        _ => None,
    })
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

fn codegen_repr_for_physical_lane(world: &World, physical: PhysicalLane) -> CodegenLaneRepr {
    match physical.source {
        PhysicalLaneSource::Structural => codegen_repr_for_lane(world, physical.lane),
        PhysicalLaneSource::Carrier => CodegenLaneRepr::ValueRef,
    }
}

fn block_param_codegen_repr_for_lane(world: &World, lane: LaneId) -> CodegenLaneRepr {
    match raw_codegen_repr_for_lane(world, lane) {
        Some(repr @ (CodegenLaneRepr::RawInt | CodegenLaneRepr::RawAtom)) => repr,
        Some(CodegenLaneRepr::RawF64 | CodegenLaneRepr::ValueRef) | None => CodegenLaneRepr::ValueRef,
    }
}

fn block_param_codegen_repr_for_physical_lane(world: &World, physical: PhysicalLane) -> CodegenLaneRepr {
    match physical.source {
        PhysicalLaneSource::Structural => block_param_codegen_repr_for_lane(world, physical.lane),
        PhysicalLaneSource::Carrier => CodegenLaneRepr::ValueRef,
    }
}

struct BackendLowerer<'a, 'tel, T: crate::telemetry::Telemetry> {
    world: &'a mut World,
    telemetry: &'tel T,
    root_id: RootId,
    value_shapes: HashMap<ValueId, ShapeId>,
    return_endpoints: HashMap<TransportPosition, BackendReturnLayout>,
    constructions: HashMap<ValueId, TransportPosition>,
}

impl<'a, 'tel, T: crate::telemetry::Telemetry> BackendLowerer<'a, 'tel, T> {
    fn new(
        world: &'a mut World,
        telemetry: &'tel T,
        root_id: RootId,
        value_shapes: HashMap<ValueId, ShapeId>,
        return_endpoints: HashMap<TransportPosition, BackendReturnLayout>,
        constructions: HashMap<ValueId, TransportPosition>,
    ) -> Self {
        Self {
            world,
            telemetry,
            root_id,
            value_shapes,
            return_endpoints,
            constructions,
        }
    }

    fn capture_positions_for_entry(
        &mut self,
        executable: &AbiReadyExecutable,
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
            LoweredStep::FunctionRef { value, function } => self.construction_step_or_omitted(
                *value,
                BackendStep::FunctionRef {
                    value: *value,
                    function: *function,
                    construction: self.constructions.get(value).cloned(),
                },
            ),
            LoweredStep::Lambda {
                value,
                function,
                captures,
            } => self.construction_step_or_omitted(
                *value,
                BackendStep::Lambda {
                    value: *value,
                    function: *function,
                    captures: captures.clone(),
                    construction: self.constructions.get(value).cloned(),
                },
            ),
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
    /// Bitstring/FunctionRef/Lambda) must respect the absence proof: when
    /// transport proves the constructed value runtime-absent, its operands were
    /// never demanded and may be unbound at runtime, so the step lowers as
    /// `Omitted` instead of executing a read of never-materialized values
    /// (fz-9in: a dead binding whose construction call survives because it
    /// allocates; fz-kdt.111: a predicate closure a shared `Enum` body proves
    /// it never invokes, whose ignored capture the eager interp still read).
    fn construction_step_or_omitted(&self, value: ValueId, step: BackendStep) -> BackendStep {
        if self.value_is_proven_runtime_absent(value) {
            BackendStep::Omitted { value }
        } else {
            step
        }
    }

    fn lower_call_args(
        &mut self,
        _executable: &AbiReadyExecutable,
        _callsite: CallSiteId,
        _closure_callee: Option<super::super::body::ValueId>,
        args: &[CallArg],
    ) -> Result<Vec<BackendCallArg>, FatalError> {
        args.iter().map(|arg| Ok(BackendCallArg { value: arg.value })).collect()
    }
}

fn lower_entry_origin(executable: &AbiReadyExecutable, entry_index: usize, entry: &LoweredEntry) -> BackendEntryOrigin {
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
            let layout = executable
                .return_endpoints
                .iter()
                .find_map(|(candidate, layout)| (candidate == &position).then(|| layout.clone()))
                .expect("resume ABI owns its return endpoint");
            return BackendEntryOrigin::DeliveredResume { value, layout };
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

fn original_entry_id(executable: &AbiReadyExecutable, entry_index: usize) -> ControlEntryId {
    executable
        .materialized
        .original_entry_ids
        .get(entry_index)
        .copied()
        .unwrap_or_else(|| ControlEntryId::from_u32(entry_index as u32))
}

fn collect_backend_atom_names(world: &mut World, executables: &[Rc<BackendExecutable>]) -> Vec<String> {
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
            if let Some(dispatch) = &executable.abi.materialized.entry_dispatch {
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

/// How many lanes a construction wrapper hands its caller back.
fn callable_return_lanes(form: BackendCallableReturn) -> usize {
    match form {
        BackendCallableReturn::Diverges | BackendCallableReturn::Absent => 0,
        BackendCallableReturn::ValueRef => 1,
    }
}

/// fz-kdt.155 — the two halves of the boxed apply seam are one calling
/// convention, and this is the only place both halves are in the same room.
///
/// A wrapper's public return form is derived from its MEMBERS' return layouts;
/// a boxed callsite's delivered payload is derived from the CALLSITE's own
/// demand. Nothing structural forces the two to agree, and when they disagreed
/// the wrapper wrote its returned value into the register the continuation
/// reads as its own closure pointer — a corrupt closure handed to
/// `fz_closure_get_capture_atom`, which the program discovers as a
/// non-unwinding abort at the FIRST call, on every door. The demand rules that
/// keep them equal (an exact first-class target contribution retaining each
/// wrapper member's required return, and `widen_boxed_closure_call_results`
/// giving a boxed callsite the seam's one lane) span several facts, so the
/// agreement gets a named invariant here rather than an abort out there.
///
/// A closure callsite reaches a wrapper exactly when its callee VALUE travels
/// in the boxed `ValueRef` carrier — the same condition
/// `materialize_closure_call_edge` uses to choose the seam over a direct edge
/// to a named target. An exact-carrier callee is excluded because it needs no
/// agreement: its result aliases the target executable's own return fact, so
/// caller and callee read one shape by construction. Among the wrappers, the
/// ones a boxed callsite could reach are those taking the same number of call
/// arguments; a wrapper whose every member diverges publishes no lanes because
/// it never returns at all, and is not a party to the convention.
fn verify_boxed_apply_seam_return_convention(
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    program: &BackendProgram,
) -> Result<(), FatalError> {
    let mut published: HashMap<usize, Vec<&BackendConstructionWrapper>> = HashMap::new();
    for wrapper in program.construction_wrappers() {
        if matches!(wrapper.return_form, BackendCallableReturn::Diverges) {
            continue;
        }
        published.entry(wrapper.call_arity).or_default().push(wrapper);
    }
    for executable in program.executables() {
        let BackendBody::Clauses { entries, .. } = &executable.body else {
            continue;
        };
        for entry in entries {
            let BackendTail::ClosureCall {
                callee,
                args,
                return_flow,
                ..
            } = &entry.tail
            else {
                continue;
            };
            if !executable
                .abi
                .value_layouts
                .get(callee)
                .is_some_and(|layout| matches!(layout.carrier, TransportCarrier::ValueRef(_)))
            {
                continue;
            }
            let delivered = match return_flow {
                Some(BackendReturnFlow::Deliver { source, .. } | BackendReturnFlow::Continue { source }) => {
                    source.layout.reprs.len()
                }
                Some(BackendReturnFlow::Tail) | Some(BackendReturnFlow::NoReturn) | None => continue,
            };
            for wrapper in published.get(&args.len()).into_iter().flatten() {
                let published_lanes = callable_return_lanes(wrapper.return_form);
                if published_lanes != delivered {
                    return Err(incomplete_backend_program(
                        tel,
                        root_id,
                        format!(
                            "boxed closure call in {:?} expects {delivered} delivered lane(s) but construction \
                             wrapper {:?} it can reach publishes {published_lanes} ({:?}): the two halves of one \
                             calling convention were compiled against different contracts",
                            executable.key.activation.function, wrapper.identity, wrapper.return_form,
                        ),
                    ));
                }
            }
        }
    }
    Ok(())
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
    use crate::compiler2::identity::ExecutableNeed;
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

    #[test]
    fn root_carrier_seam_forces_value_ref_for_a_raw_capable_lane() {
        let mut world = World::new();
        let int = world.types_mut().int();
        let lane = world.intern_lane(crate::compiler2::transport::LaneDescr {
            ty: int,
            class: crate::compiler2::transport::TransportClass::Value,
        });
        let shape = world.intern_shape(ShapeDescr::Lane(lane));
        let executable = ExecutableSymbol {
            activation: ActivationSymbol {
                function: FunctionId::for_test(1),
                arrow: int,
                input: Box::default(),
            },
            need: ExecutableNeed::Value,
        };
        let position = TransportPosition::ExecutableReturn { executable };
        let structural = symbolic_codegen_seam_facts(
            &HashMap::new(),
            &[(position.clone(), TransportLayout::structural(shape))],
            &world,
            &HashMap::new(),
        );
        let carrier = symbolic_codegen_seam_facts(
            &HashMap::new(),
            &[(
                position,
                TransportLayout {
                    structural: shape,
                    carrier: TransportCarrier::ValueRef(lane),
                },
            )],
            &world,
            &HashMap::new(),
        );

        assert_eq!(structural[0].repr, CodegenLaneRepr::RawInt);
        assert_eq!(carrier[0].repr, CodegenLaneRepr::ValueRef);
        assert_eq!(structural[0].lane, carrier[0].lane);
    }

    #[test]
    fn callable_boundary_seams_preserve_capture_and_argument_carrier_provenance() {
        let mut world = World::new();
        let float = world.types_mut().float();
        let lane = world.intern_lane(crate::compiler2::transport::LaneDescr {
            ty: float,
            class: crate::compiler2::transport::TransportClass::Value,
        });
        let shape = world.intern_shape(ShapeDescr::Lane(lane));
        let callable = world.intern_callable(crate::compiler2::transport::CallableDescr {
            function: Some(FunctionId::for_test(1)),
            arity: 0,
            capture_tys: vec![float].into_boxed_slice(),
            capture_layouts: vec![TransportLayout {
                structural: shape,
                carrier: TransportCarrier::ValueRef(lane),
            }]
            .into_boxed_slice(),
        });
        let boundary = world.intern_boundary(crate::compiler2::transport::BoundaryDescr {
            callable,
            surface_arg_layouts: vec![
                TransportLayout::structural(shape),
                TransportLayout {
                    structural: shape,
                    carrier: TransportCarrier::ValueRef(lane),
                },
            ]
            .into_boxed_slice(),
            published_value_lane: lane,
        });
        let boundaries = HashMap::from([(
            boundary,
            BoundaryFacts {
                publications: Box::default(),
                resolutions: Box::default(),
            },
        )]);

        let seams = symbolic_codegen_seam_facts(&HashMap::new(), &[], &world, &boundaries);
        let boundary_seams = seams
            .iter()
            .filter(
                |fact| matches!(fact.seam, CodegenSeam::CallableBoundary { boundary: found, .. } if found == boundary),
            )
            .collect::<Vec<_>>();

        assert_eq!(
            boundary_seams.len(),
            3,
            "duplicate physical lane occurrences remain positional"
        );
        assert!(
            boundary_seams
                .iter()
                .all(|fact| fact.lane == lane && fact.shape == Some(shape))
        );
        assert_eq!(
            boundary_seams
                .iter()
                .map(|fact| match fact.seam {
                    CodegenSeam::CallableBoundary { slot, .. } => slot,
                    _ => unreachable!(),
                })
                .collect::<Vec<_>>(),
            vec![0, 1, 2],
            "repeated lane identities remain distinct physical occurrences",
        );
        assert_eq!(
            boundary_seams
                .iter()
                .filter(|fact| fact.repr == CodegenLaneRepr::ValueRef)
                .count(),
            2,
            "the capture and carrier-bearing argument must remain ValueRef",
        );
        assert_eq!(
            boundary_seams
                .iter()
                .filter(|fact| fact.repr == CodegenLaneRepr::RawF64)
                .count(),
            1,
            "the structural argument of the same Ty remains raw",
        );
    }

    /// FIX-1 of the fz-kdt.155 re-refutation: the seam tripwire's REFUSING
    /// half must have a witness -- neutering `verify_boxed_apply_seam_return_
    /// convention` shipped green through every gate (the fz-kdt.157 pattern).
    /// A hand-built program with one Absent wrapper and one boxed closure
    /// call delivering a lane is the mismatch `a_mixed` hits when the
    /// producer half is reverted; agreement (ValueRef wrapper) must pass.
    #[test]
    fn the_seam_tripwire_refuses_a_lane_mismatch_and_passes_agreement() {
        use crate::compiler2::artifact::{
            BackendBody, BackendCallArg, BackendCallableReturn, BackendConstructionWrapper, BackendEntry,
            BackendEntryOrigin, BackendProgram, BackendReturnFlow, BackendTail,
        };
        use crate::compiler2::body::ControlDestination;
        use crate::compiler2::transport::CallableId;
        use crate::compiler2::{CallSiteId, ControlEntryId, ValueId};
        use crate::telemetry::ConfiguredTelemetry;

        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let shape = world.intern_shape(ShapeDescr::Nothing);
        let value_layout = |carrier, reprs: Vec<AbiValueRepr>| BackendValueLayout {
            structural: shape,
            carrier,
            tys: Box::default(),
            reprs: reprs.into_boxed_slice(),
        };
        let callee = ValueId::from_u32(1);
        let program = |return_form| {
            let key = ExecutableKey {
                activation: ActivationKey {
                    root: RootId::for_test(0),
                    function: FunctionId::for_test(0),
                    arrow: int,
                },
                need: ExecutableNeed::Value,
            };
            let mut executable = BackendExecutable::for_test(key.clone(), int, shape);
            Rc::make_mut(&mut executable.abi).value_layouts.insert(
                callee,
                value_layout(
                    TransportCarrier::ValueRef(LaneId::for_test(0)),
                    vec![AbiValueRepr::ValueRef],
                ),
            );
            executable.body = BackendBody::Clauses {
                clauses: Vec::new(),
                generated: Vec::new(),
                entries: vec![BackendEntry {
                    span: Span::DUMMY,
                    origin: BackendEntryOrigin::Clause,
                    params: Vec::new(),
                    captures: Vec::new(),
                    reusable_cons_captures: Vec::new(),
                    steps: Vec::new(),
                    tail: BackendTail::ClosureCall {
                        value: ValueId::from_u32(2),
                        callsite: CallSiteId::from_u32(0),
                        callee,
                        target: None,
                        args: vec![BackendCallArg {
                            value: ValueId::from_u32(3),
                        }],
                        dest: ControlDestination::Return,
                        return_flow: Some(BackendReturnFlow::Deliver {
                            source: Box::new(BackendReturnLayout {
                                layout: value_layout(
                                    TransportCarrier::ValueRef(LaneId::for_test(0)),
                                    vec![AbiValueRepr::ValueRef],
                                ),
                                diverges: false,
                            }),
                            entry: ControlEntryId::from_u32(0),
                        }),
                    },
                }],
            };
            let identity = TransportPosition::Value {
                executable: executable.abi.transport.executable.clone(),
                value: callee,
            };
            let wrapper = Rc::new(BackendConstructionWrapper {
                identity,
                callable: CallableId::for_test(0),
                captures: Box::default(),
                call_arity: 1,
                return_form,
                members: Box::default(),
                selection: None,
            });
            executable.construction_wrappers = vec![Rc::clone(&wrapper)].into_boxed_slice();
            BackendProgram::new(
                key,
                Vec::new(),
                BTreeMap::new(),
                vec![Rc::new(executable)],
                vec![wrapper],
            )
        };

        assert!(
            verify_boxed_apply_seam_return_convention(
                &tel,
                RootId::for_test(0),
                &program(BackendCallableReturn::Absent)
            )
            .is_err(),
            "a boxed call delivering one lane must refuse an Absent wrapper it can reach"
        );
        assert!(
            verify_boxed_apply_seam_return_convention(
                &tel,
                RootId::for_test(0),
                &program(BackendCallableReturn::ValueRef)
            )
            .is_ok(),
            "agreement at one lane must pass"
        );
    }
}
