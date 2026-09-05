//! Compiler2 backend product packaging.
//!
//! This module packages product-keyed symbolic backend executables into the
//! backend-owned program consumed by the interpreter and native lowering.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

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
    BackendTail, CallEdge, CallReturnFlow, DirectCallEdge, DispatchCallArm,
};
use super::super::body::{
    CallArg, CallSiteId, ControlEntryId, ControlEntryOrigin, LoweredBody, LoweredEntry, LoweredStep, LoweredTail,
    ValueId,
};
use super::super::drive::{FactKey, Job};
use super::super::facts::FactUse;
use super::super::identity::RootId;
use super::super::identity::{ActivationKey, ExecutableKey};
use super::super::pull::{ProductKey, ProductReadContext, ProductValue, PullOutcome, PullWait};
use super::super::scheduler::FatalError;
use super::super::semantic::SemanticOrd;
use super::super::transport::{
    BoundaryFacts, BoundaryId, CallableFacts, CallableId, ExecutableSymbol, PhysicalLaneSource, ShapeDescr, ShapeId,
    TransportPosition,
};
use super::super::types::Ty;
use super::super::world::World;

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
    let key = ProductKey::RootBackendProduct(root);
    let changes =
        match context.read_rooted_products(key.clone(), ProductKey::BackendExecutable(entry.clone()), world.types()) {
            Ok(changes) => changes,
            Err(waits) => return PullOutcome::Waiting(waits),
        };
    let mut program = match context.previous_product(&key) {
        Some(ProductValue::RootBackendProduct(program)) => (**program).clone(),
        None => {
            let mut program = BackendProgram::empty(entry.clone());
            program.add_builtins(world.types());
            program
        }
        Some(other) => panic!("root backend product has unexpected previous value {other:?}"),
    };
    program.set_entry(entry);
    let mut executable_changes = Vec::new();
    for (key, value) in changes {
        match (key, value) {
            (ProductKey::BackendExecutable(key), Some(ProductValue::BackendExecutable(backend))) => {
                executable_changes.push((key, Some(backend)))
            }
            (ProductKey::StructSchema(module), Some(ProductValue::StructSchema(schema))) => {
                program.replace_schema(module, Some(schema))
            }
            (ProductKey::StructSchema(module), None) => program.replace_schema(module, None),
            (ProductKey::BackendExecutable(key), None) => executable_changes.push((key, None)),
            (key, value) => panic!("root membership names unexpected contribution {key:?}: {value:?}"),
        }
    }
    program.reconcile_executables(executable_changes, world.types());
    program
        .validate_boxed_contract(tel, root)
        .expect("root backend product should compile one return convention across the boxed apply seam");
    PullOutcome::Produced(ProductValue::RootBackendProduct(Rc::new(program)))
}

pub(crate) fn produce_struct_schema(
    world: &World,
    context: &mut ProductReadContext<'_>,
    module: super::super::ModuleId,
) -> PullOutcome {
    let fact = FactUse::settled(FactKey::StructDefined(module));
    if !context.read_fact(world, fact.clone()) {
        return PullOutcome::wait_on_fact(fact);
    }
    PullOutcome::Produced(ProductValue::StructSchema(Rc::new(
        super::super::backend_program::BackendSchema {
            module,
            name: Rc::new(world.module_name(module).expect("reachable struct name").to_string()),
            fields: Rc::new(world.struct_def_fields(module).expect("settled schema").to_vec()),
        },
    )))
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
    let boxed_apply_requirements =
        super::super::backend_program::boxed_contract::BoxedApplyRequirement::for_body(&lowered, &abi);
    let mut backend = BackendExecutable {
        key: executable.clone(),
        abi,
        body: lowered,
        construction_wrappers,
        atom_names: Box::default(),
        boxed_apply_requirements,
    };
    let mut atoms = Vec::new();
    collect_executable_atoms(world, &backend, &mut HashSet::new(), &mut atoms);
    backend.atom_names = atoms.into_iter().map(Rc::new).collect();
    for edge in backend.abi.call_edges.values() {
        for callee in symbolic_call_edge_callees(&edge.target) {
            context.include_product(ProductKey::BackendExecutable(callee.clone()));
        }
    }
    for positioned in &backend.abi.callable_owners {
        for target in callable_fact_executables(root, &positioned.owner.callable_facts)
            .into_iter()
            .chain(boundary_resolution_executables(root, &positioned.owner.boundary_facts))
        {
            context.include_product(ProductKey::BackendExecutable(target));
        }
    }
    for module in &backend.abi.materialized.struct_modules {
        context.include_product(ProductKey::StructSchema(*module));
    }
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
                    let ty = world.lane(physical.lane).ty;
                    let repr = if physical.source == PhysicalLaneSource::Carrier {
                        AbiValueRepr::ValueRef
                    } else if world.types().is_integer(&ty) {
                        AbiValueRepr::RawInt
                    } else if world.types().is_atom_type(&ty) {
                        AbiValueRepr::RawAtom
                    } else {
                        AbiValueRepr::ValueRef
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
    use crate::compiler2::transport::{ActivationSymbol, ExecutableSymbol, LaneId};
    use std::collections::BTreeMap;

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

    /// FIX-1 of the fz-kdt.155 re-refutation: the seam tripwire's REFUSING
    /// half must have a witness: removing the calling-convention invariant
    /// shipped green through every gate (the fz-kdt.157 pattern).
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
            executable.boxed_apply_requirements =
                super::super::super::backend_program::boxed_contract::BoxedApplyRequirement::for_body(
                    &executable.body,
                    &executable.abi,
                );
            BackendProgram::new(
                key,
                Vec::new(),
                BTreeMap::new(),
                vec![Rc::new(executable)],
                Vec::new(),
                world.types(),
            )
        };

        assert!(
            program(BackendCallableReturn::Absent)
                .validate_boxed_contract(&tel, RootId::for_test(0))
                .is_err(),
            "a boxed call delivering one lane must refuse an Absent wrapper it can reach"
        );
        assert!(
            program(BackendCallableReturn::ValueRef)
                .validate_boxed_contract(&tel, RootId::for_test(0))
                .is_ok(),
            "agreement at one lane must pass"
        );
    }
}
