//! Compiler2 backend product packaging.
//!
//! This module packages product-keyed symbolic backend executables into the
//! backend-owned program consumed by the interpreter and native lowering.

use crate::compiler2::ValueMap;
use crate::fast_hash::{HashMap, HashSet};
use std::rc::Rc;

use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::dispatch_matrix::pattern::{
    LastResort, PatternDispatchPlan, PatternGuardDispatch, PatternGuardExpr, atom_name,
};
use crate::dispatch_matrix::{ComparisonValue, DispatchNode, ProjectionKind, Region, SubjectSource};
use crate::fz_ir::SlotStore;
use crate::ground_value::{GroundValue, entries_in_atom_key_order};
use crate::literal_term::LiteralTerm;
use crate::source::Span;
use fz_runtime::module_name::{ModuleName, STRUCT_MODULE_FIELD};
use fz_runtime::process::AtomName;

use super::super::artifact::{
    AbiReadyCallEdge, AbiReadyExecutable, AbiValueRepr, BackendBody, BackendCallArg, BackendClause,
    BackendConstructionCapture, BackendConstructionMemberAdapter, BackendConstructionWrapper, BackendEntry,
    BackendEntryCapture, BackendEntryOrigin, BackendExecutable, BackendProgram, BackendReturnFlow, BackendReturnLayout,
    BackendStep, BackendTail, CallEdge, CallReturnFlow, CallTarget, DirectCallEdge, DispatchCallArm,
};
use super::super::body::{
    CallArg, CallSiteId, ControlEntryId, ControlEntryOrigin, LoweredBody, LoweredEntry, LoweredMapKey, LoweredStep,
    LoweredTail, ValueId,
};
use super::super::drive::{FactKey, Job, emit_job_diagnostic};
use super::super::identity::{ActivationKey, ExecutableKey, ModuleId, RootId, RootKind};
use super::super::pull::{ProductKey, ProductReadContext, ProductValue, PullOutcome, PullWait};
use super::super::transport::{
    BoundaryFacts, BoundaryId, CallableFacts, CallableId, ExecutableSymbol, PhysicalLaneSource, TransportPosition,
};
use super::super::types::Ty;
use super::super::world::World;
use fz_engine::FactUse;
use fz_engine::FatalError;
use fz_engine::SemanticOrd;

/// Reports `RootBackendProduct` pull-drive failures as `FatalError`.
///
/// The three hooks that forward carry a failure that already said why:
/// `FatalError` and `PullOutcome::Failed` both mean "diagnostic emitted".
/// Restating one of those under a different code buries the message that
/// named the program's actual problem.
///
/// `no_ready_producer` is the one genuine dead end: `pop_runnable` found
/// nothing left to run anywhere, so the standing waits really are terminal.
/// It reports through `ExecutionContext::report_unresolved_waits`, the same
/// `World::unresolved_waits` -> specific-issue path the push drive
/// (`Compiler2::drive`) uses, so a nested product pull's stall names the
/// same unknown-module/unbound-function/etc. issue the top-level drive
/// would have named for the identical stall.
///
/// `fact_wait_budget_exceeded` and `request_budget_exhausted` are not dead ends --
/// they are a counter (`jobs_ran`, the outer product-stack budget) running
/// out mid-progress, while a need parks a waiter on its producer as soon as
/// it is recorded, so the frontier a budget cutoff catches is routinely
/// non-terminal. Neither hook reports.
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
        _tel: &T,
        _scope: super::super::pull::ProductScope,
        _product: &ProductKey,
    ) -> Self {
        FatalError
    }

    fn job_failed<T: crate::telemetry::Telemetry>(
        _world: &World,
        _tel: &T,
        _scope: super::super::pull::ProductScope,
        _fact: &FactUse<FactKey>,
        _job: &Job,
        source: FatalError,
    ) -> Self {
        source
    }

    fn no_ready_producer<T: crate::telemetry::Telemetry>(
        world: &mut World,
        tel: &T,
        sessions: Option<&mut super::super::pull::ProductSessions>,
        _scope: super::super::pull::ProductScope,
        _fact: &FactUse<FactKey>,
    ) -> Self {
        super::super::drive::ExecutionContext::with_optional_product_sessions(world, tel, sessions)
            .report_unresolved_waits();
        FatalError
    }

    fn fact_wait_budget_exceeded<T: crate::telemetry::Telemetry>(
        _world: &mut World,
        _tel: &T,
        _scope: super::super::pull::ProductScope,
        _budget: u64,
        _fact: &FactUse<FactKey>,
    ) -> Self {
        FatalError
    }

    fn request_budget_exhausted<T: crate::telemetry::Telemetry>(
        _world: &mut World,
        _tel: &T,
        _scope: super::super::pull::ProductScope,
        _budget: u64,
        _last_wait: Option<(&ProductKey, &[PullWait])>,
    ) -> Self {
        FatalError
    }
}

pub(crate) fn produce_root_backend_product(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    root: RootId,
) -> PullOutcome {
    let root_entry = world.root_entry(root);
    let keying_facts = world
        .activation_key_prerequisites(root, root_entry.function, &root_entry.input)
        .into_iter()
        .flatten();
    let declarations = match root_entry.kind {
        RootKind::Runtime => world.submissions_checked(),
        // A macro root compiles while the source that calls it is still
        // being scoped, so it cannot wait on that source's declarations.
        RootKind::Macro => Vec::new(),
    };
    let keying_waits = std::iter::once(FactKey::RootEntry(root))
        .chain(keying_facts)
        .chain(declarations)
        .filter(|fact| !context.read_fact(world, FactUse::settled(fact.clone())))
        .map(|fact| PullWait::Fact(FactUse::settled(fact)))
        .collect::<Vec<_>>();
    if !keying_waits.is_empty() {
        return PullOutcome::Waiting(keying_waits);
    }
    let entry = world.root_entry_executable(root);
    let key = ProductKey::RootBackendProduct(root);
    let changes = match context.read_rooted_products(
        tel,
        key.clone(),
        ProductKey::BackendExecutable(entry.clone()),
        world.types(),
    ) {
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

/// What a struct's field holds when its declaration gives it no default.
const NIL: LiteralTerm = LiteralTerm::Ground(GroundValue::Nil);

pub(crate) fn produce_struct_schema(
    world: &World,
    context: &mut ProductReadContext<'_>,
    module: super::super::ModuleId,
) -> PullOutcome {
    let fact = FactUse::settled(FactKey::StructDefined(module));
    if !context.read_fact(world, fact.clone()) {
        return PullOutcome::wait_on_fact(fact);
    }
    let def = world.struct_def(module).expect("a settled struct has its definition");
    PullOutcome::Produced(ProductValue::StructSchema(Rc::new(
        super::super::backend_program::BackendSchema {
            module,
            name: Rc::new(world.module_name(module).expect("reachable struct name").clone()),
            fields: Rc::new(def.fields.clone()),
            defaults: Rc::new(
                def.fields
                    .iter()
                    .map(|field| def.defaults.get(field).cloned().unwrap_or(NIL))
                    .collect(),
            ),
        },
    )))
}

pub(crate) fn produce_backend_executable_product(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    executable: &ExecutableKey,
) -> PullOutcome {
    let Some(value) = context.read_product(tel, &ProductKey::AbiExecutable(executable.clone()), world.types()) else {
        return PullOutcome::Waiting(vec![PullWait::Product(ProductKey::AbiExecutable(executable.clone()))]);
    };
    let ProductValue::AbiExecutable(abi) = value else {
        panic!("ABI executable product produced unexpected value {value:?}");
    };
    let abi = Rc::clone(abi);
    let root = context.session().root().expect("executable products are root-scoped");
    let mut dependencies = HashSet::default();
    for edge in abi.call_edges.values() {
        let flows = match edge.target() {
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
    let mut abis = HashMap::from_iter([(executable.clone(), Rc::clone(&abi))]);
    let mut waits = Vec::new();
    for dependency in dependencies {
        let key = ProductKey::AbiExecutable(dependency.clone());
        match context.read_product(tel, &key, world.types()) {
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
        .flat_map(|abi| abi.return_endpoints.iter().map(|(position, layout)| (position, layout)))
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
    let mut lowerer = BackendLowerer::new(
        world,
        tel,
        root,
        &abi.value_layouts,
        &abi.materialized.value_types,
        return_endpoints,
        constructions,
    );
    let lowered = lower_backend_body(&mut lowerer, &abi)
        .expect("symbolic backend lowering should be complete after ABI product exists");
    let boxed_apply_requirements =
        super::super::backend_program::boxed_contract::BoxedApplyRequirement::for_body(&lowered, &abi);
    let value_count = abi.materialized.body.value_count();
    let mut backend = BackendExecutable {
        key: executable.clone(),
        abi,
        body: lowered,
        value_count,
        construction_wrappers,
        atom_names: Box::default(),
        boxed_apply_requirements,
    };
    let mut names = ExecutableNames::default();
    collect_executable_atoms(world, &backend, &mut names);
    let mut waits = Vec::new();
    for exception in std::mem::take(&mut names.raised) {
        let name = ModuleName::from_atom_name(&exception).expect("an exception's atom names a module");
        let module = world.reference_module(name);
        let defined = FactUse::settled(FactKey::StructDefined(module));
        if !context.read_fact(world, defined.clone()) {
            waits.push(PullWait::Fact(defined));
            continue;
        }
        context.include_product(ProductKey::StructSchema(module));
        let def = world.struct_def(module).expect("a settled struct has its definition");
        for default in def.fields.iter().map(|field| def.defaults.get(field).unwrap_or(&NIL)) {
            default.each_ground(&mut |value| {
                if let Some(atom) = atom_name(value) {
                    push_atom(&mut names, atom);
                }
            });
        }
    }
    let candidates = struct_candidates(world, context, root, &backend, &names.atoms);
    waits.extend(undefined_modules(world, context, &candidates));
    if !waits.is_empty() {
        return PullOutcome::Waiting(waits);
    }
    backend.atom_names = names.atoms.iter().map(|atom| AtomName::from(atom.as_str())).collect();
    for edge in backend.abi.call_edges.values() {
        for callee in symbolic_call_edge_callees(edge.target()) {
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
    for module in candidates {
        if context.read_fact(world, FactUse::settled(FactKey::StructDefined(module))) {
            context.include_product(ProductKey::StructSchema(module));
        }
    }
    let backend = Rc::new(backend);
    PullOutcome::Produced(ProductValue::BackendExecutable(backend))
}

/// The modules whose schemas an executable may need. Its types spell some
/// under `__struct__`. A map may also be given a module under `__struct__`
/// while the program runs, and the program holds that module's atom one of
/// two ways: a body `writes` it, or the program makes it from text, and then
/// it can be any module a value can name. A macro root runs while its source
/// is still being defined, so it waits on neither.
fn struct_candidates(
    world: &mut World,
    context: &mut ProductReadContext<'_>,
    root: RootId,
    executable: &BackendExecutable,
    writes: &[String],
) -> indexmap::IndexSet<ModuleId> {
    let spelled = &executable.abi.materialized.struct_modules;
    let mut candidates: indexmap::IndexSet<ModuleId> = spelled
        .iter()
        .map(|name| world.reference_module(name.clone()))
        .collect();
    if world.root_entry(root).kind != RootKind::Runtime {
        return candidates;
    }
    let written = writes.iter().filter_map(|atom| ModuleName::from_atom_name(atom));
    candidates.extend(written.map(|name| world.reference_module(name)));
    if makes_an_atom_from_text(executable) {
        context.read_fact(world, FactUse::settled(FactKey::NameableModules));
        candidates.extend(world.nameable_modules());
    }
    candidates
}

/// Whether `executable` is the runtime entry that makes an atom from text.
/// Every other atom a program holds is one its source writes.
fn makes_an_atom_from_text(executable: &BackendExecutable) -> bool {
    let wire = executable.abi.materialized.extern_wire.as_ref();
    wire.is_some_and(|wire| wire.symbol == "fz_binary_to_atom")
}

/// The definitions still to wait for before the schemas of `candidates` can
/// be decided. A module is a struct exactly when its definition declares one,
/// so each module that can be defined is waited on until it is. A name
/// nothing defines is not a struct, and nothing waits on it.
fn undefined_modules(
    world: &mut World,
    context: &mut ProductReadContext<'_>,
    candidates: &indexmap::IndexSet<ModuleId>,
) -> Vec<PullWait> {
    let mut waits = Vec::new();
    for &module in candidates {
        if !world.can_be_defined(module) {
            continue;
        }
        let defined = FactUse::settled(FactKey::ModuleDefined(module));
        if !context.read_fact(world, defined.clone()) {
            waits.push(PullWait::Fact(defined));
        }
    }
    waits
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
            entry: symbol.activation.entry,
        },
        need: symbol.need,
    }
}

/// Where each ABI in a lowering's dependency set says a call returns.
type ReturnEndpoints<'a> = HashMap<&'a TransportPosition, &'a BackendReturnLayout>;

fn backend_call_edge(
    target: &CallEdge<ExecutableKey>,
    endpoints: &ReturnEndpoints<'_>,
) -> Result<CallEdge<ExecutableKey, BackendReturnFlow>, FatalError> {
    Ok(match target {
        CallEdge::Direct(direct) => CallEdge::Direct(DirectCallEdge {
            callee: direct.callee.clone(),
            return_flow: resolve_return_flow(&direct.return_flow, endpoints)?,
            extern_marshals: direct.extern_marshals.clone(),
        }),
        CallEdge::Dispatch(dispatch) => CallEdge::Dispatch(Box::new(super::super::artifact::DispatchCallEdge::new(
            dispatch.plan.clone(),
            dispatch
                .arms
                .iter()
                .map(|arm| {
                    Ok(DispatchCallArm {
                        callee: arm.callee.clone(),
                        return_flow: resolve_return_flow(&arm.return_flow, endpoints)?,
                        extern_marshals: arm.extern_marshals.clone(),
                    })
                })
                .collect::<Result<Vec<_>, FatalError>>()?,
        ))),
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
            let layout = abi.transport.position_layouts.layout_at(position).ok_or(FatalError)?;
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
    endpoints: &ReturnEndpoints<'_>,
) -> Result<BackendReturnFlow, FatalError> {
    let layout = |position: &TransportPosition| endpoints.get(position).copied().ok_or(FatalError);
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
                    Ok(BackendConstructionCapture { ty: capture.ty, layout })
                })
                .collect::<Result<Box<_>, FatalError>>()?;
            let function = world
                .callable(construction.callable)
                .function
                .expect("construction names a source function");
            Ok(Rc::new(BackendConstructionWrapper {
                identity: positioned.position.clone(),
                source_origin: std::sync::Arc::clone(&world.function_ref(function).denotation),
                denotation: function.denotation(),
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
    if let Some(signature) = &abi.materialized.extern_wire {
        return Ok(BackendBody::Extern {
            signature: signature.clone(),
        });
    }
    match &abi.materialized.body {
        LoweredBody::Clauses {
            clauses,
            entries,
            generated,
            ..
        } => Ok(BackendBody::Clauses {
            clauses: clauses
                .iter()
                .map(|clause| {
                    Ok(BackendClause {
                        span: clause.span,
                        params: clause.params.clone(),
                        arguments: clause.arguments.clone(),
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
    let capture_positions = lowerer.capture_positions_for_entry(abi, entry);
    Ok(BackendEntry {
        span: entry.span,
        origin: lower_entry_origin(abi, entry_index, entry),
        params: entry.params.clone(),
        captures: backend_entry_captures(lowerer.world, abi, &entry.captures, &capture_positions)?,
        physical_captures: entry.physical_captures.clone(),
        physical_params: entry.physical_params.clone(),
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
            callee,
            args,
            dest,
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
                target: backend_call_edge(edge.target(), &lowerer.return_endpoints)?,
                selector: callee.module_value(),
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
            // A closure tail's edge is a closure edge, minted with the form
            // this tail carries on unchanged.
            let Some(AbiReadyCallEdge::Closure { form, target, .. }) = abi.call_edges.get(callsite) else {
                return Err(incomplete_backend_program(
                    lowerer.telemetry,
                    lowerer.root_id,
                    format!("missing symbolic closure-call edge for callsite {}", callsite.as_u32()),
                ));
            };
            BackendTail::ClosureCall {
                value: *value,
                callsite: *callsite,
                callee: *callee,
                edge: form.clone(),
                args: lowerer.lower_call_args(abi, *callsite, Some(*callee), args)?,
                dest: dest.clone(),
                return_flow: symbolic_call_edge_return_flow(target)
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
            outcomes: receive.outcomes.clone(),
            after: receive.after.clone(),
            dest: receive.dest.clone(),
        })),
        LoweredTail::Unreachable => BackendTail::Unreachable,
        LoweredTail::Try { body, handler } => BackendTail::Try {
            body: *body,
            handler: *handler,
        },
    })
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
    value_layouts: &'a ValueMap<super::super::artifact::BackendValueLayout>,
    value_types: &'a ValueMap<Ty>,
    return_endpoints: ReturnEndpoints<'a>,
    constructions: ValueMap<TransportPosition>,
}

impl<'a, 'tel, T: crate::telemetry::Telemetry> BackendLowerer<'a, 'tel, T> {
    fn new(
        world: &'a mut World,
        telemetry: &'tel T,
        root_id: RootId,
        value_layouts: &'a ValueMap<super::super::artifact::BackendValueLayout>,
        value_types: &'a ValueMap<Ty>,
        return_endpoints: ReturnEndpoints<'a>,
        constructions: ValueMap<TransportPosition>,
    ) -> Self {
        Self {
            world,
            telemetry,
            root_id,
            value_layouts,
            value_types,
            return_endpoints,
            constructions,
        }
    }

    fn capture_positions_for_entry(
        &self,
        executable: &AbiReadyExecutable,
        entry: &LoweredEntry,
    ) -> Vec<super::super::transport::TransportPosition> {
        entry
            .capture_owners
            .iter()
            .map(|owner| super::super::transport::TransportPosition::EntryCapture {
                executable: executable.transport.executable.clone(),
                entry: executable.materialized.original_entry_id(owner.entry),
                capture_index: owner.index,
            })
            .collect()
    }

    fn lower_step(&mut self, step: &LoweredStep) -> Result<BackendStep, FatalError> {
        Ok(match step {
            LoweredStep::Const {
                value,
                literal: literal @ LiteralTerm::Ground(_),
            } => BackendStep::Const {
                value: *value,
                literal: literal.clone(),
            },
            LoweredStep::Const { value, literal } => self.step_or_omitted_when_absent(
                *value,
                BackendStep::Const {
                    value: *value,
                    literal: literal.clone(),
                },
            ),
            LoweredStep::Tuple { value, items } => self.step_or_omitted_when_absent(
                *value,
                BackendStep::Tuple {
                    value: *value,
                    items: items.clone(),
                },
            ),
            LoweredStep::List {
                value,
                items,
                tail,
                retention,
            } => self.step_or_omitted_when_absent(
                *value,
                BackendStep::List {
                    value: *value,
                    items: items.clone(),
                    tail: *tail,
                    retention: *retention,
                },
            ),
            LoweredStep::Map { value, entries } => {
                let in_key_order = entries_in_key_order(entries);
                self.step_or_omitted_when_absent(
                    *value,
                    BackendStep::Map {
                        value: *value,
                        in_key_order: in_key_order.is_some(),
                        entries: in_key_order
                            .unwrap_or_else(|| entries.iter().map(|(key, value)| (key.value, *value)).collect()),
                    },
                )
            }
            LoweredStep::MapUpdate {
                value,
                ok,
                base,
                entries,
                rewrite,
            } => self.update(*value, *ok, *base, entries, *rewrite),
            LoweredStep::Struct { value, module, fields } => self.step_or_omitted_when_absent(
                *value,
                BackendStep::Struct {
                    value: *value,
                    module_name: self.module_name(*module).clone(),
                    fields: fields.clone(),
                },
            ),
            LoweredStep::Bitstring { value, fields } => self.step_or_omitted_when_absent(
                *value,
                BackendStep::Bitstring {
                    value: *value,
                    fields: fields.clone(),
                },
            ),
            LoweredStep::FunctionRef { value, function } => self.step_or_omitted_when_absent(
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
            } => self.step_or_omitted_when_absent(
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
            LoweredStep::FieldAccess { value, base, field } => {
                self.step_or_omitted_when_absent(*value, self.field_read(*value, *base, field))
            }
            LoweredStep::PopHandler => BackendStep::PopHandler,
        })
    }

    fn value_is_proven_semantically_absent(&self, value: ValueId) -> bool {
        self.value_layouts.get(&value).is_some_and(|layout| {
            self.world.shape(layout.structural).is_semantically_absent()
                && matches!(layout.carrier, super::super::transport::TransportCarrier::Absent)
        })
    }

    /// `base.field` answered from what the types know of `base`. One known
    /// struct's module is a constant and its declared field is a slot; any
    /// other read finds the field by name at run time.
    fn field_read(&self, value: ValueId, base: ValueId, field: &str) -> BackendStep {
        let by_name = || BackendStep::FieldAccess {
            value,
            base,
            field: field.to_string(),
        };
        let Some(module) = self.known_struct(base) else {
            return by_name();
        };
        if field == STRUCT_MODULE_FIELD {
            return BackendStep::Const {
                value,
                literal: GroundValue::Atom(self.module_name(module).atom_name()).into(),
            };
        }
        match self
            .world
            .struct_def_fields(module)
            .and_then(|fields| slot_of(fields, field))
        {
            Some(slot) => BackendStep::StructSlot {
                value,
                base,
                module: self.module_name(module).clone(),
                slot,
                field: field.to_string(),
            },
            None => by_name(),
        }
    }

    /// `%{base | k: v, ...}` answered from what the types know of `base`. One
    /// known struct whose fields the keys all name has those slots replaced,
    /// in `base` itself when `rewrite` permits and nothing else holds it,
    /// otherwise in a copy; any other update finds each key at run time.
    fn update(
        &self,
        value: ValueId,
        ok: ValueId,
        base: ValueId,
        entries: &[(LoweredMapKey, ValueId)],
        rewrite: crate::fz_ir::RewritePermission,
    ) -> BackendStep {
        match self.updated_slots(base, entries) {
            Some((module, arity, stores)) => BackendStep::StructUpdate {
                value,
                ok,
                base,
                module: self.module_name(module).clone(),
                arity,
                stores,
                rewrite,
            },
            None => BackendStep::MapUpdate {
                value,
                ok,
                base,
                entries: entries.iter().map(|(key, value)| (key.value, *value)).collect(),
            },
        }
    }

    /// The one struct `base` is, how many fields it has, and the slot each
    /// entry replaces, when `base` is one known struct and every key is a
    /// literal atom naming one of its fields.
    fn updated_slots(
        &self,
        base: ValueId,
        entries: &[(LoweredMapKey, ValueId)],
    ) -> Option<(ModuleId, u32, Vec<SlotStore<ValueId>>)> {
        let module = self.known_struct(base)?;
        let fields = self.world.struct_def_fields(module)?;
        let stores = entries
            .iter()
            .map(|(key, item)| {
                let GroundValue::Atom(field) = key.literal.as_ref()? else {
                    return None;
                };
                Some(SlotStore {
                    slot: slot_of(fields, field)?,
                    key: key.value,
                    value: *item,
                })
            })
            .collect::<Option<_>>()?;
        Some((module, fields.len() as u32, stores))
    }

    /// The struct `value` is, when its type admits exactly one.
    fn known_struct(&self, value: ValueId) -> Option<ModuleId> {
        let name = self.world.types().sole_struct(self.value_types.get(&value)?)?;
        let module = self.world.module_named(&name)?;
        self.world.struct_def(module).map(|_| module)
    }

    fn module_name(&self, module: ModuleId) -> &ModuleName {
        self.world
            .module_name(module)
            .unwrap_or_else(|| panic!("struct module {} should have a name", module.as_u32()))
    }

    /// Every fresh-construction step (Tuple/List/Map/MapUpdate/Struct/
    /// Bitstring/FunctionRef/Lambda) and every projection (FieldAccess/StructSlot)
    /// must respect the absence proof: when transport proves the
    /// value runtime-absent, its operands were never demanded and may be
    /// unbound at runtime, so the step lowers as `Omitted` instead of
    /// executing a read of never-materialized values
    /// (fz-9in: a dead binding whose construction call survives because it
    /// allocates; fz-kdt.111: a predicate closure a shared `Enum` body proves
    /// it never invokes, whose ignored capture the eager interp still read).
    fn step_or_omitted_when_absent(&self, value: ValueId, step: BackendStep) -> BackendStep {
        if self.value_is_proven_semantically_absent(value) {
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
        args.iter()
            .map(|arg| {
                Ok(BackendCallArg {
                    value: arg.value,
                    ownership: arg.ownership,
                })
            })
            .collect()
    }
}

fn lower_entry_origin(executable: &AbiReadyExecutable, entry_index: usize, entry: &LoweredEntry) -> BackendEntryOrigin {
    let entry_id = executable
        .materialized
        .original_entry_id(ControlEntryId::from_u32(entry_index as u32));
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
        if matches!(entry.tail, LoweredTail::Unreachable) {
            return BackendEntryOrigin::Branch;
        }
        panic!("resume entry {entry_index} should have a settled transport position: {entry:?}");
    }
    if matches!(entry.tail, LoweredTail::Unreachable) {
        return BackendEntryOrigin::Branch;
    }
    match entry.origin {
        ControlEntryOrigin::Clause => BackendEntryOrigin::Clause,
        ControlEntryOrigin::Branch => BackendEntryOrigin::Branch,
        ControlEntryOrigin::ReceiveOutcome => BackendEntryOrigin::ReceiveOutcome,
        ControlEntryOrigin::Handler => BackendEntryOrigin::Handler,
        ControlEntryOrigin::DeliveredResume { .. } => unreachable!("delivered resumes return before branch fallback"),
    }
}

/// What an executable's code names: the atoms it writes, in the order it
/// first writes each, and the exception modules whose struct it builds when
/// it raises.
#[derive(Default)]
struct ExecutableNames {
    seen: HashSet<String>,
    atoms: Vec<String>,
    raised: Vec<String>,
}

impl ExecutableNames {
    /// Notes what `failure` raises: the atoms its fields write and the module
    /// whose struct it builds.
    fn raise(&mut self, failure: &LastResort) {
        for atom in failure.atoms() {
            push_atom(self, atom);
        }
        self.raises(failure.exception());
    }

    fn raises<'a>(&mut self, exceptions: impl IntoIterator<Item = &'a str>) {
        for exception in exceptions {
            if !self.raised.iter().any(|raised| raised == exception) {
                self.raised.push(exception.to_string());
            }
        }
    }
}

fn collect_executable_atoms(world: &mut World, executable: &BackendExecutable, names: &mut ExecutableNames) {
    if let Some(dispatch) = &executable.abi.materialized.entry_dispatch {
        collect_dispatch_atoms(world, dispatch.plan(), names);
    }
    match &executable.body {
        BackendBody::Extern { signature } => {
            if let crate::fz_ir::ExternReturn::Checked(_, failure) = &signature.ret {
                names.raise(failure);
            }
        }
        BackendBody::Clauses { entries, .. } => {
            for entry in entries {
                collect_entry_atoms(world, entry, names);
            }
        }
    }
}

/// A map literal's entries in the runtime's key order with no key repeated,
/// when every key is a literal atom.
fn entries_in_key_order(entries: &[(LoweredMapKey, ValueId)]) -> Option<Vec<(ValueId, ValueId)>> {
    entries_in_atom_key_order(
        entries
            .iter()
            .map(|(key, value)| (key.literal.as_ref(), (key.value, *value))),
    )
}

fn slot_of(fields: &[String], field: &str) -> Option<u32> {
    fields.iter().position(|name| name == field).map(|slot| slot as u32)
}

fn collect_entry_atoms(world: &mut World, entry: &BackendEntry, names: &mut ExecutableNames) {
    collect_step_atoms(world, &entry.steps, names);
    collect_tail_atoms(world, &entry.tail, names);
}

fn collect_step_atoms(_world: &mut World, steps: &[BackendStep], names: &mut ExecutableNames) {
    for step in steps {
        match step {
            BackendStep::Const { literal, .. } => {
                literal.each_ground(&mut |ground| collect_dispatch_const_atoms(ground, names));
            }
            BackendStep::FieldAccess { field, .. } | BackendStep::StructSlot { field, .. } => {
                push_atom(names, field);
            }
            BackendStep::Omitted { .. }
            | BackendStep::Tuple { .. }
            | BackendStep::List { .. }
            | BackendStep::Map { .. }
            | BackendStep::MapUpdate { .. }
            | BackendStep::StructUpdate { .. }
            | BackendStep::Struct { .. }
            | BackendStep::Bitstring { .. }
            | BackendStep::FunctionRef { .. }
            | BackendStep::Lambda { .. }
            | BackendStep::BinaryOp { .. }
            | BackendStep::UnaryOp { .. }
            | BackendStep::MapIndex { .. }
            | BackendStep::PopHandler => {}
        }
    }
}

fn collect_tail_atoms(world: &mut World, tail: &BackendTail, names: &mut ExecutableNames) {
    match tail {
        BackendTail::DirectCall { target, .. } => {
            for callee in target.callees() {
                collect_undefined_function_atoms(callee, names);
            }
            if let CallEdge::Dispatch(dispatch) = target {
                collect_dispatch_atoms(world, &dispatch.plan, names);
            }
        }
        BackendTail::Dispatch { dispatch, .. } => collect_dispatch_atoms(world, &dispatch.plan, names),
        BackendTail::Receive(receive) => collect_dispatch_atoms(world, &receive.dispatch, names),
        BackendTail::Value { .. }
        | BackendTail::Unreachable
        | BackendTail::ClosureCall { .. }
        | BackendTail::If { .. }
        | BackendTail::Try { .. } => {}
    }
}

/// The raise of a call that found no function names the function and tells
/// the modules that lack it from the atoms that name no module.
fn collect_undefined_function_atoms(callee: &CallTarget<ExecutableKey>, names: &mut ExecutableNames) {
    let CallTarget::Undefined(undefined) = callee else {
        return;
    };
    names.raises(["Elixir.UndefinedFunctionError", "Elixir.ArgumentError"]);
    push_atom(names, &undefined.function);
    for module in &undefined.modules_without {
        push_atom(names, module);
    }
}

fn collect_dispatch_atoms(world: &mut World, plan: &PatternDispatchPlan<Ty>, names: &mut ExecutableNames) {
    for prepared in &plan.prepared_keys {
        collect_dispatch_const_atoms(prepared, names);
    }
    if let Some(failure) = plan.last_resort.as_ref().filter(|_| plan.can_fail()) {
        names.raise(failure);
    }
    for subject in &plan.graph.subjects {
        match &subject.source {
            SubjectSource::Input { .. } => {}
            SubjectSource::Projection(projection) => {
                if let ProjectionKind::MapValue {
                    key: ComparisonValue::Const(key),
                } = &projection.kind
                {
                    collect_dispatch_const_atoms(key, names);
                }
                if let ProjectionKind::StructField(field) = &projection.kind {
                    push_atom(names, field);
                }
            }
        }
    }
    for guard in &plan.guards {
        collect_guard_atoms(world, guard, names);
    }
    collect_dispatch_graph_atoms(world, plan, plan.graph.root, names);
}

fn collect_dispatch_graph_atoms(
    world: &mut World,
    plan: &PatternDispatchPlan<Ty>,
    node_id: crate::dispatch_matrix::GraphNodeId,
    names: &mut ExecutableNames,
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
            collect_region_atoms(world, &predicate.region, names);
            collect_dispatch_graph_atoms(world, plan, on_match.target, names);
            collect_dispatch_graph_atoms(world, plan, on_miss.target, names);
        }
    }
}

fn collect_region_atoms(world: &mut World, region: &Region<Ty>, names: &mut ExecutableNames) {
    match region {
        Region::Equal(ComparisonValue::Const(value))
        | Region::MapKeyPresent {
            key: ComparisonValue::Const(value),
        } => {
            collect_dispatch_const_atoms(value, names);
        }
        Region::Type(ty) => {
            world
                .types()
                .runtime_type_predicate(ty)
                .each_atom_name(&mut |atom| push_atom(names, atom));
        }
        Region::Equal(ComparisonValue::Pinned(_) | ComparisonValue::Subject(_))
        | Region::MapKeyPresent {
            key: ComparisonValue::Pinned(_) | ComparisonValue::Subject(_),
        }
        | Region::TupleArity(_)
        | Region::List(_)
        | Region::MapKind
        | Region::Bitstring(_)
        | Region::Guard(_) => {}
    }
}

fn collect_guard_atoms(world: &mut World, expr: &PatternGuardExpr<Ty>, names: &mut ExecutableNames) {
    match expr {
        PatternGuardExpr::Const(value) => collect_dispatch_const_atoms(value, names),
        PatternGuardExpr::Unary { expr, .. } => collect_guard_atoms(world, expr, names),
        PatternGuardExpr::Binary { lhs, rhs, .. } => {
            collect_guard_atoms(world, lhs, names);
            collect_guard_atoms(world, rhs, names);
        }
        PatternGuardExpr::Dispatch { inputs, dispatch, .. } => {
            for input in inputs {
                collect_guard_atoms(world, input, names);
            }
            collect_guard_dispatch_atoms(world, dispatch, names);
        }
        PatternGuardExpr::Extern { args, .. } => {
            for arg in args {
                collect_guard_atoms(world, arg, names);
            }
        }
        PatternGuardExpr::Subject(_) | PatternGuardExpr::Pinned(_) | PatternGuardExpr::Fails => {}
    }
}

fn collect_guard_dispatch_atoms(world: &mut World, dispatch: &PatternGuardDispatch<Ty>, names: &mut ExecutableNames) {
    collect_dispatch_atoms(world, &dispatch.plan, names);
    for body in &dispatch.bodies {
        collect_guard_atoms(world, body, names);
    }
}

fn collect_dispatch_const_atoms(value: &GroundValue, names: &mut ExecutableNames) {
    if let GroundValue::Atom(name) = value {
        push_atom(names, name);
    }
}

fn push_atom(names: &mut ExecutableNames, name: &str) {
    if names.seen.insert(name.to_string()) {
        names.atoms.push(name.to_string());
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
    emit_job_diagnostic(tel, diagnostic)
}

#[cfg(test)]
#[path = "backend_test.rs"]
mod backend_test;
