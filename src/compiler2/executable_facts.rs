//! Immutable executable-scoped semantic projection.
//!
//! `ExecutableFacts(E)` is semantic truth owned by [`World`](super::World),
//! independent of any product session. The scheduler job that publishes the
//! fact gathers its settled inputs; product producers only read this value.

use crate::compiler2::ValueMap;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use crate::dispatch_matrix::demand::DispatchDemand;

use super::artifact::ExecutableDispatch;
use super::body::{
    CallSiteId, ControlDestination, ControlEntryId, DeliveredValueJoin, DeliveredValueSource, LoweredBody,
    LoweredClause, LoweredEntry, LoweredExtern, LoweredStep, LoweredTail, ValueId, callsite_call_args,
    delivered_value_joins,
};
use super::callsite_dispatch::{CallDestinations, call_destinations};
use super::identity::{ExecutableKey, ExecutableNeed, FunctionId};
use super::semantic::{
    ActivationAnalysis, CallSiteKey, CallSiteSummary, CallableActivationInput, CallableDemand, CallableSurface,
    RuntimeDemand, RuntimeDemandTypeInputs, RuntimeDemandTypeProjection,
};
use super::types::{Ty, Types};
use super::world::World;

#[cfg_attr(test, derive(Clone))]
#[derive(Debug, PartialEq)]
pub(crate) struct ExecutableFacts {
    pub(super) analysis: ActivationAnalysis,
    pub(super) body: LoweredBody,
    /// The wire ABI this executable's function resolved on its contract,
    /// once it names an extern. `None` for an ordinary function, whose
    /// `body` above carries its clauses instead.
    pub(super) extern_wire: Option<LoweredExtern>,
    pub(super) entry_dispatch: Option<ExecutableDispatch>,
    /// What each multi-destination callsite's own choice between its
    /// destinations reads of its arguments.
    pub(super) callsite_dispatch_demand: HashMap<CallSiteId, Box<[DispatchDemand]>>,
    pub(super) callsites: HashMap<CallSiteId, CallSiteSummary>,
    pub(super) callsite_needs: HashMap<CallSiteId, ExecutableNeed>,
    pub(super) delivered_value_joins: HashMap<ControlEntryId, DeliveredValueJoin>,
    pub(super) callsite_return_origins: HashMap<CallSiteId, TransportOrigin>,
    pub(super) value_origins: ValueMap<TransportOrigin>,
    pub(super) callable_origins: ValueMap<LocalCallableProducer>,
    pub(super) return_origins: Box<[TransportOrigin]>,
    pub(crate) demand_types: RuntimeDemandTypeInputs,
    pub(crate) callable_activation_inputs: Vec<CallableActivationInput>,
}

/// Settled semantic facts visible to RuntimeDemand; transport metadata is absent.
pub(crate) struct RuntimeDemandFacts<'a> {
    pub(crate) body: &'a LoweredBody,
    pub(crate) extern_wire: Option<&'a LoweredExtern>,
    pub(crate) reachable_clauses: &'a [u32],
    pub(crate) value_types: &'a ValueMap<Ty>,
    /// What this executable's own entry dispatch reads of each input.
    pub(crate) entry_dispatch_demand: &'a [DispatchDemand],
    /// What each multi-destination callsite's own choice between its
    /// destinations reads of its arguments.
    pub(crate) callsite_dispatch_demand: &'a HashMap<CallSiteId, Box<[DispatchDemand]>>,
    pub(crate) callsites: &'a HashMap<CallSiteId, CallSiteSummary>,
    pub(crate) callsite_needs: &'a HashMap<CallSiteId, ExecutableNeed>,
    pub(crate) delivered_value_joins: &'a HashMap<ControlEntryId, DeliveredValueJoin>,
    pub(crate) callable_origins: &'a ValueMap<LocalCallableProducer>,
    pub(crate) demand_types: &'a RuntimeDemandTypeInputs,
    type_projections: &'a HashMap<Ty, Rc<RuntimeDemandTypeProjection>>,
    pub(crate) callable_activation_inputs: &'a [CallableActivationInput],
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum TransportOrigin {
    ExecutableInput(usize),
    LocalValue(ValueId),
    CallsiteReturn(CallSiteId),
    /// A closure-call result's producer. Its carrier is decided later from
    /// the callee value's own transport product.
    ClosureCallReturn {
        callsite: CallSiteId,
        callee: ValueId,
    },
    Join(Box<[TransportOrigin]>),
    TupleValue(Box<[ValueId]>),
    Projection {
        source: ValueId,
        kind: crate::dispatch_matrix::ProjectionKind,
    },
    OutcomeSubject {
        owner: ControlEntryId,
        subject: crate::dispatch_matrix::SubjectId,
    },
    CallableValue(LocalCallableProducer),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct LocalCallableProducer {
    pub(crate) function: FunctionId,
    pub(crate) captures: Box<[ValueId]>,
}

impl ExecutableFacts {
    pub(crate) fn analysis(&self) -> &ActivationAnalysis {
        &self.analysis
    }

    pub(crate) fn body(&self) -> &LoweredBody {
        &self.body
    }

    pub(crate) fn extern_wire(&self) -> Option<&LoweredExtern> {
        self.extern_wire.as_ref()
    }

    pub(crate) fn callsites(&self) -> &HashMap<CallSiteId, CallSiteSummary> {
        &self.callsites
    }

    pub(crate) fn callsite_needs(&self) -> &HashMap<CallSiteId, ExecutableNeed> {
        &self.callsite_needs
    }

    pub(crate) fn entry_dispatch(&self) -> Option<&ExecutableDispatch> {
        self.entry_dispatch.as_ref()
    }

    /// What this executable's own entry dispatch reads of each input. An
    /// executable with no entry dispatch reads nothing.
    pub(crate) fn entry_dispatch_demand(&self) -> &[DispatchDemand] {
        self.entry_dispatch
            .as_ref()
            .map(|dispatch| dispatch.plan().input_demand())
            .unwrap_or_default()
    }

    pub(crate) fn callsite_return_origin(&self, callsite: CallSiteId) -> Option<&TransportOrigin> {
        self.callsite_return_origins.get(&callsite)
    }

    pub(crate) fn value_origin(&self, value: ValueId) -> Option<&TransportOrigin> {
        self.value_origins.get(&value)
    }

    pub(crate) fn return_origins(&self) -> &[TransportOrigin] {
        &self.return_origins
    }

    pub(crate) fn callable_origin(&self, value: ValueId) -> Option<&LocalCallableProducer> {
        self.callable_origins.get(&value)
    }

    pub(crate) fn runtime_demand_facts<'a>(
        &'a self,
        type_projections: &'a HashMap<Ty, Rc<RuntimeDemandTypeProjection>>,
    ) -> RuntimeDemandFacts<'a> {
        RuntimeDemandFacts {
            body: &self.body,
            extern_wire: self.extern_wire.as_ref(),
            reachable_clauses: self.analysis.entry_reachability.clauses(),
            value_types: &self.analysis.value_types,
            entry_dispatch_demand: self.entry_dispatch_demand(),
            callsite_dispatch_demand: &self.callsite_dispatch_demand,
            callsites: &self.callsites,
            callsite_needs: &self.callsite_needs,
            delivered_value_joins: &self.delivered_value_joins,
            callable_origins: &self.callable_origins,
            demand_types: &self.demand_types,
            type_projections,
            callable_activation_inputs: &self.callable_activation_inputs,
        }
    }
}

impl RuntimeDemandFacts<'_> {
    pub(crate) fn callable_origin(&self, value: ValueId) -> Option<&LocalCallableProducer> {
        self.callable_origins.get(&value)
    }

    pub(crate) fn callable_origins(&self) -> impl Iterator<Item = (ValueId, &LocalCallableProducer)> {
        self.callable_origins.iter()
    }

    fn projection(&self, ty: Ty) -> &RuntimeDemandTypeProjection {
        self.type_projections
            .get(&ty)
            .map(Rc::as_ref)
            .unwrap_or_else(|| panic!("World omitted runtime-demand projection for {ty:?}"))
    }

    #[cfg(test)]
    pub(crate) fn projection_identity(&self, ty: Ty) -> *const RuntimeDemandTypeProjection {
        self.projection(ty)
    }

    pub(crate) fn boundary_demand(&self, ty: Ty) -> RuntimeDemand {
        self.projection(ty).boundary.clone()
    }

    /// What this callsite's choice between its destinations reads of each
    /// argument. A callsite with one destination chooses nothing.
    pub(crate) fn callsite_dispatch_demand_of(&self, callsite: CallSiteId) -> &[DispatchDemand] {
        self.callsite_dispatch_demand
            .get(&callsite)
            .map(AsRef::as_ref)
            .unwrap_or_default()
    }

    /// The type a callsite argument carries, as the analysis settled it.
    pub(crate) fn argument_type(&self, value: ValueId) -> Ty {
        argument_type(self.value_types, self.demand_types.any, value)
    }

    pub(crate) fn dispatch_demand(&self, ty: Ty) -> RuntimeDemand {
        self.projection(ty).dispatch.clone()
    }

    pub(crate) fn callable_surfaces(&self, ty: Ty) -> Option<&BTreeSet<CallableSurface>> {
        let resolved = &self.projection(ty).boundary.callable.resolved;
        (!resolved.is_empty()).then_some(resolved)
    }

    pub(crate) fn callable_value_demand(&self, ty: Ty) -> Option<RuntimeDemand> {
        self.projection(ty).callable_value_demand.clone()
    }
}

struct RuntimeDemandTypeBuilder {
    inputs: RuntimeDemandTypeInputs,
    projections: HashMap<Ty, Rc<RuntimeDemandTypeProjection>>,
}

impl RuntimeDemandTypeBuilder {
    fn new(any: Ty) -> Self {
        Self {
            inputs: RuntimeDemandTypeInputs::new(any),
            projections: HashMap::new(),
        }
    }

    fn boundary_demand(&self, ty: Ty) -> RuntimeDemand {
        self.projections[&ty].boundary.clone()
    }

    fn dispatch_demand(&self, ty: Ty) -> RuntimeDemand {
        self.projections[&ty].dispatch.clone()
    }
}

/// Folds one executable's settled semantic inputs into its immutable shared
/// projection. The caller owns readiness and dependency recording; this
/// function owns only value construction.
pub(crate) fn project_executable_facts(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    executable: &ExecutableKey,
    mut analysis: ActivationAnalysis,
) -> Rc<ExecutableFacts> {
    let activation = &executable.activation;
    // An extern has no lowered body -- its wire ABI lives on its contract
    // instead, and everything downstream that walks entries and clauses sees
    // an executable with none of either.
    let (body, extern_wire) = if world.function_body_shape(activation.function).is_extern() {
        (
            LoweredBody::clauses(Vec::new(), Vec::new(), Vec::new()),
            world.extern_wire(activation.function),
        )
    } else {
        let mut body = (*world.lowered_body(activation.function)).clone();
        body.adopt_trimmed_plans(&analysis.trimmed.cases);
        (body, None)
    };
    let callsites: HashMap<_, _> = analysis
        .callsites
        .iter()
        .map(|callsite| {
            let key = CallSiteKey {
                activation: activation.clone(),
                callsite: *callsite,
            };
            (
                *callsite,
                world
                    .callsite_summary(&key)
                    .expect("settled callsite summary fact should have a summary")
                    .clone(),
            )
        })
        .collect();
    complete_settled_call_result_types(world, &body, &callsites, &mut analysis);
    // An extern has no fz control flow to walk: every one of these facts
    // about clauses and entries is empty by construction, rather than
    // derived from an `analysis.entry_reachability` that names clause ids a
    // body-less executable does not have.
    let (
        delivered_value_joins,
        callsite_return_origins,
        value_origins,
        callable_origins,
        return_origins,
        callsite_needs,
    ) = if extern_wire.is_some() {
        (
            HashMap::new(),
            HashMap::new(),
            ValueMap::new(),
            ValueMap::new(),
            Box::default(),
            HashMap::new(),
        )
    } else {
        let delivered_value_joins = delivered_value_joins(&body);
        let callsite_return_origins = collect_callsite_return_origins(&body);
        let value_origins = collect_value_origins(&body, &callsite_return_origins);
        let callable_origins: ValueMap<LocalCallableProducer> = value_origins
            .keys()
            .filter_map(|value| {
                local_callable_origin(&body, &value_origins, value, &[]).map(|producer| (value, producer.clone()))
            })
            .collect();
        let return_origins = collect_return_origins(&body, &analysis);
        let callsite_needs = executable_callsite_needs(
            &body,
            analysis.entry_reachability.clauses(),
            executable.need,
            tel,
            activation.function,
        );
        (
            delivered_value_joins,
            callsite_return_origins,
            value_origins,
            callable_origins,
            return_origins,
            callsite_needs,
        )
    };
    let entry_dispatch = executable_dispatch(&analysis);
    let entry_dispatch_demand = entry_dispatch
        .as_ref()
        .map(|dispatch| dispatch.plan().input_demand())
        .unwrap_or_default();
    let callsite_dispatch_demand = callsite_dispatch_demands(world.types_mut(), &callsites);
    let mut demand_builder = prepare_runtime_demand_type_inputs(
        world,
        executable,
        &analysis,
        &body,
        extern_wire.as_ref(),
        entry_dispatch_demand,
        &callsite_dispatch_demand,
        &callsites,
    );
    let capture_count = world.activation_capture_count(&executable.activation);
    let capture_called_with_own_surface = captured_inputs_called_with_own_surface(&body, capture_count);
    let callable_activation_inputs = analysis
        .input_rows
        .iter()
        .filter(|row| row.len() >= capture_count)
        .map(|row| {
            let captures = world.types_mut().address_inputs(&row[..capture_count]);
            let surface = prepare_surface(world, &mut demand_builder, &row[capture_count..]).clone();
            CallableActivationInput {
                captures,
                surface,
                capture_called_with_own_surface: capture_called_with_own_surface.clone(),
            }
        })
        .collect();
    let demand_types = demand_builder.inputs;
    Rc::new(ExecutableFacts {
        analysis,
        body,
        extern_wire,
        entry_dispatch,
        callsite_dispatch_demand,
        callsites,
        callsite_needs,
        delivered_value_joins,
        callsite_return_origins,
        value_origins,
        callable_origins,
        return_origins,
        demand_types,
        callable_activation_inputs,
    })
}

/// Close the one semantic distinction that disappears at this boundary.
///
/// During chaotic iteration, an absent call return means "no evidence yet",
/// so activation analysis must not manufacture a type for the result. Every
/// callsite summary read here is settled, however: an absent return now means
/// the callee provably never returns. Record that result as the empty type so
/// structurally retained delivered-resume entries still have a truthful ABI.
fn complete_settled_call_result_types(
    world: &mut World,
    body: &LoweredBody,
    callsites: &HashMap<CallSiteId, CallSiteSummary>,
    analysis: &mut ActivationAnalysis,
) {
    let LoweredBody::Clauses { entries, .. } = body;
    let none = world.types_mut().none();
    for entry in entries {
        let (value, callsite) = match &entry.tail {
            LoweredTail::DirectCall { value, callsite, .. } | LoweredTail::ClosureCall { value, callsite, .. } => {
                (*value, *callsite)
            }
            LoweredTail::Value { .. }
            | LoweredTail::If { .. }
            | LoweredTail::Dispatch { .. }
            | LoweredTail::Receive(_)
            | LoweredTail::Try { .. }
            | LoweredTail::Unreachable => continue,
        };
        if callsites
            .get(&callsite)
            .is_some_and(|summary| summary.return_ty.is_none())
        {
            analysis.value_types.entry(value).or_insert(none);
        }
    }
}

/// What each callsite with several destinations reads of its arguments to
/// choose among them: the demand of the same plan lowering dispatches by.
/// A callsite whose plan cannot be built reads nothing here; lowering builds
/// the same plan and reports that failure as the program's diagnostic.
pub(crate) fn callsite_dispatch_demands(
    types: &mut Types,
    callsites: &HashMap<CallSiteId, CallSiteSummary>,
) -> HashMap<CallSiteId, Box<[DispatchDemand]>> {
    callsites
        .iter()
        .filter(|(_, summary)| summary.targets.len() > 1)
        .filter_map(|(&callsite, summary)| match call_destinations(types, summary) {
            Ok(CallDestinations::Dispatch(dispatch)) => Some((callsite, dispatch.plan.input_demand().into())),
            Ok(CallDestinations::Direct(_) | CallDestinations::None) | Err(_) => None,
        })
        .collect()
}

fn argument_type(value_types: &ValueMap<Ty>, any: Ty, value: ValueId) -> Ty {
    value_types.get(&value).copied().unwrap_or(any)
}

fn prepare_runtime_demand_type_inputs(
    world: &mut World,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    body: &LoweredBody,
    extern_wire: Option<&LoweredExtern>,
    entry_dispatch_demand: &[DispatchDemand],
    callsite_dispatch_demand: &HashMap<CallSiteId, Box<[DispatchDemand]>>,
    callsites: &HashMap<CallSiteId, CallSiteSummary>,
) -> RuntimeDemandTypeBuilder {
    let any = world.types_mut().any();
    let mut builder = RuntimeDemandTypeBuilder::new(any);
    let mut tys = analysis.value_types.values().copied().collect::<HashSet<_>>();
    let activation_inputs = executable.activation.inputs(world.types());
    tys.extend(
        entry_dispatch_demand
            .iter()
            .enumerate()
            .filter(|(_, demand)| demand.asks_anything())
            .filter_map(|(index, _)| activation_inputs.get(index).copied()),
    );
    let call_args = callsite_call_args(body);
    for (callsite, demands) in callsite_dispatch_demand {
        let args = call_args.get(callsite).copied().unwrap_or_default();
        tys.extend(
            args.iter()
                .zip(demands.iter())
                .filter(|(_, demand)| demand.asks_anything())
                .map(|(arg, _)| argument_type(&analysis.value_types, any, arg.value)),
        );
    }
    if let Some(signature) = extern_wire {
        tys.extend(activation_inputs.iter().skip(signature.params.len()).copied());
    }
    for summary in callsites.values() {
        for target in &summary.targets {
            tys.extend(target.surface_inputs.iter().copied());
            prepare_surface(world, &mut builder, &target.surface_inputs);
        }
    }
    let LoweredBody::Clauses { entries, .. } = body;
    for entry in entries {
        if let LoweredTail::ClosureCall { args, .. } = &entry.tail {
            let actual_inputs = args
                .iter()
                .map(|arg| analysis.value_types.get(&arg.value).copied().unwrap_or(any))
                .collect::<Vec<_>>();
            tys.extend(actual_inputs.iter().copied());
            prepare_surface(world, &mut builder, &actual_inputs);
        }
    }
    for ty in tys {
        prepare_type_projection(world, &mut builder, ty);
    }
    builder
}

/// Records the surface a consumer of this executable's facts looks up by its
/// raw inputs: a callsite target's, a closure call's or an activation row's.
/// Surfaces nested inside a type's projection travel in that projection and
/// are never recorded here, so what is recorded does not depend on which
/// projections were memoized.
fn prepare_surface<'a>(
    world: &mut World,
    builder: &'a mut RuntimeDemandTypeBuilder,
    surface_inputs: &[Ty],
) -> &'a CallableSurface {
    let surface = resolve_surface(world, builder, surface_inputs);
    let surfaces = &mut builder.inputs.surfaces;
    surfaces
        .entry(surface.inputs.clone())
        .or_insert_with(|| surface.clone());
    surfaces.insert(surface_inputs.to_vec(), surface);
    &surfaces[surface_inputs]
}

fn resolve_surface(
    world: &mut World,
    builder: &mut RuntimeDemandTypeBuilder,
    surface_inputs: &[Ty],
) -> CallableSurface {
    for &ty in surface_inputs {
        prepare_type_projection(world, builder, ty);
    }
    let surface = CallableSurface::new(surface_inputs.to_vec(), world.types_mut());
    for &ty in &surface.inputs {
        prepare_type_projection(world, builder, ty);
    }
    surface
}

fn prepare_type_projection(world: &mut World, builder: &mut RuntimeDemandTypeBuilder, ty: Ty) {
    if builder.projections.contains_key(&ty) {
        return;
    }
    if let Some(projection) = world.runtime_demand_type_projection(ty).cloned() {
        builder.projections.insert(ty, projection);
        return;
    }
    builder.projections.insert(
        ty,
        Rc::new(RuntimeDemandTypeProjection {
            boundary: RuntimeDemand::whole(),
            dispatch: RuntimeDemand::whole(),
            callable_value_demand: None,
        }),
    );
    let boundary = prepare_runtime_demand_for_type(world, builder, ty, true);
    let dispatch = prepare_runtime_demand_for_type(world, builder, ty, false);
    let callable_value_demand = world.types_mut().callable_value_clauses(&ty).and_then(|clauses| {
        let resolved = clauses
            .into_iter()
            .map(|clause| resolve_surface(world, builder, &clause.args))
            .collect::<BTreeSet<_>>();
        (!resolved.is_empty()).then(|| {
            RuntimeDemand::callable(CallableDemand {
                resolved,
                ..CallableDemand::default()
            })
        })
    });
    let projection = RuntimeDemandTypeProjection {
        boundary,
        dispatch,
        callable_value_demand,
    };
    let projection = world.memoize_runtime_demand_type_projection(ty, projection);
    builder.projections.insert(ty, projection);
}

/// What a value of this type needs when it crosses a boundary (`escape`) or is
/// inspected by a choice, which holds a callable whole and never calls it.
fn prepare_runtime_demand_for_type(
    world: &mut World,
    builder: &mut RuntimeDemandTypeBuilder,
    ty: Ty,
    escape: bool,
) -> RuntimeDemand {
    let Some(clauses) = world.types_mut().callable_clauses(&ty) else {
        let predicate = world.types().runtime_type_predicate(&ty);
        if !predicate.tuples.arities().cofinite && predicate.tuples.arities().values.len() == 1 {
            let arity = *predicate
                .tuples
                .arities()
                .values
                .iter()
                .next()
                .expect("one exact tuple arity");
            let any = builder.inputs.any;
            let mut fields = world.types_mut().tuple_projections(&ty, arity);
            fields.resize(arity, any);
            fields.truncate(arity);
            let demands = fields
                .into_iter()
                .map(|field| {
                    prepare_type_projection(world, builder, field);
                    if escape {
                        builder.boundary_demand(field)
                    } else {
                        builder.dispatch_demand(field)
                    }
                })
                .collect();
            return read_tuple_demand(demands);
        }
        return RuntimeDemand::whole();
    };
    if !escape {
        return RuntimeDemand::whole();
    }
    let resolved = clauses
        .into_iter()
        .map(|clause| resolve_surface(world, builder, &clause.args))
        .collect();
    RuntimeDemand::callable(CallableDemand {
        resolved,
        targets: BTreeSet::new(),
        opaque: false,
        escape: true,
    })
}

/// A tuple whose fields are all ignored is still a value that was read, so it
/// stays present as a whole value; it has no lanes, so presence costs nothing.
fn read_tuple_demand(field_demands: Vec<RuntimeDemand>) -> RuntimeDemand {
    let fields = RuntimeDemand::tuple_fields(field_demands);
    if fields.is_ignore() {
        RuntimeDemand::whole()
    } else {
        fields
    }
}

/// The dispatch an executable runs to pick its clause: the entry plan its
/// activation's types leave. A plan that wins its one outcome without asking
/// anything selects nothing, and an extern has no clauses to select among.
fn executable_dispatch(analysis: &ActivationAnalysis) -> Option<ExecutableDispatch> {
    let plan = analysis.trimmed.entry.as_ref()?;
    if plan.is_direct_outcome() {
        return None;
    }
    Some(ExecutableDispatch::new(
        plan.clone(),
        analysis.entry_reachability.clauses().to_vec(),
    ))
}

fn captured_inputs_called_with_own_surface(body: &LoweredBody, capture_count: usize) -> Box<[bool]> {
    let LoweredBody::Clauses { clauses, entries, .. } = body;
    (0..capture_count)
        .map(|capture_index| {
            clauses.iter().any(|clause| {
                let Some(&callee_param) = clause.params.get(capture_index) else {
                    return false;
                };
                let own_params = clause.params.iter().skip(capture_count).copied();
                entries.iter().any(|entry| match &entry.tail {
                    LoweredTail::ClosureCall { callee, args, .. } if *callee == callee_param => {
                        args.iter().map(|arg| arg.value).eq(own_params.clone())
                    }
                    _ => false,
                })
            })
        })
        .collect()
}

/// One walk's memo: an entry reached again with the same outgoing need
/// answers with the same tuple arity it already recorded, because that
/// answer is derived from nothing else. The first arrival walks and records
/// the answer (including its callsite need, via [`record_callsite_need`]); a
/// later arrival with an equal outgoing need reuses the stored answer and
/// walks nothing below it. The table lives for one
/// [`executable_callsite_needs`] call and is never published.
#[derive(Default)]
struct CallsiteNeedWalkTable {
    answers: HashMap<(ControlEntryId, ExecutableNeed), Option<usize>>,
    /// How many entries this walk actually visited, as opposed to answered
    /// from the memo. [`emit_executable_facts_walk`] reports it.
    entries_walked: u64,
}

impl CallsiteNeedWalkTable {
    fn new() -> Self {
        Self::default()
    }

    fn get(&self, key: &(ControlEntryId, ExecutableNeed)) -> Option<Option<usize>> {
        self.answers.get(key).copied()
    }

    fn record(&mut self, key: (ControlEntryId, ExecutableNeed), answer: Option<usize>) {
        self.answers.insert(key, answer);
        self.entries_walked += 1;
    }
}

/// How many distinct (entry, outgoing need) pairs this walk actually
/// visited. A join reached again with a need the walk table already answered
/// costs nothing further, so this count grows with the entries the body
/// contains rather than with the number of paths that reach them.
fn emit_executable_facts_walk(tel: &impl crate::telemetry::Telemetry, function: FunctionId, entries_walked: u64) {
    tel.dispatch(
        &["fz", "compiler2", "executable_facts", "walk"],
        &crate::measurements! { entries_walked: entries_walked },
        &crate::metadata! { function_id: u64::from(function.as_u32()) },
    );
}

fn executable_callsite_needs(
    body: &LoweredBody,
    reachable_clauses: &[u32],
    executable_need: ExecutableNeed,
    tel: &impl crate::telemetry::Telemetry,
    function: FunctionId,
) -> HashMap<CallSiteId, ExecutableNeed> {
    let mut needs = HashMap::new();
    let LoweredBody::Clauses { clauses, entries, .. } = body;
    let mut walks = CallsiteNeedWalkTable::new();
    for clause_id in reachable_clauses {
        collect_clause_callsite_needs(
            &clauses[*clause_id as usize],
            entries,
            executable_need,
            &mut needs,
            &mut walks,
        );
    }
    emit_executable_facts_walk(tel, function, walks.entries_walked);
    needs
}

fn collect_clause_callsite_needs(
    clause: &LoweredClause,
    entries: &[LoweredEntry],
    executable_need: ExecutableNeed,
    out: &mut HashMap<CallSiteId, ExecutableNeed>,
    walks: &mut CallsiteNeedWalkTable,
) {
    collect_entry_callsite_needs(entries, clause.entry, executable_need, out, walks);
}

fn collect_entry_callsite_needs(
    entries: &[LoweredEntry],
    entry_id: ControlEntryId,
    outgoing_need: ExecutableNeed,
    out: &mut HashMap<CallSiteId, ExecutableNeed>,
    walks: &mut CallsiteNeedWalkTable,
) -> Option<usize> {
    // What this entry answers depends only on itself and the need flowing out
    // of it. A join reached again with the same outgoing need answers with
    // the arity it already recorded -- walking it again would record nothing
    // new (`record_callsite_need` joins by union), so the second arrival just
    // returns the stored answer.
    let key = (entry_id, outgoing_need);
    if let Some(answer) = walks.get(&key) {
        return answer;
    }
    let entry = &entries[entry_id.as_u32() as usize];
    let mut tuple_demands = ValueMap::new();
    match &entry.tail {
        LoweredTail::Value { value, dest } => {
            if let Some(arity) = destination_need(entries, dest, outgoing_need, out, walks) {
                tuple_demands.insert(*value, arity);
            }
        }
        LoweredTail::DirectCall {
            value, callsite, dest, ..
        }
        | LoweredTail::ClosureCall {
            value, callsite, dest, ..
        } => {
            let need = destination_need(entries, dest, outgoing_need, out, walks)
                .map(ExecutableNeed::TupleFields)
                .unwrap_or(ExecutableNeed::Value);
            record_callsite_need(out, *callsite, need);
            if let ExecutableNeed::TupleFields(arity) = need {
                tuple_demands.insert(*value, arity);
            }
        }
        LoweredTail::If {
            then_entry, else_entry, ..
        } => {
            let _ = collect_entry_callsite_needs(entries, *then_entry, outgoing_need, out, walks);
            let _ = collect_entry_callsite_needs(entries, *else_entry, outgoing_need, out, walks);
        }
        LoweredTail::Dispatch { inputs, dispatch, .. } => {
            for target in dispatch.successors() {
                let _ = collect_entry_callsite_needs(entries, target, outgoing_need, out, walks);
            }
            // A decision that cannot fail, and whose every outcome proves its
            // input to be an N-tuple, reads that input as N fields.
            if !dispatch.plan.can_fail() {
                for (ordinal, input) in inputs.iter().enumerate() {
                    if let Some(arity) = dispatch.plan.proven_tuple_arity(ordinal) {
                        tuple_demands.insert(*input, arity);
                    }
                }
            }
        }
        LoweredTail::Receive(receive) => {
            for clause in &receive.outcomes {
                let _ = collect_entry_callsite_needs(entries, clause.target, outgoing_need, out, walks);
            }
            if let Some(after) = &receive.after {
                let _ = collect_entry_callsite_needs(entries, after.entry, outgoing_need, out, walks);
            }
        }
        LoweredTail::Try { body, handler } => {
            let _ = collect_entry_callsite_needs(entries, *body, outgoing_need, out, walks);
            let _ = collect_entry_callsite_needs(entries, *handler, outgoing_need, out, walks);
        }
        LoweredTail::Unreachable => {}
    }
    for step in entry.steps.iter().rev() {
        match step {
            LoweredStep::Const { value, .. }
            | LoweredStep::Tuple { value, .. }
            | LoweredStep::List { value, .. }
            | LoweredStep::Map { value, .. }
            | LoweredStep::Struct { value, .. }
            | LoweredStep::Bitstring { value, .. }
            | LoweredStep::FunctionRef { value, .. }
            | LoweredStep::Lambda { value, .. }
            | LoweredStep::BinaryOp { value, .. }
            | LoweredStep::UnaryOp { value, .. }
            | LoweredStep::MapIndex { value, .. }
            | LoweredStep::FieldAccess { value, .. }
            | LoweredStep::RequireMapValue { value, .. }
            | LoweredStep::TupleField { value, .. } => {
                tuple_demands.remove(value);
            }
            LoweredStep::MapUpdate { value, ok, .. } => {
                tuple_demands.remove(value);
                tuple_demands.remove(ok);
            }
            LoweredStep::SplitList { head, tail, .. } => {
                tuple_demands.remove(head);
                tuple_demands.remove(tail);
            }
            LoweredStep::BitstringInit { reader, .. } => {
                tuple_demands.remove(reader);
            }
            LoweredStep::BitstringRead {
                ok, value, next_reader, ..
            } => {
                tuple_demands.remove(ok);
                tuple_demands.remove(value);
                tuple_demands.remove(next_reader);
            }
            LoweredStep::PopHandler => {}
        }
    }
    let answer = entry
        .origin
        .input_value()
        .and_then(|value| tuple_demands.remove(&value));
    walks.record(key, answer);
    answer
}

fn destination_need(
    entries: &[LoweredEntry],
    dest: &ControlDestination,
    outgoing_need: ExecutableNeed,
    out: &mut HashMap<CallSiteId, ExecutableNeed>,
    walks: &mut CallsiteNeedWalkTable,
) -> Option<usize> {
    match dest {
        ControlDestination::Return => match outgoing_need {
            ExecutableNeed::Value => None,
            ExecutableNeed::TupleFields(arity) => Some(arity),
        },
        ControlDestination::Deliver(entry_id) => {
            collect_entry_callsite_needs(entries, *entry_id, outgoing_need, out, walks)
        }
    }
}

fn record_callsite_need(out: &mut HashMap<CallSiteId, ExecutableNeed>, callsite: CallSiteId, observed: ExecutableNeed) {
    use std::collections::hash_map::Entry;
    match out.entry(callsite) {
        Entry::Vacant(entry) => {
            entry.insert(observed);
        }
        Entry::Occupied(mut entry) => match (*entry.get(), observed) {
            (ExecutableNeed::Value, ExecutableNeed::Value)
            | (ExecutableNeed::TupleFields(_), ExecutableNeed::Value) => {}
            (ExecutableNeed::Value, tuple_fields @ ExecutableNeed::TupleFields(_)) => {
                entry.insert(tuple_fields);
            }
            (ExecutableNeed::TupleFields(existing), ExecutableNeed::TupleFields(observed)) => {
                assert_eq!(
                    existing, observed,
                    "one callsite cannot require two different tuple-field return arities"
                );
            }
        },
    }
}

pub(crate) fn collect_callsite_return_origins(body: &LoweredBody) -> HashMap<CallSiteId, TransportOrigin> {
    let mut origins = HashMap::new();
    let LoweredBody::Clauses { entries, .. } = body;
    for entry in entries {
        match entry.tail {
            LoweredTail::DirectCall { callsite, .. } => {
                origins.insert(callsite, TransportOrigin::CallsiteReturn(callsite));
            }
            LoweredTail::ClosureCall { callsite, callee, .. } => {
                origins.insert(callsite, TransportOrigin::ClosureCallReturn { callsite, callee });
            }
            _ => {}
        }
    }
    origins
}

fn local_callable_origin<'a>(
    body: &LoweredBody,
    origins: &'a ValueMap<TransportOrigin>,
    value: ValueId,
    path: &[&crate::dispatch_matrix::ProjectionKind],
) -> Option<&'a LocalCallableProducer> {
    local_callable_origin_from(body, origins, origins.get(&value)?, path)
}

fn local_callable_origin_from<'a>(
    body: &LoweredBody,
    origins: &'a ValueMap<TransportOrigin>,
    origin: &'a TransportOrigin,
    path: &[&crate::dispatch_matrix::ProjectionKind],
) -> Option<&'a LocalCallableProducer> {
    use crate::dispatch_matrix::ProjectionKind;
    match origin {
        TransportOrigin::CallableValue(producer) if path.is_empty() => Some(producer),
        TransportOrigin::LocalValue(value) => local_callable_origin(body, origins, *value, path),
        TransportOrigin::Projection { source, kind } => {
            let path = std::iter::once(kind).chain(path.iter().copied()).collect::<Vec<_>>();
            local_callable_origin(body, origins, *source, &path)
        }
        TransportOrigin::OutcomeSubject { owner, subject } => {
            let (source, mut prefix) = body.dispatch_subject_origin(*owner, *subject);
            prefix.extend(path.iter().copied());
            match source {
                super::body::SubjectOriginRoot::Value(source) => local_callable_origin(body, origins, source, &prefix),
                super::body::SubjectOriginRoot::MailboxMessage(_) => None,
            }
        }
        TransportOrigin::TupleValue(items) => {
            let (ProjectionKind::TupleField(index), tail) = path.split_first()? else {
                return None;
            };
            local_callable_origin(body, origins, *items.get(*index as usize)?, tail)
        }
        TransportOrigin::Join(alternatives) => {
            let mut producers = alternatives
                .iter()
                .map(|origin| local_callable_origin_from(body, origins, origin, path));
            let first = producers.next()??;
            producers.all(|producer| producer == Some(first)).then_some(first)
        }
        _ => None,
    }
}

pub(crate) fn collect_value_origins(
    body: &LoweredBody,
    callsite_return_origins: &HashMap<CallSiteId, TransportOrigin>,
) -> ValueMap<TransportOrigin> {
    let mut origins = ValueMap::new();
    let LoweredBody::Clauses { clauses, entries, .. } = body;
    for clause in clauses {
        for step in &clause.projections {
            for (value, origin) in step_transport_origins(step) {
                origins.insert(value, origin);
            }
        }
        for (semantic_index, value) in clause.params.iter().copied().enumerate() {
            origins.insert(value, TransportOrigin::ExecutableInput(semantic_index));
        }
    }
    for (owner, entry) in entries.iter().enumerate() {
        for step in &entry.steps {
            for (value, origin) in step_transport_origins(step) {
                origins.insert(value, origin);
            }
        }
        for edge in entry.tail.outcome_edges() {
            for argument in &edge.arguments {
                origins.insert(
                    argument.parameter,
                    TransportOrigin::OutcomeSubject {
                        owner: ControlEntryId::from_u32(owner as u32),
                        subject: argument.subject,
                    },
                );
            }
        }
        match entry.tail {
            LoweredTail::DirectCall { value, callsite, .. } | LoweredTail::ClosureCall { value, callsite, .. } => {
                origins.insert(
                    value,
                    callsite_return_origins
                        .get(&callsite)
                        .expect("every lowered callsite must have a normalized return origin")
                        .clone(),
                );
            }
            _ => {}
        }
    }
    for join in delivered_value_joins(body).into_values() {
        let mut sources = join
            .sources
            .into_iter()
            .map(|source| match source {
                DeliveredValueSource::LocalValue(value) => TransportOrigin::LocalValue(value),
                DeliveredValueSource::CallsiteReturn(callsite) => callsite_return_origins
                    .get(&callsite)
                    .expect("every delivered callsite return must have a normalized origin")
                    .clone(),
            })
            .collect::<Vec<_>>();
        sources.sort_by_key(|source| match source {
            TransportOrigin::LocalValue(value) => (0, value.as_u32()),
            TransportOrigin::CallsiteReturn(callsite) => (1, callsite.as_u32()),
            TransportOrigin::ClosureCallReturn { callsite, .. } => (2, callsite.as_u32()),
            _ => unreachable!(),
        });
        sources.dedup();
        let origin = match sources.as_slice() {
            [source] => source.clone(),
            _ => TransportOrigin::Join(sources.into_boxed_slice()),
        };
        origins.insert(join.value, origin);
    }
    origins
}

fn step_transport_origins(step: &LoweredStep) -> Vec<(ValueId, TransportOrigin)> {
    use crate::dispatch_matrix::ProjectionKind;
    let projection = |value, source, kind| (value, TransportOrigin::Projection { source, kind });
    let origin = match step {
        LoweredStep::Tuple { value, items } => (
            *value,
            TransportOrigin::TupleValue(items.iter().map(|item| item.value).collect()),
        ),
        LoweredStep::TupleField { value, source, index } => {
            projection(*value, *source, ProjectionKind::TupleField(*index as u32))
        }
        LoweredStep::FieldAccess { value, base, field } => {
            projection(*value, *base, ProjectionKind::StructField(field.clone()))
        }
        LoweredStep::RequireMapValue { value, source, key } => {
            projection(*value, *source, ProjectionKind::MapValue { key: key.clone() })
        }
        LoweredStep::SplitList { source, head, tail } => {
            return vec![
                projection(*head, *source, ProjectionKind::ListHead),
                projection(*tail, *source, ProjectionKind::ListTail),
            ];
        }
        LoweredStep::FunctionRef { value, function } => (
            *value,
            TransportOrigin::CallableValue(LocalCallableProducer {
                function: *function,
                captures: Box::default(),
            }),
        ),
        LoweredStep::Lambda {
            value,
            function,
            captures,
        } => (
            *value,
            TransportOrigin::CallableValue(LocalCallableProducer {
                function: *function,
                captures: captures.clone().into_boxed_slice(),
            }),
        ),
        _ => return Vec::new(),
    };
    vec![origin]
}

fn collect_return_origins(body: &LoweredBody, analysis: &ActivationAnalysis) -> Box<[TransportOrigin]> {
    let LoweredBody::Clauses { clauses, entries, .. } = body;
    let reachable = analysis.reachable_entries.iter().copied().collect::<HashSet<_>>();
    let mut seen = HashSet::new();
    let mut origins = Vec::new();
    let mut pending = analysis
        .entry_reachability
        .clauses()
        .iter()
        .map(|clause| clauses[*clause as usize].entry)
        .collect::<Vec<_>>();
    while let Some(entry_id) = pending.pop() {
        if !reachable.contains(&entry_id) || !seen.insert(entry_id) {
            continue;
        }
        match &entries[entry_id.as_u32() as usize].tail {
            LoweredTail::Value {
                value,
                dest: ControlDestination::Return,
            } => origins.push(TransportOrigin::LocalValue(*value)),
            LoweredTail::DirectCall {
                callsite,
                dest: ControlDestination::Return,
                ..
            } => origins.push(TransportOrigin::CallsiteReturn(*callsite)),
            LoweredTail::ClosureCall {
                callsite,
                callee,
                dest: ControlDestination::Return,
                ..
            } => origins.push(TransportOrigin::ClosureCallReturn {
                callsite: *callsite,
                callee: *callee,
            }),
            LoweredTail::Value {
                dest: ControlDestination::Deliver(target),
                ..
            }
            | LoweredTail::DirectCall {
                dest: ControlDestination::Deliver(target),
                ..
            }
            | LoweredTail::ClosureCall {
                dest: ControlDestination::Deliver(target),
                ..
            } => pending.push(*target),
            LoweredTail::If {
                then_entry, else_entry, ..
            } => pending.extend([*then_entry, *else_entry]),
            LoweredTail::Dispatch { dispatch, .. } => {
                pending.extend(dispatch.successors());
            }
            LoweredTail::Receive(receive) => {
                pending.extend(receive.outcomes.iter().map(|edge| edge.target));
                pending.extend(receive.after.iter().map(|after| after.entry));
                if let ControlDestination::Deliver(target) = receive.dest {
                    pending.push(target);
                }
            }
            LoweredTail::Try { body, handler } => pending.extend([*body, *handler]),
            LoweredTail::Unreachable => {}
        }
    }
    origins.into_boxed_slice()
}

#[cfg(test)]
#[path = "executable_facts_test.rs"]
mod executable_facts_test;
