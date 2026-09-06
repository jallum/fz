//! Immutable executable-scoped semantic projection.
//!
//! `ExecutableFacts(E)` is semantic truth owned by [`World`](super::World),
//! independent of any product session. The scheduler job that publishes the
//! fact gathers its settled inputs; product producers only read this value.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use super::artifact::ExecutableDispatch;
use super::body::{
    CallSiteId, ControlDestination, ControlEntryId, DeliveredValueJoin, DeliveredValueSource, LoweredBody,
    LoweredClause, LoweredEntry, LoweredStep, LoweredTail, ValueId, delivered_value_joins,
};
use super::identity::{ExecutableKey, ExecutableNeed, FunctionId};
use super::semantic::{
    ActivationAnalysis, CallSiteKey, CallSiteSummary, CallableActivationInput, CallableDemand, CallableSurface,
    EntryReachability, RuntimeDemand, RuntimeDemandTypeInputs, RuntimeDemandTypeProjection,
};
use super::types::Ty;
use super::world::World;

#[cfg_attr(test, derive(Clone))]
#[derive(Debug, PartialEq)]
pub(crate) struct ExecutableFacts {
    pub(super) analysis: ActivationAnalysis,
    pub(super) body: LoweredBody,
    pub(super) entry_dispatch: Option<ExecutableDispatch>,
    pub(super) entry_dispatch_inputs: HashSet<usize>,
    pub(super) callsites: HashMap<CallSiteId, CallSiteSummary>,
    pub(super) callsite_needs: HashMap<CallSiteId, ExecutableNeed>,
    pub(super) delivered_value_joins: HashMap<ControlEntryId, DeliveredValueJoin>,
    pub(super) callsite_return_origins: HashMap<CallSiteId, TransportOrigin>,
    pub(super) value_origins: HashMap<ValueId, TransportOrigin>,
    pub(super) callable_origins: HashMap<ValueId, LocalCallableProducer>,
    pub(super) return_origins: Box<[TransportOrigin]>,
    pub(crate) demand_types: RuntimeDemandTypeInputs,
    pub(crate) callable_activation_inputs: Vec<CallableActivationInput>,
}

/// Settled semantic facts visible to RuntimeDemand; transport metadata is absent.
pub(crate) struct RuntimeDemandFacts<'a> {
    pub(crate) body: &'a LoweredBody,
    pub(crate) reachable_clauses: &'a [u32],
    pub(crate) value_types: &'a HashMap<ValueId, Ty>,
    pub(crate) entry_dispatch_inputs: &'a HashSet<usize>,
    pub(crate) callsites: &'a HashMap<CallSiteId, CallSiteSummary>,
    pub(crate) callsite_needs: &'a HashMap<CallSiteId, ExecutableNeed>,
    pub(crate) delivered_value_joins: &'a HashMap<ControlEntryId, DeliveredValueJoin>,
    pub(crate) callable_origins: &'a HashMap<ValueId, LocalCallableProducer>,
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
    TupleField {
        source: ValueId,
        index: usize,
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

    pub(crate) fn callsites(&self) -> &HashMap<CallSiteId, CallSiteSummary> {
        &self.callsites
    }

    pub(crate) fn callsite_needs(&self) -> &HashMap<CallSiteId, ExecutableNeed> {
        &self.callsite_needs
    }

    pub(crate) fn entry_dispatch(&self) -> Option<&ExecutableDispatch> {
        self.entry_dispatch.as_ref()
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
            reachable_clauses: self.analysis.entry_reachability.clauses(),
            value_types: &self.analysis.value_types,
            entry_dispatch_inputs: &self.entry_dispatch_inputs,
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

    pub(crate) fn callable_origins(&self) -> impl Iterator<Item = (&ValueId, &LocalCallableProducer)> {
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
    executable: &ExecutableKey,
    analysis: ActivationAnalysis,
) -> Rc<ExecutableFacts> {
    let activation = &executable.activation;
    let body = world.lowered_body(activation.function);
    let callsites = analysis
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
    let delivered_value_joins = delivered_value_joins(&body);
    let callsite_return_origins = collect_callsite_return_origins(&body);
    let value_origins = collect_value_origins(&body, &callsite_return_origins);
    let callable_origins: HashMap<ValueId, LocalCallableProducer> = value_origins
        .iter()
        .filter_map(|(&value, origin)| match origin {
            TransportOrigin::CallableValue(producer) => Some((value, producer.clone())),
            _ => None,
        })
        .collect();
    let return_origins = collect_return_origins(&body, &analysis);
    let entry_dispatch = executable_dispatch(world, activation.function, &analysis.entry_reachability);
    let entry_dispatch_inputs = entry_dispatch
        .as_ref()
        .map(ExecutableDispatch::required_input_ordinals)
        .unwrap_or_default();
    let callsite_needs = executable_callsite_needs(&body, analysis.entry_reachability.clauses(), executable.need);
    let mut demand_builder =
        prepare_runtime_demand_type_inputs(world, executable, &analysis, &body, &entry_dispatch_inputs, &callsites);
    let capture_count = executable
        .activation
        .input_len(world.types())
        .saturating_sub(world.function_arity(executable.activation.function));
    let capture_called_with_own_surface = captured_inputs_called_with_own_surface(&body, capture_count);
    let callable_activation_inputs = analysis
        .input_rows
        .iter()
        .filter(|row| row.len() >= capture_count)
        .map(|row| {
            let captures = world.types_mut().address_inputs(&row[..capture_count]);
            let surface = prepare_surface(world, &mut demand_builder, &row[capture_count..]);
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
        entry_dispatch,
        entry_dispatch_inputs,
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

fn prepare_runtime_demand_type_inputs(
    world: &mut World,
    executable: &ExecutableKey,
    analysis: &ActivationAnalysis,
    body: &LoweredBody,
    entry_dispatch_inputs: &HashSet<usize>,
    callsites: &HashMap<CallSiteId, CallSiteSummary>,
) -> RuntimeDemandTypeBuilder {
    let any = world.types_mut().any();
    let mut builder = RuntimeDemandTypeBuilder::new(any);
    let mut tys = analysis.value_types.values().copied().collect::<HashSet<_>>();
    let activation_inputs = executable.activation.inputs(world.types());
    tys.extend(
        entry_dispatch_inputs
            .iter()
            .filter_map(|index| activation_inputs.get(*index).copied()),
    );
    if let LoweredBody::Extern { signature } = body {
        tys.extend(activation_inputs.iter().skip(signature.params.len()).copied());
    }
    for summary in callsites.values() {
        for target in &summary.targets {
            tys.extend(target.surface_inputs.iter().copied());
            prepare_surface(world, &mut builder, &target.surface_inputs);
        }
    }
    if let LoweredBody::Clauses { entries, .. } = body {
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
    }
    for ty in tys {
        prepare_type_projection(world, &mut builder, ty);
    }
    builder
}

fn prepare_surface(
    world: &mut World,
    builder: &mut RuntimeDemandTypeBuilder,
    surface_inputs: &[Ty],
) -> CallableSurface {
    for &ty in surface_inputs {
        prepare_type_projection(world, builder, ty);
    }
    if let Some(surface) = builder.inputs.surfaces.get(surface_inputs) {
        return surface.clone();
    }
    let surface = CallableSurface::new(surface_inputs.to_vec(), world.types_mut());
    for &ty in &surface.inputs {
        prepare_type_projection(world, builder, ty);
    }
    builder.inputs.surfaces.insert(surface_inputs.to_vec(), surface.clone());
    builder
        .inputs
        .surfaces
        .entry(surface.inputs.clone())
        .or_insert_with(|| surface.clone());
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
            .map(|clause| prepare_surface(world, builder, &clause.args))
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
            return RuntimeDemand::tuple_fields(demands);
        }
        return RuntimeDemand::whole();
    };
    let resolved = clauses
        .into_iter()
        .map(|clause| prepare_surface(world, builder, &clause.args))
        .collect();
    RuntimeDemand::callable(CallableDemand {
        resolved,
        targets: BTreeSet::new(),
        opaque: false,
        escape,
    })
}

fn executable_dispatch(
    world: &World,
    function: FunctionId,
    reachability: &EntryReachability,
) -> Option<ExecutableDispatch> {
    if reachability.is_direct_clause() {
        return None;
    }
    match world.lowered_body(function) {
        LoweredBody::Extern { .. } => None,
        LoweredBody::Clauses { .. } => Some(ExecutableDispatch::new(
            world.entry_dispatch(function),
            reachability.clauses().to_vec(),
        )),
    }
}

fn captured_inputs_called_with_own_surface(body: &LoweredBody, capture_count: usize) -> Box<[bool]> {
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return vec![false; capture_count].into_boxed_slice();
    };
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

fn executable_callsite_needs(
    body: &LoweredBody,
    reachable_clauses: &[u32],
    executable_need: ExecutableNeed,
) -> HashMap<CallSiteId, ExecutableNeed> {
    let mut needs = HashMap::new();
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return needs;
    };
    for clause_id in reachable_clauses {
        collect_clause_callsite_needs(&clauses[*clause_id as usize], entries, executable_need, &mut needs);
    }
    needs
}

fn collect_clause_callsite_needs(
    clause: &LoweredClause,
    entries: &[LoweredEntry],
    executable_need: ExecutableNeed,
    out: &mut HashMap<CallSiteId, ExecutableNeed>,
) {
    collect_entry_callsite_needs(entries, clause.entry, executable_need, out);
}

fn collect_entry_callsite_needs(
    entries: &[LoweredEntry],
    entry_id: ControlEntryId,
    outgoing_need: ExecutableNeed,
    out: &mut HashMap<CallSiteId, ExecutableNeed>,
) -> Option<usize> {
    let entry = &entries[entry_id.as_u32() as usize];
    let mut tuple_demands = HashMap::new();
    match &entry.tail {
        LoweredTail::Value { value, dest } => {
            if let Some(arity) = destination_need(entries, dest, outgoing_need, out) {
                tuple_demands.insert(*value, arity);
            }
        }
        LoweredTail::DirectCall {
            value, callsite, dest, ..
        }
        | LoweredTail::ClosureCall {
            value, callsite, dest, ..
        } => {
            let need = destination_need(entries, dest, outgoing_need, out)
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
            let _ = collect_entry_callsite_needs(entries, *then_entry, outgoing_need, out);
            let _ = collect_entry_callsite_needs(entries, *else_entry, outgoing_need, out);
        }
        LoweredTail::Dispatch { dispatch, .. } => {
            for arm_entry in &dispatch.arm_entries {
                let _ = collect_entry_callsite_needs(entries, *arm_entry, outgoing_need, out);
            }
            let _ = collect_entry_callsite_needs(entries, dispatch.miss_entry, outgoing_need, out);
        }
        LoweredTail::Receive(receive) => {
            for clause in &receive.clauses {
                let _ = collect_entry_callsite_needs(entries, clause.entry, outgoing_need, out);
            }
            if let Some(after) = &receive.after {
                let _ = collect_entry_callsite_needs(entries, after.entry, outgoing_need, out);
            }
        }
        LoweredTail::Halt { .. } => {}
    }
    for step in entry.steps.iter().rev() {
        match step {
            LoweredStep::AssertTuple { source, arity } => {
                tuple_demands.insert(*source, *arity);
            }
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
            | LoweredStep::TupleField { value, .. } => {
                tuple_demands.remove(value);
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
            LoweredStep::AssertLiteral { .. }
            | LoweredStep::AssertStruct { .. }
            | LoweredStep::AssertEmptyList { .. }
            | LoweredStep::AssertSame { .. }
            | LoweredStep::AssertBitstringDone { .. } => {}
        }
    }
    entry
        .origin
        .input_value()
        .and_then(|value| tuple_demands.remove(&value))
}

fn destination_need(
    entries: &[LoweredEntry],
    dest: &ControlDestination,
    outgoing_need: ExecutableNeed,
    out: &mut HashMap<CallSiteId, ExecutableNeed>,
) -> Option<usize> {
    match dest {
        ControlDestination::Return => match outgoing_need {
            ExecutableNeed::Value => None,
            ExecutableNeed::TupleFields(arity) => Some(arity),
        },
        ControlDestination::Deliver(entry_id) => collect_entry_callsite_needs(entries, *entry_id, outgoing_need, out),
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
    let LoweredBody::Clauses { entries, .. } = body else {
        return origins;
    };
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

pub(crate) fn collect_value_origins(
    body: &LoweredBody,
    callsite_return_origins: &HashMap<CallSiteId, TransportOrigin>,
) -> HashMap<ValueId, TransportOrigin> {
    let mut origins = HashMap::new();
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return origins;
    };
    for clause in clauses {
        for step in &clause.projections {
            if let Some((value, origin)) = step_transport_origin(step) {
                origins.insert(value, origin);
            }
        }
        for (semantic_index, value) in clause.params.iter().copied().enumerate() {
            origins.insert(value, TransportOrigin::ExecutableInput(semantic_index));
        }
    }
    for entry in entries {
        for step in &entry.steps {
            if let Some((value, origin)) = step_transport_origin(step) {
                origins.insert(value, origin);
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

fn step_transport_origin(step: &LoweredStep) -> Option<(ValueId, TransportOrigin)> {
    match step {
        LoweredStep::Tuple { value, items } => {
            Some((*value, TransportOrigin::TupleValue(items.clone().into_boxed_slice())))
        }
        LoweredStep::TupleField { value, source, index } => Some((
            *value,
            TransportOrigin::TupleField {
                source: *source,
                index: *index,
            },
        )),
        LoweredStep::FunctionRef { value, function } => Some((
            *value,
            TransportOrigin::CallableValue(LocalCallableProducer {
                function: *function,
                captures: Box::default(),
            }),
        )),
        LoweredStep::Lambda {
            value,
            function,
            captures,
        } => Some((
            *value,
            TransportOrigin::CallableValue(LocalCallableProducer {
                function: *function,
                captures: captures.clone().into_boxed_slice(),
            }),
        )),
        _ => None,
    }
}

fn collect_return_origins(body: &LoweredBody, analysis: &ActivationAnalysis) -> Box<[TransportOrigin]> {
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return Box::default();
    };
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
                pending.extend(dispatch.arm_entries.iter().copied());
                pending.push(dispatch.miss_entry);
            }
            LoweredTail::Receive(receive) => {
                pending.extend(receive.clauses.iter().map(|clause| clause.entry));
                pending.extend(receive.after.iter().map(|after| after.entry));
                if let ControlDestination::Deliver(target) = receive.dest {
                    pending.push(target);
                }
            }
            LoweredTail::Halt { .. } => {}
        }
    }
    origins.into_boxed_slice()
}
