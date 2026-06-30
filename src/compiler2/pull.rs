//! Product-keyed pull substrate for compiler2 artifacts.
//!
//! This module is intentionally separate from the existing job scheduler. A
//! product producer answers one named demand and can only return a value or
//! explicit waits. It does not enqueue jobs, schedule follow-up work, or scan a
//! root frontier.

use std::collections::{HashMap, HashSet};

use crate::telemetry::{Telemetry, opaque_debug};
use crate::{measurements, metadata};

use super::artifact::{
    AbiReadyExecutable, BackendCallArg, BackendEntryOrigin, BackendProgram, BackendReceive, BackendStep, CallEdge,
    CallReturnFlow, EffectSummary, MaterializedExecutable, ReusableConsCapture,
};
use super::body::{
    CallSiteId, ControlDestination, ControlDispatch, ControlEntryId, DispatchBindings, LoweredExtern, ValueId,
};
use super::drive::FactKey;
use super::facts::FactUse;
use super::identity::{ExecutableKey, RootId};
use super::semantic::{ExecutableRuntimeDemand, RuntimeDemand};
use super::transport::{BoundaryFacts, BoundaryId, CallableFacts, CallableId, ShapeId, TransportPosition};
use super::world::World;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InputSlot {
    pub executable: ExecutableKey,
    pub semantic_index: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ProductKey {
    RootBackendProduct(RootId),
    BackendExecutable(ExecutableKey),
    AbiExecutable(ExecutableKey),
    MaterializedExecutable(ExecutableKey),
    ExecutableEffects(ExecutableKey),
    RuntimeDemand(ExecutableKey),
    OutgoingInputEdges(ExecutableKey),
    IncomingInputSlot(InputSlot),
    TransportShape(TransportPosition),
    TransportComponent(TransportPosition),
    CallableFacts(CallableId),
    BoundaryFacts(BoundaryId),
}

impl ProductKey {
    pub fn kind(&self) -> &'static str {
        match self {
            Self::RootBackendProduct(_) => "root_backend_product",
            Self::BackendExecutable(_) => "backend_executable",
            Self::AbiExecutable(_) => "abi_executable",
            Self::MaterializedExecutable(_) => "materialized_executable",
            Self::ExecutableEffects(_) => "executable_effects",
            Self::RuntimeDemand(_) => "runtime_demand",
            Self::OutgoingInputEdges(_) => "outgoing_input_edges",
            Self::IncomingInputSlot(_) => "incoming_input_slot",
            Self::TransportShape(_) => "transport_shape",
            Self::TransportComponent(_) => "transport_component",
            Self::CallableFacts(_) => "callable_facts",
            Self::BoundaryFacts(_) => "boundary_facts",
        }
    }

    fn executable(&self) -> Option<&ExecutableKey> {
        match self {
            Self::BackendExecutable(executable)
            | Self::AbiExecutable(executable)
            | Self::MaterializedExecutable(executable)
            | Self::ExecutableEffects(executable)
            | Self::RuntimeDemand(executable)
            | Self::OutgoingInputEdges(executable) => Some(executable),
            Self::IncomingInputSlot(slot) => Some(&slot.executable),
            Self::RootBackendProduct(_)
            | Self::TransportShape(_)
            | Self::TransportComponent(_)
            | Self::CallableFacts(_)
            | Self::BoundaryFacts(_) => None,
        }
    }

    fn transport_position(&self) -> Option<&TransportPosition> {
        match self {
            Self::TransportShape(position) | Self::TransportComponent(position) => Some(position),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TransportShapeFact {
    Shape(ShapeId),
    Absent,
}

impl TransportShapeFact {
    pub fn shape(&self) -> Option<ShapeId> {
        match self {
            Self::Shape(shape) => Some(*shape),
            Self::Absent => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ProductValue {
    Unit,
    RootBackendProduct(Box<BackendProgram>),
    BackendExecutable(Box<SymbolicBackendExecutable>),
    AbiExecutable(Box<AbiReadyExecutable>),
    MaterializedExecutable(Box<MaterializedExecutable>),
    ExecutableEffects(EffectSummary),
    RuntimeDemand(Box<ExecutableRuntimeDemand>),
    IncomingInputSlot(Box<[IncomingInputSource]>),
    TransportShape(TransportShapeFact),
    TransportComponent(TransportComponentInventory),
    CallableFacts(Option<CallableFacts>),
    BoundaryFacts(Option<BoundaryFacts>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PullWait {
    Product(ProductKey),
    Fact(FactUse<FactKey>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum PullOutcome {
    Produced(ProductValue),
    Waiting(Vec<PullWait>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct SymbolicBackendExecutable {
    pub key: ExecutableKey,
    pub abi: Box<AbiReadyExecutable>,
    pub body: SymbolicBackendBody,
    pub call_edges: HashMap<CallSiteId, CallEdge<ExecutableKey>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SymbolicBackendBody {
    Extern {
        signature: LoweredExtern,
    },
    Clauses {
        clauses: Vec<SymbolicBackendClause>,
        entries: Vec<SymbolicBackendEntry>,
        generated: Vec<super::FunctionId>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct SymbolicBackendClause {
    pub span: crate::source::Span,
    pub params: Vec<ValueId>,
    pub projections: Vec<BackendStep>,
    pub entry: ControlEntryId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SymbolicBackendEntry {
    pub span: crate::source::Span,
    pub origin: BackendEntryOrigin,
    pub params: Vec<ValueId>,
    pub captures: Vec<ValueId>,
    pub capture_positions: Vec<TransportPosition>,
    pub reusable_cons_captures: Vec<ReusableConsCapture>,
    pub steps: Vec<BackendStep>,
    pub tail: SymbolicBackendTail,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SymbolicBackendTail {
    Value {
        value: ValueId,
        dest: ControlDestination,
    },
    DirectCall {
        value: ValueId,
        callsite: CallSiteId,
        target: CallEdge<ExecutableKey>,
        args: Vec<BackendCallArg>,
        dest: ControlDestination,
    },
    ClosureCall {
        value: ValueId,
        callsite: CallSiteId,
        callee: ValueId,
        target: Option<ExecutableKey>,
        args: Vec<BackendCallArg>,
        dest: ControlDestination,
        return_flow: Option<CallReturnFlow>,
    },
    If {
        cond: ValueId,
        then_entry: ControlEntryId,
        else_entry: ControlEntryId,
    },
    Dispatch {
        inputs: Vec<ValueId>,
        bindings: DispatchBindings,
        dispatch: Box<ControlDispatch>,
    },
    Receive(Box<BackendReceive>),
    Halt {
        atom: String,
    },
}

impl PullOutcome {
    pub fn wait_on_product(key: ProductKey) -> Self {
        Self::Waiting(vec![PullWait::Product(key)])
    }

    pub fn wait_on_fact(fact: FactUse<FactKey>) -> Self {
        Self::Waiting(vec![PullWait::Fact(fact)])
    }
}

#[derive(Debug, Default)]
pub struct ProductMemo {
    produced: HashMap<ProductKey, ProductValue>,
    in_progress: HashSet<ProductKey>,
    invalidated_in_progress: HashSet<ProductKey>,
}

impl ProductMemo {
    pub fn get(&self, key: &ProductKey) -> Option<&ProductValue> {
        self.produced.get(key)
    }

    pub fn contains_in_progress(&self, key: &ProductKey) -> bool {
        self.in_progress.contains(key)
    }

    pub fn runtime_demand(&self, executable: &ExecutableKey) -> Option<&ExecutableRuntimeDemand> {
        match self.produced.get(&ProductKey::RuntimeDemand(executable.clone())) {
            Some(ProductValue::RuntimeDemand(demand)) => Some(demand.as_ref()),
            Some(
                ProductValue::Unit
                | ProductValue::RootBackendProduct(_)
                | ProductValue::BackendExecutable(_)
                | ProductValue::AbiExecutable(_)
                | ProductValue::MaterializedExecutable(_)
                | ProductValue::ExecutableEffects(_)
                | ProductValue::IncomingInputSlot(_)
                | ProductValue::TransportShape(_)
                | ProductValue::TransportComponent(_)
                | ProductValue::CallableFacts(_)
                | ProductValue::BoundaryFacts(_),
            )
            | None => None,
        }
    }

    fn begin(&mut self, key: ProductKey) -> bool {
        self.in_progress.insert(key)
    }

    fn finish(&mut self, key: &ProductKey, value: ProductValue) -> bool {
        self.in_progress.remove(key);
        if self.invalidated_in_progress.remove(key) {
            self.produced.remove(key);
            return false;
        }
        self.produced.insert(key.clone(), value);
        true
    }

    fn unblock(&mut self, key: &ProductKey) {
        self.in_progress.remove(key);
        self.invalidated_in_progress.remove(key);
    }

    fn remove(&mut self, key: &ProductKey) {
        if self.in_progress.contains(key) {
            self.invalidated_in_progress.insert(key.clone());
        }
        self.produced.remove(key);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IncomingInputSource {
    pub producer: ExecutableKey,
    pub value: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DemandedCallEdge {
    pub caller: ExecutableKey,
    pub callsite: Option<CallSiteId>,
    pub callee: ExecutableKey,
    pub inputs: Vec<(usize, IncomingInputSource)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TransportComponentInventory {
    pub anchor: TransportPosition,
    pub positions: Vec<TransportPosition>,
}

#[derive(Debug)]
pub struct PullSession {
    root: RootId,
    memo: ProductMemo,
    demanded_executables: HashSet<ExecutableKey>,
    call_edges: HashMap<ExecutableKey, Vec<DemandedCallEdge>>,
    incoming_inputs: HashMap<InputSlot, Vec<IncomingInputSource>>,
    runtime_demand_dependents: HashMap<ExecutableKey, HashSet<ExecutableKey>>,
    latest_runtime_demands: HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    // Per-caller return-demand evidence, keyed `caller -> (callee -> demand)`.
    // A callee present here is OBSERVED (even when its demand is the bottom
    // `ignore` discard marker); a callee absent is not-yet-observed. The derived
    // `return_demands` join is rebuilt from these contributions on every change
    // so a caller can RETRACT a stale (transiently whole) contribution -- the
    // join is not a monotone accumulator.
    return_demand_contributions: HashMap<ExecutableKey, HashMap<ExecutableKey, RuntimeDemand>>,
    return_demand_contributors: HashMap<ExecutableKey, HashSet<ExecutableKey>>,
    return_demands: HashMap<ExecutableKey, RuntimeDemand>,
    materialized_executables: HashMap<ExecutableKey, MaterializedExecutable>,
    executable_effects: HashMap<ExecutableKey, EffectSummary>,
    abi_executables: HashMap<ExecutableKey, AbiReadyExecutable>,
    backend_executables: HashMap<ExecutableKey, SymbolicBackendExecutable>,
    demanded_transport_positions: HashSet<TransportPosition>,
    transport_shape_facts: HashMap<TransportPosition, TransportShapeFact>,
    transport_shapes: HashMap<TransportPosition, ShapeId>,
    transport_components: HashMap<TransportPosition, TransportComponentInventory>,
    transport_positions_by_executable: HashMap<ExecutableKey, HashSet<TransportPosition>>,
    callable_facts: HashMap<CallableId, CallableFacts>,
    boundary_facts: HashMap<BoundaryId, BoundaryFacts>,
    demanded_callables: HashSet<CallableId>,
    demanded_boundaries: HashSet<BoundaryId>,
    executable_index: HashMap<ExecutableKey, usize>,
    active_runtime_demands: HashSet<ExecutableKey>,
    producer_pokes: u64,
}

impl PullSession {
    pub fn new(root: RootId) -> Self {
        Self {
            root,
            memo: ProductMemo::default(),
            demanded_executables: HashSet::new(),
            call_edges: HashMap::new(),
            incoming_inputs: HashMap::new(),
            runtime_demand_dependents: HashMap::new(),
            latest_runtime_demands: HashMap::new(),
            return_demand_contributions: HashMap::new(),
            return_demand_contributors: HashMap::new(),
            return_demands: HashMap::new(),
            materialized_executables: HashMap::new(),
            executable_effects: HashMap::new(),
            abi_executables: HashMap::new(),
            backend_executables: HashMap::new(),
            demanded_transport_positions: HashSet::new(),
            transport_shape_facts: HashMap::new(),
            transport_shapes: HashMap::new(),
            transport_components: HashMap::new(),
            transport_positions_by_executable: HashMap::new(),
            callable_facts: HashMap::new(),
            boundary_facts: HashMap::new(),
            demanded_callables: HashSet::new(),
            demanded_boundaries: HashSet::new(),
            executable_index: HashMap::new(),
            active_runtime_demands: HashSet::new(),
            producer_pokes: 0,
        }
    }

    pub fn root(&self) -> RootId {
        self.root
    }

    pub fn memo(&self) -> &ProductMemo {
        &self.memo
    }

    pub fn product_is_in_progress(&self, key: &ProductKey) -> bool {
        self.memo.in_progress.contains(key)
    }

    pub fn demanded_executables(&self) -> &HashSet<ExecutableKey> {
        &self.demanded_executables
    }

    pub fn call_edges(&self, caller: &ExecutableKey) -> &[DemandedCallEdge] {
        self.call_edges.get(caller).map(Vec::as_slice).unwrap_or(&[])
    }

    pub fn incoming_input_sources(&self, slot: &InputSlot) -> &[IncomingInputSource] {
        self.incoming_inputs.get(slot).map(Vec::as_slice).unwrap_or(&[])
    }

    pub fn record_runtime_demand_dependency(&mut self, dependency: ExecutableKey, dependent: ExecutableKey) {
        if dependency == dependent {
            return;
        }
        self.runtime_demand_dependents
            .entry(dependency)
            .or_default()
            .insert(dependent);
    }

    fn record_latest_runtime_demand(&mut self, executable: ExecutableKey, demand: ExecutableRuntimeDemand) -> bool {
        let changed = self.latest_runtime_demands.get(&executable) != Some(&demand);
        self.latest_runtime_demands.insert(executable, demand);
        changed
    }

    pub fn return_demand(&self, executable: &ExecutableKey) -> Option<&RuntimeDemand> {
        self.return_demands.get(executable)
    }

    pub fn materialized_executable(&self, executable: &ExecutableKey) -> Option<&MaterializedExecutable> {
        self.materialized_executables.get(executable)
    }

    pub fn materialized_executables(&self) -> &HashMap<ExecutableKey, MaterializedExecutable> {
        &self.materialized_executables
    }

    pub fn executable_effects(&self, executable: &ExecutableKey) -> Option<EffectSummary> {
        self.executable_effects.get(executable).copied()
    }

    pub fn executable_effects_inventory(&self) -> &HashMap<ExecutableKey, EffectSummary> {
        &self.executable_effects
    }

    pub fn abi_executable(&self, executable: &ExecutableKey) -> Option<&AbiReadyExecutable> {
        self.abi_executables.get(executable)
    }

    pub fn abi_executables(&self) -> &HashMap<ExecutableKey, AbiReadyExecutable> {
        &self.abi_executables
    }

    pub fn backend_executable(&self, executable: &ExecutableKey) -> Option<&SymbolicBackendExecutable> {
        self.backend_executables.get(executable)
    }

    pub fn backend_executables(&self) -> &HashMap<ExecutableKey, SymbolicBackendExecutable> {
        &self.backend_executables
    }

    pub fn demanded_transport_positions(&self) -> &HashSet<TransportPosition> {
        &self.demanded_transport_positions
    }

    pub fn transport_shape(&self, position: &TransportPosition) -> Option<ShapeId> {
        self.transport_shapes.get(position).copied()
    }

    pub fn transport_shape_fact(&self, position: &TransportPosition) -> Option<&TransportShapeFact> {
        self.transport_shape_facts.get(position)
    }

    pub fn transport_shapes(&self) -> &HashMap<TransportPosition, ShapeId> {
        &self.transport_shapes
    }

    pub fn transport_component(&self, anchor: &TransportPosition) -> Option<&TransportComponentInventory> {
        self.transport_components.get(anchor)
    }

    pub fn callable_facts(&self, callable: CallableId) -> Option<&CallableFacts> {
        self.callable_facts.get(&callable)
    }

    pub fn callable_facts_inventory(&self) -> &HashMap<CallableId, CallableFacts> {
        &self.callable_facts
    }

    pub fn boundary_facts(&self, boundary: BoundaryId) -> Option<&BoundaryFacts> {
        self.boundary_facts.get(&boundary)
    }

    pub fn boundary_facts_inventory(&self) -> &HashMap<BoundaryId, BoundaryFacts> {
        &self.boundary_facts
    }

    pub fn demanded_callables(&self) -> &HashSet<CallableId> {
        &self.demanded_callables
    }

    pub fn demanded_boundaries(&self) -> &HashSet<BoundaryId> {
        &self.demanded_boundaries
    }

    pub fn executable_index(&self) -> &HashMap<ExecutableKey, usize> {
        &self.executable_index
    }

    pub fn runtime_demand_is_active(&self, executable: &ExecutableKey) -> bool {
        self.active_runtime_demands.contains(executable)
    }

    pub fn producer_pokes(&self) -> u64 {
        self.producer_pokes
    }

    pub fn record_call_edge(&mut self, edge: DemandedCallEdge) {
        self.demanded_executables.insert(edge.caller.clone());
        self.demanded_executables.insert(edge.callee.clone());
        let mut changed = false;
        for (semantic_index, source) in &edge.inputs {
            let slot = InputSlot {
                executable: edge.callee.clone(),
                semantic_index: *semantic_index,
            };
            let slot_changed = push_unique(self.incoming_inputs.entry(slot.clone()).or_default(), source.clone());
            if slot_changed {
                self.memo.remove(&ProductKey::IncomingInputSlot(slot));
            }
            changed |= slot_changed;
        }
        let edges = self.call_edges.entry(edge.caller.clone()).or_default();
        changed |= push_unique(edges, edge.clone());
        if changed {
            self.invalidate_demand_derived_products(&edge.callee);
        }
    }

    pub fn record_producer_pokes(&mut self, count: u64) {
        self.producer_pokes += count;
    }

    /// Replace `caller`'s full set of return-demand contributions. Every callee
    /// the caller names becomes (or stays) OBSERVED; any callee the caller named
    /// on a previous run but not this one has its contribution withdrawn. Each
    /// affected callee's joined return demand is rebuilt from all current
    /// contributors and its demand-derived products are invalidated when the join
    /// changes -- so a contribution that DROPS (e.g. a forwarder collapsing from
    /// its transient whole-by-need seed to an observed discard) retracts cleanly
    /// instead of baking into a monotone accumulator.
    pub fn replace_return_demand_contributions(
        &mut self,
        caller: ExecutableKey,
        contributions: HashMap<ExecutableKey, RuntimeDemand>,
    ) {
        let previous = self.return_demand_contributions.remove(&caller).unwrap_or_default();
        let mut affected: HashSet<ExecutableKey> = HashSet::new();
        for target in previous.keys() {
            affected.insert(target.clone());
            if let Some(contributors) = self.return_demand_contributors.get_mut(target) {
                contributors.remove(&caller);
            }
        }
        for target in contributions.keys() {
            affected.insert(target.clone());
            self.return_demand_contributors
                .entry(target.clone())
                .or_default()
                .insert(caller.clone());
        }
        if !contributions.is_empty() {
            self.return_demand_contributions.insert(caller, contributions);
        }
        for target in affected {
            self.recompute_return_demand(&target);
        }
    }

    fn recompute_return_demand(&mut self, target: &ExecutableKey) {
        let joined = self
            .return_demand_contributors
            .get(target)
            .into_iter()
            .flatten()
            .filter_map(|caller| {
                self.return_demand_contributions
                    .get(caller)
                    .and_then(|contributions| contributions.get(target))
            })
            .fold(None::<RuntimeDemand>, |acc, demand| match acc {
                Some(mut acc) => {
                    acc.join_assign(demand);
                    Some(acc)
                }
                None => Some(demand.clone()),
            });
        let changed = self.return_demands.get(target) != joined.as_ref();
        match joined {
            Some(demand) => {
                self.demanded_executables.insert(target.clone());
                self.return_demands.insert(target.clone(), demand);
            }
            None => {
                self.return_demand_contributors.remove(target);
                self.return_demands.remove(target);
            }
        }
        if changed {
            self.invalidate_demand_derived_products(target);
        }
    }

    pub fn record_materialized_executable(&mut self, executable: ExecutableKey, materialized: MaterializedExecutable) {
        self.demanded_executables.insert(executable.clone());
        self.materialized_executables.insert(executable, materialized);
    }

    pub fn record_executable_effects(&mut self, executable: ExecutableKey, effects: EffectSummary) {
        self.demanded_executables.insert(executable.clone());
        self.executable_effects.insert(executable, effects);
    }

    pub fn record_abi_executable(&mut self, executable: ExecutableKey, abi: AbiReadyExecutable) {
        self.demanded_executables.insert(executable.clone());
        self.abi_executables.insert(executable, abi);
    }

    pub fn record_backend_executable(&mut self, executable: ExecutableKey, backend: SymbolicBackendExecutable) {
        self.demanded_executables.insert(executable.clone());
        self.backend_executables.insert(executable, backend);
    }

    pub fn record_transport_component(&mut self, anchor: TransportPosition, positions: Vec<TransportPosition>) {
        self.demanded_transport_positions.insert(anchor.clone());
        self.demanded_transport_positions.extend(positions.iter().cloned());
        self.transport_components
            .insert(anchor.clone(), TransportComponentInventory { anchor, positions });
    }

    pub fn record_transport_shape(&mut self, position: TransportPosition, shape: ShapeId) {
        self.demanded_transport_positions.insert(position.clone());
        self.transport_shape_facts
            .insert(position.clone(), TransportShapeFact::Shape(shape));
        self.transport_shapes.insert(position, shape);
    }

    pub fn record_transport_shape_for(
        &mut self,
        executable: &ExecutableKey,
        position: TransportPosition,
        shape: ShapeId,
    ) {
        self.demanded_transport_positions.insert(position.clone());
        self.transport_positions_by_executable
            .entry(executable.clone())
            .or_default()
            .insert(position.clone());
        self.transport_shape_facts
            .insert(position.clone(), TransportShapeFact::Shape(shape));
        let changed = self.transport_shapes.insert(position, shape) != Some(shape);
        if changed {
            self.invalidate_artifact_products(executable);
        }
    }

    pub fn record_absent_transport_shape_for(&mut self, executable: &ExecutableKey, position: TransportPosition) {
        self.demanded_transport_positions.insert(position.clone());
        self.transport_positions_by_executable
            .entry(executable.clone())
            .or_default()
            .insert(position.clone());
        let changed = self
            .transport_shape_facts
            .insert(position.clone(), TransportShapeFact::Absent)
            != Some(TransportShapeFact::Absent);
        self.transport_shapes.remove(&position);
        if changed {
            self.invalidate_artifact_products(executable);
        }
    }

    pub fn record_callable_facts(&mut self, callable: CallableId, facts: CallableFacts) {
        self.demanded_callables.insert(callable);
        self.callable_facts.insert(callable, facts);
    }

    pub fn record_boundary_facts(&mut self, boundary: BoundaryId, facts: BoundaryFacts) {
        self.demanded_boundaries.insert(boundary);
        self.boundary_facts.insert(boundary, facts);
    }

    pub fn assign_executable_index(&mut self, executable: ExecutableKey, index: usize) {
        self.demanded_executables.insert(executable.clone());
        self.executable_index.insert(executable, index);
    }

    fn invalidate_demand_derived_products(&mut self, executable: &ExecutableKey) {
        let mut stack = vec![executable.clone()];
        let mut seen = HashSet::new();
        while let Some(current) = stack.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            self.invalidate_demand_derived_products_one(&current);
            if let Some(dependents) = self.runtime_demand_dependents.get(&current).cloned() {
                stack.extend(dependents);
            }
        }
    }

    fn invalidate_runtime_demand_dependents(&mut self, executable: &ExecutableKey) {
        let Some(dependents) = self.runtime_demand_dependents.get(executable).cloned() else {
            return;
        };
        for dependent in dependents {
            self.invalidate_demand_derived_products_one(&dependent);
        }
    }

    fn invalidate_demand_derived_products_one(&mut self, executable: &ExecutableKey) {
        self.memo.remove(&ProductKey::RuntimeDemand(executable.clone()));
        self.invalidate_transport_products(executable);
        self.invalidate_artifact_products(executable);
    }

    fn discard_product_side_effects(&mut self, key: &ProductKey) {
        match key {
            ProductKey::MaterializedExecutable(executable) => {
                self.materialized_executables.remove(executable);
            }
            ProductKey::ExecutableEffects(executable) => {
                self.executable_effects.remove(executable);
            }
            ProductKey::AbiExecutable(executable) => {
                self.abi_executables.remove(executable);
            }
            ProductKey::BackendExecutable(executable) => {
                self.backend_executables.remove(executable);
            }
            ProductKey::TransportShape(position) => {
                self.transport_shape_facts.remove(position);
                self.transport_shapes.remove(position);
            }
            ProductKey::TransportComponent(position) => {
                self.transport_components.remove(position);
            }
            ProductKey::RootBackendProduct(_)
            | ProductKey::RuntimeDemand(_)
            | ProductKey::OutgoingInputEdges(_)
            | ProductKey::IncomingInputSlot(_)
            | ProductKey::CallableFacts(_)
            | ProductKey::BoundaryFacts(_) => {}
        }
    }

    fn invalidate_artifact_products(&mut self, executable: &ExecutableKey) {
        self.memo
            .remove(&ProductKey::MaterializedExecutable(executable.clone()));
        self.memo.remove(&ProductKey::ExecutableEffects(executable.clone()));
        self.memo.remove(&ProductKey::AbiExecutable(executable.clone()));
        self.memo.remove(&ProductKey::BackendExecutable(executable.clone()));
        self.materialized_executables.remove(executable);
        self.executable_effects.remove(executable);
        self.abi_executables.remove(executable);
        self.backend_executables.remove(executable);
    }

    fn invalidate_transport_products(&mut self, executable: &ExecutableKey) {
        let Some(positions) = self.transport_positions_by_executable.remove(executable) else {
            return;
        };
        for position in &positions {
            self.transport_shape_facts.remove(position);
            self.transport_shapes.remove(position);
            self.transport_components.remove(position);
            self.memo.remove(&ProductKey::TransportShape(position.clone()));
            self.memo.remove(&ProductKey::TransportComponent(position.clone()));
        }

        let stale_components = self
            .transport_components
            .iter()
            .filter_map(|(anchor, component)| {
                component
                    .positions
                    .iter()
                    .any(|position| positions.contains(position))
                    .then_some(anchor.clone())
            })
            .collect::<Vec<_>>();
        for anchor in stale_components {
            self.transport_components.remove(&anchor);
            self.memo.remove(&ProductKey::TransportComponent(anchor));
        }
    }

    fn enter_runtime_demand(&mut self, executable: &ExecutableKey) {
        self.active_runtime_demands.insert(executable.clone());
    }

    fn finish_runtime_demand(&mut self, executable: &ExecutableKey) {
        self.active_runtime_demands.remove(executable);
    }

    fn note_product_request(&mut self, key: &ProductKey) {
        if let Some(executable) = key.executable() {
            self.demanded_executables.insert(executable.clone());
        }
        if let Some(position) = key.transport_position() {
            self.demanded_transport_positions.insert(position.clone());
        }
        match key {
            ProductKey::CallableFacts(callable) => {
                self.demanded_callables.insert(*callable);
            }
            ProductKey::BoundaryFacts(boundary) => {
                self.demanded_boundaries.insert(*boundary);
            }
            _ => {}
        }
    }

    fn emit_finished(&self, tel: &dyn Telemetry) {
        tel.execute(
            &["fz", "compiler2", "pull", "session", "finished"],
            &measurements! {
                root_id: self.root.as_u32(),
                executables: self.demanded_executables.len(),
                transport_positions: self.demanded_transport_positions.len(),
                callables: self.demanded_callables.len(),
                boundaries: self.demanded_boundaries.len(),
                producer_pokes: self.producer_pokes,
            },
            &metadata! {},
        );
    }
}

fn push_unique<T>(items: &mut Vec<T>, value: T) -> bool
where
    T: PartialEq,
{
    if !items.contains(&value) {
        items.push(value);
        true
    } else {
        false
    }
}

pub trait ProductProducers {
    fn produce_root_backend_product(&mut self, session: &mut PullSession, root: RootId) -> PullOutcome;
    fn produce_backend_executable(&mut self, session: &mut PullSession, executable: &ExecutableKey) -> PullOutcome;
    fn produce_abi_executable(&mut self, session: &mut PullSession, executable: &ExecutableKey) -> PullOutcome;
    fn produce_materialized_executable(&mut self, session: &mut PullSession, executable: &ExecutableKey)
    -> PullOutcome;
    fn produce_executable_effects(&mut self, session: &mut PullSession, executable: &ExecutableKey) -> PullOutcome;
    fn produce_runtime_demand(&mut self, session: &mut PullSession, executable: &ExecutableKey) -> PullOutcome;
    fn produce_outgoing_input_edges(&mut self, session: &mut PullSession, executable: &ExecutableKey) -> PullOutcome;
    fn produce_incoming_input_slot(&mut self, session: &mut PullSession, slot: &InputSlot) -> PullOutcome;
    fn produce_transport_shape(&mut self, session: &mut PullSession, position: &TransportPosition) -> PullOutcome;
    fn produce_transport_component(&mut self, session: &mut PullSession, position: &TransportPosition) -> PullOutcome;
    fn produce_callable_facts(&mut self, session: &mut PullSession, callable: CallableId) -> PullOutcome;
    fn produce_boundary_facts(&mut self, session: &mut PullSession, boundary: BoundaryId) -> PullOutcome;
}

pub struct WorldProductProducers<'w, 'a> {
    world: &'w mut World<'a>,
}

impl<'w, 'a> WorldProductProducers<'w, 'a> {
    pub fn new(world: &'w mut World<'a>) -> Self {
        Self { world }
    }
}

impl ProductProducers for WorldProductProducers<'_, '_> {
    fn produce_root_backend_product(&mut self, session: &mut PullSession, root: RootId) -> PullOutcome {
        super::jobs::backend::produce_root_backend_product(self.world, session, root)
    }

    fn produce_backend_executable(&mut self, session: &mut PullSession, executable: &ExecutableKey) -> PullOutcome {
        super::jobs::backend::produce_backend_executable_product(self.world, session, executable)
    }

    fn produce_abi_executable(&mut self, session: &mut PullSession, executable: &ExecutableKey) -> PullOutcome {
        super::jobs::artifact::produce_abi_executable_product(self.world, session, executable)
    }

    fn produce_materialized_executable(
        &mut self,
        session: &mut PullSession,
        executable: &ExecutableKey,
    ) -> PullOutcome {
        super::jobs::artifact::produce_materialized_executable_product(self.world, session, executable)
    }

    fn produce_executable_effects(&mut self, session: &mut PullSession, executable: &ExecutableKey) -> PullOutcome {
        super::jobs::artifact::produce_executable_effects_product(self.world, session, executable)
    }

    fn produce_runtime_demand(&mut self, session: &mut PullSession, executable: &ExecutableKey) -> PullOutcome {
        super::jobs::runtime_demand::produce_runtime_demand_product(self.world, session, executable)
    }

    fn produce_outgoing_input_edges(&mut self, session: &mut PullSession, executable: &ExecutableKey) -> PullOutcome {
        super::jobs::runtime_demand::produce_outgoing_input_edges_product(self.world, session, executable)
    }

    fn produce_incoming_input_slot(&mut self, session: &mut PullSession, slot: &InputSlot) -> PullOutcome {
        PullOutcome::Produced(ProductValue::IncomingInputSlot(
            session.incoming_input_sources(slot).to_vec().into_boxed_slice(),
        ))
    }

    fn produce_transport_shape(&mut self, session: &mut PullSession, position: &TransportPosition) -> PullOutcome {
        super::jobs::transport::produce_transport_shape_product(self.world, session, position)
    }

    fn produce_transport_component(&mut self, session: &mut PullSession, position: &TransportPosition) -> PullOutcome {
        super::jobs::transport::produce_transport_component_product(self.world, session, position)
    }

    fn produce_callable_facts(&mut self, session: &mut PullSession, callable: CallableId) -> PullOutcome {
        PullOutcome::Produced(ProductValue::CallableFacts(session.callable_facts(callable).cloned()))
    }

    fn produce_boundary_facts(&mut self, session: &mut PullSession, boundary: BoundaryId) -> PullOutcome {
        PullOutcome::Produced(ProductValue::BoundaryFacts(session.boundary_facts(boundary).cloned()))
    }
}

pub struct ProductDriver<'a> {
    tel: &'a dyn Telemetry,
    session: PullSession,
}

impl<'a> ProductDriver<'a> {
    pub fn new(tel: &'a dyn Telemetry, root: RootId) -> Self {
        Self::with_session(tel, PullSession::new(root))
    }

    pub fn with_session(tel: &'a dyn Telemetry, session: PullSession) -> Self {
        Self { tel, session }
    }

    pub fn session(&self) -> &PullSession {
        &self.session
    }

    pub fn session_mut(&mut self) -> &mut PullSession {
        &mut self.session
    }

    pub fn finish_session(&self) {
        self.session.emit_finished(self.tel);
    }

    pub fn pull(&mut self, producers: &mut impl ProductProducers, key: ProductKey) -> PullOutcome {
        self.emit("requested", &key, 0);
        self.session.note_product_request(&key);
        if !matches!(key, ProductKey::RuntimeDemand(_))
            && let Some(value) = self.session.memo.get(&key)
        {
            self.emit("cache_hit", &key, 0);
            return PullOutcome::Produced(value.clone());
        }
        if !self.session.memo.begin(key.clone()) {
            self.emit("reentered", &key, 1);
            return PullOutcome::Waiting(vec![PullWait::Product(key)]);
        }

        if let ProductKey::RuntimeDemand(executable) = &key {
            self.session.enter_runtime_demand(executable);
        }

        let outcome = match &key {
            ProductKey::RootBackendProduct(root) => producers.produce_root_backend_product(&mut self.session, *root),
            ProductKey::BackendExecutable(executable) => {
                producers.produce_backend_executable(&mut self.session, executable)
            }
            ProductKey::AbiExecutable(executable) => producers.produce_abi_executable(&mut self.session, executable),
            ProductKey::MaterializedExecutable(executable) => {
                producers.produce_materialized_executable(&mut self.session, executable)
            }
            ProductKey::ExecutableEffects(executable) => {
                producers.produce_executable_effects(&mut self.session, executable)
            }
            ProductKey::RuntimeDemand(executable) => producers.produce_runtime_demand(&mut self.session, executable),
            ProductKey::OutgoingInputEdges(executable) => {
                producers.produce_outgoing_input_edges(&mut self.session, executable)
            }
            ProductKey::IncomingInputSlot(slot) => producers.produce_incoming_input_slot(&mut self.session, slot),
            ProductKey::TransportShape(position) => producers.produce_transport_shape(&mut self.session, position),
            ProductKey::TransportComponent(position) => {
                producers.produce_transport_component(&mut self.session, position)
            }
            ProductKey::CallableFacts(callable) => producers.produce_callable_facts(&mut self.session, *callable),
            ProductKey::BoundaryFacts(boundary) => producers.produce_boundary_facts(&mut self.session, *boundary),
        };

        match outcome {
            PullOutcome::Produced(value) => {
                let settled = self.session.memo.finish(&key, value.clone());
                if let ProductKey::RuntimeDemand(executable) = &key {
                    self.session.finish_runtime_demand(executable);
                    if settled
                        && let ProductValue::RuntimeDemand(demand) = &value
                        && self
                            .session
                            .record_latest_runtime_demand(executable.clone(), demand.as_ref().clone())
                    {
                        self.session.invalidate_runtime_demand_dependents(executable);
                    }
                }
                if !settled {
                    self.session.discard_product_side_effects(&key);
                    let waits = vec![PullWait::Product(key.clone())];
                    self.emit_waited(&key, &waits);
                    return PullOutcome::Waiting(waits);
                }
                self.emit("produced", &key, 0);
                PullOutcome::Produced(value)
            }
            PullOutcome::Waiting(waits) => {
                self.session.memo.unblock(&key);
                self.emit_waited(&key, &waits);
                PullOutcome::Waiting(waits)
            }
        }
    }

    fn emit(&self, event: &'static str, key: &ProductKey, wait_count: usize) {
        self.tel.execute(
            &["fz", "compiler2", "pull", "product", event],
            &measurements! {
                wait_count: wait_count,
            },
            &metadata! {
                kind: key.kind(),
                product: opaque_debug(key),
            },
        );
    }

    fn emit_waited(&self, key: &ProductKey, waits: &Vec<PullWait>) {
        self.tel.execute(
            &["fz", "compiler2", "pull", "product", "waited"],
            &measurements! {
                wait_count: waits.len(),
            },
            &metadata! {
                kind: key.kind(),
                product: opaque_debug(key),
                waits: opaque_debug(waits),
            },
        );
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::telemetry::{Capture, ConfiguredTelemetry};

    use super::*;

    #[derive(Debug, Default)]
    struct FakeProducers {
        produced: HashSet<ProductKey>,
        calls: Vec<ProductKey>,
        reenter: Option<ProductKey>,
        root_entry: Option<ExecutableKey>,
    }

    impl FakeProducers {
        fn produce(&mut self, key: ProductKey) -> PullOutcome {
            self.calls.push(key.clone());
            match key {
                ProductKey::RootBackendProduct(root) => {
                    let prerequisite =
                        ProductKey::RuntimeDemand(self.root_entry.clone().expect("fake root entry should be set"));
                    if self.produced.contains(&prerequisite) {
                        self.produced.insert(ProductKey::RootBackendProduct(root));
                        PullOutcome::Produced(ProductValue::Unit)
                    } else {
                        PullOutcome::wait_on_product(prerequisite)
                    }
                }
                ProductKey::RuntimeDemand(_) => {
                    self.produced.insert(key);
                    PullOutcome::Produced(ProductValue::Unit)
                }
                ProductKey::BackendExecutable(_) => {
                    PullOutcome::wait_on_fact(FactUse::current(FactKey::CodeIndexed(super::super::CodeId::ZERO)))
                }
                ProductKey::ExecutableEffects(_) if self.reenter.as_ref() == Some(&key) => {
                    PullOutcome::wait_on_product(key)
                }
                _ => {
                    self.produced.insert(key);
                    PullOutcome::Produced(ProductValue::Unit)
                }
            }
        }
    }

    impl ProductProducers for FakeProducers {
        fn produce_root_backend_product(&mut self, _session: &mut PullSession, root: RootId) -> PullOutcome {
            self.produce(ProductKey::RootBackendProduct(root))
        }

        fn produce_backend_executable(
            &mut self,
            _session: &mut PullSession,
            executable: &ExecutableKey,
        ) -> PullOutcome {
            self.produce(ProductKey::BackendExecutable(executable.clone()))
        }

        fn produce_abi_executable(&mut self, _session: &mut PullSession, executable: &ExecutableKey) -> PullOutcome {
            self.produce(ProductKey::AbiExecutable(executable.clone()))
        }

        fn produce_materialized_executable(
            &mut self,
            _session: &mut PullSession,
            executable: &ExecutableKey,
        ) -> PullOutcome {
            self.produce(ProductKey::MaterializedExecutable(executable.clone()))
        }

        fn produce_executable_effects(
            &mut self,
            _session: &mut PullSession,
            executable: &ExecutableKey,
        ) -> PullOutcome {
            self.produce(ProductKey::ExecutableEffects(executable.clone()))
        }

        fn produce_runtime_demand(&mut self, _session: &mut PullSession, executable: &ExecutableKey) -> PullOutcome {
            self.produce(ProductKey::RuntimeDemand(executable.clone()))
        }

        fn produce_outgoing_input_edges(
            &mut self,
            _session: &mut PullSession,
            executable: &ExecutableKey,
        ) -> PullOutcome {
            self.produce(ProductKey::OutgoingInputEdges(executable.clone()))
        }

        fn produce_incoming_input_slot(&mut self, _session: &mut PullSession, slot: &InputSlot) -> PullOutcome {
            self.produce(ProductKey::IncomingInputSlot(slot.clone()))
        }

        fn produce_transport_shape(&mut self, _session: &mut PullSession, position: &TransportPosition) -> PullOutcome {
            self.produce(ProductKey::TransportShape(position.clone()))
        }

        fn produce_transport_component(
            &mut self,
            _session: &mut PullSession,
            position: &TransportPosition,
        ) -> PullOutcome {
            self.produce(ProductKey::TransportComponent(position.clone()))
        }

        fn produce_callable_facts(&mut self, _session: &mut PullSession, callable: CallableId) -> PullOutcome {
            self.produce(ProductKey::CallableFacts(callable))
        }

        fn produce_boundary_facts(&mut self, _session: &mut PullSession, boundary: BoundaryId) -> PullOutcome {
            self.produce(ProductKey::BoundaryFacts(boundary))
        }
    }

    #[test]
    fn product_driver_names_prerequisites_without_follow_up_jobs() {
        let tel = ConfiguredTelemetry::new();
        let capture = Capture::new();
        tel.attach(&[], capture.handler());
        let root = RootId::for_test(0);
        let executable = fake_executable(root);
        let root_key = ProductKey::RootBackendProduct(root);
        let prerequisite = ProductKey::RuntimeDemand(executable.clone());
        let mut producers = FakeProducers {
            root_entry: Some(executable),
            ..FakeProducers::default()
        };
        let mut driver = ProductDriver::new(&tel, root);

        let first = driver.pull(&mut producers, root_key.clone());
        assert_eq!(first, PullOutcome::wait_on_product(prerequisite.clone()));
        assert_eq!(
            driver.pull(&mut producers, prerequisite),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(
            driver.pull(&mut producers, root_key.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(
            driver.pull(&mut producers, root_key.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );

        assert_eq!(producers.calls.iter().filter(|key| **key == root_key).count(), 2);
        assert_eq!(capture.count(&["fz", "compiler2", "pull", "product", "waited"]), 1);
        assert_eq!(capture.count(&["fz", "compiler2", "pull", "product", "produced"]), 2);
        assert_eq!(capture.count(&["fz", "compiler2", "pull", "product", "cache_hit"]), 1);
    }

    #[test]
    fn product_driver_reports_fact_waits_as_waits_not_scheduler_work() {
        let tel = ConfiguredTelemetry::new();
        let capture = Capture::new();
        tel.attach(&[], capture.handler());
        let root = RootId::for_test(1);
        let executable = fake_executable(root);
        let key = ProductKey::BackendExecutable(executable);
        let mut producers = FakeProducers::default();
        let mut driver = ProductDriver::new(&tel, root);

        let outcome = driver.pull(&mut producers, key.clone());

        assert_eq!(
            outcome,
            PullOutcome::wait_on_fact(FactUse::current(FactKey::CodeIndexed(super::super::CodeId::ZERO)))
        );
        assert!(driver.session().memo().get(&key).is_none());
        assert!(!driver.session().memo().contains_in_progress(&key));
        assert_eq!(capture.count(&["fz", "compiler2", "pull", "product", "waited"]), 1);
    }

    #[test]
    fn product_driver_turns_reentry_into_a_product_wait() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(2);
        let executable = fake_executable(root);
        let key = ProductKey::ExecutableEffects(executable);
        let mut driver = ProductDriver::new(&tel, root);
        let mut producers = FakeProducers {
            reenter: Some(key.clone()),
            ..FakeProducers::default()
        };

        assert!(driver.session.memo.begin(key.clone()));
        let outcome = driver.pull(&mut producers, key.clone());

        assert_eq!(outcome, PullOutcome::wait_on_product(key));
    }

    #[test]
    fn pull_session_records_outgoing_edges_into_exact_incoming_input_slots() {
        let caller = fake_executable(RootId::for_test(3));
        let callee = fake_executable(RootId::for_test(4));
        let source = IncomingInputSource {
            producer: caller.clone(),
            value: ValueId::from_u32(7),
        };
        let edge = DemandedCallEdge {
            caller: caller.clone(),
            callsite: Some(CallSiteId::from_u32(2)),
            callee: callee.clone(),
            inputs: vec![(1, source.clone())],
        };
        let mut session = PullSession::new(RootId::for_test(3));
        session.memo.finish(
            &ProductKey::RuntimeDemand(callee.clone()),
            ProductValue::RuntimeDemand(Box::default()),
        );

        session.record_call_edge(edge.clone());

        assert_eq!(session.call_edges(&caller), std::slice::from_ref(&edge));
        assert_eq!(
            session.incoming_input_sources(&InputSlot {
                executable: callee.clone(),
                semantic_index: 1,
            }),
            std::slice::from_ref(&source)
        );
        assert!(
            session.memo().get(&ProductKey::RuntimeDemand(callee)).is_none(),
            "recording a new incoming edge invalidates stale request-local callee runtime demand"
        );
        assert_eq!(session.producer_pokes(), 0);
    }

    #[test]
    fn pull_session_invalidates_runtime_demand_when_return_demand_grows() {
        let caller = fake_executable(RootId::for_test(5));
        let callee = fake_executable(RootId::for_test(5));
        let mut session = PullSession::new(RootId::for_test(5));
        session.memo.finish(
            &ProductKey::RuntimeDemand(callee.clone()),
            ProductValue::RuntimeDemand(Box::default()),
        );

        session.replace_return_demand_contributions(caller, HashMap::from([(callee.clone(), RuntimeDemand::whole())]));

        assert_eq!(
            session.return_demand(&callee),
            Some(&RuntimeDemand::whole()),
            "the joined return demand should be retained for the next pull"
        );
        assert!(
            session.memo().get(&ProductKey::RuntimeDemand(callee)).is_none(),
            "recording a stronger return demand invalidates stale request-local runtime demand"
        );
    }

    #[test]
    fn pull_session_retracts_return_demand_when_a_caller_collapses_to_a_discard() {
        // The "unknown is not none" guard at the session layer: a forwarder that
        // first contributes `whole` off its transient whole-by-need seed and
        // later collapses to an observed discard must DROP its callee's joined
        // demand, not bake the stale `whole`. An observed discard is the bottom
        // `ignore` cell -- still present (observed), distinct from a callee no
        // caller has named (absent -> None).
        let caller = fake_executable(RootId::for_test(7));
        let callee = fake_executable(RootId::for_test(7));
        let mut session = PullSession::new(RootId::for_test(7));

        session.replace_return_demand_contributions(
            caller.clone(),
            HashMap::from([(callee.clone(), RuntimeDemand::whole())]),
        );
        assert_eq!(session.return_demand(&callee), Some(&RuntimeDemand::whole()));

        session.memo.finish(
            &ProductKey::RuntimeDemand(callee.clone()),
            ProductValue::RuntimeDemand(Box::default()),
        );
        session.replace_return_demand_contributions(
            caller.clone(),
            HashMap::from([(callee.clone(), RuntimeDemand::ignore())]),
        );

        assert_eq!(
            session.return_demand(&callee),
            Some(&RuntimeDemand::ignore()),
            "a collapsed forwarder retracts its callee's whole demand down to the observed discard"
        );
        assert!(
            session.memo().get(&ProductKey::RuntimeDemand(callee.clone())).is_none(),
            "retracting a callee's return demand invalidates its stale request-local runtime demand"
        );

        session.replace_return_demand_contributions(caller, HashMap::new());
        assert_eq!(
            session.return_demand(&callee),
            None,
            "withdrawing the last contributor leaves the callee not-yet-observed (distinct from an observed discard)"
        );
    }

    #[test]
    fn world_product_reads_incoming_input_slot_from_session_inventory() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(6);
        let caller = fake_executable(root);
        let callee = fake_executable(root);
        let slot = InputSlot {
            executable: callee.clone(),
            semantic_index: 0,
        };
        let source = IncomingInputSource {
            producer: caller.clone(),
            value: ValueId::from_u32(9),
        };
        let mut driver = ProductDriver::new(&tel, root);
        driver.session_mut().record_call_edge(DemandedCallEdge {
            caller,
            callsite: Some(CallSiteId::from_u32(1)),
            callee,
            inputs: vec![(slot.semantic_index, source.clone())],
        });
        let mut world = World::new(&tel);
        let mut producers = WorldProductProducers::new(&mut world);

        let outcome = driver.pull(&mut producers, ProductKey::IncomingInputSlot(slot));

        assert_eq!(
            outcome,
            PullOutcome::Produced(ProductValue::IncomingInputSlot(Box::new([source])))
        );
        assert_eq!(driver.session().producer_pokes(), 0);
    }

    #[test]
    fn incoming_input_slot_product_invalidates_when_outgoing_edge_records_source() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(61);
        let caller = fake_executable(root);
        let callee = fake_executable_with_function(root, 62);
        let slot = InputSlot {
            executable: callee.clone(),
            semantic_index: 0,
        };
        let source = IncomingInputSource {
            producer: caller.clone(),
            value: ValueId::from_u32(11),
        };
        let mut driver = ProductDriver::new(&tel, root);
        let mut world = World::new(&tel);

        let empty = {
            let mut producers = WorldProductProducers::new(&mut world);
            driver.pull(&mut producers, ProductKey::IncomingInputSlot(slot.clone()))
        };
        assert_eq!(
            empty,
            PullOutcome::Produced(ProductValue::IncomingInputSlot(Box::new([])))
        );

        driver.session_mut().record_call_edge(DemandedCallEdge {
            caller,
            callsite: Some(CallSiteId::from_u32(1)),
            callee,
            inputs: vec![(slot.semantic_index, source.clone())],
        });
        let updated = {
            let mut producers = WorldProductProducers::new(&mut world);
            driver.pull(&mut producers, ProductKey::IncomingInputSlot(slot))
        };

        assert_eq!(
            updated,
            PullOutcome::Produced(ProductValue::IncomingInputSlot(Box::new([source])))
        );
    }

    #[test]
    fn world_product_transport_shape_waits_for_component_inventory() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(63);
        let position = TransportPosition::ExecutableReturn {
            executable: executable_symbol_for_test(&fake_executable(root)),
        };
        let mut driver = ProductDriver::new(&tel, root);
        let mut world = World::new(&tel);
        let mut producers = WorldProductProducers::new(&mut world);

        let outcome = driver.pull(&mut producers, ProductKey::TransportShape(position.clone()));

        assert_eq!(
            outcome,
            PullOutcome::wait_on_product(ProductKey::TransportComponent(position))
        );
    }

    #[test]
    fn world_product_transport_artifacts_are_session_backed_not_self_waits() {
        use super::super::transport::{
            ActivationSymbol, CallableDescr, CallableFacts, ExecutableSymbol, LaneDescr, ShapeDescr, TransportClass,
        };

        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(7);
        let executable = fake_executable(root);
        let mut world = World::new(&tel);
        let int = world.types_mut().int();
        let lane = world.intern_lane(LaneDescr {
            ty: int,
            class: TransportClass::Value,
        });
        let shape = world.intern_shape(ShapeDescr::Lane(lane));
        let callable = world.intern_callable(CallableDescr {
            function: Some(executable.activation.function),
            capture_shapes: Box::default(),
            capture_lanes: Box::default(),
        });
        let callable_facts = CallableFacts {
            resolutions: Box::new([ExecutableSymbol {
                activation: ActivationSymbol {
                    function: executable.activation.function,
                    input: Box::default(),
                },
                need: executable.need,
            }]),
            direct_surfaces: Box::new([Box::new([shape])]),
            direct_edges: Box::default(),
            boundary_ids: Box::default(),
        };
        let position = TransportPosition::ExecutableReturn {
            executable: callable_facts.resolutions[0].clone(),
        };
        let mut driver = ProductDriver::new(&tel, root);
        driver.session_mut().record_transport_shape(position.clone(), shape);
        driver
            .session_mut()
            .record_transport_component(position.clone(), vec![position.clone()]);
        driver
            .session_mut()
            .record_callable_facts(callable, callable_facts.clone());
        let mut producers = WorldProductProducers::new(&mut world);

        assert_eq!(
            driver.pull(&mut producers, ProductKey::TransportShape(position.clone())),
            PullOutcome::Produced(ProductValue::TransportShape(TransportShapeFact::Shape(shape)))
        );
        assert_eq!(
            driver.pull(&mut producers, ProductKey::TransportComponent(position.clone())),
            PullOutcome::Produced(ProductValue::TransportComponent(TransportComponentInventory {
                anchor: position.clone(),
                positions: vec![position],
            }))
        );
        assert_eq!(
            driver.pull(&mut producers, ProductKey::CallableFacts(callable)),
            PullOutcome::Produced(ProductValue::CallableFacts(Some(callable_facts)))
        );
        assert_eq!(driver.session().producer_pokes(), 0);
    }

    #[test]
    fn executable_effects_product_settles_symbolic_mutual_recursion_without_root_loop() {
        use super::super::artifact::{
            CallEdge, CallReturnFlow, CallTarget, DirectCallEdge, MaterializedCallEdge, MaterializedExecutable,
            MaterializedExecutableTransport,
        };
        use super::super::body::{
            ControlEntryId, ControlEntryOrigin, LoweredClause, LoweredEntry, LoweredStep, LoweredTail,
        };
        use super::super::transport::ExecutableSymbol;
        use crate::source::Span;

        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(8);
        let first = fake_executable_with_function(root, 80);
        let second = fake_executable_with_function(root, 81);
        let first_symbol = executable_symbol_for_test(&first);
        let second_symbol = executable_symbol_for_test(&second);
        let mut driver = ProductDriver::new(&tel, root);
        driver.session_mut().record_materialized_executable(
            first.clone(),
            fake_materialized_executable(
                allocating_body(),
                first_symbol.clone(),
                Some(fake_call_edge(
                    second.clone(),
                    first_symbol.clone(),
                    second_symbol.clone(),
                )),
            ),
        );
        driver.session_mut().record_materialized_executable(
            second.clone(),
            fake_materialized_executable(
                empty_body(),
                second_symbol.clone(),
                Some(fake_call_edge(first.clone(), second_symbol, first_symbol)),
            ),
        );
        let mut world = World::new(&tel);
        let mut producers = WorldProductProducers::new(&mut world);

        let outcome = driver.pull(&mut producers, ProductKey::ExecutableEffects(second.clone()));

        let PullOutcome::Produced(ProductValue::ExecutableEffects(effects)) = outcome else {
            panic!("effects product should settle the local symbolic SCC, got {outcome:?}")
        };
        assert!(effects.allocates, "effects should propagate through mutual recursion");
        assert!(
            driver
                .session()
                .executable_effects(&first)
                .is_some_and(|effects| effects.allocates)
        );
        assert!(
            driver
                .session()
                .executable_effects(&second)
                .is_some_and(|effects| effects.allocates)
        );
        assert_eq!(driver.session().producer_pokes(), 0);

        fn fake_materialized_executable(
            body: super::super::LoweredBody,
            executable: ExecutableSymbol,
            edge: Option<MaterializedCallEdge>,
        ) -> MaterializedExecutable {
            let return_position = TransportPosition::ExecutableReturn {
                executable: executable.clone(),
            };
            MaterializedExecutable {
                entry_dispatch: None,
                return_ty: test_ty(),
                runtime_demand: ExecutableRuntimeDemand::default(),
                transport: MaterializedExecutableTransport {
                    executable,
                    input_positions: Vec::new(),
                    return_position,
                    resume_positions: Vec::new(),
                    return_payload_positions: Vec::new(),
                    entry_capture_positions: Vec::new(),
                    call_arg_positions: Vec::new(),
                    value_positions: Vec::new(),
                },
                original_entry_ids: Vec::new(),
                value_types: HashMap::new(),
                effects: EffectSummary::default(),
                body,
                call_edges: edge
                    .map(|edge| HashMap::from([(CallSiteId::from_u32(0), edge)]))
                    .unwrap_or_default(),
            }
        }

        fn fake_call_edge(
            callee: ExecutableKey,
            caller_symbol: ExecutableSymbol,
            callee_symbol: ExecutableSymbol,
        ) -> MaterializedCallEdge {
            MaterializedCallEdge {
                target: CallEdge::Direct(DirectCallEdge {
                    callee: CallTarget::Local(callee),
                    return_flow: CallReturnFlow::Tail {
                        callee_return: TransportPosition::ExecutableReturn {
                            executable: callee_symbol,
                        },
                        caller_return: TransportPosition::ExecutableReturn {
                            executable: caller_symbol,
                        },
                    },
                    extern_marshals: None,
                }),
                return_ty: test_ty(),
            }
        }

        fn allocating_body() -> super::super::LoweredBody {
            let value = ValueId::from_u32(0);
            clauses_with_projection(vec![LoweredStep::Tuple {
                value,
                items: Vec::new(),
            }])
        }

        fn empty_body() -> super::super::LoweredBody {
            clauses_with_projection(Vec::new())
        }

        fn clauses_with_projection(projections: Vec<LoweredStep>) -> super::super::LoweredBody {
            super::super::LoweredBody::Clauses {
                clauses: vec![LoweredClause {
                    span: Span::DUMMY,
                    params: Vec::new(),
                    projections,
                    entry: ControlEntryId::from_u32(0),
                }],
                entries: vec![LoweredEntry {
                    span: Span::DUMMY,
                    origin: ControlEntryOrigin::Clause,
                    params: Vec::new(),
                    captures: Vec::new(),
                    reusable_cons_captures: Vec::new(),
                    steps: Vec::new(),
                    tail: LoweredTail::Halt {
                        atom: "done".to_string(),
                    },
                }],
                generated: Vec::new(),
            }
        }

        fn test_ty() -> super::super::Ty {
            let mut types = super::super::Types::new();
            types.none()
        }
    }

    #[test]
    fn pull_session_finished_telemetry_reports_producer_pokes() {
        let tel = ConfiguredTelemetry::new();
        let capture = Capture::new();
        tel.attach(&[], capture.handler());
        let root = RootId::for_test(5);
        let executable = fake_executable(root);
        let mut driver = ProductDriver::new(&tel, root);
        let mut producers = FakeProducers::default();

        assert_eq!(
            driver.pull(&mut producers, ProductKey::RuntimeDemand(executable)),
            PullOutcome::Produced(ProductValue::Unit)
        );
        driver.session_mut().record_producer_pokes(2);
        driver.finish_session();

        let finished = capture
            .last(&["fz", "compiler2", "pull", "session", "finished"])
            .expect("pull session should emit final inventory telemetry");
        assert_eq!(measurement_u64(&finished, "executables"), 1);
        assert_eq!(measurement_u64(&finished, "producer_pokes"), 2);
    }

    #[test]
    fn root_executable_frontier_emits_legacy_scan_telemetry() {
        let tel = ConfiguredTelemetry::new();
        let capture = Capture::new();
        tel.attach(&[], capture.handler());
        let root = RootId::for_test(8);
        let world = World::new(&tel);

        assert!(world.root_executable_frontier(root).is_empty());

        let event = capture
            .last(&["fz", "compiler2", "legacy", "root_executable_frontier"])
            .expect("root frontier scan should emit legacy telemetry");
        assert_eq!(measurement_u64(&event, "root_id"), root.as_u32() as u64);
        assert_eq!(measurement_u64(&event, "executable_count"), 0);
    }

    fn fake_executable(root: RootId) -> ExecutableKey {
        fake_executable_with_function(root, root.as_u32() + 10)
    }

    fn fake_executable_with_function(root: RootId, function: u32) -> ExecutableKey {
        let function = super::super::FunctionId::for_test(function);
        let mut types = super::super::Types::new();
        let activation = super::super::ActivationKey::from_inputs(root, function, &[], &mut types);
        ExecutableKey {
            activation,
            need: super::super::ExecutableNeed::Value,
        }
    }

    fn executable_symbol_for_test(executable: &ExecutableKey) -> super::super::transport::ExecutableSymbol {
        super::super::transport::ExecutableSymbol {
            activation: super::super::transport::ActivationSymbol {
                function: executable.activation.function,
                input: Box::default(),
            },
            need: executable.need,
        }
    }

    fn measurement_u64(event: &crate::telemetry::capture::OwnedEvent, key: &str) -> u64 {
        match event.measurements.get(key) {
            Some(crate::telemetry::Value::U64(value)) => *value,
            other => panic!("expected u64 measurement {key}, got {other:?}"),
        }
    }
}
