//! Product-keyed pull substrate for compiler2 artifacts.
//!
//! This module is intentionally separate from the existing job scheduler. A
//! product producer answers one named demand and can only return a value or
//! explicit waits. It does not enqueue jobs, schedule follow-up work, or scan a
//! root frontier.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::telemetry::{Telemetry, TelemetryExt as _};

use super::artifact::{
    AbiReadyExecutable, BackendCallArg, BackendReceive, BackendStep, CallEdge, CallReturnFlow, EffectSummary,
    MaterializedExecutable, ReusableConsCapture, RootBackendProductAnswer,
};
use super::body::{
    CallSiteId, ControlDestination, ControlDispatch, ControlEntryId, DispatchBindings, LoweredExtern, ValueId,
};
use super::drive::FactKey;
use super::facts::{FactMovement, FactState, FactUse};
use super::identity::{ExecutableKey, RootId};
use super::jobs::runtime_demand::ExecutableFacts;
use super::scheduler::WorkStartTally;
use super::semantic::{ExecutableRuntimeDemand, RuntimeDemand};
use super::transport::{CallableConstructionOwner, ShapeId, TransportPosition};
pub use super::transport::{TransportCarrier, TransportLayout};
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
    ExecutableFacts(ExecutableKey),
    RuntimeDemand(ExecutableKey),
    OutgoingEdgeFrontier(RootId),
    OutgoingInputEdges(ExecutableKey),
    IncomingInputRelations(RootId),
    IncomingInputSlot(InputSlot),
    TransportShape(TransportPosition),
    CallableConstruction(TransportPosition),
}

impl ProductKey {
    pub fn kind(&self) -> &'static str {
        match self {
            Self::RootBackendProduct(_) => "root_backend_product",
            Self::BackendExecutable(_) => "backend_executable",
            Self::AbiExecutable(_) => "abi_executable",
            Self::MaterializedExecutable(_) => "materialized_executable",
            Self::ExecutableEffects(_) => "executable_effects",
            Self::ExecutableFacts(_) => "executable_facts",
            Self::RuntimeDemand(_) => "runtime_demand",
            Self::OutgoingEdgeFrontier(_) => "outgoing_edge_frontier",
            Self::OutgoingInputEdges(_) => "outgoing_input_edges",
            Self::IncomingInputRelations(_) => "incoming_input_relations",
            Self::IncomingInputSlot(_) => "incoming_input_slot",
            Self::TransportShape(_) => "transport_shape",
            Self::CallableConstruction(_) => "callable_construction",
        }
    }

    fn executable(&self) -> Option<&ExecutableKey> {
        match self {
            Self::BackendExecutable(executable)
            | Self::AbiExecutable(executable)
            | Self::MaterializedExecutable(executable)
            | Self::ExecutableEffects(executable)
            | Self::ExecutableFacts(executable)
            | Self::RuntimeDemand(executable)
            | Self::OutgoingInputEdges(executable) => Some(executable),
            Self::IncomingInputSlot(slot) => Some(&slot.executable),
            Self::RootBackendProduct(_)
            | Self::OutgoingEdgeFrontier(_)
            | Self::IncomingInputRelations(_)
            | Self::TransportShape(_)
            | Self::CallableConstruction(_) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TransportShapeFact {
    Layout(TransportLayout),
}

impl TransportShapeFact {
    pub fn shape(&self) -> Option<ShapeId> {
        match self {
            Self::Layout(layout) => Some(layout.structural),
        }
    }

    pub fn layout(&self) -> Option<TransportLayout> {
        match self {
            Self::Layout(layout) => Some(*layout),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ProductValue {
    Unit,
    RootBackendProduct(Box<RootBackendProductAnswer>),
    BackendExecutable(Box<SymbolicBackendExecutable>),
    AbiExecutable(Box<AbiReadyExecutable>),
    MaterializedExecutable(Box<MaterializedExecutable>),
    ExecutableEffects(EffectSummary),
    ExecutableFacts(Rc<ExecutableFacts>),
    RuntimeDemand(Box<ExecutableRuntimeDemand>),
    OutgoingEdgeFrontier(Rc<HashSet<ExecutableKey>>),
    OutgoingInputEdges(Rc<HashMap<InputSlot, HashSet<IncomingInputSource>>>),
    IncomingInputRelations(Rc<HashMap<InputSlot, HashSet<IncomingInputSource>>>),
    IncomingInputSlot(HashSet<IncomingInputSource>),
    TransportShape(TransportShapeFact),
    CallableConstruction(Box<CallableConstructionOwner>),
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
    pub origin: SymbolicBackendEntryOrigin,
    pub params: Vec<ValueId>,
    pub captures: Vec<ValueId>,
    pub capture_positions: Vec<TransportPosition>,
    pub reusable_cons_captures: Vec<ReusableConsCapture>,
    pub steps: Vec<BackendStep>,
    pub tail: SymbolicBackendTail,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolicBackendEntryOrigin {
    Clause,
    Branch,
    ReceiveOutcome,
    DeliveredResume {
        value: ValueId,
        position: TransportPosition,
    },
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
    produced: HashMap<ProductKey, ProductEntry>,
    displaced: HashMap<ProductKey, ProductEntry>,
    pending_dependencies: HashMap<ProductKey, ProductDependencies>,
    product_readers: HashMap<ProductKey, HashSet<ProductKey>>,
    fact_readers: HashMap<FactKey, HashSet<ProductKey>>,
    fact_stale_dependencies: HashMap<ProductKey, HashSet<FactKey>>,
    dirty_descendants: HashSet<ProductKey>,
    in_progress: HashSet<ProductKey>,
    invalidated_in_progress: HashSet<ProductKey>,
}

#[derive(Debug, Clone, PartialEq)]
struct ProductEntry {
    value: ProductValue,
    generation: u64,
    dependencies: ProductDependencies,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ProductDependencies {
    products: HashMap<ProductKey, Option<u64>>,
    facts: HashMap<FactUse<FactKey>, FactState>,
}

impl ProductMemo {
    pub fn get(&self, key: &ProductKey) -> Option<&ProductValue> {
        self.produced.get(key).map(|entry| &entry.value)
    }

    pub fn generation(&self, key: &ProductKey) -> Option<u64> {
        self.produced.get(key).map(|entry| entry.generation)
    }

    #[cfg(test)]
    pub(crate) fn product_dependencies(&self, key: &ProductKey) -> Option<&HashMap<ProductKey, Option<u64>>> {
        self.produced.get(key).map(|entry| &entry.dependencies.products)
    }

    pub fn contains_in_progress(&self, key: &ProductKey) -> bool {
        self.in_progress.contains(key)
    }

    fn pending_dependency_reaches(&self, from: &ProductKey, target: &ProductKey) -> bool {
        let mut pending = vec![from.clone()];
        let mut seen = HashSet::new();
        while let Some(key) = pending.pop() {
            if key == *target {
                return true;
            }
            if !seen.insert(key.clone()) {
                continue;
            }
            if let Some(dependencies) = self.product_dependencies_for_group(&key) {
                pending.extend(dependencies.products.keys().cloned());
            }
        }
        false
    }

    fn pending_strong_component(
        &self,
        current: &ProductKey,
        current_dependencies: &ProductDependencies,
        member: fn(&ProductKey) -> bool,
    ) -> Vec<ProductKey> {
        let mut candidates = self
            .pending_dependencies
            .keys()
            .chain(self.produced.keys())
            .chain(self.displaced.keys())
            .filter(|key| member(key))
            .cloned()
            .collect::<HashSet<_>>();
        candidates.insert(current.clone());
        candidates
            .into_iter()
            .filter(|candidate| {
                self.dependency_reaches_with_current(current, candidate, current, current_dependencies, member)
                    && self.dependency_reaches_with_current(candidate, current, current, current_dependencies, member)
            })
            .collect()
    }

    fn dependency_reaches_with_current(
        &self,
        from: &ProductKey,
        target: &ProductKey,
        current: &ProductKey,
        current_dependencies: &ProductDependencies,
        member: fn(&ProductKey) -> bool,
    ) -> bool {
        let mut pending = vec![from.clone()];
        let mut seen = HashSet::new();
        while let Some(key) = pending.pop() {
            if key == *target {
                return true;
            }
            if !seen.insert(key.clone()) {
                continue;
            }
            let dependencies = if &key == current {
                Some(current_dependencies)
            } else {
                self.product_dependencies_for_group(&key)
            };
            if let Some(dependencies) = dependencies {
                pending.extend(
                    dependencies
                        .products
                        .keys()
                        .filter(|dependency| member(dependency))
                        .cloned(),
                );
            }
        }
        false
    }

    fn product_dependencies_for_group(&self, key: &ProductKey) -> Option<&ProductDependencies> {
        self.pending_dependencies
            .get(key)
            .or_else(|| self.produced.get(key).map(|entry| &entry.dependencies))
            .or_else(|| self.displaced.get(key).map(|entry| &entry.dependencies))
    }

    fn is_displaced(&self, key: &ProductKey) -> bool {
        self.displaced.contains_key(key)
    }

    pub fn runtime_demand(&self, executable: &ExecutableKey) -> Option<&ExecutableRuntimeDemand> {
        match self.get(&ProductKey::RuntimeDemand(executable.clone())) {
            Some(ProductValue::RuntimeDemand(demand)) => Some(demand.as_ref()),
            Some(
                ProductValue::Unit
                | ProductValue::RootBackendProduct(_)
                | ProductValue::BackendExecutable(_)
                | ProductValue::AbiExecutable(_)
                | ProductValue::MaterializedExecutable(_)
                | ProductValue::ExecutableEffects(_)
                | ProductValue::ExecutableFacts(_)
                | ProductValue::OutgoingEdgeFrontier(_)
                | ProductValue::OutgoingInputEdges(_)
                | ProductValue::IncomingInputRelations(_)
                | ProductValue::IncomingInputSlot(_)
                | ProductValue::TransportShape(_)
                | ProductValue::CallableConstruction(_),
            )
            | None => None,
        }
    }

    fn begin(&mut self, key: ProductKey) -> bool {
        self.in_progress.insert(key)
    }

    fn finish(&mut self, key: &ProductKey, value: ProductValue, dependencies: ProductDependencies) -> bool {
        self.in_progress.remove(key);
        if self.invalidated_in_progress.remove(key) {
            self.produced.remove(key);
            return false;
        }
        let previous = self.produced.remove(key).or_else(|| self.displaced.remove(key));
        self.remove_reader_dependencies(key, previous.as_ref().map(|entry| &entry.dependencies));
        self.take_pending_dependencies(key);
        let changed = previous.as_ref().is_none_or(|entry| entry.value != value);
        let generation = previous.as_ref().map_or(1, |entry| {
            if changed {
                entry.generation + 1
            } else {
                entry.generation
            }
        });
        self.install_reader_dependencies(key, &dependencies);
        self.fact_stale_dependencies.remove(key);
        self.dirty_descendants.remove(key);
        self.produced.insert(
            key.clone(),
            ProductEntry {
                value,
                generation,
                dependencies,
            },
        );
        if changed {
            self.invalidate_readers(key);
        } else {
            self.refresh_reader_dirtiness(key);
        }
        true
    }

    fn finish_group(&mut self, members: Vec<(ProductKey, ProductValue, ProductDependencies)>) -> bool {
        let member_keys = members.iter().map(|(key, _, _)| key.clone()).collect::<HashSet<_>>();
        assert_eq!(member_keys.len(), members.len());
        if member_keys.iter().any(|key| self.invalidated_in_progress.contains(key)) {
            self.reject_group(&member_keys);
            return false;
        }

        let mut group_dependencies = ProductDependencies::default();
        for (_, _, dependencies) in &members {
            for (dependency, generation) in &dependencies.products {
                if member_keys.contains(dependency) {
                    continue;
                }
                if group_dependencies
                    .products
                    .get(dependency)
                    .is_some_and(|recorded| recorded != generation)
                {
                    self.reject_group(&member_keys);
                    return false;
                }
                group_dependencies.products.insert(dependency.clone(), *generation);
            }
            for (fact, state) in &dependencies.facts {
                if group_dependencies
                    .facts
                    .get(fact)
                    .is_some_and(|recorded| recorded != state)
                {
                    self.reject_group(&member_keys);
                    return false;
                }
                group_dependencies.facts.insert(fact.clone(), *state);
            }
        }

        let mut prepared = Vec::with_capacity(members.len());
        for (key, value, _) in members {
            self.in_progress.remove(&key);
            let previous = self.produced.remove(&key).or_else(|| self.displaced.remove(&key));
            self.remove_reader_dependencies(&key, previous.as_ref().map(|entry| &entry.dependencies));
            self.take_pending_dependencies(&key);
            let changed = previous.as_ref().is_none_or(|entry| entry.value != value);
            let generation = previous.as_ref().map_or(1, |entry| {
                if changed {
                    entry.generation + 1
                } else {
                    entry.generation
                }
            });
            prepared.push((key, value, group_dependencies.clone(), generation, changed));
        }

        for (key, value, dependencies, generation, _) in &prepared {
            self.install_reader_dependencies(key, dependencies);
            self.fact_stale_dependencies.remove(key);
            self.dirty_descendants.remove(key);
            self.produced.insert(
                key.clone(),
                ProductEntry {
                    value: value.clone(),
                    generation: *generation,
                    dependencies: dependencies.clone(),
                },
            );
        }
        for (key, _, _, _, changed) in prepared {
            if changed {
                self.invalidate_readers(&key);
            } else {
                self.refresh_reader_dirtiness(&key);
            }
        }
        true
    }

    fn reject_group(&mut self, member_keys: &HashSet<ProductKey>) {
        for key in member_keys {
            self.in_progress.remove(key);
            self.invalidated_in_progress.remove(key);
            self.take_pending_dependencies(key);
            if let Some(entry) = self.produced.remove(key) {
                self.remove_reader_dependencies(key, Some(&entry.dependencies));
                self.displaced.insert(key.clone(), entry);
                self.mark_readers_dirty(key);
            }
            if let Some(entry) = self.displaced.get_mut(key) {
                entry.dependencies = ProductDependencies::default();
            }
        }
    }

    fn unblock(&mut self, key: &ProductKey, dependencies: ProductDependencies) {
        self.in_progress.remove(key);
        self.invalidated_in_progress.remove(key);
        let previous = self.take_pending_dependencies(key).unwrap_or_default();
        let mut retained = previous;
        retained.products.extend(dependencies.products);
        retained.facts.extend(dependencies.facts);
        self.install_reader_dependencies(key, &retained);
        self.pending_dependencies.insert(key.clone(), retained);
    }

    fn remove(&mut self, key: &ProductKey) {
        self.displace_for_reproduction(key);
    }

    fn displace_for_reproduction(&mut self, key: &ProductKey) {
        if self.in_progress.contains(key) {
            self.invalidated_in_progress.insert(key.clone());
        }
        let pending = self.take_pending_dependencies(key).is_some();
        if let Some(entry) = self.produced.remove(key) {
            self.remove_reader_dependencies(key, Some(&entry.dependencies));
            self.displaced.insert(key.clone(), entry);
            self.mark_readers_dirty(key);
        }
        if pending {
            self.invalidate_readers(key);
        }
    }

    fn prepare_stale_for_reproduction(&mut self, key: &ProductKey) {
        self.fact_stale_dependencies.remove(key);
        self.displace_for_reproduction(key);
    }

    fn install_reader_dependencies(&mut self, reader: &ProductKey, dependencies: &ProductDependencies) {
        for dependency in dependencies.products.keys() {
            if dependency != reader {
                self.product_readers
                    .entry(dependency.clone())
                    .or_default()
                    .insert(reader.clone());
            }
        }
        for fact in dependencies.facts.keys() {
            self.fact_readers
                .entry(fact.fact().clone())
                .or_default()
                .insert(reader.clone());
        }
    }

    fn remove_reader_dependencies(&mut self, reader: &ProductKey, dependencies: Option<&ProductDependencies>) {
        let Some(dependencies) = dependencies else {
            return;
        };
        for dependency in dependencies.products.keys() {
            let remove_entry = self.product_readers.get_mut(dependency).is_some_and(|readers| {
                readers.remove(reader);
                readers.is_empty()
            });
            if remove_entry {
                self.product_readers.remove(dependency);
            }
        }
        for fact in dependencies.facts.keys() {
            let remove_entry = self.fact_readers.get_mut(fact.fact()).is_some_and(|readers| {
                readers.remove(reader);
                readers.is_empty()
            });
            if remove_entry {
                self.fact_readers.remove(fact.fact());
            }
        }
    }

    fn take_pending_dependencies(&mut self, reader: &ProductKey) -> Option<ProductDependencies> {
        let pending = self.pending_dependencies.remove(reader);
        self.remove_reader_dependencies(reader, pending.as_ref());
        pending
    }

    fn invalidate_readers(&mut self, key: &ProductKey) {
        let readers = self.product_readers.get(key).cloned().unwrap_or_default();
        for reader in readers {
            self.displace_for_reproduction(&reader);
        }
    }

    fn reconcile_fact_movements(&mut self, pending: &HashMap<FactKey, FactState>) {
        for (fact_key, final_state) in pending {
            let readers = self.fact_readers.get(fact_key).cloned().unwrap_or_default();
            for reader in readers {
                let pending_stale = self.pending_dependencies.get(&reader).is_some_and(|dependencies| {
                    dependencies
                        .facts
                        .iter()
                        .any(|(fact, recorded)| fact.fact() == fact_key && final_state.projected(fact) != *recorded)
                });
                if pending_stale {
                    self.displace_for_reproduction(&reader);
                    continue;
                }
                let stale = self.produced.get(&reader).is_some_and(|entry| {
                    entry
                        .dependencies
                        .facts
                        .iter()
                        .any(|(fact, recorded)| fact.fact() == fact_key && final_state.projected(fact) != *recorded)
                });
                let was_stale = self.fact_stale_dependencies.contains_key(&reader);
                if stale {
                    self.fact_stale_dependencies
                        .entry(reader.clone())
                        .or_default()
                        .insert(fact_key.clone());
                } else if let Some(stale_facts) = self.fact_stale_dependencies.get_mut(&reader) {
                    stale_facts.remove(fact_key);
                    if stale_facts.is_empty() {
                        self.fact_stale_dependencies.remove(&reader);
                    }
                }
                let is_stale = self.fact_stale_dependencies.contains_key(&reader);
                if !was_stale && is_stale {
                    self.mark_readers_dirty(&reader);
                } else if was_stale && !is_stale {
                    self.refresh_reader_dirtiness(&reader);
                }
            }
        }
    }

    fn mark_readers_dirty(&mut self, key: &ProductKey) {
        let readers = self.product_readers.get(key).cloned().unwrap_or_default();
        for reader in readers {
            if self.dirty_descendants.insert(reader.clone()) {
                self.mark_readers_dirty(&reader);
            }
        }
    }

    fn refresh_reader_dirtiness(&mut self, key: &ProductKey) {
        let readers = self.product_readers.get(key).cloned().unwrap_or_default();
        for reader in readers {
            let dirty = self.produced.get(&reader).is_some_and(|entry| {
                entry.dependencies.products.keys().any(|dependency| {
                    self.displaced.contains_key(dependency)
                        || self.fact_stale_dependencies.contains_key(dependency)
                        || self.dirty_descendants.contains(dependency)
                })
            });
            if dirty {
                self.dirty_descendants.insert(reader.clone());
            } else if self.dirty_descendants.remove(&reader) {
                self.refresh_reader_dirtiness(&reader);
            }
        }
    }

    fn stale_dependency(&self, key: &ProductKey) -> Option<ProductKey> {
        self.stale_dependency_inner(key, &mut HashSet::new())
    }

    fn stale_dependency_inner(&self, key: &ProductKey, visiting: &mut HashSet<ProductKey>) -> Option<ProductKey> {
        if self.fact_stale_dependencies.contains_key(key) {
            return Some(key.clone());
        }
        if self.displaced.contains_key(key) {
            return Some(key.clone());
        }
        if !self.dirty_descendants.contains(key) {
            return None;
        }
        let entry = self.produced.get(key)?;
        if !visiting.insert(key.clone()) {
            return Some(key.clone());
        }
        for (dependency, generation) in &entry.dependencies.products {
            let current = self.produced.get(dependency).map(|entry| entry.generation);
            if current != *generation {
                visiting.remove(key);
                return Some(if current.is_none() {
                    dependency.clone()
                } else {
                    key.clone()
                });
            }
            if generation.is_some()
                && let Some(stale) = self.stale_dependency_inner(dependency, visiting)
            {
                visiting.remove(key);
                return Some(stale);
            }
        }
        visiting.remove(key);
        None
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IncomingInputSource {
    pub producer: ExecutableKey,
    pub value: ValueId,
    pub role: IncomingInputRole,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IncomingInputRole {
    CallArgument,
    CallableCapture {
        construction: ValueId,
        capture_index: usize,
    },
}

#[derive(Debug)]
pub struct PullSession {
    root: RootId,
    memo: ProductMemo,
    outgoing_edge_request_set: HashSet<ExecutableKey>,
    demanded_executables: HashSet<ExecutableKey>,
    runtime_demand_dependents: HashMap<ExecutableKey, HashSet<ExecutableKey>>,
    // Reverse callable-flow demand edges `resolution -> producers`, kept apart
    // from `runtime_demand_dependents` (direct callsite reads) so the
    // edge-derived transport invalidation walks only the direct graph while
    // the demand EPOCH wipe reaches flow-coupled members too.
    demand_flow_dependents: HashMap<ExecutableKey, HashSet<ExecutableKey>>,
    // The demand-relevant callee set each executable's demand settle used (its
    // cone edges). Re-materialization is the demand epoch gate: a materialized
    // call-edge set that escapes this settled set re-keys the call graph, so
    // the executable's demand cone is invalidated and re-settled -- the ONLY
    // path that retracts settled demand, mirroring how the effect projection
    // gate re-settles effects.
    settled_demand_callees: HashMap<ExecutableKey, HashSet<ExecutableKey>>,
    // The effect-relevant projection (local effect summary + local callee
    // set) of the latest materialized executable recorded per key. Effect
    // products are invalidated only when this projection moves; re-derived
    // materialized values that only carry demand/transport wobble leave the
    // effect cone standing.
    latest_effect_inputs: HashMap<ExecutableKey, (EffectSummary, HashSet<ExecutableKey>)>,
    // Reverse effect edges `callee -> callers`, maintained in lockstep with
    // `latest_effect_inputs`: whenever a materialized executable is recorded,
    // its callee set (the SAME `CallEdge::local_callees` set the effects
    // producer traverses -- Direct targets plus every Dispatch arm, which
    // includes closure/boundary-resolved callees) replaces the caller's
    // previous edges. `invalidate_effect_cone` walks THIS graph, so every
    // caller whose ExecutableEffects consumed a callee's projection is
    // reachable by construction. The runtime-demand dependents graph only
    // carries CallSiteSummary direct-target edges and MUST NOT be used for
    // effect invalidation.
    effect_dependents: HashMap<ExecutableKey, HashSet<ExecutableKey>>,
    // Per-caller SETTLED return-demand evidence, keyed `caller -> (callee ->
    // demand)` -- the cross-settle channel a demand cone reads as external
    // caller input (`external_return_demand`). A callee present here is
    // OBSERVED (even when its demand is the bottom `ignore` discard marker); a
    // callee absent is not-yet-observed. Every entry is a settled fixpoint
    // value: producers replace their contributions only at settle time, and a
    // re-settled caller whose contribution DROPS (an epoch event) retracts
    // cleanly because the `return_demands` join is rebuilt from current
    // contributions -- the join is not a monotone accumulator.
    return_demand_contributions: HashMap<ExecutableKey, HashMap<ExecutableKey, RuntimeDemand>>,
    return_demand_contributors: HashMap<ExecutableKey, HashSet<ExecutableKey>>,
    return_demands: HashMap<ExecutableKey, RuntimeDemand>,
    // The INPUT-side sibling of the three fields above: a boundary-published
    // callable's contract can pin specific argument POSITIONS on a resolved
    // target even when the target's own body elides them (a destructor that
    // ignores its payload). Keyed the same way, with an extra position level
    // (`usize` = semantic input index) nested under the target.
    input_demand_contributions: HashMap<ExecutableKey, HashMap<ExecutableKey, HashMap<usize, RuntimeDemand>>>,
    input_demand_contributors: HashMap<ExecutableKey, HashSet<ExecutableKey>>,
    input_demands: HashMap<ExecutableKey, HashMap<usize, RuntimeDemand>>,
    materialized_executables: HashMap<ExecutableKey, MaterializedExecutable>,
    executable_effects: HashMap<ExecutableKey, EffectSummary>,
    abi_executables: HashMap<ExecutableKey, AbiReadyExecutable>,
    backend_executables: HashMap<ExecutableKey, SymbolicBackendExecutable>,
    executable_index: HashMap<ExecutableKey, usize>,
    producer_pokes: u64,
    /// The world's cumulative work-start attribution snapshot, recorded by the
    /// caller that has `World` in scope at `finish_session` time (mirrors
    /// `record_producer_pokes`'s pattern for the same reason: the session
    /// itself never touches `World`). `unsanctioned_work_starts()` must be zero
    /// on every production-driven path; see `WorkStartReason::Unclassified`.
    work_starts: WorkStartTally,
    pending_fact_states: HashMap<FactKey, FactState>,
}

impl PullSession {
    pub fn new(root: RootId) -> Self {
        Self {
            root,
            memo: ProductMemo::default(),
            outgoing_edge_request_set: HashSet::new(),
            demanded_executables: HashSet::new(),
            runtime_demand_dependents: HashMap::new(),
            demand_flow_dependents: HashMap::new(),
            settled_demand_callees: HashMap::new(),
            latest_effect_inputs: HashMap::new(),
            effect_dependents: HashMap::new(),
            return_demand_contributions: HashMap::new(),
            return_demand_contributors: HashMap::new(),
            return_demands: HashMap::new(),
            input_demand_contributions: HashMap::new(),
            input_demand_contributors: HashMap::new(),
            input_demands: HashMap::new(),
            materialized_executables: HashMap::new(),
            executable_effects: HashMap::new(),
            abi_executables: HashMap::new(),
            backend_executables: HashMap::new(),
            executable_index: HashMap::new(),
            producer_pokes: 0,
            work_starts: WorkStartTally::default(),
            pending_fact_states: HashMap::new(),
        }
    }

    pub fn root(&self) -> RootId {
        self.root
    }

    fn outgoing_edge_requests(&self) -> &HashSet<ExecutableKey> {
        &self.outgoing_edge_request_set
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

    pub fn record_runtime_demand_dependency(&mut self, dependency: ExecutableKey, dependent: ExecutableKey) {
        if dependency == dependent {
            return;
        }
        self.runtime_demand_dependents
            .entry(dependency)
            .or_default()
            .insert(dependent);
    }

    /// Record a callable-flow demand dependency `resolution <- producer`. These
    /// edges join the demand EPOCH wipe's walk only; they never widen the
    /// edge-derived transport invalidation.
    pub fn record_demand_flow_dependency(&mut self, dependency: ExecutableKey, dependent: ExecutableKey) {
        if dependency == dependent {
            return;
        }
        self.demand_flow_dependents
            .entry(dependency)
            .or_default()
            .insert(dependent);
    }

    /// Memoize one cone member's settled runtime demand. The demand SCC settles
    /// inside its producer, so every member is published here at once -- only
    /// the settled fixpoint is ever observable. A re-settle that changes a
    /// member's value invalidates the member's transport and artifact products
    /// (they consumed the displaced demand); an unchanged re-settle leaves them
    /// standing.
    #[cfg(test)]
    pub fn record_settled_runtime_demand(&mut self, executable: ExecutableKey, demand: ExecutableRuntimeDemand) {
        let key = ProductKey::RuntimeDemand(executable.clone());
        let previous = match self.memo.produced.get(&key).or_else(|| self.memo.displaced.get(&key)) {
            Some(ProductEntry {
                value: ProductValue::RuntimeDemand(previous),
                ..
            }) => Some(previous.as_ref().clone()),
            _ => None,
        };
        let changed = previous.is_some_and(|previous| previous != demand);
        self.memo.finish(
            &key,
            ProductValue::RuntimeDemand(Box::new(demand)),
            ProductDependencies::default(),
        );
        if changed {
            self.invalidate_artifact_products(&executable);
        }
    }

    /// Record the demand-relevant callee set a settle derived for `executable`
    /// -- the epoch baseline `record_materialized_executable` gates on.
    pub fn record_settled_demand_callees(&mut self, executable: ExecutableKey, callees: HashSet<ExecutableKey>) {
        self.settled_demand_callees.insert(executable, callees);
    }

    /// The demand-relevant callee set recorded for `executable`, including any
    /// materialized call edges an epoch gate folded in -- a settled call-edge
    /// fact source for demand-cone discovery.
    pub fn settled_demand_callees(&self, executable: &ExecutableKey) -> Option<&HashSet<ExecutableKey>> {
        self.settled_demand_callees.get(executable)
    }

    /// The joined return demand contributed to `target` by settled contributors
    /// OUTSIDE `members` -- the cross-settle evidence a cone consumes as an
    /// external input. Contributions from `members` are excluded: they are
    /// re-derived inside the ascent, and a member's stored entry may belong to
    /// a displaced epoch.
    pub fn external_return_demand(
        &self,
        target: &ExecutableKey,
        members: &HashSet<ExecutableKey>,
    ) -> Option<RuntimeDemand> {
        self.return_demand_contributors
            .get(target)
            .into_iter()
            .flatten()
            .filter(|contributor| !members.contains(*contributor))
            .filter_map(|contributor| {
                self.return_demand_contributions
                    .get(contributor)
                    .and_then(|contributions| contributions.get(target))
            })
            .fold(None::<RuntimeDemand>, |acc, demand| match acc {
                Some(mut acc) => {
                    acc.join_assign(demand);
                    Some(acc)
                }
                None => Some(demand.clone()),
            })
    }

    /// The INPUT-side sibling of [`Self::external_return_demand`]: the joined
    /// per-position demand contributed to `target` by settled contributors
    /// OUTSIDE `members` (a boundary contract pinning an argument position on
    /// a resolution this cone treats as an already-settled external).
    pub fn external_input_demand(
        &self,
        target: &ExecutableKey,
        members: &HashSet<ExecutableKey>,
    ) -> HashMap<usize, RuntimeDemand> {
        let mut joined: HashMap<usize, RuntimeDemand> = HashMap::new();
        for contributor in self.input_demand_contributors.get(target).into_iter().flatten() {
            if members.contains(contributor) {
                continue;
            }
            let Some(positions) = self
                .input_demand_contributions
                .get(contributor)
                .and_then(|c| c.get(target))
            else {
                continue;
            };
            for (index, demand) in positions {
                joined
                    .entry(*index)
                    .and_modify(|current| current.join_assign(demand))
                    .or_insert_with(|| demand.clone());
            }
        }
        joined
    }

    pub fn materialized_executable(&self, executable: &ExecutableKey) -> Option<&MaterializedExecutable> {
        self.materialized_executables.get(executable)
    }

    pub fn invalidate_artifact_products_for(&mut self, executable: &ExecutableKey) {
        self.invalidate_artifact_products(executable);
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

    pub fn executable_index(&self) -> &HashMap<ExecutableKey, usize> {
        &self.executable_index
    }

    pub fn producer_pokes(&self) -> u64 {
        self.producer_pokes
    }

    /// The recorded work-start attribution snapshot (per-reason agenda-entry
    /// counts plus whole-fact-table scans). Zero until `record_work_starts`
    /// runs at finish time.
    pub fn work_starts(&self) -> WorkStartTally {
        self.work_starts
    }

    /// Records the world's cumulative work-start attribution snapshot
    /// (`World::work_start_tally`) so `emit_finished` and the guard can read
    /// it. The caller is the pull-drive site that still has `World` in scope
    /// (`ProductDriver::finish_session` cannot -- `PullSession` never holds a
    /// `World` reference).
    pub fn record_work_starts(&mut self, tally: WorkStartTally) {
        self.work_starts = tally;
    }

    pub fn record_producer_pokes(&mut self, count: u64) {
        self.producer_pokes += count;
    }

    /// Replace `caller`'s full set of SETTLED return-demand contributions.
    /// Every callee the caller names becomes (or stays) OBSERVED; any callee the
    /// caller named on a previous settle but not this one has its contribution
    /// withdrawn. Each affected callee's joined return demand is rebuilt from
    /// all current contributors.
    ///
    /// Retraction is epoch-scoped by construction: within one settlement the
    /// joins are quiescent (`settled_members` carries the cone that was just
    /// solved together, and its members' joins equal the fixpoint the settle
    /// computed), so only a NON-member target whose join moves -- a settled
    /// executable outside the re-settled cone consuming displaced evidence --
    /// has its demand-derived products invalidated and re-settled.
    ///
    /// Returns every executable whose demand-derived products the moved joins
    /// displaced (the moved targets plus their transitive demand readers). The
    /// publishing producer inspects this set: a displaced executable it
    /// consumed as an EXTERNAL input means its just-settled members were
    /// derived against pre-growth demands, and the cone must re-settle with
    /// the displaced executable absorbed (the stale-caller window).
    pub fn replace_settled_return_demand_contributions(
        &mut self,
        caller: ExecutableKey,
        contributions: HashMap<ExecutableKey, RuntimeDemand>,
        settled_members: &HashSet<ExecutableKey>,
    ) -> HashSet<ExecutableKey> {
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
        let mut displaced = HashSet::new();
        for target in affected {
            displaced.extend(self.recompute_return_demand(&target, settled_members));
        }
        displaced
    }

    fn recompute_return_demand(
        &mut self,
        target: &ExecutableKey,
        settled_members: &HashSet<ExecutableKey>,
    ) -> HashSet<ExecutableKey> {
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
        debug_assert_eq!(
            self.return_demand_contributors
                .get(target)
                .is_some_and(|c| !c.is_empty()),
            self.return_demands.contains_key(target),
            "return_demand_contributors[target] and return_demands must stay in lockstep: a \
             target is present in one iff present in the other (absent from both = \
             not-yet-observed; present in both = observed, possibly joined to an `ignore` \
             marker). A target present in only one map means the two fell out of sync."
        );
        if changed && !settled_members.contains(target) {
            self.invalidate_demand_derived_products(target)
        } else {
            HashSet::new()
        }
    }

    /// The INPUT-side sibling of [`Self::replace_settled_return_demand_contributions`]:
    /// replace `caller`'s full set of SETTLED boundary input-demand pins
    /// (target -> position -> demand). Same OBSERVED/retraction semantics —
    /// a re-settled caller whose pin drops retracts cleanly because each
    /// target's joined positions are rebuilt from current contributors.
    pub fn replace_settled_input_demand_contributions(
        &mut self,
        caller: ExecutableKey,
        contributions: HashMap<ExecutableKey, HashMap<usize, RuntimeDemand>>,
        settled_members: &HashSet<ExecutableKey>,
    ) -> HashSet<ExecutableKey> {
        let previous = self.input_demand_contributions.remove(&caller).unwrap_or_default();
        let mut affected: HashSet<ExecutableKey> = HashSet::new();
        for target in previous.keys() {
            affected.insert(target.clone());
            if let Some(contributors) = self.input_demand_contributors.get_mut(target) {
                contributors.remove(&caller);
            }
        }
        for target in contributions.keys() {
            affected.insert(target.clone());
            self.input_demand_contributors
                .entry(target.clone())
                .or_default()
                .insert(caller.clone());
        }
        if !contributions.is_empty() {
            self.input_demand_contributions.insert(caller, contributions);
        }
        let mut displaced = HashSet::new();
        for target in affected {
            displaced.extend(self.recompute_input_demand(&target, settled_members));
        }
        displaced
    }

    fn recompute_input_demand(
        &mut self,
        target: &ExecutableKey,
        settled_members: &HashSet<ExecutableKey>,
    ) -> HashSet<ExecutableKey> {
        let mut joined: HashMap<usize, RuntimeDemand> = HashMap::new();
        for contributor in self.input_demand_contributors.get(target).into_iter().flatten() {
            let Some(positions) = self
                .input_demand_contributions
                .get(contributor)
                .and_then(|c| c.get(target))
            else {
                continue;
            };
            for (index, demand) in positions {
                joined
                    .entry(*index)
                    .and_modify(|current| current.join_assign(demand))
                    .or_insert_with(|| demand.clone());
            }
        }
        let changed = self.input_demands.get(target).cloned().unwrap_or_default() != joined;
        if joined.is_empty() {
            self.input_demand_contributors.remove(target);
            self.input_demands.remove(target);
        } else {
            self.demanded_executables.insert(target.clone());
            self.input_demands.insert(target.clone(), joined);
        }
        debug_assert_eq!(
            self.input_demand_contributors
                .get(target)
                .is_some_and(|c| !c.is_empty()),
            self.input_demands.contains_key(target),
            "input_demand_contributors[target] and input_demands must stay in lockstep: a \
             target is present in one iff present in the other (absent from both = \
             not-yet-observed; present in both = observed, possibly joined to per-position \
             demand). A target present in only one map means the two fell out of sync."
        );
        if changed && !settled_members.contains(target) {
            self.invalidate_demand_derived_products(target)
        } else {
            HashSet::new()
        }
    }

    pub fn record_materialized_executable(&mut self, executable: ExecutableKey, materialized: MaterializedExecutable) {
        self.demanded_executables.insert(executable.clone());
        // The demand epoch gate: materialization resolving a call edge the
        // demand settle never derived means the settled cone was keyed against
        // a smaller call graph -- re-key and re-settle it. Edges within the
        // settled callee set (the overwhelming case: the cone over-approximates
        // from settled facts) leave settled demand standing.
        if let Some(settled_callees) = self.settled_demand_callees.get(&executable) {
            let materialized_callees: HashSet<ExecutableKey> = materialized
                .call_edges
                .values()
                .flat_map(|edge| edge.target.local_callees())
                .cloned()
                .collect();
            if !materialized_callees.is_subset(settled_callees) {
                self.settled_demand_callees
                    .entry(executable.clone())
                    .or_default()
                    .extend(materialized_callees);
                self.invalidate_demand_derived_products(&executable);
            }
        }
        let effect_inputs = effect_relevant_inputs(&materialized);
        let effect_inputs_changed = self.latest_effect_inputs.get(&executable) != Some(&effect_inputs);
        let previous = self.latest_effect_inputs.insert(executable.clone(), effect_inputs);
        self.replace_effect_dependent_edges(&executable, previous.map(|(_, callees)| callees));
        self.materialized_executables.insert(executable.clone(), materialized);
        if effect_inputs_changed {
            self.invalidate_effect_cone(&executable);
        }
    }

    /// Rebuild `caller`'s reverse effect edges from its just-recorded callee
    /// set, retracting edges to callees the re-materialization dropped --
    /// `effect_dependents` and `latest_effect_inputs` move in lockstep at
    /// this single site.
    fn replace_effect_dependent_edges(&mut self, caller: &ExecutableKey, previous: Option<HashSet<ExecutableKey>>) {
        let current = &self
            .latest_effect_inputs
            .get(caller)
            .expect("caller's effect inputs are recorded before its reverse edges")
            .1;
        for callee in previous.iter().flatten() {
            if current.contains(callee) {
                continue;
            }
            if let Some(dependents) = self.effect_dependents.get_mut(callee) {
                dependents.remove(caller);
                if dependents.is_empty() {
                    self.effect_dependents.remove(callee);
                }
            }
        }
        let added = current
            .iter()
            .filter(|callee| !previous.as_ref().is_some_and(|previous| previous.contains(*callee)))
            .cloned()
            .collect::<Vec<_>>();
        for callee in added {
            self.effect_dependents.entry(callee).or_default().insert(caller.clone());
        }
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

    fn apply_fact_movements(&mut self, movements: &[FactMovement<FactKey>]) {
        for movement in movements {
            self.pending_fact_states.insert(movement.key.clone(), movement.state);
        }
    }

    fn reconcile_fact_movements(&mut self) {
        let pending = std::mem::take(&mut self.pending_fact_states);
        self.memo.reconcile_fact_movements(&pending);
    }

    pub fn assign_executable_index(&mut self, executable: ExecutableKey, index: usize) {
        self.demanded_executables.insert(executable.clone());
        self.executable_index.insert(executable, index);
    }

    /// The demand EPOCH wipe: settled demand retracts only here. Walks the
    /// demand-read dependents (callers) transitively, displacing each member's
    /// RuntimeDemand memo plus the transport/artifact products derived from it,
    /// so the next demand pull re-settles the affected cone against the new
    /// call graph. Returns the displaced executables.
    fn invalidate_demand_derived_products(&mut self, executable: &ExecutableKey) -> HashSet<ExecutableKey> {
        let mut stack = vec![executable.clone()];
        let mut seen = HashSet::new();
        while let Some(current) = stack.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            self.memo.remove(&ProductKey::RuntimeDemand(current.clone()));
            self.invalidate_artifact_products(&current);
            if let Some(dependents) = self.runtime_demand_dependents.get(&current).cloned() {
                stack.extend(dependents);
            }
            if let Some(dependents) = self.demand_flow_dependents.get(&current).cloned() {
                stack.extend(dependents);
            }
        }
        seen
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
            ProductKey::TransportShape(_) => {}
            ProductKey::RootBackendProduct(_)
            | ProductKey::ExecutableFacts(_)
            | ProductKey::RuntimeDemand(_)
            | ProductKey::OutgoingEdgeFrontier(_)
            | ProductKey::OutgoingInputEdges(_)
            | ProductKey::IncomingInputRelations(_)
            | ProductKey::IncomingInputSlot(_)
            | ProductKey::CallableConstruction(_) => {}
        }
    }

    fn invalidate_artifact_products(&mut self, executable: &ExecutableKey) {
        self.memo
            .remove(&ProductKey::MaterializedExecutable(executable.clone()));
        self.memo.remove(&ProductKey::AbiExecutable(executable.clone()));
        self.memo.remove(&ProductKey::BackendExecutable(executable.clone()));
        self.materialized_executables.remove(executable);
        self.abi_executables.remove(executable);
        self.backend_executables.remove(executable);
    }

    /// A materialized executable's effect-relevant content (local effect
    /// summary or local callee set) actually changed: the effect summaries
    /// derived from it are stale. Effects read the callee cone through
    /// callers, so wipe the effects of the executable and its transitive
    /// dependents along the reverse effect edges -- the graph built from the
    /// same materialized call edges the effects producer traverses, so every
    /// consumer (including closure/boundary-resolved callers absent from the
    /// runtime-demand dependents graph) is reached. Materialized
    /// re-derivations that leave the projection unchanged leave the effect
    /// cone standing.
    fn invalidate_effect_cone(&mut self, executable: &ExecutableKey) {
        let mut stack = vec![executable.clone()];
        let mut seen = HashSet::new();
        while let Some(current) = stack.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            self.memo.remove(&ProductKey::ExecutableEffects(current.clone()));
            self.executable_effects.remove(&current);
            if let Some(dependents) = self.effect_dependents.get(&current).cloned() {
                stack.extend(dependents);
            }
        }
    }

    /// End-of-session freshness audit (debug builds): every cached
    /// ExecutableEffects value must equal the effects recomputed from scratch
    /// -- the union of local effect summaries over the transitive closure of
    /// the current effect-relevant projections. Any under-invalidation that
    /// leaves a stale summary standing fails loudly here instead of lingering
    /// as a schedule-protected latent hole.
    #[cfg(debug_assertions)]
    fn assert_executable_effects_fresh(&self) {
        for (key, cached) in &self.executable_effects {
            let mut expected = EffectSummary::default();
            let mut stack = vec![key.clone()];
            let mut seen = HashSet::new();
            let mut complete = true;
            while let Some(current) = stack.pop() {
                if !seen.insert(current.clone()) {
                    continue;
                }
                let Some((local, callees)) = self.latest_effect_inputs.get(&current) else {
                    complete = false;
                    break;
                };
                expected.union_with(*local);
                stack.extend(callees.iter().cloned());
            }
            assert!(
                !complete || *cached == expected,
                "stale ExecutableEffects at session finish for {key:?}: cached {cached:?}, recomputed {expected:?}"
            );
        }
    }

    fn note_product_request(&mut self, key: &ProductKey) {
        if let ProductKey::OutgoingInputEdges(executable) = key
            && self.outgoing_edge_request_set.insert(executable.clone())
        {
            self.memo.remove(&ProductKey::OutgoingEdgeFrontier(self.root));
        }
        if let Some(executable) = key.executable() {
            self.demanded_executables.insert(executable.clone());
        }
    }

    fn emit_finished(&self, tel: &impl Telemetry) {
        tel.raw_event1(&["fz", "compiler2", "pull", "session", "finished"], self);
    }
}

fn effect_relevant_inputs(materialized: &MaterializedExecutable) -> (EffectSummary, HashSet<ExecutableKey>) {
    let callees = materialized
        .call_edges
        .values()
        .flat_map(|edge| edge.target.local_callees())
        .cloned()
        .collect();
    (materialized.effects, callees)
}

pub struct ProductReadContext<'s> {
    session: &'s mut PullSession,
    dependencies: ProductDependencies,
    finished_group: bool,
}

impl<'s> ProductReadContext<'s> {
    pub(crate) fn new(session: &'s mut PullSession) -> Self {
        Self {
            session,
            dependencies: ProductDependencies::default(),
            finished_group: false,
        }
    }

    pub fn read_product(&mut self, key: ProductKey) -> Option<&ProductValue> {
        self.read_product_entry(key)
    }

    pub(crate) fn pending_dependency_reaches(&self, from: &ProductKey, target: &ProductKey) -> bool {
        self.session.memo.pending_dependency_reaches(from, target)
    }

    pub(crate) fn pending_transport_shape_group(&self, current: &ProductKey) -> Vec<ProductKey> {
        self.session
            .memo
            .pending_strong_component(current, &self.dependencies, |key| {
                matches!(key, ProductKey::TransportShape(_))
            })
    }

    pub(crate) fn pending_callable_construction_group(&self, current: &ProductKey) -> Vec<ProductKey> {
        self.session
            .memo
            .pending_strong_component(current, &self.dependencies, |key| {
                matches!(key, ProductKey::CallableConstruction(_))
            })
    }

    pub(crate) fn recursive_group_transport_layouts(&self, members: &[ProductKey]) -> Vec<TransportLayout> {
        let member_set = members.iter().collect::<HashSet<_>>();
        members
            .iter()
            .flat_map(|member| {
                self.session
                    .memo
                    .pending_dependencies
                    .get(member)
                    .into_iter()
                    .flat_map(|dependencies| dependencies.products.keys())
            })
            .filter(|dependency| !member_set.contains(dependency))
            .filter_map(|dependency| match self.session.memo.get(dependency) {
                Some(ProductValue::TransportShape(TransportShapeFact::Layout(layout))) => Some(*layout),
                _ => None,
            })
            .collect()
    }

    pub(crate) fn finish_transport_shape_group(
        &mut self,
        current: &ProductKey,
        members: &[ProductKey],
        value: ProductValue,
    ) -> bool {
        self.finish_product_group(current, members, vec![value; members.len()])
    }

    pub(crate) fn recursive_group_callable_owners(&self, members: &[ProductKey]) -> Vec<CallableConstructionOwner> {
        let member_set = members.iter().collect::<HashSet<_>>();
        members
            .iter()
            .flat_map(|member| {
                self.session
                    .memo
                    .product_dependencies_for_group(member)
                    .into_iter()
                    .flat_map(|dependencies| dependencies.products.keys())
            })
            .filter(|dependency| !member_set.contains(dependency))
            .filter_map(|dependency| match self.session.memo.get(dependency) {
                Some(ProductValue::CallableConstruction(owner)) => Some(owner.as_ref().clone()),
                _ => None,
            })
            .collect()
    }

    pub(crate) fn callable_group_layout(&self, member: &ProductKey) -> Option<TransportLayout> {
        let ProductKey::CallableConstruction(position) = member else {
            return None;
        };
        match self.session.memo.get(&ProductKey::TransportShape(position.clone())) {
            Some(ProductValue::TransportShape(TransportShapeFact::Layout(layout))) => Some(*layout),
            _ => None,
        }
    }

    pub(crate) fn finish_callable_construction_group(
        &mut self,
        current: &ProductKey,
        members: &[ProductKey],
        values: Vec<ProductValue>,
    ) -> bool {
        self.finish_product_group(current, members, values)
    }

    fn finish_product_group(
        &mut self,
        current: &ProductKey,
        members: &[ProductKey],
        values: Vec<ProductValue>,
    ) -> bool {
        assert_eq!(members.len(), values.len());
        let entries = members
            .iter()
            .cloned()
            .zip(values)
            .map(|(key, value)| {
                let dependencies = if &key == current {
                    self.dependencies.clone()
                } else {
                    self.session
                        .memo
                        .product_dependencies_for_group(&key)
                        .cloned()
                        .unwrap_or_default()
                };
                (key, value, dependencies)
            })
            .collect();
        self.finished_group = self.session.memo.finish_group(entries);
        if !self.finished_group {
            self.dependencies = ProductDependencies::default();
        }
        self.finished_group
    }

    fn read_product_entry(&mut self, key: ProductKey) -> Option<&ProductValue> {
        if let Some(stale) = self.session.memo.stale_dependency(&key) {
            self.session.memo.prepare_stale_for_reproduction(&stale);
            let generation = self.session.memo.generation(&key);
            self.dependencies.products.insert(key, generation);
            return None;
        }
        let generation = self.session.memo.generation(&key);
        self.dependencies.products.insert(key.clone(), generation);
        self.session.memo.get(&key)
    }

    pub fn read_runtime_demand(&mut self, executable: &ExecutableKey) -> Option<ExecutableRuntimeDemand> {
        match self.read_product(ProductKey::RuntimeDemand(executable.clone())) {
            Some(ProductValue::RuntimeDemand(demand)) => Some(demand.as_ref().clone()),
            Some(other) => panic!("runtime demand product produced unexpected value {other:?}"),
            None => None,
        }
    }

    pub(crate) fn read_executable_facts(&mut self, executable: &ExecutableKey) -> Option<Rc<ExecutableFacts>> {
        match self.read_product(ProductKey::ExecutableFacts(executable.clone())) {
            Some(ProductValue::ExecutableFacts(facts)) => Some(Rc::clone(facts)),
            Some(other) => panic!("executable facts product produced unexpected value {other:?}"),
            None => None,
        }
    }

    pub fn read_fact(&mut self, world: &World, fact: FactUse<FactKey>) -> bool {
        let state = FactState {
            revision: match &fact {
                FactUse::SettledPresence(_) => None,
                _ => world.fact_revision(fact.fact()),
            },
            settled: match &fact {
                FactUse::Current(_) => false,
                _ => world.fact_is_settled(fact.fact()),
            },
        };
        let ready = match fact.readiness() {
            super::facts::FactReadiness::Current => state.revision.is_some(),
            super::facts::FactReadiness::Settled => state.settled,
        };
        self.dependencies.facts.insert(fact, state);
        ready
    }

    #[cfg(test)]
    fn record_fact_state(&mut self, fact: FactUse<FactKey>, state: FactState) {
        self.dependencies.facts.insert(fact, state);
    }

    pub(crate) fn publish_product(&mut self, key: ProductKey, value: ProductValue) {
        self.session.memo.finish(&key, value, self.dependencies.clone());
    }

    pub(crate) fn remove_product_dependencies(&mut self, dependencies: impl IntoIterator<Item = ProductKey>) {
        for dependency in dependencies {
            self.dependencies.products.remove(&dependency);
        }
    }

    pub fn session(&self) -> &PullSession {
        self.session
    }

    pub fn session_mut(&mut self) -> &mut PullSession {
        self.session
    }

    fn into_dependencies(self) -> (ProductDependencies, bool) {
        (self.dependencies, self.finished_group)
    }
}

pub trait ProductProducers {
    fn produce_root_backend_product(&mut self, context: &mut ProductReadContext<'_>, root: RootId) -> PullOutcome;
    fn produce_backend_executable(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome;
    fn produce_abi_executable(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome;
    fn produce_materialized_executable(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome;
    fn produce_executable_effects(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome;
    fn produce_executable_facts(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome;
    fn produce_runtime_demand(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome;
    fn produce_outgoing_edge_frontier(&mut self, context: &mut ProductReadContext<'_>, root: RootId) -> PullOutcome;
    fn produce_outgoing_input_edges(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome;
    fn produce_incoming_input_relations(&mut self, context: &mut ProductReadContext<'_>, root: RootId) -> PullOutcome;
    fn produce_incoming_input_slot(&mut self, context: &mut ProductReadContext<'_>, slot: &InputSlot) -> PullOutcome;
    fn produce_transport_shape(
        &mut self,
        context: &mut ProductReadContext<'_>,
        position: &TransportPosition,
    ) -> PullOutcome;
    fn produce_callable_construction(
        &mut self,
        _context: &mut ProductReadContext<'_>,
        _position: &TransportPosition,
    ) -> PullOutcome {
        panic!("callable construction producer is not installed")
    }
}

pub struct WorldProductProducers<'w, 'a, T: crate::telemetry::Telemetry> {
    world: &'w mut World,
    telemetry: &'a T,
}

impl<'w, 'a, T: crate::telemetry::Telemetry> WorldProductProducers<'w, 'a, T> {
    pub fn new(world: &'w mut World, telemetry: &'a T) -> Self {
        Self { world, telemetry }
    }
}

impl<T: crate::telemetry::Telemetry> ProductProducers for WorldProductProducers<'_, '_, T> {
    fn produce_root_backend_product(&mut self, context: &mut ProductReadContext<'_>, root: RootId) -> PullOutcome {
        super::jobs::backend::produce_root_backend_product(self.world, self.telemetry, context, root)
    }

    fn produce_backend_executable(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome {
        super::jobs::backend::produce_backend_executable_product(self.world, self.telemetry, context, executable)
    }

    fn produce_abi_executable(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome {
        super::jobs::artifact::produce_abi_executable_product(self.world, self.telemetry, context, executable)
    }

    fn produce_materialized_executable(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome {
        super::jobs::artifact::produce_materialized_executable_product(self.world, self.telemetry, context, executable)
    }

    fn produce_executable_effects(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome {
        super::jobs::artifact::produce_executable_effects_product(self.telemetry, context, executable)
    }

    fn produce_executable_facts(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome {
        super::jobs::runtime_demand::produce_executable_facts_product(self.world, context, executable)
    }

    fn produce_runtime_demand(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome {
        super::jobs::runtime_demand::produce_runtime_demand_product(self.world, context, executable)
    }

    fn produce_outgoing_edge_frontier(&mut self, context: &mut ProductReadContext<'_>, _root: RootId) -> PullOutcome {
        PullOutcome::Produced(ProductValue::OutgoingEdgeFrontier(Rc::new(
            context.session().outgoing_edge_requests().clone(),
        )))
    }

    fn produce_outgoing_input_edges(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome {
        super::jobs::runtime_demand::produce_outgoing_input_edges_product(self.world, context, executable)
    }

    fn produce_incoming_input_relations(&mut self, context: &mut ProductReadContext<'_>, root: RootId) -> PullOutcome {
        let frontier_key = ProductKey::OutgoingEdgeFrontier(root);
        let publishers = match context.read_product(frontier_key.clone()) {
            Some(ProductValue::OutgoingEdgeFrontier(publishers)) => Rc::clone(publishers),
            Some(value) => panic!("outgoing edge frontier produced unexpected value {value:?}"),
            None => return PullOutcome::wait_on_product(frontier_key),
        };
        let mut slots: HashMap<InputSlot, HashSet<IncomingInputSource>> = HashMap::new();
        let mut waits = Vec::new();
        for publisher in publishers.iter() {
            let key = ProductKey::OutgoingInputEdges(publisher.clone());
            match context.read_product(key.clone()) {
                Some(ProductValue::OutgoingInputEdges(contribution)) => {
                    for (slot, published) in contribution.iter() {
                        slots.entry(slot.clone()).or_default().extend(published.iter().cloned());
                    }
                }
                Some(value) => panic!("outgoing input product produced unexpected value {value:?}"),
                None => waits.push(PullWait::Product(key)),
            }
        }
        if waits.is_empty() {
            PullOutcome::Produced(ProductValue::IncomingInputRelations(Rc::new(slots)))
        } else {
            PullOutcome::Waiting(waits)
        }
    }

    fn produce_incoming_input_slot(&mut self, context: &mut ProductReadContext<'_>, slot: &InputSlot) -> PullOutcome {
        let relations_key = ProductKey::IncomingInputRelations(context.session().root());
        match context.read_product(relations_key.clone()) {
            Some(ProductValue::IncomingInputRelations(relations)) => PullOutcome::Produced(
                ProductValue::IncomingInputSlot(relations.get(slot).cloned().unwrap_or_default()),
            ),
            Some(value) => panic!("incoming input relations produced unexpected value {value:?}"),
            None => PullOutcome::wait_on_product(relations_key),
        }
    }

    fn produce_transport_shape(
        &mut self,
        context: &mut ProductReadContext<'_>,
        position: &TransportPosition,
    ) -> PullOutcome {
        super::jobs::transport::produce_transport_shape_product(self.world, context, position)
    }

    fn produce_callable_construction(
        &mut self,
        context: &mut ProductReadContext<'_>,
        position: &TransportPosition,
    ) -> PullOutcome {
        super::jobs::transport::produce_callable_construction_product(self.world, context, position)
    }
}

pub struct ProductDriver<'a, T: Telemetry> {
    tel: &'a T,
    session: PullSession,
}

impl<'a, T: Telemetry> ProductDriver<'a, T> {
    pub fn new(tel: &'a T, root: RootId) -> Self {
        Self::with_session(tel, PullSession::new(root))
    }

    #[cfg(test)]
    pub(crate) fn telemetry(&self) -> &'a T {
        self.tel
    }

    pub fn with_session(tel: &'a T, session: PullSession) -> Self {
        Self { tel, session }
    }

    pub fn session(&self) -> &PullSession {
        &self.session
    }

    pub fn session_mut(&mut self) -> &mut PullSession {
        &mut self.session
    }

    pub fn finish_session(&self) {
        #[cfg(debug_assertions)]
        self.session.assert_executable_effects_fresh();
        self.session.emit_finished(self.tel);
    }

    pub(crate) fn apply_fact_movements(&mut self, movements: &[FactMovement<FactKey>]) {
        self.session.apply_fact_movements(movements);
    }

    pub fn pull(&mut self, producers: &mut impl ProductProducers, key: ProductKey) -> PullOutcome {
        self.session.reconcile_fact_movements();
        self.session.note_product_request(&key);
        if let Some(stale) = self.session.memo.stale_dependency(&key) {
            self.session.memo.prepare_stale_for_reproduction(&stale);
            if stale != key {
                return PullOutcome::wait_on_product(stale);
            }
        }
        if let Some(value) = self.session.memo.get(&key) {
            self.emit("cache_hit", &key);
            return PullOutcome::Produced(value.clone());
        }
        if self.session.memo.is_displaced(&key) {
            self.session.discard_product_side_effects(&key);
        }
        if !self.session.memo.begin(key.clone()) {
            self.emit("reentered", &key);
            return PullOutcome::Waiting(vec![PullWait::Product(key)]);
        }

        let mut context = ProductReadContext::new(&mut self.session);
        let outcome = match &key {
            ProductKey::RootBackendProduct(root) => producers.produce_root_backend_product(&mut context, *root),
            ProductKey::BackendExecutable(executable) => producers.produce_backend_executable(&mut context, executable),
            ProductKey::AbiExecutable(executable) => producers.produce_abi_executable(&mut context, executable),
            ProductKey::MaterializedExecutable(executable) => {
                producers.produce_materialized_executable(&mut context, executable)
            }
            ProductKey::ExecutableEffects(executable) => producers.produce_executable_effects(&mut context, executable),
            ProductKey::ExecutableFacts(executable) => producers.produce_executable_facts(&mut context, executable),
            ProductKey::RuntimeDemand(executable) => producers.produce_runtime_demand(&mut context, executable),
            ProductKey::OutgoingEdgeFrontier(root) => producers.produce_outgoing_edge_frontier(&mut context, *root),
            ProductKey::OutgoingInputEdges(executable) => {
                producers.produce_outgoing_input_edges(&mut context, executable)
            }
            ProductKey::IncomingInputRelations(root) => producers.produce_incoming_input_relations(&mut context, *root),
            ProductKey::IncomingInputSlot(slot) => producers.produce_incoming_input_slot(&mut context, slot),
            ProductKey::TransportShape(position) => producers.produce_transport_shape(&mut context, position),
            ProductKey::CallableConstruction(position) => {
                producers.produce_callable_construction(&mut context, position)
            }
        };
        let (dependencies, finished_group) = context.into_dependencies();
        if let PullOutcome::Waiting(waits) = &outcome {
            for wait in waits {
                if let PullWait::Product(product) = wait {
                    self.session.note_product_request(product);
                }
            }
        }

        match outcome {
            PullOutcome::Produced(value) => {
                if finished_group {
                    self.tel
                        .raw_event2(&["fz", "compiler2", "pull", "product", "settled"], &key, &value);
                    return PullOutcome::Produced(value);
                }
                let settled = self.session.memo.finish(&key, value.clone(), dependencies);
                if !settled {
                    self.session.discard_product_side_effects(&key);
                    let waits = vec![PullWait::Product(key.clone())];
                    PullOutcome::Waiting(waits)
                } else {
                    self.tel
                        .raw_event2(&["fz", "compiler2", "pull", "product", "settled"], &key, &value);
                    PullOutcome::Produced(value)
                }
            }
            PullOutcome::Waiting(waits) => {
                self.session.memo.unblock(&key, dependencies);
                PullOutcome::Waiting(waits)
            }
        }
    }

    fn emit(&self, event: &'static str, key: &ProductKey) {
        self.tel.raw_event1(&["fz", "compiler2", "pull", "product", event], key);
    }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::collections::{HashMap, HashSet};
    use std::rc::Rc;

    use crate::telemetry::ConfiguredTelemetry;

    use super::super::facts::FactReadiness;
    use super::super::identity::{ExecutableNeed, FunctionId};
    use super::super::transport::{BoundaryFacts, BoundaryId, CallableFacts, CallableId, ExecutableSymbol};
    use super::*;

    fn fact_movement(key: FactKey, revision: Option<u64>, settled: bool) -> FactMovement<FactKey> {
        FactMovement {
            key,
            state: FactState { revision, settled },
        }
    }

    struct ProductTelemetryCapture {
        produced: Rc<Cell<u64>>,
        cache_hits: Rc<Cell<u64>>,
    }

    impl ProductTelemetryCapture {
        fn install(telemetry: &ConfiguredTelemetry) -> Self {
            let capture = Self {
                produced: Rc::new(Cell::new(0)),
                cache_hits: Rc::new(Cell::new(0)),
            };
            let cache_hits = Rc::clone(&capture.cache_hits);
            telemetry.attach_raw_event1::<ProductKey, _>(
                &["fz", "compiler2", "pull", "product", "cache_hit"],
                move |_, _, _, _| cache_hits.set(cache_hits.get() + 1),
            );
            let produced = Rc::clone(&capture.produced);
            telemetry.attach_raw_event2::<ProductKey, ProductValue, _>(
                &["fz", "compiler2", "pull", "product", "settled"],
                move |_, _, _, _, _| produced.set(produced.get() + 1),
            );
            capture
        }
    }

    #[derive(Debug, Default)]
    struct FakeProducers {
        produced: HashSet<ProductKey>,
        calls: Vec<ProductKey>,
        reenter: Option<ProductKey>,
        root_entry: Option<ExecutableKey>,
        root_prerequisites: Vec<ProductKey>,
        facts: HashMap<FactKey, FactState>,
        runtime_fact: Option<FactUse<FactKey>>,
        runtime_value: Option<ProductValue>,
        runtime_child: Option<ProductKey>,
        backend_fact: Option<FactUse<FactKey>>,
        backend_value: Option<ProductValue>,
        fact_state_reads: usize,
    }

    impl FakeProducers {
        fn fact_state(&mut self, fact: &FactUse<FactKey>) -> FactState {
            self.fact_state_reads += 1;
            self.facts.get(fact.fact()).copied().unwrap_or(FactState {
                revision: None,
                settled: false,
            })
        }

        fn produce(&mut self, key: ProductKey) -> PullOutcome {
            self.calls.push(key.clone());
            if self.reenter.as_ref() == Some(&key) {
                return PullOutcome::wait_on_product(key);
            }
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
                _ => {
                    self.produced.insert(key);
                    PullOutcome::Produced(ProductValue::Unit)
                }
            }
        }
    }

    impl ProductProducers for FakeProducers {
        fn produce_root_backend_product(&mut self, context: &mut ProductReadContext<'_>, root: RootId) -> PullOutcome {
            let key = ProductKey::RootBackendProduct(root);
            self.calls.push(key.clone());
            if !self.root_prerequisites.is_empty() {
                let waits = self
                    .root_prerequisites
                    .iter()
                    .filter(|prerequisite| context.read_product_entry((*prerequisite).clone()).is_none())
                    .cloned()
                    .map(PullWait::Product)
                    .collect::<Vec<_>>();
                if !waits.is_empty() {
                    return PullOutcome::Waiting(waits);
                }
            }
            let prerequisite =
                ProductKey::RuntimeDemand(self.root_entry.clone().expect("fake root entry should be set"));
            if context.read_product_entry(prerequisite.clone()).is_some() {
                self.produced.insert(key);
                PullOutcome::Produced(ProductValue::Unit)
            } else {
                PullOutcome::wait_on_product(prerequisite)
            }
        }

        fn produce_backend_executable(
            &mut self,
            context: &mut ProductReadContext<'_>,
            executable: &ExecutableKey,
        ) -> PullOutcome {
            let key = ProductKey::BackendExecutable(executable.clone());
            self.calls.push(key.clone());
            if let Some(fact) = self.backend_fact.clone() {
                let state = self.fact_state(&fact);
                let ready = match fact.readiness() {
                    FactReadiness::Current => state.revision.is_some(),
                    FactReadiness::Settled => state.settled,
                };
                context.record_fact_state(fact.clone(), state);
                if !ready {
                    return PullOutcome::wait_on_fact(fact);
                }
            }
            self.produced.insert(key);
            PullOutcome::Produced(self.backend_value.clone().unwrap_or(ProductValue::Unit))
        }

        fn produce_abi_executable(
            &mut self,
            _context: &mut ProductReadContext<'_>,
            executable: &ExecutableKey,
        ) -> PullOutcome {
            self.produce(ProductKey::AbiExecutable(executable.clone()))
        }

        fn produce_materialized_executable(
            &mut self,
            _context: &mut ProductReadContext<'_>,
            executable: &ExecutableKey,
        ) -> PullOutcome {
            self.produce(ProductKey::MaterializedExecutable(executable.clone()))
        }

        fn produce_executable_effects(
            &mut self,
            _context: &mut ProductReadContext<'_>,
            executable: &ExecutableKey,
        ) -> PullOutcome {
            self.produce(ProductKey::ExecutableEffects(executable.clone()))
        }

        fn produce_executable_facts(
            &mut self,
            _context: &mut ProductReadContext<'_>,
            executable: &ExecutableKey,
        ) -> PullOutcome {
            self.produce(ProductKey::ExecutableFacts(executable.clone()))
        }

        fn produce_runtime_demand(
            &mut self,
            context: &mut ProductReadContext<'_>,
            executable: &ExecutableKey,
        ) -> PullOutcome {
            let key = ProductKey::RuntimeDemand(executable.clone());
            self.calls.push(key.clone());
            if let Some(fact) = self.runtime_fact.clone() {
                let state = self.fact_state(&fact);
                let ready = match fact.readiness() {
                    FactReadiness::Current => state.revision.is_some(),
                    FactReadiness::Settled => state.settled,
                };
                context.record_fact_state(fact.clone(), state);
                if !ready {
                    return PullOutcome::wait_on_fact(fact);
                }
            }
            if let Some(child) = self.runtime_child.clone()
                && context.read_product_entry(child.clone()).is_none()
            {
                return PullOutcome::wait_on_product(child);
            }
            self.produced.insert(key);
            PullOutcome::Produced(self.runtime_value.clone().unwrap_or(ProductValue::Unit))
        }

        fn produce_outgoing_edge_frontier(
            &mut self,
            _context: &mut ProductReadContext<'_>,
            root: RootId,
        ) -> PullOutcome {
            self.produce(ProductKey::OutgoingEdgeFrontier(root))
        }

        fn produce_outgoing_input_edges(
            &mut self,
            _context: &mut ProductReadContext<'_>,
            executable: &ExecutableKey,
        ) -> PullOutcome {
            self.produce(ProductKey::OutgoingInputEdges(executable.clone()))
        }

        fn produce_incoming_input_relations(
            &mut self,
            _context: &mut ProductReadContext<'_>,
            root: RootId,
        ) -> PullOutcome {
            self.produce(ProductKey::IncomingInputRelations(root))
        }

        fn produce_incoming_input_slot(
            &mut self,
            _context: &mut ProductReadContext<'_>,
            slot: &InputSlot,
        ) -> PullOutcome {
            self.produce(ProductKey::IncomingInputSlot(slot.clone()))
        }

        fn produce_transport_shape(
            &mut self,
            _context: &mut ProductReadContext<'_>,
            position: &TransportPosition,
        ) -> PullOutcome {
            self.produce(ProductKey::TransportShape(position.clone()))
        }
    }

    #[test]
    fn product_driver_names_prerequisites_without_follow_up_jobs() {
        let tel = ConfiguredTelemetry::new();
        let capture = ProductTelemetryCapture::install(&tel);
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
        assert_eq!(capture.produced.get(), 2);
        assert_eq!(capture.cache_hits.get(), 1);
    }

    #[test]
    fn product_driver_refreshes_deepest_stale_child_without_waking_equal_value_readers() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(7);
        let executable = fake_executable(root);
        let parent = ProductKey::RootBackendProduct(root);
        let child = ProductKey::RuntimeDemand(executable.clone());
        let fact = FactUse::current(FactKey::CodeIndexed(super::super::CodeId::ZERO));
        let mut producers = FakeProducers {
            root_entry: Some(executable),
            runtime_fact: Some(fact.clone()),
            facts: HashMap::from([(
                fact.fact().clone(),
                FactState {
                    revision: Some(1),
                    settled: false,
                },
            )]),
            ..FakeProducers::default()
        };
        let mut driver = ProductDriver::new(&tel, root);

        assert_eq!(
            driver.pull(&mut producers, parent.clone()),
            PullOutcome::wait_on_product(child.clone())
        );
        assert_eq!(
            driver.pull(&mut producers, child.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(
            driver.pull(&mut producers, parent.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(driver.session().memo().generation(&child), Some(1));
        assert_eq!(driver.session().memo().generation(&parent), Some(1));

        producers.facts.insert(
            fact.fact().clone(),
            FactState {
                revision: Some(2),
                settled: false,
            },
        );
        driver.apply_fact_movements(&[fact_movement(fact.fact().clone(), Some(2), true)]);
        let reads_before_cache_pull = producers.fact_state_reads;
        assert_eq!(
            driver.pull(&mut producers, parent.clone()),
            PullOutcome::wait_on_product(child.clone())
        );
        assert_eq!(producers.fact_state_reads, reads_before_cache_pull);
        assert_eq!(driver.session().memo().generation(&parent), Some(1));
        assert_eq!(driver.session().memo().generation(&child), None);
        assert_eq!(
            driver.pull(&mut producers, child.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(driver.session().memo().generation(&child), Some(1));
        assert_eq!(
            driver.pull(&mut producers, parent.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(driver.session().memo().generation(&parent), Some(1));

        producers.facts.insert(
            fact.fact().clone(),
            FactState {
                revision: Some(3),
                settled: false,
            },
        );
        driver.apply_fact_movements(&[fact_movement(fact.fact().clone(), Some(3), true)]);
        let changed_value = ProductValue::ExecutableEffects(EffectSummary {
            allocates: true,
            ..EffectSummary::default()
        });
        producers.runtime_value = Some(changed_value.clone());
        assert_eq!(
            driver.pull(&mut producers, parent.clone()),
            PullOutcome::wait_on_product(child.clone())
        );
        assert_eq!(
            driver.pull(&mut producers, child.clone()),
            PullOutcome::Produced(changed_value)
        );
        assert_eq!(driver.session().memo().generation(&child), Some(2));
        assert_eq!(driver.session().memo().generation(&parent), None);
        assert_eq!(
            driver.pull(&mut producers, parent.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(driver.session().memo().generation(&parent), Some(1));
        assert_eq!(producers.calls.iter().filter(|called| **called == parent).count(), 3);
    }

    #[test]
    fn readiness_movement_invalidates_a_mixed_current_and_settled_fact_reader() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(70);
        let fact = FactKey::CodeIndexed(super::super::CodeId::ZERO);
        let key = ProductKey::RuntimeDemand(fake_executable(root));
        let mut driver = ProductDriver::new(&tel, root);
        driver.session_mut().memo.finish(
            &key,
            ProductValue::Unit,
            ProductDependencies {
                products: HashMap::new(),
                facts: HashMap::from([
                    (
                        FactUse::current(fact.clone()),
                        FactState {
                            revision: Some(1),
                            settled: false,
                        },
                    ),
                    (
                        FactUse::settled(fact.clone()),
                        FactState {
                            revision: Some(1),
                            settled: true,
                        },
                    ),
                ]),
            },
        );

        driver.apply_fact_movements(&[fact_movement(fact, Some(1), false)]);

        assert!(driver.session().memo().get(&key).is_some());
        let mut producers = FakeProducers::default();
        assert_eq!(
            driver.pull(&mut producers, key.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(producers.calls, vec![key]);
    }

    #[test]
    fn settled_reader_coalesces_dirty_and_equal_resettlement() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(71);
        let fact = FactKey::CodeIndexed(super::super::CodeId::ZERO);
        let key = ProductKey::RuntimeDemand(fake_executable(root));
        let mut driver = ProductDriver::new(&tel, root);
        driver.session_mut().memo.finish(
            &key,
            ProductValue::Unit,
            ProductDependencies {
                products: HashMap::new(),
                facts: HashMap::from([(
                    FactUse::settled(fact.clone()),
                    FactState {
                        revision: Some(1),
                        settled: true,
                    },
                )]),
            },
        );
        for _ in 0..100 {
            driver.apply_fact_movements(&[fact_movement(fact.clone(), Some(1), false)]);
            driver.apply_fact_movements(&[fact_movement(fact.clone(), Some(1), true)]);
        }
        assert_eq!(driver.session().pending_fact_states.len(), 1);
        assert!(driver.session().memo.fact_stale_dependencies.is_empty());
        assert!(driver.session().memo.dirty_descendants.is_empty());

        let mut producers = FakeProducers::default();
        assert_eq!(
            driver.pull(&mut producers, key),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert!(producers.calls.is_empty());
    }

    #[test]
    fn settled_reader_reproduces_after_changed_resettlement() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(72);
        let fact = FactKey::CodeIndexed(super::super::CodeId::ZERO);
        let key = ProductKey::RuntimeDemand(fake_executable(root));
        let mut driver = ProductDriver::new(&tel, root);
        driver.session_mut().memo.finish(
            &key,
            ProductValue::Unit,
            ProductDependencies {
                products: HashMap::new(),
                facts: HashMap::from([(
                    FactUse::settled(fact.clone()),
                    FactState {
                        revision: Some(1),
                        settled: true,
                    },
                )]),
            },
        );
        driver.apply_fact_movements(&[fact_movement(fact, Some(2), true)]);

        let mut producers = FakeProducers::default();
        assert_eq!(
            driver.pull(&mut producers, key.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(producers.calls, vec![key]);
    }

    #[test]
    fn settled_presence_reader_ignores_content_only_movement() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(73);
        let fact = FactKey::CodeIndexed(super::super::CodeId::ZERO);
        let key = ProductKey::RuntimeDemand(fake_executable(root));
        let mut driver = ProductDriver::new(&tel, root);
        driver.session_mut().memo.finish(
            &key,
            ProductValue::Unit,
            ProductDependencies {
                products: HashMap::new(),
                facts: HashMap::from([(
                    FactUse::settled_presence(fact.clone()),
                    FactState {
                        revision: None,
                        settled: true,
                    },
                )]),
            },
        );
        driver.apply_fact_movements(&[fact_movement(fact, Some(2), true)]);

        let mut producers = FakeProducers::default();
        assert_eq!(
            driver.pull(&mut producers, key),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert!(producers.calls.is_empty());
    }

    #[test]
    fn settled_presence_reader_reproduces_after_same_key_publication_then_dirtying() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(74);
        let fact = FactKey::CodeIndexed(super::super::CodeId::ZERO);
        let missing = FactKey::RootEntry(root);
        let key = ProductKey::RuntimeDemand(fake_executable(root));
        let mut driver = ProductDriver::new(&tel, root);
        driver.session_mut().memo.finish(
            &key,
            ProductValue::Unit,
            ProductDependencies {
                products: HashMap::new(),
                facts: HashMap::from([(
                    FactUse::settled_presence(fact.clone()),
                    FactState {
                        revision: None,
                        settled: true,
                    },
                )]),
            },
        );
        let mut scheduler = super::super::scheduler::Scheduler::<u32, FactKey>::new();
        scheduler.complete(
            &1,
            HashSet::new(),
            HashSet::new(),
            vec![fact.clone()],
            vec![fact.clone()],
        );
        let blocked = scheduler.complete(
            &1,
            HashSet::new(),
            HashSet::from([FactUse::current(missing)]),
            vec![fact.clone()],
            vec![fact],
        );
        driver.apply_fact_movements(&blocked.movements);

        let mut producers = FakeProducers::default();
        assert_eq!(
            driver.pull(&mut producers, key.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(producers.calls, vec![key]);
    }

    #[test]
    fn equal_parent_reproduction_does_not_invalidate_its_grandparent() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(17);
        let executable = fake_executable(root);
        let grandparent = ProductKey::RootBackendProduct(root);
        let parent = ProductKey::RuntimeDemand(executable.clone());
        let child = ProductKey::BackendExecutable(executable);
        let fact = FactUse::current(FactKey::CodeIndexed(super::super::CodeId::ZERO));
        let mut producers = FakeProducers {
            root_entry: match &parent {
                ProductKey::RuntimeDemand(executable) => Some(executable.clone()),
                _ => unreachable!(),
            },
            runtime_child: Some(child.clone()),
            backend_fact: Some(fact.clone()),
            facts: HashMap::from([(
                fact.fact().clone(),
                FactState {
                    revision: Some(1),
                    settled: false,
                },
            )]),
            ..FakeProducers::default()
        };
        let mut driver = ProductDriver::new(&tel, root);

        assert_eq!(
            driver.pull(&mut producers, grandparent.clone()),
            PullOutcome::wait_on_product(parent.clone())
        );
        assert_eq!(
            driver.pull(&mut producers, parent.clone()),
            PullOutcome::wait_on_product(child.clone())
        );
        assert_eq!(
            driver.pull(&mut producers, child.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(
            driver.pull(&mut producers, parent.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(
            driver.pull(&mut producers, grandparent.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );

        producers.facts.insert(
            fact.fact().clone(),
            FactState {
                revision: Some(2),
                settled: false,
            },
        );
        let changed_value = ProductValue::ExecutableEffects(EffectSummary {
            allocates: true,
            ..EffectSummary::default()
        });
        producers.backend_value = Some(changed_value.clone());
        driver.apply_fact_movements(&[fact_movement(fact.fact().clone(), Some(2), false)]);
        assert_eq!(
            driver.pull(&mut producers, grandparent.clone()),
            PullOutcome::wait_on_product(child.clone())
        );
        assert_eq!(driver.session().memo().generation(&grandparent), Some(1));
        assert_eq!(driver.session().memo().generation(&parent), Some(1));
        assert_eq!(driver.pull(&mut producers, child), PullOutcome::Produced(changed_value));
        assert_eq!(driver.session().memo().generation(&parent), None);
        assert_eq!(driver.session().memo().generation(&grandparent), Some(1));
        assert_eq!(
            driver.pull(&mut producers, grandparent.clone()),
            PullOutcome::wait_on_product(parent.clone())
        );
        assert_eq!(
            driver.pull(&mut producers, parent.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(driver.session().memo().generation(&parent), Some(1));
        assert_eq!(driver.session().memo().generation(&grandparent), Some(1));
        let grandparent_calls = producers.calls.iter().filter(|called| **called == grandparent).count();
        assert_eq!(
            driver.pull(&mut producers, grandparent.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(
            producers.calls.iter().filter(|called| **called == grandparent).count(),
            grandparent_calls
        );
        assert_eq!(driver.session().memo().generation(&grandparent), Some(1));
    }

    #[test]
    fn product_driver_reports_fact_waits_as_waits_not_scheduler_work() {
        let tel = ConfiguredTelemetry::new();
        let capture = ProductTelemetryCapture::install(&tel);
        let root = RootId::for_test(1);
        let executable = fake_executable(root);
        let key = ProductKey::BackendExecutable(executable);
        let mut producers = FakeProducers {
            backend_fact: Some(FactUse::current(FactKey::CodeIndexed(super::super::CodeId::ZERO))),
            ..FakeProducers::default()
        };
        let mut driver = ProductDriver::new(&tel, root);

        let outcome = driver.pull(&mut producers, key.clone());

        assert_eq!(
            outcome,
            PullOutcome::wait_on_fact(FactUse::current(FactKey::CodeIndexed(super::super::CodeId::ZERO)))
        );
        assert!(driver.session().memo().get(&key).is_none());
        assert!(!driver.session().memo().contains_in_progress(&key));
        assert_eq!(capture.produced.get(), 0);
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
    fn outgoing_edge_frontier_tracks_actual_publisher_requests_as_a_set() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(3);
        let first = fake_executable(root);
        let second = fake_executable_with_function(root, 4);
        let frontier = ProductKey::OutgoingEdgeFrontier(root);
        let mut driver = ProductDriver::new(&tel, root);
        let mut fake = FakeProducers::default();
        let mut world = World::new();

        driver.pull(&mut fake, ProductKey::OutgoingInputEdges(first.clone()));
        let first_frontier = {
            let mut producers = WorldProductProducers::new(&mut world, &tel);
            driver.pull(&mut producers, frontier.clone())
        };
        assert_eq!(
            first_frontier,
            PullOutcome::Produced(ProductValue::OutgoingEdgeFrontier(Rc::new(HashSet::from([
                first.clone(),
            ]))))
        );
        let first_generation = driver.session().memo().generation(&frontier);

        driver.pull(&mut fake, ProductKey::OutgoingInputEdges(first.clone()));
        driver.pull(&mut fake, ProductKey::BackendExecutable(first.clone()));
        assert_eq!(driver.session().memo().generation(&frontier), first_generation);

        fake.reenter = Some(ProductKey::OutgoingInputEdges(second.clone()));
        assert_eq!(
            driver.pull(&mut fake, ProductKey::OutgoingInputEdges(second.clone())),
            PullOutcome::wait_on_product(ProductKey::OutgoingInputEdges(second.clone()))
        );
        let expanded = {
            let mut producers = WorldProductProducers::new(&mut world, &tel);
            driver.pull(&mut producers, frontier.clone())
        };
        assert_eq!(
            expanded,
            PullOutcome::Produced(ProductValue::OutgoingEdgeFrontier(Rc::new(HashSet::from([
                first, second,
            ]))))
        );
        assert_ne!(driver.session().memo().generation(&frontier), first_generation);
    }

    #[test]
    fn publisher_frontier_moves_once_for_an_atomic_sibling_wait_set() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(5);
        let first = fake_executable(root);
        let second = fake_executable_with_function(root, 6);
        let later = fake_executable_with_function(root, 7);
        let first_key = ProductKey::OutgoingInputEdges(first.clone());
        let second_key = ProductKey::OutgoingInputEdges(second.clone());
        let later_key = ProductKey::OutgoingInputEdges(later.clone());
        let root_key = ProductKey::RootBackendProduct(root);
        let frontier_key = ProductKey::OutgoingEdgeFrontier(root);
        let mut driver = ProductDriver::new(&tel, root);
        let mut fake = FakeProducers {
            root_prerequisites: vec![first_key.clone(), second_key.clone()],
            ..Default::default()
        };
        let mut world = World::new();

        assert_eq!(
            driver.pull(&mut fake, root_key.clone()),
            PullOutcome::Waiting(vec![
                PullWait::Product(first_key.clone()),
                PullWait::Product(second_key.clone())
            ])
        );
        let initial = {
            let mut producers = WorldProductProducers::new(&mut world, &tel);
            driver.pull(&mut producers, frontier_key.clone())
        };
        assert_eq!(
            initial,
            PullOutcome::Produced(ProductValue::OutgoingEdgeFrontier(Rc::new(HashSet::from([
                first, second,
            ]))))
        );
        let initial_generation = driver.session().memo().generation(&frontier_key);

        driver.pull(&mut fake, second_key);
        driver.pull(&mut fake, first_key);
        driver.pull(&mut fake, ProductKey::BackendExecutable(later));
        assert_eq!(driver.session().memo().generation(&frontier_key), initial_generation);

        fake.root_prerequisites.push(later_key.clone());
        assert_eq!(
            driver.pull(&mut fake, root_key),
            PullOutcome::wait_on_product(later_key)
        );
        let expanded = {
            let mut producers = WorldProductProducers::new(&mut world, &tel);
            driver.pull(&mut producers, frontier_key.clone())
        };
        assert_eq!(
            expanded,
            PullOutcome::Produced(ProductValue::OutgoingEdgeFrontier(Rc::new(HashSet::from([
                fake_executable_with_function(root, 7),
                fake_executable_with_function(root, 6),
                fake_executable(root),
            ]))))
        );
        assert_ne!(driver.session().memo().generation(&frontier_key), initial_generation);
    }

    #[test]
    fn pull_session_invalidates_runtime_demand_when_return_demand_grows() {
        let caller = fake_executable(RootId::for_test(5));
        let callee = fake_executable(RootId::for_test(5));
        let mut session = PullSession::new(RootId::for_test(5));
        session.memo.finish(
            &ProductKey::RuntimeDemand(callee.clone()),
            ProductValue::RuntimeDemand(Box::default()),
            ProductDependencies::default(),
        );

        session.replace_settled_return_demand_contributions(
            caller,
            HashMap::from([(callee.clone(), RuntimeDemand::whole())]),
            &HashSet::new(),
        );

        assert_eq!(
            session.external_return_demand(&callee, &HashSet::new()),
            Some(RuntimeDemand::whole()),
            "the joined return demand should be retained for the next pull"
        );
        assert!(
            session.memo().get(&ProductKey::RuntimeDemand(callee)).is_none(),
            "an epoch contribution that grows a non-member target's return demand re-settles it"
        );
    }

    #[test]
    fn pull_session_retracts_return_demand_when_a_caller_collapses_to_a_discard() {
        // The "unknown is not none" guard at the session layer, epoch-scoped: a
        // caller re-settled across an epoch whose contribution collapses to an
        // observed discard must DROP its callee's joined demand, not bake the
        // stale `whole`. An observed discard is the bottom `ignore` cell --
        // still present (observed), distinct from a callee no caller has named
        // (absent -> None).
        let caller = fake_executable(RootId::for_test(7));
        let callee = fake_executable(RootId::for_test(7));
        let mut session = PullSession::new(RootId::for_test(7));

        session.replace_settled_return_demand_contributions(
            caller.clone(),
            HashMap::from([(callee.clone(), RuntimeDemand::whole())]),
            &HashSet::new(),
        );
        assert_eq!(
            session.external_return_demand(&callee, &HashSet::new()),
            Some(RuntimeDemand::whole())
        );

        session.memo.finish(
            &ProductKey::RuntimeDemand(callee.clone()),
            ProductValue::RuntimeDemand(Box::default()),
            ProductDependencies::default(),
        );
        session.replace_settled_return_demand_contributions(
            caller.clone(),
            HashMap::from([(callee.clone(), RuntimeDemand::ignore())]),
            &HashSet::new(),
        );

        assert_eq!(
            session.external_return_demand(&callee, &HashSet::new()),
            Some(RuntimeDemand::ignore()),
            "a collapsed caller retracts its callee's whole demand down to the observed discard"
        );
        assert!(
            session.memo().get(&ProductKey::RuntimeDemand(callee.clone())).is_none(),
            "retracting a non-member callee's return demand re-settles its runtime demand"
        );

        session.replace_settled_return_demand_contributions(caller, HashMap::new(), &HashSet::new());
        assert_eq!(
            session.external_return_demand(&callee, &HashSet::new()),
            None,
            "withdrawing the last contributor leaves the callee not-yet-observed (distinct from an observed discard)"
        );
    }

    #[test]
    fn pull_session_invalidates_runtime_demand_when_input_demand_grows() {
        let caller = fake_executable(RootId::for_test(9));
        let callee = fake_executable(RootId::for_test(9));
        let mut session = PullSession::new(RootId::for_test(9));
        session.memo.finish(
            &ProductKey::RuntimeDemand(callee.clone()),
            ProductValue::RuntimeDemand(Box::default()),
            ProductDependencies::default(),
        );

        session.replace_settled_input_demand_contributions(
            caller,
            HashMap::from([(callee.clone(), HashMap::from([(0, RuntimeDemand::whole())]))]),
            &HashSet::new(),
        );

        assert_eq!(
            session.external_input_demand(&callee, &HashSet::new()),
            HashMap::from([(0, RuntimeDemand::whole())]),
            "the joined input demand should be retained for the next pull"
        );
        assert!(
            session.memo().get(&ProductKey::RuntimeDemand(callee)).is_none(),
            "an epoch contribution that grows a non-member target's input demand re-settles it"
        );
    }

    #[test]
    fn pull_session_retracts_input_demand_when_a_caller_collapses_to_a_discard() {
        // The input-side sibling of the return-demand retraction test above:
        // a caller re-settled across an epoch whose contribution collapses to
        // an observed discard must DROP its callee's joined position demand,
        // not bake the stale `whole`.
        let caller = fake_executable(RootId::for_test(11));
        let callee = fake_executable(RootId::for_test(11));
        let mut session = PullSession::new(RootId::for_test(11));

        session.replace_settled_input_demand_contributions(
            caller.clone(),
            HashMap::from([(callee.clone(), HashMap::from([(0, RuntimeDemand::whole())]))]),
            &HashSet::new(),
        );
        assert_eq!(
            session.external_input_demand(&callee, &HashSet::new()),
            HashMap::from([(0, RuntimeDemand::whole())])
        );

        session.memo.finish(
            &ProductKey::RuntimeDemand(callee.clone()),
            ProductValue::RuntimeDemand(Box::default()),
            ProductDependencies::default(),
        );
        session.replace_settled_input_demand_contributions(
            caller.clone(),
            HashMap::from([(callee.clone(), HashMap::from([(0, RuntimeDemand::ignore())]))]),
            &HashSet::new(),
        );

        assert_eq!(
            session.external_input_demand(&callee, &HashSet::new()),
            HashMap::from([(0, RuntimeDemand::ignore())]),
            "a collapsed caller retracts its callee's whole position demand down to the observed discard"
        );
        assert!(
            session.memo().get(&ProductKey::RuntimeDemand(callee.clone())).is_none(),
            "retracting a non-member callee's input demand re-settles its runtime demand"
        );

        session.replace_settled_input_demand_contributions(caller, HashMap::new(), &HashSet::new());
        assert_eq!(
            session.external_input_demand(&callee, &HashSet::new()),
            HashMap::new(),
            "withdrawing the last contributor leaves the callee not-yet-observed (distinct from an observed discard)"
        );
        assert!(
            !session.input_demand_contributors.contains_key(&callee),
            "withdrawing the last contributor must remove the stale empty contributor entry, \
             not leave it behind as an empty HashSet"
        );
    }

    #[test]
    fn incoming_input_relations_follow_frontier_generations_and_slots_project_exact_values() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(6);
        let caller = fake_executable(root);
        let unrelated = fake_executable_with_function(root, 7);
        let callee = fake_executable_with_function(root, 8);
        let slot = InputSlot {
            executable: callee,
            semantic_index: 0,
        };
        let source = IncomingInputSource {
            producer: caller.clone(),
            value: ValueId::from_u32(9),
            role: IncomingInputRole::CallArgument,
        };
        let mut driver = ProductDriver::new(&tel, root);
        let mut fake = FakeProducers::default();
        let mut world = World::new();
        let caller_key = ProductKey::OutgoingInputEdges(caller);
        driver.pull(&mut fake, caller_key.clone());
        driver.session.memo.remove(&caller_key);
        driver.session.memo.finish(
            &caller_key,
            ProductValue::OutgoingInputEdges(Rc::new(HashMap::from([(
                slot.clone(),
                HashSet::from([source.clone()]),
            )]))),
            ProductDependencies::default(),
        );

        let incoming_key = ProductKey::IncomingInputSlot(slot);
        let relations_key = ProductKey::IncomingInputRelations(root);
        let frontier_key = ProductKey::OutgoingEdgeFrontier(root);
        {
            let mut producers = WorldProductProducers::new(&mut world, &tel);
            assert_eq!(
                driver.pull(&mut producers, incoming_key.clone()),
                PullOutcome::wait_on_product(relations_key.clone())
            );
            assert_eq!(
                driver.pull(&mut producers, relations_key.clone()),
                PullOutcome::wait_on_product(frontier_key.clone())
            );
            driver.pull(&mut producers, frontier_key.clone());
            driver.pull(&mut producers, relations_key.clone());
            assert_eq!(
                driver.pull(&mut producers, incoming_key.clone()),
                PullOutcome::Produced(ProductValue::IncomingInputSlot(HashSet::from([source.clone()])))
            );
        }
        let source_generation = driver.session.memo.generation(&incoming_key);
        let relations_generation = driver.session.memo.generation(&relations_key);

        let unrelated_key = ProductKey::OutgoingInputEdges(unrelated);
        driver.pull(&mut fake, unrelated_key.clone());
        driver.session.memo.remove(&unrelated_key);
        driver.session.memo.finish(
            &unrelated_key,
            ProductValue::OutgoingInputEdges(Rc::new(HashMap::new())),
            ProductDependencies::default(),
        );
        {
            let mut producers = WorldProductProducers::new(&mut world, &tel);
            assert_eq!(
                driver.pull(&mut producers, incoming_key.clone()),
                PullOutcome::wait_on_product(frontier_key.clone())
            );
            driver.pull(&mut producers, frontier_key);
            driver.pull(&mut producers, relations_key.clone());
            assert_eq!(
                driver.pull(&mut producers, incoming_key.clone()),
                PullOutcome::Produced(ProductValue::IncomingInputSlot(HashSet::from([source])))
            );
        }
        assert_eq!(driver.session.memo.generation(&incoming_key), source_generation);
        assert_eq!(driver.session.memo.generation(&relations_key), relations_generation);

        driver.session.memo.remove(&caller_key);
        driver.session.memo.finish(
            &caller_key,
            ProductValue::OutgoingInputEdges(Rc::new(HashMap::new())),
            ProductDependencies::default(),
        );
        let withdrawn_wait = {
            let mut producers = WorldProductProducers::new(&mut world, &tel);
            driver.pull(&mut producers, incoming_key.clone())
        };
        assert_eq!(withdrawn_wait, PullOutcome::wait_on_product(relations_key.clone()));
        let withdrawn = {
            let mut producers = WorldProductProducers::new(&mut world, &tel);
            driver.pull(&mut producers, relations_key);
            driver.pull(&mut producers, incoming_key)
        };
        assert_eq!(
            withdrawn,
            PullOutcome::Produced(ProductValue::IncomingInputSlot(HashSet::new()))
        );
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
        record_materialized_product(
            driver.session_mut(),
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
        record_materialized_product(
            driver.session_mut(),
            second.clone(),
            fake_materialized_executable(
                empty_body(),
                second_symbol.clone(),
                Some(fake_call_edge(first.clone(), second_symbol, first_symbol)),
            ),
        );
        let mut world = World::new();
        let mut producers = WorldProductProducers::new(&mut world, &tel);

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
                    position_layouts: Vec::new(),
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
                        source: TransportPosition::ExecutableReturn {
                            executable: callee_symbol,
                        },
                        payload: TransportPosition::ReturnPayload {
                            executable: caller_symbol.clone(),
                            callsite: CallSiteId::from_u32(0),
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
    fn effect_products_survive_rematerialization_with_unchanged_effect_projection() {
        // A materialized executable re-derived with the same local effect
        // summary and the same local callee set must leave the effect cone
        // standing (no re-production); only a projection change (a new local
        // effect or callee) may wipe the executable's effects and its caller
        // cone's.
        use super::super::artifact::{
            CallEdge, CallReturnFlow, CallTarget, DirectCallEdge, MaterializedCallEdge, MaterializedExecutable,
            MaterializedExecutableTransport,
        };
        use super::super::body::{ControlEntryId, ControlEntryOrigin, LoweredClause, LoweredEntry, LoweredTail};
        use super::super::transport::ExecutableSymbol;
        use crate::source::Span;

        let tel = ConfiguredTelemetry::new();
        let capture = ProductTelemetryCapture::install(&tel);
        let root = RootId::for_test(90);
        let caller = fake_executable_with_function(root, 90);
        let callee = fake_executable_with_function(root, 91);
        let caller_symbol = executable_symbol_for_test(&caller);
        let callee_symbol = executable_symbol_for_test(&callee);
        let effects_key = ProductKey::ExecutableEffects(callee.clone());
        let mut driver = ProductDriver::new(&tel, root);
        driver
            .session_mut()
            .record_runtime_demand_dependency(callee.clone(), caller.clone());
        record_materialized_product(
            driver.session_mut(),
            caller.clone(),
            fake_materialized(
                caller_symbol.clone(),
                Some(fake_edge(callee.clone(), caller_symbol.clone(), callee_symbol.clone())),
                EffectSummary::default(),
            ),
        );
        let callee_materialized = fake_materialized(
            callee_symbol.clone(),
            Some(fake_edge(caller.clone(), callee_symbol, caller_symbol)),
            EffectSummary::default(),
        );
        record_materialized_product(driver.session_mut(), callee.clone(), callee_materialized.clone());
        let mut world = World::new();
        let mut producers = WorldProductProducers::new(&mut world, &tel);
        assert!(matches!(
            driver.pull(&mut producers, effects_key.clone()),
            PullOutcome::Produced(ProductValue::ExecutableEffects(_))
        ));
        let produced_after_settle = capture.produced.get();

        record_materialized_product(driver.session_mut(), callee.clone(), callee_materialized.clone());

        assert!(
            driver.session().executable_effects(&callee).is_some()
                && driver.session().executable_effects(&caller).is_some(),
            "an unchanged effect projection must leave the settled effect cone standing"
        );
        assert!(matches!(
            driver.pull(&mut producers, effects_key.clone()),
            PullOutcome::Produced(ProductValue::ExecutableEffects(_))
        ));
        assert_eq!(
            capture.produced.get(),
            produced_after_settle,
            "an unchanged effect projection must not re-produce the effects product"
        );

        let mut changed = callee_materialized;
        changed.effects = EffectSummary {
            scheduler_visible: true,
            ..EffectSummary::default()
        };
        record_materialized_product(driver.session_mut(), callee.clone(), changed);

        assert!(
            driver.session().executable_effects(&callee).is_none(),
            "a changed local effect summary must invalidate the executable's effects"
        );
        assert!(
            driver.session().executable_effects(&caller).is_none(),
            "a changed local effect summary must invalidate the caller cone's effects"
        );
        assert!(matches!(
            driver.pull(&mut producers, effects_key),
            PullOutcome::Produced(ProductValue::ExecutableEffects(_))
        ));
        assert!(
            capture.produced.get() > produced_after_settle,
            "a changed effect projection must re-produce the effects product"
        );

        fn fake_materialized(
            executable: ExecutableSymbol,
            edge: Option<MaterializedCallEdge>,
            effects: EffectSummary,
        ) -> MaterializedExecutable {
            let return_position = TransportPosition::ExecutableReturn {
                executable: executable.clone(),
            };
            MaterializedExecutable {
                entry_dispatch: None,
                return_ty: fake_ty(),
                runtime_demand: ExecutableRuntimeDemand::default(),
                transport: MaterializedExecutableTransport {
                    executable,
                    position_layouts: Vec::new(),
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
                effects,
                body: super::super::LoweredBody::Clauses {
                    clauses: vec![LoweredClause {
                        span: Span::DUMMY,
                        params: Vec::new(),
                        projections: Vec::new(),
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
                },
                call_edges: edge
                    .map(|edge| HashMap::from([(CallSiteId::from_u32(0), edge)]))
                    .unwrap_or_default(),
            }
        }

        fn fake_edge(
            callee: ExecutableKey,
            caller_symbol: ExecutableSymbol,
            callee_symbol: ExecutableSymbol,
        ) -> MaterializedCallEdge {
            MaterializedCallEdge {
                target: CallEdge::Direct(DirectCallEdge {
                    callee: CallTarget::Local(callee),
                    return_flow: CallReturnFlow::Tail {
                        source: TransportPosition::ExecutableReturn {
                            executable: callee_symbol,
                        },
                        payload: TransportPosition::ReturnPayload {
                            executable: caller_symbol.clone(),
                            callsite: CallSiteId::from_u32(0),
                        },
                        caller_return: TransportPosition::ExecutableReturn {
                            executable: caller_symbol,
                        },
                    },
                    extern_marshals: None,
                }),
                return_ty: fake_ty(),
            }
        }

        fn fake_ty() -> super::super::Ty {
            let mut types = super::super::Types::new();
            types.none()
        }
    }

    #[test]
    fn effect_cone_invalidation_reaches_dependents_without_runtime_demand_edges() {
        // Closure/boundary-resolved call edges materialize as ordinary local
        // call edges WITHOUT ever registering a runtime-demand dependency
        // (that graph carries CallSiteSummary direct targets only). When such
        // a callee's effect projection changes after its dependents settled,
        // the whole caller cone's effects must still be invalidated -- the
        // effect-dependents graph is derived from the materialized call edges
        // themselves, so no edge here is hand-registered.
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
        let root = RootId::for_test(93);
        let grand = fake_executable_with_function(root, 93);
        let caller = fake_executable_with_function(root, 94);
        let callee = fake_executable_with_function(root, 95);
        let grand_symbol = executable_symbol_for_test(&grand);
        let caller_symbol = executable_symbol_for_test(&caller);
        let callee_symbol = executable_symbol_for_test(&callee);
        let mut driver = ProductDriver::new(&tel, root);
        record_materialized_product(
            driver.session_mut(),
            grand.clone(),
            fake_materialized(
                grand_symbol.clone(),
                Some(fake_edge(caller.clone(), grand_symbol, caller_symbol.clone())),
                EffectSummary::default(),
            ),
        );
        record_materialized_product(
            driver.session_mut(),
            caller.clone(),
            fake_materialized(
                caller_symbol.clone(),
                Some(fake_edge(callee.clone(), caller_symbol, callee_symbol.clone())),
                EffectSummary::default(),
            ),
        );
        record_materialized_product(
            driver.session_mut(),
            callee.clone(),
            fake_materialized(callee_symbol, None, EffectSummary::default()),
        );
        let mut world = World::new();
        let mut producers = WorldProductProducers::new(&mut world, &tel);
        for key in [&callee, &caller, &grand] {
            assert!(matches!(
                driver.pull(&mut producers, ProductKey::ExecutableEffects(key.clone())),
                PullOutcome::Produced(ProductValue::ExecutableEffects(_))
            ));
        }

        let changed = fake_materialized(
            executable_symbol_for_test(&callee),
            None,
            EffectSummary {
                allocates: true,
                ..EffectSummary::default()
            },
        );
        record_materialized_product(driver.session_mut(), callee.clone(), changed);

        assert!(
            driver.session().executable_effects(&callee).is_none(),
            "the changed callee's own effects must be invalidated"
        );
        assert!(
            driver.session().executable_effects(&caller).is_none(),
            "the direct caller's effects must be invalidated without a runtime-demand edge"
        );
        assert!(
            driver.session().executable_effects(&grand).is_none(),
            "the transitive dependent's effects must be invalidated without runtime-demand edges"
        );
        for key in [&callee, &caller] {
            assert!(matches!(
                driver.pull(&mut producers, ProductKey::ExecutableEffects(key.clone())),
                PullOutcome::Produced(ProductValue::ExecutableEffects(_))
            ));
        }
        let outcome = driver.pull(&mut producers, ProductKey::ExecutableEffects(grand));
        let PullOutcome::Produced(ProductValue::ExecutableEffects(effects)) = outcome else {
            panic!("re-pulled effects should re-produce, got {outcome:?}")
        };
        assert!(
            effects.allocates,
            "the transitive dependent must observe the callee's new effect projection"
        );
        driver.finish_session();

        // The body is kept consistent with the requested local effect summary
        // (an allocating step iff `allocates`) the way production
        // materialization derives `effects` from the body, so the effects
        // producer's recompute and the recorded projection agree.
        fn fake_materialized(
            executable: ExecutableSymbol,
            edge: Option<MaterializedCallEdge>,
            effects: EffectSummary,
        ) -> MaterializedExecutable {
            let projections = if effects.allocates {
                vec![LoweredStep::Tuple {
                    value: ValueId::from_u32(0),
                    items: Vec::new(),
                }]
            } else {
                Vec::new()
            };
            let return_position = TransportPosition::ExecutableReturn {
                executable: executable.clone(),
            };
            MaterializedExecutable {
                entry_dispatch: None,
                return_ty: fake_ty(),
                runtime_demand: ExecutableRuntimeDemand::default(),
                transport: MaterializedExecutableTransport {
                    executable,
                    position_layouts: Vec::new(),
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
                effects,
                body: super::super::LoweredBody::Clauses {
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
                },
                call_edges: edge
                    .map(|edge| HashMap::from([(CallSiteId::from_u32(0), edge)]))
                    .unwrap_or_default(),
            }
        }

        fn fake_edge(
            callee: ExecutableKey,
            caller_symbol: ExecutableSymbol,
            callee_symbol: ExecutableSymbol,
        ) -> MaterializedCallEdge {
            MaterializedCallEdge {
                target: CallEdge::Direct(DirectCallEdge {
                    callee: CallTarget::Local(callee),
                    return_flow: CallReturnFlow::Tail {
                        source: TransportPosition::ExecutableReturn {
                            executable: callee_symbol,
                        },
                        payload: TransportPosition::ReturnPayload {
                            executable: caller_symbol.clone(),
                            callsite: CallSiteId::from_u32(0),
                        },
                        caller_return: TransportPosition::ExecutableReturn {
                            executable: caller_symbol,
                        },
                    },
                    extern_marshals: None,
                }),
                return_ty: fake_ty(),
            }
        }

        fn fake_ty() -> super::super::Ty {
            let mut types = super::super::Types::new();
            types.none()
        }
    }

    #[test]
    fn pull_session_finished_telemetry_reports_producer_pokes() {
        let tel = ConfiguredTelemetry::new();
        let observed = Rc::new(Cell::new(None));
        let sink = Rc::clone(&observed);
        tel.attach_raw_event1::<PullSession, _>(
            &["fz", "compiler2", "pull", "session", "finished"],
            move |_, _, _, session| {
                sink.set(Some((session.demanded_executables.len(), session.producer_pokes)));
            },
        );
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

        assert_eq!(observed.get(), Some((1, 2)));
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

    fn record_materialized_product(
        session: &mut PullSession,
        executable: ExecutableKey,
        materialized: MaterializedExecutable,
    ) {
        session.record_materialized_executable(executable.clone(), materialized.clone());
        session.memo.finish(
            &ProductKey::MaterializedExecutable(executable),
            ProductValue::MaterializedExecutable(Box::new(materialized)),
            ProductDependencies::default(),
        );
    }

    fn executable_symbol_for_test(executable: &ExecutableKey) -> super::super::transport::ExecutableSymbol {
        super::super::transport::ExecutableSymbol {
            activation: super::super::transport::ActivationSymbol {
                function: executable.activation.function,
                arrow: executable.activation.arrow,
                input: Box::default(),
            },
            need: executable.need,
        }
    }

    #[derive(Debug, Default, PartialEq, Eq)]
    struct OwnerCallableAggregation {
        resolutions: HashSet<ExecutableSymbol>,
        direct_surfaces: HashSet<Box<[ShapeId]>>,
        direct_edges: HashSet<super::super::transport::CallableDirectEdge>,
        boundary_ids: HashSet<BoundaryId>,
    }

    #[derive(Debug, Default, PartialEq, Eq)]
    struct OwnerBoundaryAggregation {
        publications: HashSet<TransportPosition>,
        resolutions: HashSet<ExecutableSymbol>,
    }

    #[derive(Debug, Default, PartialEq, Eq)]
    struct OwnerAggregation {
        callables: HashMap<CallableId, OwnerCallableAggregation>,
        boundaries: HashMap<BoundaryId, OwnerBoundaryAggregation>,
    }

    fn aggregate_callable_owners(memo: &ProductMemo, owners: &[ProductKey]) -> OwnerAggregation {
        let mut out = OwnerAggregation::default();
        for owner in owners {
            let Some(ProductValue::CallableConstruction(answer)) = memo.get(owner) else {
                continue;
            };
            for (callable, facts) in &answer.callable_facts {
                let aggregate = out.callables.entry(*callable).or_default();
                aggregate.resolutions.extend(facts.resolutions.iter().cloned());
                aggregate.direct_surfaces.extend(facts.direct_surfaces.iter().cloned());
                aggregate.direct_edges.extend(facts.direct_edges.iter().cloned());
                aggregate.boundary_ids.extend(facts.boundary_ids.iter().copied());
            }
            for (boundary, facts) in &answer.boundary_facts {
                let aggregate = out.boundaries.entry(*boundary).or_default();
                aggregate.publications.extend(facts.publications.iter().cloned());
                aggregate.resolutions.extend(facts.resolutions.iter().cloned());
            }
        }
        out
    }

    fn callable_owner_answer(
        layout: TransportLayout,
        owner: TransportPosition,
        callable: CallableId,
        boundary: BoundaryId,
        resolution: ExecutableSymbol,
    ) -> ProductValue {
        ProductValue::CallableConstruction(Box::new(CallableConstructionOwner {
            layout,
            construction: None,
            callable_facts: HashMap::from([(
                callable,
                CallableFacts {
                    resolutions: Box::new([resolution.clone()]),
                    direct_surfaces: Box::default(),
                    direct_edges: Box::default(),
                    boundary_ids: Box::new([boundary]),
                },
            )]),
            boundary_facts: HashMap::from([(
                boundary,
                BoundaryFacts {
                    publications: Box::new([owner]),
                    resolutions: Box::new([resolution]),
                },
            )]),
        }))
    }

    fn withdrawn_callable_owner_answer(layout: TransportLayout) -> ProductValue {
        ProductValue::CallableConstruction(Box::new(CallableConstructionOwner {
            layout,
            construction: None,
            callable_facts: HashMap::new(),
            boundary_facts: HashMap::new(),
        }))
    }

    fn finish_test_product(
        memo: &mut ProductMemo,
        key: &ProductKey,
        value: ProductValue,
        dependencies: impl IntoIterator<Item = ProductKey>,
    ) {
        assert!(memo.begin(key.clone()));
        let products = dependencies
            .into_iter()
            .map(|dependency| {
                let generation = memo.generation(&dependency);
                (dependency, generation)
            })
            .collect();
        assert!(memo.finish(
            key,
            value,
            ProductDependencies {
                products,
                facts: HashMap::new(),
            },
        ));
    }

    #[test]
    fn callable_owner_products_aggregate_order_free_and_retract_independently() {
        let root = RootId::for_test(35);
        let left_position = TransportPosition::Value {
            executable: executable_symbol_for_test(&fake_executable_with_function(root, 350)),
            value: ValueId::from_u32(0),
        };
        let right_position = TransportPosition::Value {
            executable: executable_symbol_for_test(&fake_executable_with_function(root, 351)),
            value: ValueId::from_u32(0),
        };
        let left_resolution = executable_symbol_for_test(&fake_executable_with_function(root, 352));
        let right_resolution = executable_symbol_for_test(&fake_executable_with_function(root, 353));
        let replacement_resolution = executable_symbol_for_test(&fake_executable_with_function(root, 354));
        let mut world = World::new();
        let callable = world.intern_callable(super::super::transport::CallableDescr {
            function: Some(FunctionId::for_test(355)),
            arity: 0,
            capture_tys: Box::default(),
            capture_shapes: Box::default(),
            capture_lanes: Box::default(),
        });
        let boundary = BoundaryId::for_test(8);
        let layout = TransportLayout::structural(ShapeId::for_test(9));
        let left_key = ProductKey::CallableConstruction(left_position.clone());
        let right_key = ProductKey::CallableConstruction(right_position.clone());
        let left_abi = ProductKey::AbiExecutable(fake_executable_with_function(root, 350));
        let right_abi = ProductKey::AbiExecutable(fake_executable_with_function(root, 351));
        let root_key = ProductKey::RootBackendProduct(root);
        let mut memo = ProductMemo::default();

        let left_value = callable_owner_answer(
            layout,
            left_position.clone(),
            callable,
            boundary,
            left_resolution.clone(),
        );
        let right_value = callable_owner_answer(
            layout,
            right_position.clone(),
            callable,
            boundary,
            right_resolution.clone(),
        );
        finish_test_product(&mut memo, &left_key, left_value, []);
        finish_test_product(&mut memo, &right_key, right_value, []);
        finish_test_product(&mut memo, &left_abi, ProductValue::Unit, [left_key.clone()]);
        finish_test_product(&mut memo, &right_abi, ProductValue::Unit, [right_key.clone()]);
        finish_test_product(
            &mut memo,
            &root_key,
            ProductValue::RootBackendProduct(Box::new(RootBackendProductAnswer {
                program: super::super::artifact::BackendProgram {
                    backend_revision: 0,
                    entry: 0,
                    atom_names: Vec::new(),
                    struct_schemas: Default::default(),
                    executables: Vec::new(),
                    construction_wrappers: Vec::new(),
                },
                transport: super::super::artifact::MaterializedTransportPlan {
                    entry: left_resolution.clone(),
                    executable_membership: Box::default(),
                    position_layouts: Vec::new(),
                    callable_boundaries: Vec::new(),
                    boundary_ids: Vec::new(),
                    publication_boundaries: Vec::new(),
                    codegen_seam_facts: Box::default(),
                    callable_owners: Box::default(),
                    callable_facts: HashMap::new(),
                    boundary_facts: HashMap::new(),
                },
            })),
            [left_abi.clone(), right_abi.clone()],
        );

        let forward = aggregate_callable_owners(&memo, &[left_key.clone(), right_key.clone()]);
        let reverse = aggregate_callable_owners(&memo, &[right_key.clone(), left_key.clone()]);
        assert_eq!(forward, reverse);
        assert_eq!(
            forward.callables[&callable].resolutions,
            HashSet::from([left_resolution.clone(), right_resolution.clone()])
        );
        assert_eq!(
            forward.boundaries[&boundary].publications,
            HashSet::from([left_position.clone(), right_position.clone()])
        );
        assert_eq!(
            memo.product_dependencies(&left_abi).unwrap(),
            &HashMap::from([(left_key.clone(), Some(1))])
        );
        assert_eq!(
            memo.product_dependencies(&right_abi).unwrap(),
            &HashMap::from([(right_key.clone(), Some(1))])
        );
        assert_eq!(
            memo.product_dependencies(&root_key).unwrap(),
            &HashMap::from([(left_abi.clone(), Some(1)), (right_abi.clone(), Some(1))])
        );

        let right_generation = memo.generation(&right_key);
        memo.remove(&left_key);
        finish_test_product(
            &mut memo,
            &left_key,
            callable_owner_answer(
                layout,
                left_position,
                callable,
                boundary,
                replacement_resolution.clone(),
            ),
            [],
        );
        let replaced_generation = memo.generation(&left_key);
        let replaced = aggregate_callable_owners(&memo, &[left_key.clone(), right_key.clone()]);
        assert_eq!(
            replaced.callables[&callable].resolutions,
            HashSet::from([replacement_resolution, right_resolution.clone()])
        );
        assert!(!replaced.callables[&callable].resolutions.contains(&left_resolution));
        assert_eq!(memo.generation(&right_key), right_generation);
        assert!(memo.stale_dependency(&left_abi).is_some());
        assert!(memo.stale_dependency(&right_abi).is_none());
        assert!(memo.stale_dependency(&root_key).is_some());

        let reproduced = memo.get(&left_key).cloned().expect("replaced owner product");
        memo.remove(&left_key);
        finish_test_product(&mut memo, &left_key, reproduced, []);
        assert_eq!(memo.generation(&left_key), replaced_generation);
        assert_eq!(memo.generation(&right_key), right_generation);

        memo.remove(&left_key);
        finish_test_product(&mut memo, &left_key, withdrawn_callable_owner_answer(layout), []);
        let withdrawn = aggregate_callable_owners(&memo, &[left_key, right_key]);
        assert_eq!(
            withdrawn.callables[&callable].resolutions,
            HashSet::from([right_resolution])
        );
        assert_eq!(
            withdrawn.boundaries[&boundary].publications,
            HashSet::from([right_position])
        );
    }

    type OwnerSymbolKey = (u32, super::super::types::Ty, Vec<super::super::types::Ty>, u8, usize);
    type OwnerPositionKey = (u8, OwnerSymbolKey, u64, u64, usize);

    fn owner_symbol_key(symbol: &ExecutableSymbol) -> OwnerSymbolKey {
        let need = match symbol.need {
            ExecutableNeed::Value => (0, 0),
            ExecutableNeed::TupleFields(arity) => (1, arity),
        };
        (
            symbol.activation.function.as_u32(),
            symbol.activation.arrow,
            symbol.activation.input.to_vec(),
            need.0,
            need.1,
        )
    }

    fn owner_position_key(position: &TransportPosition) -> OwnerPositionKey {
        let local = match position {
            TransportPosition::ExecutableInput { semantic_index, .. } => (0, 0, 0, *semantic_index),
            TransportPosition::ExecutableReturn { .. } => (1, 0, 0, 0),
            TransportPosition::ResumePayload { callsite, entry, .. } => (
                2,
                callsite.map_or(0, |callsite| u64::from(callsite.as_u32()) + 1),
                u64::from(entry.as_u32()),
                0,
            ),
            TransportPosition::ReturnPayload { callsite, .. } => (3, u64::from(callsite.as_u32()), 0, 0),
            TransportPosition::CallArg {
                callsite,
                semantic_index,
                ..
            } => (4, u64::from(callsite.as_u32()), 0, *semantic_index),
            TransportPosition::EntryCapture {
                entry, capture_index, ..
            } => (5, u64::from(entry.as_u32()), 0, *capture_index),
            TransportPosition::Value { value, .. } => (6, u64::from(value.as_u32()), 0, 0),
        };
        (
            local.0,
            owner_symbol_key(position.executable()),
            local.1,
            local.2,
            local.3,
        )
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct OwnerState {
        layout: TransportLayout,
        resolutions: HashSet<ExecutableSymbol>,
        publications: HashSet<TransportPosition>,
    }

    impl OwnerState {
        fn bottom(layout: TransportLayout) -> Self {
            Self {
                layout,
                resolutions: HashSet::new(),
                publications: HashSet::new(),
            }
        }

        fn join_assign(&mut self, other: &Self) {
            self.resolutions.extend(other.resolutions.iter().cloned());
            self.publications.extend(other.publications.iter().cloned());
        }

        fn product_value(&self, callable: CallableId, boundary: BoundaryId) -> ProductValue {
            let mut resolutions = self.resolutions.iter().cloned().collect::<Vec<_>>();
            resolutions.sort_by_key(owner_symbol_key);
            let direct_edges = resolutions
                .iter()
                .cloned()
                .map(|resolution| super::super::transport::CallableDirectEdge {
                    surface_inputs: Box::default(),
                    surface_arg_shapes: Box::new([self.layout.structural]),
                    resolution,
                    capture_semantic_inputs: Box::default(),
                    surface_semantic_inputs: Box::default(),
                })
                .collect();
            let mut publications = self.publications.iter().cloned().collect::<Vec<_>>();
            publications.sort_by_key(owner_position_key);
            ProductValue::CallableConstruction(Box::new(CallableConstructionOwner {
                layout: self.layout,
                construction: None,
                callable_facts: (!resolutions.is_empty())
                    .then(|| {
                        (
                            callable,
                            CallableFacts {
                                resolutions: resolutions.clone().into_boxed_slice(),
                                direct_surfaces: Box::new([Box::new([self.layout.structural])]),
                                direct_edges,
                                boundary_ids: Box::new([boundary]),
                            },
                        )
                    })
                    .into_iter()
                    .collect(),
                boundary_facts: (!publications.is_empty() || !resolutions.is_empty())
                    .then(|| {
                        (
                            boundary,
                            BoundaryFacts {
                                publications: publications.into_boxed_slice(),
                                resolutions: resolutions.into_boxed_slice(),
                            },
                        )
                    })
                    .into_iter()
                    .collect(),
            }))
        }
    }

    #[derive(Clone)]
    struct OwnerEquation {
        seed: OwnerState,
        children: Vec<usize>,
    }

    fn settle_owner_equations(equations: &[OwnerEquation], reverse: bool) -> (Vec<OwnerState>, usize) {
        let mut answers = equations
            .iter()
            .map(|equation| OwnerState::bottom(equation.seed.layout))
            .collect::<Vec<_>>();
        let mut order = (0..equations.len()).collect::<Vec<_>>();
        if reverse {
            order.reverse();
        }
        for round in 0..16 {
            let previous = answers.clone();
            for index in order.iter().copied() {
                let mut answer = equations[index].seed.clone();
                for child in &equations[index].children {
                    answer.join_assign(&answers[*child]);
                }
                answers[index] = answer;
            }
            if answers == previous {
                return (answers, round);
            }
        }
        panic!("finite callable owner equations did not settle")
    }

    fn finish_owner_group(
        memo: &mut ProductMemo,
        keys: &[ProductKey],
        answers: &[OwnerState],
        external: &[ProductKey],
        callable: CallableId,
        boundary: BoundaryId,
        reverse: bool,
    ) {
        for key in keys {
            assert!(memo.begin(key.clone()));
            assert!(memo.get(key).is_none());
        }
        let mut order = (0..keys.len()).collect::<Vec<_>>();
        if reverse {
            order.reverse();
        }
        let entries = order
            .into_iter()
            .map(|index| {
                let products = keys
                    .iter()
                    .chain(external)
                    .cloned()
                    .map(|dependency| {
                        let generation = memo.generation(&dependency);
                        (dependency, generation)
                    })
                    .collect();
                (
                    keys[index].clone(),
                    answers[index].product_value(callable, boundary),
                    ProductDependencies {
                        products,
                        facts: HashMap::new(),
                    },
                )
            })
            .collect();
        assert!(memo.finish_group(entries));
    }

    #[test]
    fn transport_shape_group_retains_every_external_dependency_for_every_member() {
        let root = RootId::for_test(38);
        let symbol = executable_symbol_for_test(&fake_executable_with_function(root, 380));
        let left = ProductKey::TransportShape(TransportPosition::Value {
            executable: symbol.clone(),
            value: ValueId::from_u32(1),
        });
        let right = ProductKey::TransportShape(TransportPosition::Value {
            executable: symbol,
            value: ValueId::from_u32(2),
        });
        let external = ProductKey::IncomingInputSlot(InputSlot {
            executable: fake_executable_with_function(root, 381),
            semantic_index: 0,
        });
        let left_reader = ProductKey::AbiExecutable(fake_executable_with_function(root, 382));
        let right_reader = ProductKey::AbiExecutable(fake_executable_with_function(root, 383));
        let unrelated = ProductKey::AbiExecutable(fake_executable_with_function(root, 384));
        let first_layout = TransportLayout::structural(ShapeId::for_test(110));
        let second_layout = TransportLayout::structural(ShapeId::for_test(111));
        let external_value = |producer| {
            ProductValue::IncomingInputSlot(HashSet::from([IncomingInputSource {
                producer: fake_executable_with_function(root, producer),
                value: ValueId::from_u32(1),
                role: IncomingInputRole::CallArgument,
            }]))
        };

        for reverse in [false, true] {
            let mut memo = ProductMemo::default();
            finish_test_product(&mut memo, &external, external_value(385), []);
            for key in [&left, &right] {
                assert!(memo.begin(key.clone()));
            }
            let mut entries = vec![
                (
                    left.clone(),
                    ProductValue::TransportShape(TransportShapeFact::Layout(first_layout)),
                    ProductDependencies {
                        products: HashMap::from([
                            (right.clone(), None),
                            (external.clone(), memo.generation(&external)),
                        ]),
                        facts: HashMap::new(),
                    },
                ),
                (
                    right.clone(),
                    ProductValue::TransportShape(TransportShapeFact::Layout(first_layout)),
                    ProductDependencies {
                        products: HashMap::from([(left.clone(), None)]),
                        facts: HashMap::new(),
                    },
                ),
            ];
            if reverse {
                entries.reverse();
            }
            assert!(memo.finish_group(entries));
            for key in [&left, &right] {
                assert_eq!(
                    memo.product_dependencies(key),
                    Some(&HashMap::from([(external.clone(), Some(1))]))
                );
            }

            finish_test_product(&mut memo, &left_reader, ProductValue::Unit, [left.clone()]);
            finish_test_product(&mut memo, &right_reader, ProductValue::Unit, [right.clone()]);
            finish_test_product(&mut memo, &unrelated, ProductValue::Unit, []);
            let unrelated_generation = memo.generation(&unrelated);

            memo.remove(&external);
            finish_test_product(&mut memo, &external, external_value(386), []);
            assert!(memo.get(&left).is_none());
            assert!(memo.get(&right).is_none());
            assert!(memo.get(&unrelated).is_some());

            for key in [&left, &right] {
                assert!(memo.begin(key.clone()));
            }
            assert!(memo.finish_group(vec![
                (
                    left.clone(),
                    ProductValue::TransportShape(TransportShapeFact::Layout(second_layout)),
                    ProductDependencies {
                        products: HashMap::from([
                            (right.clone(), memo.generation(&right)),
                            (external.clone(), memo.generation(&external)),
                        ]),
                        facts: HashMap::new(),
                    },
                ),
                (
                    right.clone(),
                    ProductValue::TransportShape(TransportShapeFact::Layout(second_layout)),
                    ProductDependencies {
                        products: HashMap::from([(left.clone(), memo.generation(&left))]),
                        facts: HashMap::new(),
                    },
                ),
            ]));
            assert_eq!(memo.generation(&left), Some(2));
            assert_eq!(memo.generation(&right), Some(2));
            assert!(memo.get(&left_reader).is_none());
            assert!(memo.get(&right_reader).is_none());
            assert_eq!(memo.generation(&unrelated), unrelated_generation);
        }
    }

    #[test]
    fn changed_product_authority_discards_pending_reader_snapshots_before_group_settlement() {
        let root = RootId::for_test(39);
        let external = ProductKey::RuntimeDemand(fake_executable_with_function(root, 390));
        let left = ProductKey::RuntimeDemand(fake_executable_with_function(root, 391));
        let right = ProductKey::RuntimeDemand(fake_executable_with_function(root, 392));
        let unrelated = ProductKey::RuntimeDemand(fake_executable_with_function(root, 393));
        let first = ProductValue::ExecutableEffects(EffectSummary::default());
        let second = ProductValue::ExecutableEffects(EffectSummary {
            allocates: true,
            ..EffectSummary::default()
        });

        for reverse in [false, true] {
            let mut memo = ProductMemo::default();
            finish_test_product(&mut memo, &external, first.clone(), []);
            finish_test_product(&mut memo, &unrelated, ProductValue::Unit, []);
            let unrelated_generation = memo.generation(&unrelated);

            assert!(memo.begin(left.clone()));
            memo.unblock(
                &left,
                ProductDependencies {
                    products: HashMap::from([(right.clone(), None), (external.clone(), Some(1))]),
                    facts: HashMap::new(),
                },
            );
            assert!(memo.pending_dependencies.contains_key(&left));

            memo.remove(&external);
            finish_test_product(&mut memo, &external, second.clone(), []);

            assert!(!memo.pending_dependencies.contains_key(&left));
            assert!(
                memo.product_readers
                    .get(&external)
                    .is_none_or(|readers| !readers.contains(&left))
            );
            assert!(
                memo.product_readers
                    .get(&right)
                    .is_none_or(|readers| !readers.contains(&left))
            );

            for key in [&left, &right] {
                assert!(memo.begin(key.clone()));
            }
            let mut entries = vec![
                (
                    left.clone(),
                    ProductValue::Unit,
                    ProductDependencies {
                        products: HashMap::from([(right.clone(), None), (external.clone(), Some(2))]),
                        facts: HashMap::new(),
                    },
                ),
                (
                    right.clone(),
                    ProductValue::Unit,
                    ProductDependencies {
                        products: HashMap::from([(left.clone(), None), (external.clone(), Some(2))]),
                        facts: HashMap::new(),
                    },
                ),
            ];
            if reverse {
                entries.reverse();
            }
            assert!(memo.finish_group(entries));
            for key in [&left, &right] {
                assert_eq!(
                    memo.product_dependencies(key),
                    Some(&HashMap::from([(external.clone(), Some(2))]))
                );
            }
            assert_eq!(memo.generation(&unrelated), unrelated_generation);
        }
    }

    #[test]
    fn changed_fact_authority_discards_only_pending_readers_of_that_fact() {
        let root = RootId::for_test(40);
        let reader = ProductKey::RuntimeDemand(fake_executable_with_function(root, 400));
        let unrelated = ProductKey::RuntimeDemand(fake_executable_with_function(root, 401));
        let fact = FactUse::current(FactKey::CodeIndexed(super::super::CodeId::ZERO));
        let other_fact = FactUse::settled(FactKey::RootEntry(root));
        let first = FactState {
            revision: Some(1),
            settled: false,
        };
        let second = FactState {
            revision: Some(2),
            settled: false,
        };

        let mut memo = ProductMemo::default();
        for (key, dependency, state) in [
            (&reader, fact.clone(), first),
            (
                &unrelated,
                other_fact.clone(),
                FactState {
                    revision: Some(1),
                    settled: true,
                },
            ),
        ] {
            assert!(memo.begin(key.clone()));
            memo.unblock(
                key,
                ProductDependencies {
                    products: HashMap::new(),
                    facts: HashMap::from([(dependency, state)]),
                },
            );
        }

        memo.reconcile_fact_movements(&HashMap::from([(fact.fact().clone(), first)]));
        assert!(memo.pending_dependencies.contains_key(&reader));
        memo.reconcile_fact_movements(&HashMap::from([(fact.fact().clone(), second)]));

        assert!(!memo.pending_dependencies.contains_key(&reader));
        assert!(memo.pending_dependencies.contains_key(&unrelated));
        assert!(
            memo.fact_readers
                .get(fact.fact())
                .is_none_or(|readers| !readers.contains(&reader))
        );
        assert!(
            memo.fact_readers
                .get(other_fact.fact())
                .is_some_and(|readers| readers.contains(&unrelated))
        );
    }

    #[test]
    fn group_settlement_rejects_discordant_dependency_snapshots_before_publication() {
        let root = RootId::for_test(41);
        let left = ProductKey::RuntimeDemand(fake_executable_with_function(root, 410));
        let right = ProductKey::RuntimeDemand(fake_executable_with_function(root, 411));
        let external = ProductKey::RuntimeDemand(fake_executable_with_function(root, 412));
        let unrelated = ProductKey::RuntimeDemand(fake_executable_with_function(root, 413));
        let fact = FactUse::current(FactKey::CodeIndexed(super::super::CodeId::ZERO));
        let fact_one = FactState {
            revision: Some(1),
            settled: false,
        };
        let fact_two = FactState {
            revision: Some(2),
            settled: false,
        };

        for reverse in [false, true] {
            for discordant_fact in [false, true] {
                let mut memo = ProductMemo::default();
                finish_test_product(&mut memo, &unrelated, ProductValue::Unit, []);
                let unrelated_generation = memo.generation(&unrelated);
                let left_dependencies = ProductDependencies {
                    products: HashMap::from([(external.clone(), if discordant_fact { Some(2) } else { Some(1) })]),
                    facts: HashMap::from([(fact.clone(), fact_one)]),
                };
                let right_dependencies = ProductDependencies {
                    products: HashMap::from([(external.clone(), Some(2))]),
                    facts: HashMap::from([(fact.clone(), if discordant_fact { fact_two } else { fact_one })]),
                };
                assert!(memo.begin(left.clone()));
                memo.unblock(&left, left_dependencies.clone());
                assert!(memo.begin(right.clone()));
                let mut entries = vec![
                    (left.clone(), ProductValue::Unit, left_dependencies),
                    (right.clone(), ProductValue::Unit, right_dependencies),
                ];
                if reverse {
                    entries.reverse();
                }

                assert!(!memo.finish_group(entries));
                for key in [&left, &right] {
                    assert!(memo.get(key).is_none());
                    assert!(!memo.pending_dependencies.contains_key(key));
                    assert!(!memo.in_progress.contains(key));
                }
                assert!(
                    memo.product_readers
                        .get(&external)
                        .is_none_or(|readers| !readers.contains(&left) && !readers.contains(&right))
                );
                assert!(
                    memo.fact_readers
                        .get(fact.fact())
                        .is_none_or(|readers| !readers.contains(&left) && !readers.contains(&right))
                );
                assert_eq!(memo.generation(&unrelated), unrelated_generation);

                for key in [&left, &right] {
                    assert!(memo.begin(key.clone()));
                }
                let concordant = ProductDependencies {
                    products: HashMap::from([(external.clone(), Some(2))]),
                    facts: HashMap::from([(fact.clone(), fact_two)]),
                };
                assert!(memo.finish_group(vec![
                    (left.clone(), ProductValue::Unit, concordant.clone()),
                    (right.clone(), ProductValue::Unit, concordant),
                ]));
            }
        }
    }

    #[test]
    fn rejected_group_retries_without_displaced_dependency_snapshots() {
        let root = RootId::for_test(42);
        let left = ProductKey::RuntimeDemand(fake_executable_with_function(root, 420));
        let right = ProductKey::RuntimeDemand(fake_executable_with_function(root, 421));
        let external = ProductKey::RuntimeDemand(fake_executable_with_function(root, 422));

        for reverse in [false, true] {
            let mut memo = ProductMemo::default();
            for key in [&left, &right] {
                assert!(memo.begin(key.clone()));
            }
            let first = ProductDependencies {
                products: HashMap::from([(external.clone(), Some(1))]),
                facts: HashMap::new(),
            };
            assert!(memo.finish_group(vec![
                (left.clone(), ProductValue::Unit, first.clone()),
                (right.clone(), ProductValue::Unit, first),
            ]));
            for key in [&left, &right] {
                memo.remove(key);
            }

            assert!(memo.begin(right.clone()));
            let current = ProductDependencies {
                products: HashMap::from([(external.clone(), Some(2))]),
                facts: HashMap::new(),
            };
            memo.unblock(&right, current.clone());
            assert!(memo.begin(left.clone()));
            let stale = memo
                .displaced
                .get(&left)
                .expect("left should retain its prior value while reproducing")
                .dependencies
                .clone();
            let mut entries = vec![
                (left.clone(), ProductValue::Unit, stale),
                (right.clone(), ProductValue::Unit, current.clone()),
            ];
            if reverse {
                entries.reverse();
            }
            assert!(!memo.finish_group(entries));

            for key in [&left, &right] {
                let displaced = memo
                    .displaced
                    .get(key)
                    .expect("rejected member should retain its prior value and generation");
                assert_eq!(displaced.generation, 1);
                assert_eq!(displaced.dependencies, ProductDependencies::default());
                assert!(memo.begin(key.clone()));
            }
            assert!(memo.finish_group(vec![
                (left.clone(), ProductValue::Unit, current.clone()),
                (right.clone(), ProductValue::Unit, current),
            ]));
            assert_eq!(memo.generation(&left), Some(1));
            assert_eq!(memo.generation(&right), Some(1));
        }
    }

    #[test]
    fn callable_owner_scc_is_finite_order_free_and_contains_only_pass_through_owners() {
        let root = RootId::for_test(36);
        let x = TransportPosition::ExecutableInput {
            executable: executable_symbol_for_test(&fake_executable_with_function(root, 360)),
            semantic_index: 1,
        };
        let left = TransportPosition::Value {
            executable: executable_symbol_for_test(&fake_executable_with_function(root, 361)),
            value: ValueId::from_u32(1),
        };
        let right = TransportPosition::Value {
            executable: executable_symbol_for_test(&fake_executable_with_function(root, 361)),
            value: ValueId::from_u32(2),
        };
        let left_resolution = executable_symbol_for_test(&fake_executable_with_function(root, 362));
        let right_resolution = executable_symbol_for_test(&fake_executable_with_function(root, 363));
        let x_layout = TransportLayout {
            structural: ShapeId::for_test(91),
            carrier: TransportCarrier::ValueRef,
        };
        let y_layout = TransportLayout::structural(ShapeId::for_test(92));
        let no_anchor = [OwnerEquation {
            seed: OwnerState::bottom(x_layout),
            children: vec![0],
        }];
        assert_eq!(
            settle_owner_equations(&no_anchor, false).0[0],
            OwnerState::bottom(x_layout)
        );

        let seed = OwnerState {
            layout: x_layout,
            resolutions: HashSet::from([left_resolution.clone(), left_resolution, right_resolution]),
            publications: HashSet::from([x, left, right]),
        };
        let pair = [
            OwnerEquation {
                seed: seed.clone(),
                children: vec![1],
            },
            OwnerEquation {
                seed: OwnerState::bottom(y_layout),
                children: vec![0],
            },
        ];
        let pair_forward = settle_owner_equations(&pair, false);
        let pair_reverse = settle_owner_equations(&pair, true);
        assert_eq!(pair_forward.0, pair_reverse.0);
        assert!(pair_forward.1 <= 3 && pair_reverse.1 <= 3);
        assert_eq!(pair_forward.0[0].layout, x_layout);
        assert_eq!(pair_forward.0[1].layout, y_layout);

        let ring = [
            OwnerEquation {
                seed,
                children: vec![1],
            },
            OwnerEquation {
                seed: OwnerState::bottom(y_layout),
                children: vec![2],
            },
            OwnerEquation {
                seed: OwnerState::bottom(x_layout),
                children: vec![3],
            },
            OwnerEquation {
                seed: OwnerState::bottom(y_layout),
                children: vec![0],
            },
        ];
        let ring_forward = settle_owner_equations(&ring, false);
        let ring_reverse = settle_owner_equations(&ring, true);
        assert_eq!(ring_forward.0, ring_reverse.0);
        assert!(ring_forward.1 <= 5 && ring_reverse.1 <= 5);

        let mut world = World::new();
        let callable = world.intern_callable(super::super::transport::CallableDescr {
            function: None,
            arity: 0,
            capture_tys: Box::default(),
            capture_shapes: Box::default(),
            capture_lanes: Box::default(),
        });
        for answer in pair_forward.0 {
            let ProductValue::CallableConstruction(answer) = answer.product_value(callable, BoundaryId::for_test(9))
            else {
                unreachable!()
            };
            assert!(answer.construction.is_none());
            assert_eq!(answer.callable_facts[&callable].resolutions.len(), 2);
            assert_eq!(answer.callable_facts[&callable].direct_edges.len(), 2);
            assert_eq!(answer.boundary_facts[&BoundaryId::for_test(9)].publications.len(), 3);
        }
    }

    #[test]
    fn callable_owner_group_is_atomic_replacement_safe_and_frontier_relative() {
        let root = RootId::for_test(37);
        let x_position = TransportPosition::ExecutableInput {
            executable: executable_symbol_for_test(&fake_executable_with_function(root, 370)),
            semantic_index: 1,
        };
        let y_position = TransportPosition::Value {
            executable: executable_symbol_for_test(&fake_executable_with_function(root, 370)),
            value: ValueId::from_u32(5),
        };
        let terminal_position = TransportPosition::Value {
            executable: executable_symbol_for_test(&fake_executable_with_function(root, 371)),
            value: ValueId::from_u32(1),
        };
        let x = ProductKey::CallableConstruction(x_position.clone());
        let y = ProductKey::CallableConstruction(y_position);
        let terminal = ProductKey::CallableConstruction(terminal_position.clone());
        let slot = ProductKey::IncomingInputSlot(InputSlot {
            executable: fake_executable_with_function(root, 370),
            semantic_index: 1,
        });
        let parent = ProductKey::AbiExecutable(fake_executable_with_function(root, 370));
        let unrelated = ProductKey::CallableConstruction(TransportPosition::Value {
            executable: executable_symbol_for_test(&fake_executable_with_function(root, 372)),
            value: ValueId::from_u32(0),
        });
        let unrelated_parent = ProductKey::AbiExecutable(fake_executable_with_function(root, 372));
        let mut world = World::new();
        let callable = world.intern_callable(super::super::transport::CallableDescr {
            function: None,
            arity: 0,
            capture_tys: Box::default(),
            capture_shapes: Box::default(),
            capture_lanes: Box::default(),
        });
        let boundary = BoundaryId::for_test(10);
        let layout = TransportLayout {
            structural: ShapeId::for_test(101),
            carrier: TransportCarrier::ValueRef,
        };
        let first_resolution = executable_symbol_for_test(&fake_executable_with_function(root, 373));
        let second_resolution = executable_symbol_for_test(&fake_executable_with_function(root, 374));
        let equations = |resolution: ExecutableSymbol, publication: TransportPosition| {
            [
                OwnerEquation {
                    seed: OwnerState {
                        layout,
                        resolutions: HashSet::from([resolution]),
                        publications: HashSet::from([publication, x_position.clone()]),
                    },
                    children: vec![1],
                },
                OwnerEquation {
                    seed: OwnerState::bottom(layout),
                    children: vec![0],
                },
            ]
        };
        let first_answers =
            settle_owner_equations(&equations(first_resolution.clone(), terminal_position.clone()), false).0;
        let keys = [x.clone(), y.clone()];
        let external = [terminal.clone(), slot.clone()];
        let slot_value = ProductValue::IncomingInputSlot(HashSet::from([IncomingInputSource {
            producer: fake_executable_with_function(root, 371),
            value: ValueId::from_u32(1),
            role: IncomingInputRole::CallArgument,
        }]));

        let mut memos = Vec::new();
        for reverse in [false, true] {
            let mut memo = ProductMemo::default();
            finish_test_product(
                &mut memo,
                &terminal,
                callable_owner_answer(
                    layout,
                    terminal_position.clone(),
                    callable,
                    boundary,
                    first_resolution.clone(),
                ),
                [],
            );
            finish_test_product(&mut memo, &slot, slot_value.clone(), []);
            finish_owner_group(&mut memo, &keys, &first_answers, &external, callable, boundary, reverse);
            memos.push(memo);
        }
        let mut memo = memos.remove(0);
        let reverse = memos.remove(0);
        for key in &keys {
            assert_eq!(memo.get(key), reverse.get(key));
            assert_eq!(memo.generation(key), reverse.generation(key));
            assert_eq!(
                memo.product_dependencies(key),
                Some(&HashMap::from([(terminal.clone(), Some(1)), (slot.clone(), Some(1))]))
            );
        }

        finish_test_product(&mut memo, &parent, ProductValue::Unit, [x.clone()]);
        finish_test_product(&mut memo, &unrelated, withdrawn_callable_owner_answer(layout), []);
        finish_test_product(&mut memo, &unrelated_parent, ProductValue::Unit, [unrelated.clone()]);
        let unrelated_generations = (memo.generation(&unrelated), memo.generation(&unrelated_parent));

        let generations = keys.clone().map(|key| memo.generation(&key));
        for key in &keys {
            memo.remove(key);
        }
        finish_owner_group(&mut memo, &keys, &first_answers, &external, callable, boundary, true);
        assert_eq!(keys.clone().map(|key| memo.generation(&key)), generations);

        let replacement_position = TransportPosition::Value {
            executable: executable_symbol_for_test(&fake_executable_with_function(root, 371)),
            value: ValueId::from_u32(2),
        };
        memo.remove(&terminal);
        finish_test_product(
            &mut memo,
            &terminal,
            callable_owner_answer(
                layout,
                replacement_position.clone(),
                callable,
                boundary,
                second_resolution.clone(),
            ),
            [],
        );
        assert!(keys.iter().all(|key| memo.get(key).is_none()));
        assert!(memo.stale_dependency(&parent).is_some());
        let replacement_answers = settle_owner_equations(
            &equations(second_resolution.clone(), replacement_position.clone()),
            true,
        )
        .0;
        finish_owner_group(
            &mut memo,
            &keys,
            &replacement_answers,
            &external,
            callable,
            boundary,
            false,
        );
        assert!(keys.iter().all(|key| memo.generation(key) == Some(2)));
        assert!(memo.get(&parent).is_none());

        memo.remove(&terminal);
        finish_test_product(
            &mut memo,
            &terminal,
            callable_owner_answer(layout, replacement_position, callable, boundary, second_resolution),
            [],
        );
        assert!(keys.iter().all(|key| memo.generation(key) == Some(2)));

        memo.remove(&terminal);
        finish_test_product(&mut memo, &terminal, withdrawn_callable_owner_answer(layout), []);
        assert!(keys.iter().all(|key| memo.get(key).is_none()));
        let empty = settle_owner_equations(
            &equations(
                executable_symbol_for_test(&fake_executable_with_function(root, 376)),
                x_position.clone(),
            ),
            false,
        )
        .0
        .into_iter()
        .map(|answer| OwnerState::bottom(answer.layout))
        .collect::<Vec<_>>();
        finish_owner_group(&mut memo, &keys, &empty, &external, callable, boundary, false);
        assert!(keys.iter().all(|key| memo.generation(key) == Some(3)));

        memo.remove(&slot);
        finish_test_product(
            &mut memo,
            &slot,
            ProductValue::IncomingInputSlot(HashSet::from([
                IncomingInputSource {
                    producer: fake_executable_with_function(root, 371),
                    value: ValueId::from_u32(1),
                    role: IncomingInputRole::CallArgument,
                },
                IncomingInputSource {
                    producer: fake_executable_with_function(root, 375),
                    value: ValueId::from_u32(2),
                    role: IncomingInputRole::CallArgument,
                },
            ])),
            [],
        );
        assert!(keys.iter().all(|key| memo.get(key).is_none()));
        finish_owner_group(
            &mut memo,
            std::slice::from_ref(&x),
            std::slice::from_ref(&empty[0]),
            &external,
            callable,
            boundary,
            false,
        );
        assert!(memo.get(&x).is_some());
        assert!(memo.get(&y).is_none());
        assert_eq!(
            (memo.generation(&unrelated), memo.generation(&unrelated_parent)),
            unrelated_generations
        );
    }
}
