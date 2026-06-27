//! Product-keyed pull substrate for compiler2 artifacts.
//!
//! This module is intentionally separate from the existing job scheduler. A
//! product producer answers one named demand and can only return a value or
//! explicit waits. It does not enqueue jobs, schedule follow-up work, or scan a
//! root frontier.

use std::collections::{HashMap, HashSet};

use crate::telemetry::{Telemetry, opaque_debug};
use crate::{measurements, metadata};

use super::body::{CallSiteId, ValueId};
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
pub enum ProductValue {
    Unit,
    RuntimeDemand(Box<ExecutableRuntimeDemand>),
    IncomingInputSlot(Box<[IncomingInputSource]>),
    TransportShape(Option<ShapeId>),
    TransportComponent(TransportComponentInventory),
    CallableFacts(Option<CallableFacts>),
    BoundaryFacts(Option<BoundaryFacts>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PullWait {
    Product(ProductKey),
    Fact(FactUse<FactKey>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PullOutcome {
    Produced(ProductValue),
    Waiting(Vec<PullWait>),
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

    fn finish(&mut self, key: &ProductKey, value: ProductValue) {
        self.in_progress.remove(key);
        self.produced.insert(key.clone(), value);
    }

    fn unblock(&mut self, key: &ProductKey) {
        self.in_progress.remove(key);
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
    return_demands: HashMap<ExecutableKey, RuntimeDemand>,
    demanded_transport_positions: HashSet<TransportPosition>,
    transport_shapes: HashMap<TransportPosition, ShapeId>,
    transport_components: HashMap<TransportPosition, TransportComponentInventory>,
    callable_facts: HashMap<CallableId, CallableFacts>,
    boundary_facts: HashMap<BoundaryId, BoundaryFacts>,
    demanded_callables: HashSet<CallableId>,
    demanded_boundaries: HashSet<BoundaryId>,
    executable_index: HashMap<ExecutableKey, usize>,
    root_scans: u64,
    follow_ups: u64,
}

impl PullSession {
    pub fn new(root: RootId) -> Self {
        Self {
            root,
            memo: ProductMemo::default(),
            demanded_executables: HashSet::new(),
            call_edges: HashMap::new(),
            incoming_inputs: HashMap::new(),
            return_demands: HashMap::new(),
            demanded_transport_positions: HashSet::new(),
            transport_shapes: HashMap::new(),
            transport_components: HashMap::new(),
            callable_facts: HashMap::new(),
            boundary_facts: HashMap::new(),
            demanded_callables: HashSet::new(),
            demanded_boundaries: HashSet::new(),
            executable_index: HashMap::new(),
            root_scans: 0,
            follow_ups: 0,
        }
    }

    pub fn root(&self) -> RootId {
        self.root
    }

    pub fn memo(&self) -> &ProductMemo {
        &self.memo
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

    pub fn return_demand(&self, executable: &ExecutableKey) -> Option<&RuntimeDemand> {
        self.return_demands.get(executable)
    }

    pub fn demanded_transport_positions(&self) -> &HashSet<TransportPosition> {
        &self.demanded_transport_positions
    }

    pub fn transport_shape(&self, position: &TransportPosition) -> Option<ShapeId> {
        self.transport_shapes.get(position).copied()
    }

    pub fn transport_component(&self, anchor: &TransportPosition) -> Option<&TransportComponentInventory> {
        self.transport_components.get(anchor)
    }

    pub fn callable_facts(&self, callable: CallableId) -> Option<&CallableFacts> {
        self.callable_facts.get(&callable)
    }

    pub fn boundary_facts(&self, boundary: BoundaryId) -> Option<&BoundaryFacts> {
        self.boundary_facts.get(&boundary)
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

    pub fn root_scans(&self) -> u64 {
        self.root_scans
    }

    pub fn follow_ups(&self) -> u64 {
        self.follow_ups
    }

    pub fn record_call_edge(&mut self, edge: DemandedCallEdge) {
        self.demanded_executables.insert(edge.caller.clone());
        self.demanded_executables.insert(edge.callee.clone());
        for (semantic_index, source) in &edge.inputs {
            let slot = InputSlot {
                executable: edge.callee.clone(),
                semantic_index: *semantic_index,
            };
            push_unique(self.incoming_inputs.entry(slot).or_default(), source.clone());
        }
        self.call_edges.entry(edge.caller.clone()).or_default().push(edge);
    }

    pub fn record_return_demand(&mut self, executable: ExecutableKey, demand: RuntimeDemand) {
        if demand.is_ignore() {
            return;
        }
        self.demanded_executables.insert(executable.clone());
        self.return_demands
            .entry(executable)
            .and_modify(|existing| existing.join_assign(&demand))
            .or_insert(demand);
    }

    pub fn record_transport_component(&mut self, anchor: TransportPosition, positions: Vec<TransportPosition>) {
        self.demanded_transport_positions.insert(anchor.clone());
        self.demanded_transport_positions.extend(positions.iter().cloned());
        self.transport_components
            .insert(anchor.clone(), TransportComponentInventory { anchor, positions });
    }

    pub fn record_transport_shape(&mut self, position: TransportPosition, shape: ShapeId) {
        self.demanded_transport_positions.insert(position.clone());
        self.transport_shapes.insert(position, shape);
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
                follow_ups: self.follow_ups,
                root_scans: self.root_scans,
            },
            &metadata! {},
        );
    }
}

fn push_unique<T>(items: &mut Vec<T>, value: T)
where
    T: PartialEq,
{
    if !items.contains(&value) {
        items.push(value);
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
    fn produce_root_backend_product(&mut self, _session: &mut PullSession, root: RootId) -> PullOutcome {
        PullOutcome::wait_on_product(ProductKey::RootBackendProduct(root))
    }

    fn produce_backend_executable(&mut self, _session: &mut PullSession, executable: &ExecutableKey) -> PullOutcome {
        PullOutcome::wait_on_product(ProductKey::BackendExecutable(executable.clone()))
    }

    fn produce_abi_executable(&mut self, _session: &mut PullSession, executable: &ExecutableKey) -> PullOutcome {
        PullOutcome::wait_on_product(ProductKey::AbiExecutable(executable.clone()))
    }

    fn produce_materialized_executable(
        &mut self,
        _session: &mut PullSession,
        executable: &ExecutableKey,
    ) -> PullOutcome {
        PullOutcome::wait_on_product(ProductKey::MaterializedExecutable(executable.clone()))
    }

    fn produce_executable_effects(&mut self, _session: &mut PullSession, executable: &ExecutableKey) -> PullOutcome {
        PullOutcome::wait_on_product(ProductKey::ExecutableEffects(executable.clone()))
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
                self.session.memo.finish(&key, value.clone());
                self.emit("produced", &key, 0);
                PullOutcome::Produced(value)
            }
            PullOutcome::Waiting(waits) => {
                self.session.memo.unblock(&key);
                self.emit("waited", &key, waits.len());
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

        session.record_call_edge(edge.clone());

        assert_eq!(session.call_edges(&caller), std::slice::from_ref(&edge));
        assert_eq!(
            session.incoming_input_sources(&InputSlot {
                executable: callee,
                semantic_index: 1,
            }),
            std::slice::from_ref(&source)
        );
        assert_eq!(session.root_scans(), 0);
        assert_eq!(session.follow_ups(), 0);
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
        assert_eq!(driver.session().root_scans(), 0);
        assert_eq!(driver.session().follow_ups(), 0);
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
            PullOutcome::Produced(ProductValue::TransportShape(Some(shape)))
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
        assert_eq!(driver.session().root_scans(), 0);
        assert_eq!(driver.session().follow_ups(), 0);
    }

    #[test]
    fn pull_session_finished_telemetry_reports_zero_push_counters() {
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
        driver.finish_session();

        let finished = capture
            .last(&["fz", "compiler2", "pull", "session", "finished"])
            .expect("pull session should emit final inventory telemetry");
        assert_eq!(measurement_u64(&finished, "executables"), 1);
        assert_eq!(measurement_u64(&finished, "follow_ups"), 0);
        assert_eq!(measurement_u64(&finished, "root_scans"), 0);
    }

    fn fake_executable(root: RootId) -> ExecutableKey {
        let function = super::super::FunctionId::for_test(root.as_u32() + 10);
        let mut types = super::super::Types::new();
        let activation = super::super::ActivationKey::from_inputs(root, function, &[], &mut types);
        ExecutableKey {
            activation,
            need: super::super::ExecutableNeed::Value,
        }
    }

    fn measurement_u64(event: &crate::telemetry::capture::OwnedEvent, key: &str) -> u64 {
        match event.measurements.get(key) {
            Some(crate::telemetry::Value::U64(value)) => *value,
            other => panic!("expected u64 measurement {key}, got {other:?}"),
        }
    }
}
