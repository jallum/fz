//! Product-keyed pull substrate for compiler2 artifacts.
//!
//! This module is intentionally separate from the existing job scheduler. A
//! product producer answers one named demand and can only return a value or
//! explicit waits. It does not enqueue jobs, schedule follow-up work, or scan a
//! root frontier.

use std::collections::{HashMap, HashSet};

use crate::telemetry::{Telemetry, opaque_debug};
use crate::{measurements, metadata};

use super::drive::FactKey;
use super::facts::FactUse;
use super::identity::{ExecutableKey, RootId};
use super::transport::{BoundaryId, CallableId, TransportPosition};

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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProductValue {
    Unit,
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

pub trait ProductProducers {
    fn produce_root_backend_product(&mut self, root: RootId) -> PullOutcome;
    fn produce_backend_executable(&mut self, executable: &ExecutableKey) -> PullOutcome;
    fn produce_abi_executable(&mut self, executable: &ExecutableKey) -> PullOutcome;
    fn produce_materialized_executable(&mut self, executable: &ExecutableKey) -> PullOutcome;
    fn produce_executable_effects(&mut self, executable: &ExecutableKey) -> PullOutcome;
    fn produce_runtime_demand(&mut self, executable: &ExecutableKey) -> PullOutcome;
    fn produce_outgoing_input_edges(&mut self, executable: &ExecutableKey) -> PullOutcome;
    fn produce_incoming_input_slot(&mut self, slot: &InputSlot) -> PullOutcome;
    fn produce_transport_shape(&mut self, position: &TransportPosition) -> PullOutcome;
    fn produce_transport_component(&mut self, position: &TransportPosition) -> PullOutcome;
    fn produce_callable_facts(&mut self, callable: CallableId) -> PullOutcome;
    fn produce_boundary_facts(&mut self, boundary: BoundaryId) -> PullOutcome;
}

pub struct ProductDriver<'a> {
    tel: &'a dyn Telemetry,
    memo: ProductMemo,
}

impl<'a> ProductDriver<'a> {
    pub fn new(tel: &'a dyn Telemetry) -> Self {
        Self {
            tel,
            memo: ProductMemo::default(),
        }
    }

    pub fn memo(&self) -> &ProductMemo {
        &self.memo
    }

    pub fn pull(&mut self, producers: &mut impl ProductProducers, key: ProductKey) -> PullOutcome {
        self.emit("requested", &key, 0);
        if let Some(value) = self.memo.get(&key) {
            self.emit("cache_hit", &key, 0);
            return PullOutcome::Produced(value.clone());
        }
        if !self.memo.begin(key.clone()) {
            self.emit("reentered", &key, 1);
            return PullOutcome::Waiting(vec![PullWait::Product(key)]);
        }

        let outcome = match &key {
            ProductKey::RootBackendProduct(root) => producers.produce_root_backend_product(*root),
            ProductKey::BackendExecutable(executable) => producers.produce_backend_executable(executable),
            ProductKey::AbiExecutable(executable) => producers.produce_abi_executable(executable),
            ProductKey::MaterializedExecutable(executable) => producers.produce_materialized_executable(executable),
            ProductKey::ExecutableEffects(executable) => producers.produce_executable_effects(executable),
            ProductKey::RuntimeDemand(executable) => producers.produce_runtime_demand(executable),
            ProductKey::OutgoingInputEdges(executable) => producers.produce_outgoing_input_edges(executable),
            ProductKey::IncomingInputSlot(slot) => producers.produce_incoming_input_slot(slot),
            ProductKey::TransportShape(position) => producers.produce_transport_shape(position),
            ProductKey::TransportComponent(position) => producers.produce_transport_component(position),
            ProductKey::CallableFacts(callable) => producers.produce_callable_facts(*callable),
            ProductKey::BoundaryFacts(boundary) => producers.produce_boundary_facts(*boundary),
        };

        match outcome {
            PullOutcome::Produced(value) => {
                self.memo.finish(&key, value.clone());
                self.emit("produced", &key, 0);
                PullOutcome::Produced(value)
            }
            PullOutcome::Waiting(waits) => {
                self.memo.unblock(&key);
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
        fn produce_root_backend_product(&mut self, root: RootId) -> PullOutcome {
            self.produce(ProductKey::RootBackendProduct(root))
        }

        fn produce_backend_executable(&mut self, executable: &ExecutableKey) -> PullOutcome {
            self.produce(ProductKey::BackendExecutable(executable.clone()))
        }

        fn produce_abi_executable(&mut self, executable: &ExecutableKey) -> PullOutcome {
            self.produce(ProductKey::AbiExecutable(executable.clone()))
        }

        fn produce_materialized_executable(&mut self, executable: &ExecutableKey) -> PullOutcome {
            self.produce(ProductKey::MaterializedExecutable(executable.clone()))
        }

        fn produce_executable_effects(&mut self, executable: &ExecutableKey) -> PullOutcome {
            self.produce(ProductKey::ExecutableEffects(executable.clone()))
        }

        fn produce_runtime_demand(&mut self, executable: &ExecutableKey) -> PullOutcome {
            self.produce(ProductKey::RuntimeDemand(executable.clone()))
        }

        fn produce_outgoing_input_edges(&mut self, executable: &ExecutableKey) -> PullOutcome {
            self.produce(ProductKey::OutgoingInputEdges(executable.clone()))
        }

        fn produce_incoming_input_slot(&mut self, slot: &InputSlot) -> PullOutcome {
            self.produce(ProductKey::IncomingInputSlot(slot.clone()))
        }

        fn produce_transport_shape(&mut self, position: &TransportPosition) -> PullOutcome {
            self.produce(ProductKey::TransportShape(position.clone()))
        }

        fn produce_transport_component(&mut self, position: &TransportPosition) -> PullOutcome {
            self.produce(ProductKey::TransportComponent(position.clone()))
        }

        fn produce_callable_facts(&mut self, callable: CallableId) -> PullOutcome {
            self.produce(ProductKey::CallableFacts(callable))
        }

        fn produce_boundary_facts(&mut self, boundary: BoundaryId) -> PullOutcome {
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
        let mut driver = ProductDriver::new(&tel);

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
        let executable = fake_executable(RootId::for_test(1));
        let key = ProductKey::BackendExecutable(executable);
        let mut producers = FakeProducers::default();
        let mut driver = ProductDriver::new(&tel);

        let outcome = driver.pull(&mut producers, key.clone());

        assert_eq!(
            outcome,
            PullOutcome::wait_on_fact(FactUse::current(FactKey::CodeIndexed(super::super::CodeId::ZERO)))
        );
        assert!(driver.memo().get(&key).is_none());
        assert!(!driver.memo().contains_in_progress(&key));
        assert_eq!(capture.count(&["fz", "compiler2", "pull", "product", "waited"]), 1);
    }

    #[test]
    fn product_driver_turns_reentry_into_a_product_wait() {
        let tel = ConfiguredTelemetry::new();
        let executable = fake_executable(RootId::for_test(2));
        let key = ProductKey::ExecutableEffects(executable);
        let mut driver = ProductDriver::new(&tel);
        let mut producers = FakeProducers {
            reenter: Some(key.clone()),
            ..FakeProducers::default()
        };

        assert!(driver.memo.begin(key.clone()));
        let outcome = driver.pull(&mut producers, key.clone());

        assert_eq!(outcome, PullOutcome::wait_on_product(key));
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
}
