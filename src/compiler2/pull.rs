//! Product-keyed pull substrate for compiler2 artifacts.
//!
//! This module is intentionally separate from the existing job scheduler. A
//! product producer answers one named demand and can only return a value or
//! explicit waits. It does not enqueue jobs, schedule follow-up work, or scan a
//! root frontier.

#[cfg(test)]
use super::body::{CallSiteId, ValueId};
use super::world::World;
use std::cell::{Cell, Ref, RefCell, RefMut};
use std::collections::{HashMap, HashSet};
use std::num::NonZeroU64;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::telemetry::{Telemetry, TelemetryExt as _};

use super::artifact::{
    AbiReadyExecutable, BackendExecutable, BackendProgram, EffectSummary, MaterializedExecutable, NativeProgram,
    RootBackendProductAnswer,
};
use super::drive::{DependencyKey, FactKey, ProductAddress};
use super::executable_facts::ExecutableFacts;
use super::facts::{FactChange, FactMovement, FactState, FactUse};
use super::identity::{ExecutableKey, RootId};
use super::scheduler::WorkStartTally;
use super::semantic::{ExecutableRuntimeDemand, SemanticOrd};
#[cfg(test)]
use super::transport::LaneId;
#[cfg(test)]
use super::transport::ShapeId;
use super::transport::{CallableConstructionOwner, TransportPosition};
pub use super::transport::{TransportCarrier, TransportLayout};
static NEXT_PULL_SESSION_ID: AtomicU64 = AtomicU64::new(1);
const SESSION_STARTED_EVENT: &[&str] = &["fz", "compiler2", "pull", "session", "started"];
const SESSION_FINISHED_EVENT: &[&str] = &["fz", "compiler2", "pull", "session", "finished"];
const PRODUCT_REQUESTED_EVENT: &[&str] = &["fz", "compiler2", "pull", "product", "requested"];
const PRODUCT_EVALUATED_EVENT: &[&str] = &["fz", "compiler2", "pull", "product", "evaluated"];
const PRODUCT_COPUBLISHED_EVENT: &[&str] = &["fz", "compiler2", "pull", "product", "copublished"];
const RECURSIVE_GROUP_PUBLISHED_EVENT: &[&str] = &["fz", "compiler2", "pull", "recursive_group", "published"];

fn causal_product_events_enabled(tel: &impl Telemetry) -> bool {
    [
        PRODUCT_REQUESTED_EVENT,
        PRODUCT_EVALUATED_EVENT,
        PRODUCT_COPUBLISHED_EVENT,
        RECURSIVE_GROUP_PUBLISHED_EVENT,
    ]
    .into_iter()
    .any(|event| tel.is_raw_event_enabled(event))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PullSessionId(NonZeroU64);

impl PullSessionId {
    pub(crate) fn get(self) -> u64 {
        self.0.get()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProductRequestId(NonZeroU64);

impl ProductRequestId {
    pub(crate) fn get(self) -> u64 {
        self.0.get()
    }
}

#[derive(Debug)]
struct ProductRequestIds {
    next: Option<NonZeroU64>,
}

impl ProductRequestIds {
    fn new() -> Self {
        Self {
            next: NonZeroU64::new(1),
        }
    }

    fn allocate(&mut self) -> ProductRequestId {
        let id = self.next.expect("product request identity exhausted");
        self.next = id.get().checked_add(1).and_then(NonZeroU64::new);
        ProductRequestId(id)
    }
}

fn allocate_pull_session_id(counter: &AtomicU64) -> PullSessionId {
    let id = counter
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
            (next != 0).then(|| next.checked_add(1).unwrap_or(0))
        })
        .unwrap_or_else(|_| panic!("pull session identity exhausted"));
    PullSessionId(NonZeroU64::new(id).expect("the allocator never returns its exhausted sentinel"))
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ProductKey {
    RootBackendProduct(RootId),
    RootBackendContent(RootId),
    NativeProgram(RootId),
    BackendExecutable(ExecutableKey),
    AbiExecutable(ExecutableKey),
    MaterializedExecutable(ExecutableKey),
    ExecutableEffects(ExecutableKey),
    TransportShape(TransportPosition),
    CallableConstruction(TransportPosition),
}

impl SemanticOrd<super::types::Types> for ProductKey {
    fn semantic_cmp(&self, other: &Self, types: &super::types::Types) -> std::cmp::Ordering {
        product_rank(self)
            .cmp(&product_rank(other))
            .then_with(|| match (self, other) {
                (Self::AbiExecutable(left), Self::AbiExecutable(right))
                | (Self::BackendExecutable(left), Self::BackendExecutable(right))
                | (Self::MaterializedExecutable(left), Self::MaterializedExecutable(right))
                | (Self::ExecutableEffects(left), Self::ExecutableEffects(right)) => left.semantic_cmp(right, types),
                (Self::RootBackendProduct(left), Self::RootBackendProduct(right))
                | (Self::RootBackendContent(left), Self::RootBackendContent(right))
                | (Self::NativeProgram(left), Self::NativeProgram(right)) => left.cmp(right),
                (Self::TransportShape(left), Self::TransportShape(right))
                | (Self::CallableConstruction(left), Self::CallableConstruction(right)) => {
                    left.semantic_cmp(right, types)
                }
                _ => std::cmp::Ordering::Equal,
            })
    }
}

fn product_rank(product: &ProductKey) -> u8 {
    match product {
        ProductKey::AbiExecutable(_) => 0,
        ProductKey::BackendExecutable(_) => 1,
        ProductKey::CallableConstruction(_) => 2,
        ProductKey::ExecutableEffects(_) => 3,
        ProductKey::MaterializedExecutable(_) => 6,
        ProductKey::RootBackendProduct(_) => 9,
        ProductKey::RootBackendContent(_) => 10,
        ProductKey::NativeProgram(_) => 11,
        ProductKey::TransportShape(_) => 12,
    }
}

impl ProductKey {
    pub fn kind(&self) -> &'static str {
        match self {
            Self::RootBackendProduct(_) => "root_backend_product",
            Self::RootBackendContent(_) => "root_backend_content",
            Self::NativeProgram(_) => "native_program",
            Self::BackendExecutable(_) => "backend_executable",
            Self::AbiExecutable(_) => "abi_executable",
            Self::MaterializedExecutable(_) => "materialized_executable",
            Self::ExecutableEffects(_) => "executable_effects",
            Self::TransportShape(_) => "transport_shape",
            Self::CallableConstruction(_) => "callable_construction",
        }
    }

    fn executable(&self) -> Option<&ExecutableKey> {
        match self {
            Self::BackendExecutable(executable)
            | Self::AbiExecutable(executable)
            | Self::MaterializedExecutable(executable)
            | Self::ExecutableEffects(executable) => Some(executable),
            Self::RootBackendProduct(_)
            | Self::RootBackendContent(_)
            | Self::NativeProgram(_)
            | Self::TransportShape(_)
            | Self::CallableConstruction(_) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TransportShapeFact {
    Layout(TransportLayout),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ProductValue {
    #[cfg(test)]
    Unit,
    RootBackendProduct(RootBackendProductAnswer),
    RootBackendContent(Rc<BackendProgram>),
    NativeProgram(Rc<NativeProgram>),
    BackendExecutable(Rc<BackendExecutable>),
    AbiExecutable(Rc<AbiReadyExecutable>),
    MaterializedExecutable(Rc<MaterializedExecutable>),
    ExecutableEffects(EffectSummary),
    TransportShape(TransportShapeFact),
    CallableConstruction(Rc<CallableConstructionOwner>),
}

fn same_product_value(left: &ProductValue, right: &ProductValue) -> bool {
    match (left, right) {
        (ProductValue::RootBackendProduct(left), ProductValue::RootBackendProduct(right)) => {
            (Rc::ptr_eq(&left.program, &right.program) || left.program == right.program)
                && (Rc::ptr_eq(&left.transport, &right.transport) || left.transport == right.transport)
        }
        (ProductValue::RootBackendContent(left), ProductValue::RootBackendContent(right)) => Rc::ptr_eq(left, right),
        (ProductValue::NativeProgram(left), ProductValue::NativeProgram(right)) => {
            Rc::ptr_eq(left, right) || super::artifact::native_programs_equal(left, right)
        }
        (ProductValue::BackendExecutable(left), ProductValue::BackendExecutable(right)) => {
            Rc::ptr_eq(left, right) || left == right
        }
        (ProductValue::AbiExecutable(left), ProductValue::AbiExecutable(right)) => {
            Rc::ptr_eq(left, right) || left == right
        }
        (ProductValue::MaterializedExecutable(left), ProductValue::MaterializedExecutable(right)) => {
            Rc::ptr_eq(left, right) || left == right
        }
        (ProductValue::CallableConstruction(left), ProductValue::CallableConstruction(right)) => {
            Rc::ptr_eq(left, right) || left == right
        }
        _ => left == right,
    }
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
    Failed(ProductFailure),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProductFailure {
    NativeLowering,
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
    fact_subscription_changes: Vec<(FactKey, bool)>,
    /// Monotone counter stamping each settled group with a distinct id. The
    /// first group settled gets id 1 (the field itself starts at the
    /// `Default` zero and is pre-incremented before use).
    next_group_id: u64,
    observed_products: HashSet<ProductKey>,
    external_changes: Vec<FactChange<ProductKey>>,
}

type ProductCommitMember = (ProductKey, ProductValue, ProductDependencies);

enum ProductCompletion {
    Batch(Vec<ProductCommitMember>),
    RecursiveGroup(Vec<ProductCommitMember>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ReaderMutation {
    Invalidate,
    Dirty,
    Refresh,
}

impl ReaderMutation {
    fn rank(self) -> u8 {
        match self {
            Self::Invalidate => 0,
            Self::Dirty => 1,
            Self::Refresh => 2,
        }
    }
}

/// One settled product's causal identity, carried on the `pull.product.settled`
/// event alongside the settled `ProductKey`/`ProductValue` pair. Stack-built
/// at every emit site -- never stored in the memo itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProductSettlement {
    pub generation: u64,
    pub changed: bool,
    pub group: Option<u64>,
}

#[derive(Debug, Clone, Copy)]
struct PendingNode {
    index: usize,
    lowlink: usize,
}

/// One Tarjan traversal over the dependency-reachable pending graph.
struct PendingStrongComponent {
    next_index: usize,
    nodes: HashMap<ProductKey, PendingNode>,
    stack: Vec<ProductKey>,
    on_stack: HashSet<ProductKey>,
    candidate_inventory: u64,
    vertex_visits: u64,
    edge_scans: u64,
}

fn sort_product_keys(keys: &mut [ProductKey], types: &super::types::Types) {
    keys.sort_by(|left, right| left.semantic_cmp(right, types));
    for pair in keys.windows(2) {
        debug_assert!(
            pair[0] == pair[1] || pair[0].semantic_cmp(&pair[1], types) != std::cmp::Ordering::Equal,
            "distinct product keys share one semantic order identity: {:?} vs {:?}",
            pair[0],
            pair[1]
        );
    }
}

impl PendingStrongComponent {
    fn find(
        memo: &ProductMemo,
        current: &ProductKey,
        current_dependencies: &ProductDependencies,
        dependency: &ProductKey,
    ) -> (Vec<ProductKey>, u64, u64, u64) {
        let mut search = Self {
            next_index: 0,
            nodes: HashMap::new(),
            stack: Vec::new(),
            on_stack: HashSet::new(),
            candidate_inventory: 0,
            vertex_visits: 0,
            edge_scans: 0,
        };
        if dependency != current && memo.pending_product_dependencies(dependency).is_none() {
            return (Vec::new(), 0, 0, 0);
        }
        let members = search
            .visit(memo, current, current_dependencies, dependency)
            .expect("the traversal root must complete its strong component");
        (
            members,
            search.candidate_inventory,
            search.vertex_visits,
            search.edge_scans,
        )
    }

    fn visit(
        &mut self,
        memo: &ProductMemo,
        current: &ProductKey,
        current_dependencies: &ProductDependencies,
        key: &ProductKey,
    ) -> Option<Vec<ProductKey>> {
        let index = self.next_index;
        self.next_index += 1;
        self.nodes.insert(key.clone(), PendingNode { index, lowlink: index });
        self.stack.push(key.clone());
        self.on_stack.insert(key.clone());
        self.vertex_visits += 1;

        let dependencies = if key == current {
            Some(current_dependencies)
        } else {
            memo.pending_product_dependencies(key)
        };
        if dependencies.is_some() && key.kind() == current.kind() {
            self.candidate_inventory += 1;
        }
        for dependency in dependencies
            .into_iter()
            .flat_map(|dependencies| dependencies.products.keys())
        {
            if dependency != current && memo.pending_product_dependencies(dependency).is_none() {
                continue;
            }
            self.edge_scans += 1;
            if !self.nodes.contains_key(dependency) {
                let _ = self.visit(memo, current, current_dependencies, dependency);
                let dependency_lowlink = self.nodes[dependency].lowlink;
                let node = self.nodes.get_mut(key).expect("visited product node");
                node.lowlink = node.lowlink.min(dependency_lowlink);
            } else if self.on_stack.contains(dependency) {
                let dependency_index = self.nodes[dependency].index;
                let node = self.nodes.get_mut(key).expect("visited product node");
                node.lowlink = node.lowlink.min(dependency_index);
            }
        }

        let node = self.nodes[key];
        if node.lowlink != node.index {
            return None;
        }

        let mut component = Vec::new();
        loop {
            let member = self
                .stack
                .pop()
                .expect("a strong-component root must remain on the stack");
            self.on_stack.remove(&member);
            let complete = member == *key;
            component.push(member);
            if complete {
                break;
            }
        }
        Some(component)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecursiveGroupSearch {
    pub candidate_inventory: u64,
    pub vertex_visits: u64,
    pub edge_scans: u64,
    pub cycle_closed: bool,
    pub group_members: u64,
}

#[derive(Debug, Clone, PartialEq)]
struct ProductEntry {
    value: ProductValue,
    generation: u64,
    dependencies: Rc<ProductDependencies>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ProductDependencies {
    products: HashMap<ProductKey, Option<u64>>,
    facts: HashMap<FactUse<FactKey>, FactState>,
}

impl ProductMemo {
    fn external_state(&self, key: &ProductKey) -> FactState {
        FactState {
            revision: self
                .produced
                .get(key)
                .or_else(|| self.displaced.get(key))
                .map(|entry| entry.generation),
            settled: self.produced.contains_key(key)
                && !self.fact_stale_dependencies.contains_key(key)
                && !self.dirty_descendants.contains(key),
        }
    }

    fn record_external_change(&mut self, key: &ProductKey, before: FactState) {
        if self.observed_products.contains(key) {
            let after = self.external_state(key);
            if before != after {
                self.external_changes.push(FactChange {
                    key: key.clone(),
                    old_revision: before.revision,
                    new_revision: after.revision,
                    old_settled: before.settled,
                    new_settled: after.settled,
                });
            }
        }
    }
    pub fn get(&self, key: &ProductKey) -> Option<&ProductValue> {
        self.produced.get(key).map(|entry| &entry.value)
    }

    pub fn generation(&self, key: &ProductKey) -> Option<u64> {
        self.produced.get(key).map(|entry| entry.generation)
    }

    #[cfg(test)]
    pub fn materialized_executables(&self) -> impl Iterator<Item = (&ExecutableKey, &Rc<MaterializedExecutable>)> {
        self.produced
            .iter()
            .filter_map(|(key, entry)| match (key, &entry.value) {
                (
                    ProductKey::MaterializedExecutable(executable),
                    ProductValue::MaterializedExecutable(materialized),
                ) => Some((executable, materialized)),
                _ => None,
            })
    }

    #[cfg(test)]
    pub fn materialized_executable(&self, executable: &ExecutableKey) -> Option<&Rc<MaterializedExecutable>> {
        match self.get(&ProductKey::MaterializedExecutable(executable.clone())) {
            Some(ProductValue::MaterializedExecutable(materialized)) => Some(materialized),
            _ => None,
        }
    }

    #[cfg(test)]
    pub fn abi_executables(&self) -> impl Iterator<Item = (&ExecutableKey, &Rc<AbiReadyExecutable>)> {
        self.produced
            .iter()
            .filter_map(|(key, entry)| match (key, &entry.value) {
                (ProductKey::AbiExecutable(executable), ProductValue::AbiExecutable(abi)) => Some((executable, abi)),
                _ => None,
            })
    }

    #[cfg(test)]
    pub fn abi_executable(&self, executable: &ExecutableKey) -> Option<&Rc<AbiReadyExecutable>> {
        match self.get(&ProductKey::AbiExecutable(executable.clone())) {
            Some(ProductValue::AbiExecutable(abi)) => Some(abi),
            _ => None,
        }
    }

    #[cfg(test)]
    pub fn backend_executables(&self) -> impl Iterator<Item = (&ExecutableKey, &Rc<BackendExecutable>)> {
        self.produced
            .iter()
            .filter_map(|(key, entry)| match (key, &entry.value) {
                (ProductKey::BackendExecutable(executable), ProductValue::BackendExecutable(backend)) => {
                    Some((executable, backend))
                }
                _ => None,
            })
    }

    #[cfg(test)]
    pub(crate) fn product_dependencies(&self, key: &ProductKey) -> Option<&HashMap<ProductKey, Option<u64>>> {
        self.produced.get(key).map(|entry| &entry.dependencies.products)
    }

    #[cfg(test)]
    pub(crate) fn fact_dependencies(&self, key: &ProductKey) -> Option<&HashMap<FactUse<FactKey>, FactState>> {
        self.produced.get(key).map(|entry| &entry.dependencies.facts)
    }

    #[cfg(test)]
    pub(crate) fn produced_keys(&self) -> impl Iterator<Item = &ProductKey> {
        self.produced.keys()
    }

    /// Has `key` settled -- does reading it answer now, with a value it already
    /// holds? A displaced product has not: it is waiting to be produced again.
    #[cfg(test)]
    pub(crate) fn is_settled(&self, key: &ProductKey) -> bool {
        self.produced.contains_key(key)
    }

    /// Every `reader -> dependency` edge the memo holds, over the produced,
    /// displaced and in-flight products alike.
    #[cfg(test)]
    pub(crate) fn dependency_edges(&self) -> impl Iterator<Item = (&ProductKey, &ProductKey)> {
        self.pending_dependencies
            .iter()
            .chain(
                self.produced
                    .iter()
                    .chain(self.displaced.iter())
                    .map(|(key, entry)| (key, entry.dependencies.as_ref())),
            )
            .flat_map(|(key, dependencies)| dependencies.products.keys().map(move |dependency| (key, dependency)))
    }

    pub fn contains_in_progress(&self, key: &ProductKey) -> bool {
        self.in_progress.contains(key)
    }

    /// The products that are mutually reachable with `current`: the recursive
    /// group that has to settle as one because no member can be believed
    /// before the others are.
    ///
    /// Only unsettled products are candidates: a settled product is already
    /// believed, so it is not waiting on this group and does not belong to it.
    fn pending_strong_component(
        &self,
        current: &ProductKey,
        current_dependencies: &ProductDependencies,
        dependency: &ProductKey,
        types: &super::types::Types,
    ) -> (Option<Vec<ProductKey>>, RecursiveGroupSearch) {
        let (component, candidate_inventory, vertex_visits, edge_scans) =
            PendingStrongComponent::find(self, current, current_dependencies, dependency);
        let cycle_closed = component.iter().any(|member| member == current);
        let members = cycle_closed.then(|| {
            let mut members = component
                .into_iter()
                .filter(|member| member.kind() == current.kind())
                .collect::<Vec<_>>();
            sort_product_keys(&mut members, types);
            members
        });
        let search = RecursiveGroupSearch {
            candidate_inventory,
            vertex_visits,
            edge_scans,
            cycle_closed,
            group_members: members.as_ref().map_or(0, |members| members.len() as u64),
        };
        (members, search)
    }

    /// The freshly evaluated dependencies of a formula that completed with
    /// unresolved waits. Settled and displaced entries are deliberately absent:
    /// neither is current evidence that a formula is waiting on a cycle.
    fn pending_product_dependencies(&self, key: &ProductKey) -> Option<&ProductDependencies> {
        self.pending_dependencies.get(key)
    }

    fn begin(&mut self, key: ProductKey) -> bool {
        self.in_progress.insert(key)
    }

    fn finish_completion(
        &mut self,
        tel: &impl Telemetry,
        emit_causal: bool,
        requested: &ProductKey,
        mut completion: ProductCompletion,
        types: &super::types::Types,
    ) -> bool {
        let members = match &mut completion {
            ProductCompletion::Batch(members) | ProductCompletion::RecursiveGroup(members) => members,
        };
        members.sort_by(|(left, _, _), (right, _, _)| left.semantic_cmp(right, types));
        assert!(
            members.iter().any(|(key, _, _)| key == requested),
            "a product completion must commit its requested anchor"
        );
        for pair in members.windows(2) {
            assert_ne!(pair[0].0, pair[1].0, "one completion published a product twice");
            debug_assert_ne!(
                pair[0].0.semantic_cmp(&pair[1].0, types),
                std::cmp::Ordering::Equal,
                "distinct product keys share one semantic order identity: {:?} vs {:?}",
                pair[0].0,
                pair[1].0
            );
        }
        match completion {
            ProductCompletion::Batch(members) => {
                if members
                    .iter()
                    .any(|(key, _, _)| self.invalidated_in_progress.contains(key))
                {
                    for (key, _, _) in &members {
                        self.in_progress.remove(key);
                        self.invalidated_in_progress.remove(key);
                    }
                    self.produced.remove(requested);
                    return false;
                }
                self.commit_members(tel, emit_causal, requested, members, None, None, types);
            }
            ProductCompletion::RecursiveGroup(members) => {
                let member_keys = members.iter().map(|(key, _, _)| key.clone()).collect::<HashSet<_>>();
                if member_keys.iter().any(|key| self.invalidated_in_progress.contains(key)) {
                    self.reject_group(tel, &member_keys, types);
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
                            self.reject_group(tel, &member_keys, types);
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
                            self.reject_group(tel, &member_keys, types);
                            return false;
                        }
                        group_dependencies.facts.insert(fact.clone(), *state);
                    }
                }
                self.next_group_id += 1;
                let group_id = self.next_group_id;
                self.commit_members(
                    tel,
                    emit_causal,
                    requested,
                    members,
                    Some(Rc::new(group_dependencies)),
                    Some(group_id),
                    types,
                );
            }
        }
        true
    }

    fn commit_members(
        &mut self,
        tel: &impl Telemetry,
        emit_causal: bool,
        requested: &ProductKey,
        members: Vec<(ProductKey, ProductValue, ProductDependencies)>,
        shared_dependencies: Option<Rc<ProductDependencies>>,
        group: Option<u64>,
        types: &super::types::Types,
    ) {
        let mut prepared = Vec::with_capacity(members.len());
        let mut external_before = Vec::new();
        for (key, mut value, dependencies) in members {
            if self.observed_products.contains(&key) {
                external_before.push((key.clone(), self.external_state(&key)));
            }
            self.in_progress.remove(&key);
            let previous = self.produced.remove(&key).or_else(|| self.displaced.remove(&key));
            if let (
                Some(ProductEntry {
                    value: ProductValue::RootBackendProduct(previous),
                    ..
                }),
                ProductValue::RootBackendProduct(answer),
            ) = (&previous, &mut value)
                && !Rc::ptr_eq(&previous.program, &answer.program)
                && previous.program == answer.program
            {
                answer.program = Rc::clone(&previous.program);
            }
            self.remove_reader_dependencies(&key, previous.as_ref().map(|entry| entry.dependencies.as_ref()));
            self.take_pending_dependencies(&key);
            let changed = previous
                .as_ref()
                .is_none_or(|entry| !same_product_value(&entry.value, &value));
            let value = if changed {
                value
            } else {
                previous
                    .as_ref()
                    .expect("an unchanged product has a previous memo entry")
                    .value
                    .clone()
            };
            let generation = previous.as_ref().map_or(1, |entry| {
                if changed {
                    entry.generation + 1
                } else {
                    entry.generation
                }
            });
            let dependencies = shared_dependencies
                .as_ref()
                .map_or_else(|| Rc::new(dependencies), Rc::clone);
            prepared.push((key, value, dependencies, generation, changed));
        }

        for (key, value, dependencies, generation, changed) in &prepared {
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
            tel.raw_event3(
                &["fz", "compiler2", "pull", "product", "settled"],
                key,
                value,
                &ProductSettlement {
                    generation: *generation,
                    changed: *changed,
                    group,
                },
            );
            if emit_causal && group.is_some() {
                tel.raw_event2(RECURSIVE_GROUP_PUBLISHED_EVENT, requested, key);
            } else if emit_causal && key != requested {
                tel.raw_event2(PRODUCT_COPUBLISHED_EVENT, requested, key);
            }
        }
        for (key, before) in external_before {
            self.record_external_change(&key, before);
        }
        let mutations = prepared.iter().flat_map(|(key, _, _, _, changed)| {
            self.reader_mutations(
                key,
                if *changed {
                    ReaderMutation::Invalidate
                } else {
                    ReaderMutation::Refresh
                },
            )
        });
        self.mutate_product_wave(tel, mutations.collect(), types);
    }

    fn reject_group(&mut self, tel: &impl Telemetry, member_keys: &HashSet<ProductKey>, types: &super::types::Types) {
        let mut member_keys = member_keys.iter().cloned().collect::<Vec<_>>();
        sort_product_keys(&mut member_keys, types);
        let mut mutations = Vec::new();
        for key in &member_keys {
            self.in_progress.remove(key);
            self.invalidated_in_progress.remove(key);
            self.take_pending_dependencies(key);
            if let Some(entry) = self.produced.remove(key) {
                self.remove_reader_dependencies(key, Some(&entry.dependencies));
                self.displaced.insert(key.clone(), entry);
                mutations.extend(self.reader_mutations(key, ReaderMutation::Dirty));
                tel.raw_event1(&["fz", "compiler2", "pull", "product", "displaced"], key);
            }
            if let Some(entry) = self.displaced.get_mut(key) {
                entry.dependencies = Rc::new(ProductDependencies::default());
            }
        }
        self.mutate_product_wave(tel, mutations, types);
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

    fn abort(&mut self, key: &ProductKey) {
        self.in_progress.remove(key);
        self.invalidated_in_progress.remove(key);
        self.take_pending_dependencies(key);
    }

    #[cfg(test)]
    fn remove(&mut self, tel: &impl Telemetry, key: &ProductKey, types: &super::types::Types) {
        self.invalidate_products(tel, [key.clone()], types);
    }

    fn invalidate_products(
        &mut self,
        tel: &impl Telemetry,
        keys: impl IntoIterator<Item = ProductKey>,
        types: &super::types::Types,
    ) {
        self.mutate_product_wave(
            tel,
            keys.into_iter().map(|key| (ReaderMutation::Invalidate, key)).collect(),
            types,
        );
    }

    fn displace_for_reproduction_shallow(&mut self, tel: &impl Telemetry, key: &ProductKey) -> (bool, bool) {
        if self.in_progress.contains(key) {
            self.invalidated_in_progress.insert(key.clone());
        }
        let pending = self.take_pending_dependencies(key).is_some();
        let mut produced = false;
        if let Some(entry) = self.produced.remove(key) {
            produced = true;
            self.remove_reader_dependencies(key, Some(&entry.dependencies));
            self.displaced.insert(key.clone(), entry);
            tel.raw_event1(&["fz", "compiler2", "pull", "product", "displaced"], key);
        }
        (pending, produced)
    }

    fn prepare_stale_for_reproduction(&mut self, tel: &impl Telemetry, key: &ProductKey, types: &super::types::Types) {
        self.fact_stale_dependencies.remove(key);
        self.invalidate_products(tel, [key.clone()], types);
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
            let fact = fact.fact().clone();
            let readers = self.fact_readers.entry(fact.clone()).or_default();
            let was_empty = readers.is_empty();
            readers.insert(reader.clone());
            if was_empty {
                self.fact_subscription_changes.push((fact, true));
            }
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
                let fact = fact.fact().clone();
                self.fact_readers.remove(&fact);
                self.fact_subscription_changes.push((fact, false));
            }
        }
    }

    fn take_fact_subscription_changes(&mut self) -> Vec<(FactKey, bool)> {
        std::mem::take(&mut self.fact_subscription_changes)
    }

    fn take_pending_dependencies(&mut self, reader: &ProductKey) -> Option<ProductDependencies> {
        let pending = self.pending_dependencies.remove(reader);
        self.remove_reader_dependencies(reader, pending.as_ref());
        pending
    }

    fn reader_mutations(
        &self,
        key: &ProductKey,
        mutation: ReaderMutation,
    ) -> impl Iterator<Item = (ReaderMutation, ProductKey)> + '_ {
        self.product_readers
            .get(key)
            .into_iter()
            .flatten()
            .cloned()
            .map(move |reader| (mutation, reader))
    }

    fn mutate_product_wave(
        &mut self,
        tel: &impl Telemetry,
        mut pending: Vec<(ReaderMutation, ProductKey)>,
        types: &super::types::Types,
    ) {
        let mut seen = HashSet::new();
        while !pending.is_empty() {
            let next = pending
                .iter()
                .enumerate()
                .min_by(|(_, (left_mutation, left)), (_, (right_mutation, right))| {
                    left.semantic_cmp(right, types)
                        .then_with(|| left_mutation.rank().cmp(&right_mutation.rank()))
                })
                .map(|(index, _)| index)
                .expect("non-empty reader mutation worklist");
            let (mutation, reader) = pending.swap_remove(next);
            if !seen.insert((mutation, reader.clone())) {
                continue;
            }
            let external_before = self
                .observed_products
                .contains(&reader)
                .then(|| (reader.clone(), self.external_state(&reader)));
            match mutation {
                ReaderMutation::Invalidate => {
                    let (was_pending, was_produced) = self.displace_for_reproduction_shallow(tel, &reader);
                    let next = if was_pending {
                        Some(ReaderMutation::Invalidate)
                    } else if was_produced {
                        Some(ReaderMutation::Dirty)
                    } else {
                        None
                    };
                    if let Some(next) = next {
                        pending.extend(
                            self.product_readers
                                .get(&reader)
                                .into_iter()
                                .flatten()
                                .cloned()
                                .map(|reader| (next, reader)),
                        );
                    }
                }
                ReaderMutation::Dirty => {
                    if self.pending_dependencies.contains_key(&reader) {
                        pending.push((ReaderMutation::Invalidate, reader));
                        continue;
                    }
                    if self.dirty_descendants.insert(reader.clone()) {
                        pending.extend(
                            self.product_readers
                                .get(&reader)
                                .into_iter()
                                .flatten()
                                .cloned()
                                .map(|reader| (ReaderMutation::Dirty, reader)),
                        );
                    }
                }
                ReaderMutation::Refresh => {
                    let dirty = self.produced.get(&reader).is_some_and(|entry| {
                        entry.dependencies.products.keys().any(|dependency| {
                            self.displaced.contains_key(dependency)
                                || self.fact_stale_dependencies.contains_key(dependency)
                                || self.dirty_descendants.contains(dependency)
                        })
                    });
                    if dirty {
                        self.dirty_descendants.insert(reader);
                    } else if self.dirty_descendants.remove(&reader) {
                        pending.extend(
                            self.product_readers
                                .get(&reader)
                                .into_iter()
                                .flatten()
                                .cloned()
                                .map(|reader| (ReaderMutation::Refresh, reader)),
                        );
                    }
                }
            }
            if let Some((observed, before)) = external_before {
                self.record_external_change(&observed, before);
            }
        }
    }

    fn reconcile_fact_movements(
        &mut self,
        tel: &impl Telemetry,
        pending: &HashMap<FactKey, FactState>,
        types: &super::types::Types,
    ) {
        let mut facts = pending.iter().collect::<Vec<_>>();
        facts.sort_by(|(left, _), (right, _)| left.semantic_cmp(right, types));
        let mut prior_stale = HashMap::<ProductKey, bool>::new();
        let mut external_before = HashMap::new();
        let mut mutations = Vec::new();
        for (fact_key, final_state) in facts {
            let readers = self.fact_readers.get(fact_key).cloned().unwrap_or_default();
            for reader in readers {
                if self.observed_products.contains(&reader) {
                    external_before
                        .entry(reader.clone())
                        .or_insert_with(|| self.external_state(&reader));
                }
                let pending_stale = self.pending_dependencies.get(&reader).is_some_and(|dependencies| {
                    dependencies
                        .facts
                        .iter()
                        .any(|(fact, recorded)| fact.fact() == fact_key && final_state.projected(fact) != *recorded)
                });
                if pending_stale {
                    mutations.push((ReaderMutation::Invalidate, reader));
                    continue;
                }
                let stale = self.produced.get(&reader).is_some_and(|entry| {
                    entry
                        .dependencies
                        .facts
                        .iter()
                        .any(|(fact, recorded)| fact.fact() == fact_key && final_state.projected(fact) != *recorded)
                });
                prior_stale
                    .entry(reader.clone())
                    .or_insert_with(|| self.fact_stale_dependencies.contains_key(&reader));
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
            }
        }
        mutations.extend(prior_stale.into_iter().filter_map(|(reader, was_stale)| {
            let is_stale = self.fact_stale_dependencies.contains_key(&reader);
            match (was_stale, is_stale) {
                (false, true) => Some((ReaderMutation::Dirty, reader)),
                (true, false) => Some((ReaderMutation::Refresh, reader)),
                _ => None,
            }
        }));
        self.mutate_product_wave(tel, mutations, types);
        for (key, before) in external_before {
            self.record_external_change(&key, before);
        }
    }

    fn stale_dependency(&self, key: &ProductKey, types: &super::types::Types) -> Option<ProductKey> {
        self.stale_dependency_inner(key, &mut HashSet::new(), types)
    }

    fn stale_dependency_inner(
        &self,
        key: &ProductKey,
        visiting: &mut HashSet<ProductKey>,
        types: &super::types::Types,
    ) -> Option<ProductKey> {
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
        let mut dependencies = entry.dependencies.products.iter().collect::<Vec<_>>();
        dependencies.sort_by(|(left, _), (right, _)| left.semantic_cmp(right, types));
        for (dependency, generation) in dependencies {
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
                && let Some(stale) = self.stale_dependency_inner(dependency, visiting, types)
            {
                visiting.remove(key);
                return Some(stale);
            }
        }
        visiting.remove(key);
        None
    }
}

#[derive(Debug)]
pub struct PullSession {
    id: Option<PullSessionId>,
    request_ids: ProductRequestIds,
    root: RootId,
    memo: ProductMemo,
    demanded_executables: HashSet<ExecutableKey>,
    // Request-local counters reset whenever this retained session is
    // reactivated. The memo and dependency indexes above remain durable.
    producer_pokes: u64,
    work_starts: WorkStartTally,
    pending_fact_states: HashMap<FactKey, FactState>,
}

impl PullSession {
    pub fn new(root: RootId) -> Self {
        Self {
            id: None,
            request_ids: ProductRequestIds::new(),
            root,
            memo: ProductMemo::default(),
            demanded_executables: HashSet::new(),
            producer_pokes: 0,
            work_starts: WorkStartTally::default(),
            pending_fact_states: HashMap::new(),
        }
    }

    pub fn root(&self) -> RootId {
        self.root
    }

    pub fn id(&self) -> Option<PullSessionId> {
        self.id
    }

    pub fn memo(&self) -> &ProductMemo {
        &self.memo
    }

    #[cfg(test)]
    pub fn demanded_executables(&self) -> &HashSet<ExecutableKey> {
        &self.demanded_executables
    }

    pub fn producer_pokes(&self) -> u64 {
        self.producer_pokes
    }

    /// This activation's work-start attribution (per-reason agenda-entry
    /// counts plus whole-fact-table scans and global drain-discovery sweeps).
    pub fn work_starts(&self) -> WorkStartTally {
        self.work_starts
    }

    fn begin_activation(&mut self) {
        self.producer_pokes = 0;
        self.work_starts = WorkStartTally::default();
    }

    fn finish_activation(&mut self, tally: WorkStartTally) {
        self.work_starts = tally;
    }

    pub fn record_producer_pokes(&mut self, count: u64) {
        self.producer_pokes += count;
    }

    fn apply_fact_movements(&mut self, movements: &[FactMovement<FactKey>]) {
        for movement in movements {
            self.pending_fact_states.insert(movement.key.clone(), movement.state);
        }
    }

    fn reconcile_fact_movements(&mut self, tel: &impl Telemetry, types: &super::types::Types) {
        let pending = std::mem::take(&mut self.pending_fact_states);
        self.memo.reconcile_fact_movements(tel, &pending, types);
    }

    fn note_product_request(&mut self, key: &ProductKey) {
        if let Some(executable) = key.executable() {
            self.demanded_executables.insert(executable.clone());
        }
    }

    fn emit_finished(&self, tel: &impl Telemetry) {
        tel.raw_event1(&["fz", "compiler2", "pull", "session", "finished"], self);
    }
}

/// Compiler-owned retained product sessions and their exact fact-movement
/// routing index. `World` owns facts; this store owns every root's product
/// spreadsheet and only the reverse routing needed to deliver a moved fact to
/// sessions that currently read it.
#[derive(Debug, Default)]
pub(crate) struct ProductSessions {
    sessions: HashMap<RootId, Rc<RefCell<PullSession>>>,
    subscriptions_by_root: HashMap<RootId, HashSet<FactKey>>,
    roots_by_fact: HashMap<FactKey, HashSet<RootId>>,
    active_roots: HashMap<RootId, ActiveRootProduct>,
    work_start_cursor: WorkStartTally,
    active_work_starts: Vec<WorkStartOwner>,
    pending_requests: super::agenda::Agenda<ProductAddress>,
    requested: HashSet<ProductAddress>,
}

#[derive(Debug, Default)]
struct ActiveRootProduct {
    movements: HashMap<FactKey, FactState>,
    parked_requests: Vec<ProductAddress>,
}

#[derive(Debug)]
enum WorkStartOwner {
    StandaloneDrive,
    Root(RootId, WorkStartTally),
}

impl ProductSessions {
    pub(crate) fn observe(&mut self, address: &ProductAddress) {
        self.sessions
            .entry(address.root)
            .or_insert_with(|| Rc::new(RefCell::new(PullSession::new(address.root))))
            .borrow_mut()
            .memo
            .observed_products
            .insert(address.key.clone());
        if !self
            .get(address.root)
            .expect("observed root exists")
            .memo
            .external_state(&address.key)
            .settled
        {
            self.request(address.clone());
        }
    }

    pub(crate) fn unobserve(&mut self, address: &ProductAddress) {
        if let Some(session) = self.sessions.get(&address.root) {
            session.borrow_mut().memo.observed_products.remove(&address.key);
        }
        self.requested.remove(address);
    }

    fn request(&mut self, address: ProductAddress) {
        if self.requested.insert(address.clone()) {
            self.pending_requests.enqueue(address);
        }
    }

    pub(crate) fn next_request(&mut self) -> Option<ProductAddress> {
        while let Some(address) = self.pending_requests.pop() {
            if !self.requested.contains(&address) {
                continue;
            }
            if let Some(active) = self.active_roots.get_mut(&address.root) {
                active.parked_requests.push(address);
            } else {
                self.observe(&address);
                return Some(address);
            }
        }
        None
    }

    pub(crate) fn retry_request(&mut self, address: ProductAddress) {
        self.pending_requests.enqueue(address);
    }

    pub(crate) fn product(&self, address: &ProductAddress) -> Option<ProductValue> {
        let session = self.get(address.root)?;
        session
            .memo
            .external_state(&address.key)
            .settled
            .then(|| session.memo.get(&address.key).cloned())
            .flatten()
    }

    pub(crate) fn take_product_changes(
        &mut self,
        root: RootId,
        types: &super::types::Types,
    ) -> Vec<FactChange<DependencyKey>> {
        let Some(session) = self.sessions.get(&root) else {
            return Vec::new();
        };
        let changes = std::mem::take(&mut session.borrow_mut().memo.external_changes);
        let mut coalesced = HashMap::<ProductKey, FactChange<ProductKey>>::new();
        for change in changes {
            coalesced
                .entry(change.key.clone())
                .and_modify(|prior| {
                    prior.new_revision = change.new_revision;
                    prior.new_settled = change.new_settled;
                })
                .or_insert(change);
        }
        let mut changes = coalesced
            .into_values()
            .filter(|change| change.content_changed() || change.readiness_changed())
            .map(|change| FactChange {
                key: DependencyKey::Product(ProductAddress { root, key: change.key }),
                old_revision: change.old_revision,
                new_revision: change.new_revision,
                old_settled: change.old_settled,
                new_settled: change.new_settled,
            })
            .collect::<Vec<_>>();
        changes.sort_by(|left, right| left.key.semantic_cmp(&right.key, types));
        for change in &changes {
            let DependencyKey::Product(address) = &change.key else {
                unreachable!()
            };
            if change.new_settled {
                self.requested.remove(address);
            } else {
                self.request(address.clone());
            }
        }
        changes
    }
    pub(crate) fn begin_standalone_drive(&mut self, work_starts: WorkStartTally) {
        assert!(
            self.active_work_starts.is_empty() && self.active_roots.is_empty(),
            "a standalone drive cannot begin inside a root product activation"
        );
        let _ = self.take_work_start_delta(work_starts);
        self.active_work_starts.push(WorkStartOwner::StandaloneDrive);
    }

    pub(crate) fn finish_standalone_drive(&mut self, work_starts: WorkStartTally) {
        let _ = self.take_work_start_delta(work_starts);
        match self.active_work_starts.pop() {
            Some(WorkStartOwner::StandaloneDrive) => {}
            Some(WorkStartOwner::Root(..)) => panic!("a root product activation outlived its standalone drive"),
            None => panic!("finishing a standalone drive that never began"),
        }
        assert!(
            self.active_roots.is_empty(),
            "a root product activation outlived its standalone drive"
        );
    }

    pub(crate) fn take(&mut self, root: RootId, work_starts: WorkStartTally) -> (Rc<RefCell<PullSession>>, bool) {
        assert!(
            self.active_roots.insert(root, ActiveRootProduct::default()).is_none(),
            "one root product session cannot be driven recursively"
        );
        let delta = self.take_work_start_delta(work_starts);
        let initial = match self.active_work_starts.last_mut() {
            Some(WorkStartOwner::StandaloneDrive) => WorkStartTally::default(),
            Some(WorkStartOwner::Root(_, outer)) => {
                outer.add(delta);
                WorkStartTally::default()
            }
            None => delta,
        };
        self.active_work_starts.push(WorkStartOwner::Root(root, initial));
        let retained = self.sessions.contains_key(&root);
        let session = Rc::clone(
            self.sessions
                .entry(root)
                .or_insert_with(|| Rc::new(RefCell::new(PullSession::new(root)))),
        );
        session.borrow_mut().begin_activation();
        (session, retained)
    }

    pub(crate) fn finish_activation(&mut self, root: RootId, session: &mut PullSession, work_starts: WorkStartTally) {
        let delta = self.take_work_start_delta(work_starts);
        let (active_root, mut tally) = match self.active_work_starts.pop() {
            Some(WorkStartOwner::Root(active_root, tally)) => (active_root, tally),
            Some(WorkStartOwner::StandaloneDrive) => {
                panic!("finishing a root without an active root work tally")
            }
            None => panic!("finishing a root without an active work tally"),
        };
        assert_eq!(active_root, root, "root product activations must finish in stack order");
        tally.add(delta);
        session.finish_activation(tally);
    }

    fn take_work_start_delta(&mut self, current: WorkStartTally) -> WorkStartTally {
        let delta = current.delta_since(self.work_start_cursor);
        self.work_start_cursor = current;
        delta
    }

    pub(crate) fn sync_subscriptions(&mut self, root: RootId, session: &mut PullSession) {
        for (fact, subscribe) in session.memo.take_fact_subscription_changes() {
            if subscribe {
                let inserted = self.subscriptions_by_root.entry(root).or_default().insert(fact.clone());
                if inserted {
                    self.roots_by_fact.entry(fact).or_default().insert(root);
                }
            } else {
                let removed = self
                    .subscriptions_by_root
                    .get_mut(&root)
                    .is_some_and(|facts| facts.remove(&fact));
                if removed {
                    let remove_fact = self.roots_by_fact.get_mut(&fact).is_some_and(|roots| {
                        roots.remove(&root);
                        roots.is_empty()
                    });
                    if remove_fact {
                        self.roots_by_fact.remove(&fact);
                    }
                }
                if self.subscriptions_by_root.get(&root).is_some_and(HashSet::is_empty) {
                    self.subscriptions_by_root.remove(&root);
                }
            }
        }
    }

    pub(crate) fn publish(
        &mut self,
        tel: &impl Telemetry,
        types: &super::types::Types,
        movements: &[FactMovement<FactKey>],
    ) -> Vec<FactChange<DependencyKey>> {
        let Self {
            sessions,
            roots_by_fact,
            active_roots,
            ..
        } = self;
        let mut observed_roots = HashSet::new();
        for movement in movements {
            for root in roots_by_fact.get(&movement.key).into_iter().flatten() {
                let session = sessions.get(root).expect("subscribed root retains its session");
                if !session.borrow().memo.observed_products.is_empty() {
                    session
                        .borrow_mut()
                        .apply_fact_movements(std::slice::from_ref(movement));
                    observed_roots.insert(*root);
                } else if let Some(active) = active_roots.get_mut(root) {
                    active.movements.insert(movement.key.clone(), movement.state);
                } else {
                    session
                        .borrow_mut()
                        .apply_fact_movements(std::slice::from_ref(movement));
                }
            }
        }
        let mut changes = Vec::new();
        let mut observed_roots = observed_roots.into_iter().collect::<Vec<_>>();
        observed_roots.sort_unstable();
        for root in observed_roots {
            self.sessions[&root].borrow_mut().reconcile_fact_movements(tel, types);
            changes.extend(self.take_product_changes(root, types));
        }
        changes
    }

    pub(crate) fn drain_active_movements(&mut self, root: RootId, session: &mut PullSession) {
        let pending = self
            .active_roots
            .get_mut(&root)
            .map(|active| &mut active.movements)
            .expect("draining a root that is not active");
        if !pending.is_empty() {
            session.pending_fact_states.extend(std::mem::take(pending));
        }
    }

    pub(crate) fn restore(&mut self, session: Rc<RefCell<PullSession>>) {
        let root = session.borrow().root();
        self.drain_active_movements(root, &mut session.borrow_mut());
        self.sync_subscriptions(root, &mut session.borrow_mut());
        let active = self
            .active_roots
            .remove(&root)
            .expect("restoring a root that is not active");
        for address in active.parked_requests {
            self.pending_requests.enqueue(address);
        }
        assert!(Rc::ptr_eq(
            self.sessions.get(&root).expect("active root retains its session"),
            &session
        ));
    }

    pub(crate) fn get(&self, root: RootId) -> Option<Ref<'_, PullSession>> {
        self.sessions.get(&root).map(|session| session.borrow())
    }

    pub(crate) fn retire(&mut self, root: RootId, types: &super::types::Types) -> bool {
        assert!(
            !self.active_roots.contains_key(&root),
            "cannot retire an active root session"
        );
        let Some(session) = self.sessions.remove(&root) else {
            return false;
        };
        let mut observed = session
            .borrow()
            .memo
            .observed_products
            .iter()
            .cloned()
            .collect::<Vec<_>>();
        observed.sort_by(|left, right| left.semantic_cmp(right, types));
        for key in observed {
            self.request(ProductAddress { root, key });
        }
        for fact in self.subscriptions_by_root.remove(&root).unwrap_or_default() {
            let remove_fact = self.roots_by_fact.get_mut(&fact).is_some_and(|roots| {
                roots.remove(&root);
                roots.is_empty()
            });
            if remove_fact {
                self.roots_by_fact.remove(&fact);
            }
        }
        true
    }

    pub(crate) fn retirement_changes(&self, root: RootId) -> Vec<FactChange<DependencyKey>> {
        let Some(session) = self.get(root) else {
            return Vec::new();
        };
        session
            .memo
            .observed_products
            .iter()
            .map(|key| {
                let before = session.memo.external_state(key);
                FactChange {
                    key: DependencyKey::Product(ProductAddress { root, key: key.clone() }),
                    old_revision: before.revision,
                    new_revision: None,
                    old_settled: before.settled,
                    new_settled: false,
                }
            })
            .collect()
    }

    #[cfg(test)]
    pub(crate) fn counts(&self) -> (usize, usize) {
        (
            self.sessions.len(),
            self.subscriptions_by_root.values().map(HashSet::len).sum(),
        )
    }
}

impl super::scheduler::ExternalDependencyStates<DependencyKey> for ProductSessions {
    fn has_unsettled_dependencies(&self) -> bool {
        !self.requested.is_empty()
    }
    fn external_state(&self, key: &DependencyKey) -> Option<FactState> {
        match key {
            DependencyKey::Fact(_) => None,
            DependencyKey::Product(address) => Some(self.get(address.root).map_or(
                FactState {
                    revision: None,
                    settled: false,
                },
                |session| session.memo.external_state(&address.key),
            )),
        }
    }
}

pub struct ProductReadContext<'s> {
    session: &'s mut PullSession,
    dependencies: ProductDependencies,
    staged: Vec<ProductCommitMember>,
    recursive_group: Option<Vec<ProductCommitMember>>,
}

pub(crate) enum RecursiveProductRead<'a> {
    Ready(&'a ProductValue),
    Waiting,
    Group(Vec<ProductKey>),
}

impl<'s> ProductReadContext<'s> {
    pub(crate) fn new(session: &'s mut PullSession) -> Self {
        Self {
            session,
            dependencies: ProductDependencies::default(),
            staged: Vec::new(),
            recursive_group: None,
        }
    }

    pub fn read_product(
        &mut self,
        tel: &impl Telemetry,
        key: ProductKey,
        types: &super::types::Types,
    ) -> Option<&ProductValue> {
        self.read_product_entry(tel, key, types)
    }

    /// Record the prospective read, then borrow the dependency graph for one
    /// traversal that decides whether it closes a recursive group. A pending
    /// formula snapshot is already the current evidence that the dependency is
    /// waiting; stale-read normalization applies only to ordinary settled or
    /// displaced reads outside the group.
    pub(crate) fn read_recursive_product(
        &mut self,
        tel: &impl Telemetry,
        dependency: ProductKey,
        current: &ProductKey,
        types: &super::types::Types,
    ) -> RecursiveProductRead<'_> {
        let generation = self.session.memo.generation(&dependency);
        self.dependencies.products.insert(dependency.clone(), generation);
        let (members, search) =
            self.session
                .memo
                .pending_strong_component(current, &self.dependencies, &dependency, types);
        if search.vertex_visits > 0 {
            tel.raw_event3(
                &["fz", "compiler2", "pull", "recursive_group", "searched"],
                current,
                &dependency,
                &search,
            );
        }
        if let Some(members) = members {
            return RecursiveProductRead::Group(members);
        }
        match self.read_product_entry(tel, dependency, types) {
            Some(value) => RecursiveProductRead::Ready(value),
            None => RecursiveProductRead::Waiting,
        }
    }

    pub(crate) fn recursive_group_callable_owners(
        &self,
        current: &ProductKey,
        members: &[ProductKey],
        types: &super::types::Types,
    ) -> Vec<Rc<CallableConstructionOwner>> {
        let member_set = members.iter().collect::<HashSet<_>>();
        let mut dependencies = self
            .recorded_recursive_group_dependencies(current, members)
            .into_iter()
            .flat_map(|dependencies| dependencies.products.keys())
            .filter(|dependency| !member_set.contains(dependency))
            .cloned()
            .collect::<Vec<_>>();
        dependencies.sort_by(|left, right| left.semantic_cmp(right, types));
        dependencies.dedup();
        dependencies
            .iter()
            .filter_map(|dependency| match self.session.memo.get(dependency) {
                Some(ProductValue::CallableConstruction(owner)) => Some(Rc::clone(owner)),
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

    pub(crate) fn recorded_recursive_group_inputs(
        &self,
        current: &ProductKey,
        members: &[ProductKey],
        types: &super::types::Types,
    ) -> Vec<(ProductKey, Option<ProductValue>)> {
        let member_set = members.iter().collect::<HashSet<_>>();
        let mut inputs = self
            .recorded_recursive_group_dependencies(current, members)
            .into_iter()
            .flat_map(|dependencies| dependencies.products.keys())
            .filter(|dependency| !member_set.contains(dependency))
            .cloned()
            .collect::<Vec<_>>();
        sort_product_keys(&mut inputs, types);
        inputs.dedup();
        inputs
            .into_iter()
            .map(|key| {
                let value = self.session.memo.get(&key).cloned();
                (key, value)
            })
            .collect()
    }

    pub(crate) fn stage_recursive_group(
        &mut self,
        current: &ProductKey,
        members: &[ProductKey],
        values: Vec<ProductValue>,
    ) -> ProductValue {
        assert_eq!(members.len(), values.len());
        assert!(
            self.staged.is_empty(),
            "recursive completion cannot also stage ordinary peer products"
        );
        let current_value = members
            .iter()
            .zip(&values)
            .find_map(|(member, value)| (member == current).then(|| value.clone()))
            .expect("recursive completion must contain its requested anchor");
        let dependencies = self
            .recorded_recursive_group_dependencies(current, members)
            .into_iter()
            .cloned();
        let entries = members
            .iter()
            .cloned()
            .zip(values)
            .zip(dependencies)
            .map(|((key, value), dependencies)| (key, value, dependencies))
            .collect();
        assert!(
            self.recursive_group.replace(entries).is_none(),
            "one producer staged two recursive completions"
        );
        current_value
    }

    fn recorded_recursive_group_dependencies<'a>(
        &'a self,
        current: &ProductKey,
        members: &[ProductKey],
    ) -> Vec<&'a ProductDependencies> {
        assert!(
            members.contains(current),
            "a recursive group must contain its current member"
        );
        members
            .iter()
            .map(|member| {
                if member == current {
                    &self.dependencies
                } else {
                    self.session
                        .memo
                        .pending_product_dependencies(member)
                        .expect("a non-current recursive member must have a freshly evaluated pending formula")
                }
            })
            .collect()
    }

    fn read_product_entry(
        &mut self,
        tel: &impl Telemetry,
        key: ProductKey,
        types: &super::types::Types,
    ) -> Option<&ProductValue> {
        if let Some(stale) = self.session.memo.stale_dependency(&key, types) {
            self.session.memo.prepare_stale_for_reproduction(tel, &stale, types);
            let generation = self.session.memo.generation(&key);
            self.dependencies.products.insert(key.clone(), generation);
            return None;
        }
        let generation = self.session.memo.generation(&key);
        self.dependencies.products.insert(key.clone(), generation);
        self.session.memo.get(&key)
    }

    pub(crate) fn read_runtime_demand_fact(
        &mut self,
        world: &World,
        executable: &ExecutableKey,
    ) -> Option<Rc<ExecutableRuntimeDemand>> {
        let fact = FactUse::settled(FactKey::RuntimeDemand(executable.clone()));
        self.read_fact(world, fact).then(|| {
            Rc::clone(
                world
                    .runtime_demand(executable)
                    .expect("settled runtime demand should have a value"),
            )
        })
    }

    pub(crate) fn read_executable_facts(
        &mut self,
        world: &World,
        executable: &ExecutableKey,
    ) -> Option<Rc<ExecutableFacts>> {
        let fact = FactUse::settled(FactKey::ExecutableFacts(executable.clone()));
        self.read_fact(world, fact).then(|| {
            Rc::clone(
                world
                    .executable_facts(executable)
                    .expect("settled executable facts should have a value"),
            )
        })
    }

    pub fn read_fact(&mut self, world: &World, fact: FactUse<FactKey>) -> bool {
        let state = FactState {
            revision: world.fact_revision(fact.fact()),
            settled: world.fact_is_settled(fact.fact()),
        }
        .projected(&fact);
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

    pub fn session(&self) -> &PullSession {
        self.session
    }

    fn into_completion(
        self,
    ) -> (
        ProductDependencies,
        Vec<ProductCommitMember>,
        Option<Vec<ProductCommitMember>>,
    ) {
        (self.dependencies, self.staged, self.recursive_group)
    }
}

pub trait ProductProducers {
    fn product_types(&self) -> &super::types::Types;
    fn produce(&mut self, context: &mut ProductReadContext<'_>, key: &ProductKey) -> PullOutcome;
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
    fn product_types(&self) -> &super::types::Types {
        self.world.types()
    }

    fn produce(&mut self, context: &mut ProductReadContext<'_>, key: &ProductKey) -> PullOutcome {
        match key {
            ProductKey::RootBackendProduct(root) => {
                super::jobs::backend::produce_root_backend_product(self.world, self.telemetry, context, *root)
            }
            ProductKey::RootBackendContent(root) => {
                super::jobs::backend::produce_root_backend_content(self.telemetry, context, *root, self.world.types())
            }
            ProductKey::NativeProgram(root) => {
                super::jobs::produce_native_program(self.world, self.telemetry, context, *root)
            }
            ProductKey::BackendExecutable(executable) => super::jobs::backend::produce_backend_executable_product(
                self.world,
                self.telemetry,
                context,
                executable,
            ),
            ProductKey::AbiExecutable(executable) => {
                super::jobs::artifact::produce_abi_executable_product(self.world, self.telemetry, context, executable)
            }
            ProductKey::MaterializedExecutable(executable) => {
                super::jobs::artifact::produce_materialized_executable_product(
                    self.world,
                    self.telemetry,
                    context,
                    executable,
                )
            }
            ProductKey::ExecutableEffects(executable) => super::jobs::artifact::produce_executable_effects_product(
                self.telemetry,
                context,
                executable,
                self.world.types(),
            ),
            ProductKey::TransportShape(position) => {
                super::jobs::transport::produce_transport_shape_product(self.world, self.telemetry, context, position)
            }
            ProductKey::CallableConstruction(position) => {
                super::jobs::transport::produce_callable_construction_product(
                    self.world,
                    self.telemetry,
                    context,
                    position,
                )
            }
        }
    }
}

pub struct ProductDriver<'a, T: Telemetry> {
    tel: &'a T,
    session: Option<Rc<RefCell<PullSession>>>,
    emit_causal_products: bool,
    emit_session_lifecycle: bool,
    finished: Cell<bool>,
}

impl<'a, T: Telemetry> ProductDriver<'a, T> {
    #[cfg(test)]
    pub fn new(tel: &'a T, root: RootId) -> Self {
        Self::with_session(tel, PullSession::new(root))
    }

    #[cfg(test)]
    pub(crate) fn telemetry(&self) -> &'a T {
        self.tel
    }

    #[cfg(test)]
    pub fn with_session(tel: &'a T, session: PullSession) -> Self {
        Self::with_session_id_source(tel, session, || allocate_pull_session_id(&NEXT_PULL_SESSION_ID))
    }

    pub(crate) fn with_shared_session(tel: &'a T, session: Rc<RefCell<PullSession>>) -> Self {
        Self::with_shared_session_id_source(tel, session, || allocate_pull_session_id(&NEXT_PULL_SESSION_ID))
    }

    #[cfg(test)]
    fn with_session_id_source(
        tel: &'a T,
        session: PullSession,
        allocate_session_id: impl FnOnce() -> PullSessionId,
    ) -> Self {
        Self::with_shared_session_id_source(tel, Rc::new(RefCell::new(session)), allocate_session_id)
    }

    fn with_shared_session_id_source(
        tel: &'a T,
        shared: Rc<RefCell<PullSession>>,
        allocate_session_id: impl FnOnce() -> PullSessionId,
    ) -> Self {
        let mut session = shared.borrow_mut();
        let emit_session_lifecycle =
            tel.is_raw_event_enabled(SESSION_STARTED_EVENT) || tel.is_raw_event_enabled(SESSION_FINISHED_EVENT);
        if session.id.is_none() && emit_session_lifecycle {
            session.id = Some(allocate_session_id());
        }
        if emit_session_lifecycle {
            tel.raw_event1(
                SESSION_STARTED_EVENT,
                &session.id.expect("enabled session telemetry requires an identity"),
            );
        }
        drop(session);
        Self {
            tel,
            session: Some(shared),
            emit_causal_products: causal_product_events_enabled(tel),
            emit_session_lifecycle,
            finished: Cell::new(false),
        }
    }

    pub fn session(&self) -> Ref<'_, PullSession> {
        self.session
            .as_ref()
            .expect("product driver session already retained")
            .borrow()
    }

    pub fn session_mut(&mut self) -> RefMut<'_, PullSession> {
        self.session
            .as_ref()
            .expect("product driver session already retained")
            .borrow_mut()
    }

    pub(crate) fn into_session(mut self) -> Rc<RefCell<PullSession>> {
        self.emit_finished_once();
        self.session.take().expect("product driver session already retained")
    }

    #[cfg(test)]
    pub fn finish_session(&self) {
        self.emit_finished_once();
    }

    pub(crate) fn apply_fact_movements(&mut self, movements: &[FactMovement<FactKey>]) {
        self.session_mut().apply_fact_movements(movements);
    }

    pub fn pull(&mut self, producers: &mut impl ProductProducers, key: ProductKey) -> PullOutcome {
        let tel = self.tel;
        let emit_causal_products = self.emit_causal_products;
        assert!(
            !self.session().memo.contains_in_progress(&key),
            "safe product producers cannot recursively enter ProductDriver::pull"
        );
        let request = self.session_mut().request_ids.allocate();
        if self.emit_causal_products {
            tel.raw_event2(PRODUCT_REQUESTED_EVENT, &key, &request);
        }
        self.session_mut()
            .reconcile_fact_movements(tel, producers.product_types());
        self.session_mut().note_product_request(&key);
        let stale = self.session().memo.stale_dependency(&key, producers.product_types());
        if let Some(stale) = stale {
            self.session_mut()
                .memo
                .prepare_stale_for_reproduction(tel, &stale, producers.product_types());
            if stale != key {
                return PullOutcome::wait_on_product(stale);
            }
        }
        if let Some(value) = self.session().memo.get(&key) {
            self.emit("cache_hit", &key);
            return PullOutcome::Produced(value.clone());
        }
        assert!(
            self.session_mut().memo.begin(key.clone()),
            "safe product producers cannot recursively enter ProductDriver::pull"
        );

        let (outcome, dependencies, mut staged, recursive_group) = {
            let mut session = self.session_mut();
            let mut context = ProductReadContext::new(&mut session);
            let outcome = producers.produce(&mut context, &key);
            let (dependencies, staged, recursive_group) = context.into_completion();
            (outcome, dependencies, staged, recursive_group)
        };
        if self.emit_causal_products {
            tel.raw_event3(PRODUCT_EVALUATED_EVENT, &key, &request, &outcome);
        }

        match outcome {
            PullOutcome::Produced(value) => {
                let completion = if let Some(members) = recursive_group {
                    assert!(
                        staged.is_empty(),
                        "recursive completion cannot also stage ordinary peer products"
                    );
                    ProductCompletion::RecursiveGroup(members)
                } else {
                    staged.push((key.clone(), value, dependencies));
                    ProductCompletion::Batch(staged)
                };
                let settled = self.session_mut().memo.finish_completion(
                    tel,
                    emit_causal_products,
                    &key,
                    completion,
                    producers.product_types(),
                );
                if !settled {
                    let waits = vec![PullWait::Product(key.clone())];
                    PullOutcome::Waiting(waits)
                } else {
                    PullOutcome::Produced(
                        self.session()
                            .memo
                            .get(&key)
                            .expect("settled completion must install its requested product")
                            .clone(),
                    )
                }
            }
            PullOutcome::Waiting(waits) => {
                self.session_mut().memo.unblock(&key, dependencies);
                PullOutcome::Waiting(waits)
            }
            PullOutcome::Failed(failure) => {
                assert!(staged.is_empty(), "a failed product cannot publish peers");
                assert!(
                    recursive_group.is_none(),
                    "a failed product cannot publish a recursive group"
                );
                self.session_mut().memo.abort(&key);
                PullOutcome::Failed(failure)
            }
        }
    }

    fn emit(&self, event: &'static str, key: &ProductKey) {
        self.tel.raw_event1(&["fz", "compiler2", "pull", "product", event], key);
    }

    fn emit_finished_once(&self) {
        if self.emit_session_lifecycle && !self.finished.replace(true) {
            self.session().emit_finished(self.tel);
        }
    }
}

impl<T: Telemetry> Drop for ProductDriver<'_, T> {
    fn drop(&mut self) {
        self.emit_finished_once();
    }
}

#[cfg(test)]
mod tests {
    use std::cell::{Cell, RefCell};
    use std::collections::{HashMap, HashSet};
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::rc::Rc;

    use crate::telemetry::causal::{
        CausalReport, ProductEvaluationCause, ProductEvaluationTriggerKind, ProductEvaluationWait, parse_public_trace,
    };
    use crate::telemetry::{ConfiguredTelemetry, JsonlBackend};

    use super::super::artifact::{
        CallEdge, CallReturnFlow, CallTarget, DirectCallEdge, MaterializedCallEdge, MaterializedExecutable,
        MaterializedExecutableTransport,
    };
    use super::super::body::{
        ControlEntryId, ControlEntryOrigin, LoweredClause, LoweredEntry, LoweredStep, LoweredTail,
    };
    use super::super::facts::FactReadiness;
    use super::super::identity::{ExecutableNeed, FunctionId};
    use super::super::transport::{BoundaryFacts, BoundaryId, CallableFacts, CallableId, ExecutableSymbol};
    use super::*;

    fn prospective_dependency(dependency: &ProductKey) -> ProductDependencies {
        ProductDependencies {
            products: HashMap::from([(dependency.clone(), None)]),
            facts: HashMap::new(),
        }
    }

    fn finish_test_entry(
        memo: &mut ProductMemo,
        tel: &impl Telemetry,
        key: &ProductKey,
        value: ProductValue,
        dependencies: ProductDependencies,
        types: &super::super::types::Types,
    ) -> bool {
        memo.finish_completion(
            tel,
            causal_product_events_enabled(tel),
            key,
            ProductCompletion::Batch(vec![(key.clone(), value, dependencies)]),
            types,
        )
    }

    fn finish_test_batch(
        memo: &mut ProductMemo,
        tel: &impl Telemetry,
        requested: &ProductKey,
        members: Vec<(ProductKey, ProductValue, ProductDependencies)>,
        types: &super::super::types::Types,
    ) -> bool {
        memo.finish_completion(
            tel,
            causal_product_events_enabled(tel),
            requested,
            ProductCompletion::Batch(members),
            types,
        )
    }

    fn finish_test_group(
        memo: &mut ProductMemo,
        tel: &impl Telemetry,
        requested: &ProductKey,
        members: Vec<(ProductKey, ProductValue, ProductDependencies)>,
        types: &super::super::types::Types,
    ) -> bool {
        memo.finish_completion(
            tel,
            causal_product_events_enabled(tel),
            requested,
            ProductCompletion::RecursiveGroup(members),
            types,
        )
    }

    fn retained_test_session(root: RootId, fact: &FactKey, types: &super::super::types::Types) -> PullSession {
        let tel = ConfiguredTelemetry::new();
        let mut session = PullSession::new(root);
        let key = ProductKey::RootBackendProduct(root);
        assert!(finish_test_entry(
            &mut session.memo,
            &tel,
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
            types,
        ));
        session
    }

    #[test]
    fn retiring_a_never_produced_observed_product_preserves_its_pending_demand() {
        use super::super::scheduler::Scheduler;

        let types = fake_types();
        let root = RootId::for_test(1);
        let address = ProductAddress {
            root,
            key: ProductKey::RootBackendContent(root),
        };
        let mut sessions = ProductSessions::default();
        sessions.observe(&address);
        let mut scheduler = Scheduler::new();
        scheduler.complete_ordered_with_external(
            &super::super::Job::SeedRoot(root),
            HashSet::from([FactUse::current(DependencyKey::Product(address.clone()))]),
            Vec::new(),
            &sessions,
            &types,
        );
        assert_eq!(sessions.next_request(), Some(address.clone()));
        sessions.retry_request(address.clone());
        let withdrawal = sessions.retirement_changes(root);
        assert!(sessions.retire(root, &types));
        scheduler.apply_external_changes_ordered(withdrawal, &sessions, &types);
        assert_eq!(
            scheduler.pending_jobs(),
            0,
            "missing-to-missing withdrawal does not wake the standing waiter"
        );
        assert!(scheduler.has_dependency_consumers(&DependencyKey::Product(address.clone())));
        assert!(
            sessions.get(root).is_none(),
            "retirement must release the memo before any later drive"
        );
        assert_eq!(
            sessions.next_request(),
            Some(address.clone()),
            "an unchanged missing state cannot wake the standing scheduler waiter; its original demand must survive"
        );
        assert!(
            sessions
                .get(root)
                .unwrap()
                .memo
                .observed_products
                .contains(&address.key)
        );
        assert!(
            sessions.next_request().is_none(),
            "retirement must not duplicate the already queued failed demand"
        );
        sessions.unobserve(&address);
        sessions.retry_request(address);
        assert!(
            sessions.next_request().is_none(),
            "detaching the actual scheduler consumer cancels demand"
        );
    }

    #[test]
    fn renewed_product_demand_does_not_revive_duplicate_stale_queue_entries() {
        let root = RootId::for_test(1);
        let address = ProductAddress {
            root,
            key: ProductKey::RootBackendContent(root),
        };
        let mut sessions = ProductSessions::default();
        sessions.observe(&address);
        sessions.unobserve(&address);
        sessions.observe(&address);
        assert!(sessions.retire(root, &fake_types()));
        assert_eq!(sessions.next_request(), Some(address));
        assert!(
            sessions.next_request().is_none(),
            "renewed demand must not turn stale queue entries into duplicate validations"
        );
    }

    #[test]
    fn retained_session_broker_fans_runtime_demand_movement_to_dormant_and_nested_active_roots_once() {
        let types = fake_types();
        let fact = FactKey::RuntimeDemand(fake_executable_with_function(RootId::for_test(99), 99));
        let left = RootId::for_test(1);
        let right = RootId::for_test(2);
        let dormant = RootId::for_test(3);
        let mut sessions = ProductSessions::default();
        for session in [
            retained_test_session(left, &fact, &types),
            retained_test_session(right, &fact, &types),
            retained_test_session(dormant, &fact, &types),
        ] {
            let root = session.root();
            sessions.active_roots.insert(root, ActiveRootProduct::default());
            let session = Rc::new(RefCell::new(session));
            sessions.sessions.insert(root, Rc::clone(&session));
            sessions.restore(session);
        }
        assert_eq!(sessions.counts(), (3, 3));

        let (active_left, _) = sessions.take(left, WorkStartTally::default());
        let (active_right, _) = sessions.take(right, WorkStartTally::default());
        let tel = ConfiguredTelemetry::new();
        sessions.publish(
            &tel,
            &types,
            &[FactMovement {
                key: fact.clone(),
                state: FactState {
                    revision: Some(2),
                    settled: false,
                },
            }],
        );
        sessions.publish(
            &tel,
            &types,
            &[FactMovement {
                key: fact.clone(),
                state: FactState {
                    revision: Some(2),
                    settled: true,
                },
            }],
        );
        sessions.drain_active_movements(left, &mut active_left.borrow_mut());
        sessions.drain_active_movements(right, &mut active_right.borrow_mut());
        let final_state = FactState {
            revision: Some(2),
            settled: true,
        };
        assert_eq!(
            active_left.borrow().pending_fact_states,
            HashMap::from([(fact.clone(), final_state)])
        );
        assert_eq!(
            active_right.borrow().pending_fact_states,
            HashMap::from([(fact.clone(), final_state)])
        );
        assert_eq!(
            sessions.sessions[&dormant].borrow().pending_fact_states,
            HashMap::from([(fact.clone(), final_state)])
        );
        sessions.finish_activation(right, &mut active_right.borrow_mut(), WorkStartTally::default());
        sessions.restore(active_right);
        sessions.finish_activation(left, &mut active_left.borrow_mut(), WorkStartTally::default());
        sessions.restore(active_left);

        assert!(sessions.retire(left, &types));
        assert_eq!(sessions.counts(), (2, 2));
        assert_eq!(sessions.roots_by_fact[&fact], HashSet::from([right, dormant]));
    }

    #[test]
    fn equal_fact_delivery_keeps_both_retained_root_products_settled() {
        let types = fake_types();
        let tel = ConfiguredTelemetry::new();
        let fact = FactKey::RootEntry(RootId::for_test(99));
        let roots = [RootId::for_test(1), RootId::for_test(2)];
        let mut sessions = ProductSessions::default();
        for root in roots {
            let session = retained_test_session(root, &fact, &types);
            sessions.active_roots.insert(root, ActiveRootProduct::default());
            let session = Rc::new(RefCell::new(session));
            sessions.sessions.insert(root, Rc::clone(&session));
            sessions.restore(session);
        }
        sessions.publish(
            &tel,
            &types,
            &[FactMovement {
                key: fact,
                state: FactState {
                    revision: Some(1),
                    settled: true,
                },
            }],
        );
        for root in roots {
            let mut session = sessions.sessions.get(&root).expect("retained root").borrow_mut();
            session.reconcile_fact_movements(&tel, &types);
            assert!(session.memo.get(&ProductKey::RootBackendProduct(root)).is_some());
        }
    }

    /// Recursive search work is a property of the pending graph, not of the
    /// fresh `RandomState` assigned to each memo. The side branch made the old
    /// early-exit gate visit a variable prefix before its repeated component
    /// scans. One traversal must inspect each reachable vertex and edge once.
    #[test]
    fn recursive_group_search_work_is_a_function_of_the_pending_graph() {
        let types = fake_types();
        let root = RootId::for_test(81);
        let callable = |function, value| {
            ProductKey::CallableConstruction(TransportPosition::Value {
                executable: executable_symbol_for_test(&fake_executable_with_function(root, function)),
                value: ValueId::from_u32(value),
            })
        };
        let current = callable(810, 0);
        let target = callable(811, 1);
        let detour_1 = callable(812, 2);
        let detour_2 = callable(813, 3);
        let detour_3 = callable(814, 4);

        for _ in 0..32 {
            let mut memo = ProductMemo::default();
            for (key, dependencies) in [
                (
                    target.clone(),
                    ProductDependencies {
                        products: HashMap::from([(current.clone(), None), (detour_1.clone(), None)]),
                        facts: HashMap::new(),
                    },
                ),
                (
                    detour_1.clone(),
                    ProductDependencies {
                        products: HashMap::from([(detour_2.clone(), None)]),
                        facts: HashMap::new(),
                    },
                ),
                (
                    detour_2.clone(),
                    ProductDependencies {
                        products: HashMap::from([(detour_3.clone(), None)]),
                        facts: HashMap::new(),
                    },
                ),
                (detour_3.clone(), ProductDependencies::default()),
            ] {
                memo.unblock(&key, dependencies);
            }

            let (members, search) =
                memo.pending_strong_component(&current, &prospective_dependency(&target), &target, &types);
            assert_eq!(
                members.map(|members| members.into_iter().collect::<HashSet<_>>()),
                Some(HashSet::from([current.clone(), target.clone()]))
            );
            assert_eq!(
                search,
                RecursiveGroupSearch {
                    candidate_inventory: 5,
                    vertex_visits: 5,
                    edge_scans: 5,
                    cycle_closed: true,
                    group_members: 2,
                }
            );
        }
    }

    #[test]
    fn recursive_group_search_matches_pending_graph_boundaries() {
        let types = fake_types();
        let root = RootId::for_test(84);
        let current = ProductKey::AbiExecutable(fake_executable_with_function(root, 840));
        let dependency = ProductKey::AbiExecutable(fake_executable_with_function(root, 841));
        let peer = ProductKey::AbiExecutable(fake_executable_with_function(root, 842));
        let bridge = ProductKey::RootBackendProduct(root);
        let missing = ProductMemo::default();
        assert_eq!(
            missing.pending_strong_component(&current, &prospective_dependency(&dependency), &dependency, &types),
            (
                None,
                RecursiveGroupSearch {
                    candidate_inventory: 0,
                    vertex_visits: 0,
                    edge_scans: 0,
                    cycle_closed: false,
                    group_members: 0,
                }
            )
        );

        let mut displaced = ProductMemo::default();
        finish_test_product(&mut displaced, &dependency, ProductValue::Unit, [current.clone()]);
        displaced.remove(&ConfiguredTelemetry::new(), &dependency, &types);
        assert_eq!(
            displaced.pending_strong_component(&current, &prospective_dependency(&dependency), &dependency, &types,),
            (
                None,
                RecursiveGroupSearch {
                    candidate_inventory: 0,
                    vertex_visits: 0,
                    edge_scans: 0,
                    cycle_closed: false,
                    group_members: 0,
                }
            ),
            "a displaced product's last settled dependencies are not pending cycle evidence"
        );

        let mut self_cycle = ProductMemo::default();
        self_cycle.unblock(&current, ProductDependencies::default());
        assert_eq!(
            self_cycle.pending_strong_component(&current, &prospective_dependency(&current), &current, &types),
            (
                Some(vec![current.clone()]),
                RecursiveGroupSearch {
                    candidate_inventory: 1,
                    vertex_visits: 1,
                    edge_scans: 1,
                    cycle_closed: true,
                    group_members: 1,
                }
            )
        );

        let mut disjoint = ProductMemo::default();
        disjoint.unblock(
            &dependency,
            ProductDependencies {
                products: HashMap::from([(peer.clone(), None)]),
                facts: HashMap::new(),
            },
        );
        disjoint.unblock(
            &peer,
            ProductDependencies {
                products: HashMap::from([(dependency.clone(), None)]),
                facts: HashMap::new(),
            },
        );
        assert_eq!(
            disjoint.pending_strong_component(&current, &prospective_dependency(&dependency), &dependency, &types,),
            (
                None,
                RecursiveGroupSearch {
                    candidate_inventory: 2,
                    vertex_visits: 2,
                    edge_scans: 2,
                    cycle_closed: false,
                    group_members: 0,
                }
            )
        );

        let mut cross_kind = ProductMemo::default();
        cross_kind.unblock(
            &dependency,
            ProductDependencies {
                products: HashMap::from([(bridge.clone(), None)]),
                facts: HashMap::new(),
            },
        );
        cross_kind.unblock(
            &bridge,
            ProductDependencies {
                products: HashMap::from([(current.clone(), None)]),
                facts: HashMap::new(),
            },
        );
        let (members, search) =
            cross_kind.pending_strong_component(&current, &prospective_dependency(&dependency), &dependency, &types);
        assert_eq!(
            members.map(|members| members.into_iter().collect::<HashSet<_>>()),
            Some(HashSet::from([current.clone(), dependency.clone()]))
        );
        assert_eq!(
            search,
            RecursiveGroupSearch {
                candidate_inventory: 2,
                vertex_visits: 3,
                edge_scans: 3,
                cycle_closed: true,
                group_members: 2,
            }
        );
    }

    #[test]
    fn recursive_reads_record_exact_dependency_generation_on_every_outcome() {
        let tel = ConfiguredTelemetry::new();
        let types = fake_types();
        let root = RootId::for_test(85);
        let current = ProductKey::AbiExecutable(fake_executable_with_function(root, 850));
        let missing = ProductKey::AbiExecutable(fake_executable_with_function(root, 851));
        let ready = ProductKey::AbiExecutable(fake_executable_with_function(root, 852));
        let cyclic = ProductKey::AbiExecutable(fake_executable_with_function(root, 853));
        let mut session = PullSession::new(root);

        {
            let mut context = ProductReadContext::new(&mut session);
            assert!(matches!(
                context.read_recursive_product(&tel, missing.clone(), &current, &types),
                RecursiveProductRead::Waiting
            ));
            assert_eq!(context.dependencies.products.get(&missing), Some(&None));
        }

        finish_test_product(&mut session.memo, &ready, ProductValue::Unit, []);
        assert_eq!(
            session
                .memo
                .pending_strong_component(&current, &prospective_dependency(&ready), &ready, &types),
            (
                None,
                RecursiveGroupSearch {
                    candidate_inventory: 0,
                    vertex_visits: 0,
                    edge_scans: 0,
                    cycle_closed: false,
                    group_members: 0,
                }
            )
        );
        {
            let mut context = ProductReadContext::new(&mut session);
            assert!(matches!(
                context.read_recursive_product(&tel, ready.clone(), &current, &types),
                RecursiveProductRead::Ready(ProductValue::Unit)
            ));
            assert_eq!(context.dependencies.products.get(&ready), Some(&Some(1)));
        }

        session.memo.unblock(
            &cyclic,
            ProductDependencies {
                products: HashMap::from([(current.clone(), None)]),
                facts: HashMap::new(),
            },
        );
        let mut context = ProductReadContext::new(&mut session);
        let RecursiveProductRead::Group(members) =
            context.read_recursive_product(&tel, cyclic.clone(), &current, &types)
        else {
            panic!("the prospective edge should close the pending cycle");
        };
        assert_eq!(
            members.into_iter().collect::<HashSet<_>>(),
            HashSet::from([current, cyclic.clone()])
        );
        assert_eq!(context.dependencies.products.get(&cyclic), Some(&None));
    }

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
            telemetry.attach_raw_event3::<ProductKey, ProductValue, ProductSettlement, _>(
                &["fz", "compiler2", "pull", "product", "settled"],
                move |_, _, _, _, _, _| produced.set(produced.get() + 1),
            );
            capture
        }
    }

    #[test]
    fn completion_batch_commits_one_semantic_sequence_for_every_requested_anchor() {
        let root = RootId::for_test(86);
        let mut types = super::super::Types::new();
        let keys =
            [860, 861, 862].map(|function| ProductKey::AbiExecutable(fake_executable_in(&mut types, root, function)));
        let mut expected = keys.to_vec();
        sort_product_keys(&mut expected, &types);

        for requested in &keys {
            for reverse in [false, true] {
                let tel = ConfiguredTelemetry::new();
                let observed = Rc::new(RefCell::new(Vec::new()));
                let sink = Rc::clone(&observed);
                tel.attach_raw_event3::<ProductKey, ProductValue, ProductSettlement, _>(
                    &["fz", "compiler2", "pull", "product", "settled"],
                    move |_, _, _, key, _, _| sink.borrow_mut().push(key.clone()),
                );
                let mut order = keys.to_vec();
                if reverse {
                    order.reverse();
                }
                let entries = order
                    .into_iter()
                    .map(|key| (key, ProductValue::Unit, ProductDependencies::default()))
                    .collect();
                let mut memo = ProductMemo::default();
                assert!(memo.begin(requested.clone()));
                assert!(finish_test_batch(&mut memo, &tel, requested, entries, &types));
                assert_eq!(*observed.borrow(), expected);
                assert!(keys.iter().all(|key| memo.generation(key) == Some(1)));
            }
        }
    }

    #[test]
    fn recursive_group_commits_one_semantic_sequence_for_every_requested_anchor() {
        let root = RootId::for_test(88);
        let mut types = super::super::Types::new();
        let keys =
            [880, 881, 882].map(|function| ProductKey::AbiExecutable(fake_executable_in(&mut types, root, function)));
        let mut expected = keys.to_vec();
        sort_product_keys(&mut expected, &types);

        for requested in &keys {
            for reverse in [false, true] {
                let tel = ConfiguredTelemetry::new();
                let observed = Rc::new(RefCell::new(Vec::new()));
                let sink = Rc::clone(&observed);
                tel.attach_raw_event3::<ProductKey, ProductValue, ProductSettlement, _>(
                    &["fz", "compiler2", "pull", "product", "settled"],
                    move |_, _, _, key, _, settlement| sink.borrow_mut().push((key.clone(), settlement.group)),
                );
                let mut order = keys.to_vec();
                if reverse {
                    order.reverse();
                }
                let entries = order
                    .into_iter()
                    .map(|key| (key, ProductValue::Unit, ProductDependencies::default()))
                    .collect();
                let mut memo = ProductMemo::default();
                for key in &keys {
                    assert!(memo.begin(key.clone()));
                }
                assert!(finish_test_group(&mut memo, &tel, requested, entries, &types));
                let observed = observed.borrow();
                assert_eq!(
                    observed.iter().map(|(key, _)| key.clone()).collect::<Vec<_>>(),
                    expected
                );
                let groups = observed.iter().map(|(_, group)| *group).collect::<HashSet<_>>();
                assert_eq!(groups.len(), 1);
                assert!(!groups.contains(&None));
            }
        }
    }

    #[test]
    fn changed_batch_drains_produced_and_pending_reader_diamond_in_semantic_order() {
        let root = RootId::for_test(87);
        let mut types = super::super::Types::new();
        let keys = [870, 871, 872, 873, 874, 875, 876]
            .map(|function| ProductKey::AbiExecutable(fake_executable_in(&mut types, root, function)));
        let [left, right, left_reader, right_reader, join, pending, pending_child] = &keys;
        let mut expected_displaced = vec![left_reader.clone(), right_reader.clone()];
        sort_product_keys(&mut expected_displaced, &types);

        for reverse in [false, true] {
            let tel = ConfiguredTelemetry::new();
            let mut memo = ProductMemo::default();
            let mut sources = vec![left.clone(), right.clone()];
            if reverse {
                sources.reverse();
            }
            for source in &sources {
                finish_test_product(&mut memo, source, ProductValue::Unit, []);
            }
            finish_test_product(&mut memo, left_reader, ProductValue::Unit, [left.clone()]);
            finish_test_product(&mut memo, right_reader, ProductValue::Unit, [right.clone()]);
            finish_test_product(
                &mut memo,
                join,
                ProductValue::Unit,
                [left_reader.clone(), right_reader.clone()],
            );
            memo.unblock(
                pending,
                ProductDependencies {
                    products: HashMap::from([
                        (left.clone(), memo.generation(left)),
                        (right.clone(), memo.generation(right)),
                    ]),
                    facts: HashMap::new(),
                },
            );
            memo.unblock(
                pending_child,
                ProductDependencies {
                    products: HashMap::from([(pending.clone(), None)]),
                    facts: HashMap::new(),
                },
            );

            let displaced = Rc::new(RefCell::new(Vec::new()));
            let sink = Rc::clone(&displaced);
            tel.attach_raw_event1::<ProductKey, _>(
                &["fz", "compiler2", "pull", "product", "displaced"],
                move |_, _, _, key| sink.borrow_mut().push(key.clone()),
            );
            let replacement = ProductValue::ExecutableEffects(EffectSummary::default());
            let entries = sources
                .iter()
                .cloned()
                .map(|key| (key, replacement.clone(), ProductDependencies::default()))
                .collect();
            assert!(finish_test_batch(&mut memo, &tel, left, entries, &types));

            assert_eq!(*displaced.borrow(), expected_displaced);
            assert!(memo.get(join).is_some());
            assert!(memo.dirty_descendants.contains(join));
            assert!(!memo.pending_dependencies.contains_key(pending));
            assert!(!memo.pending_dependencies.contains_key(pending_child));
        }
    }

    #[test]
    fn transitive_dirtiness_retracts_pending_readers_but_leaves_settled_readers_lazy() {
        let tel = ConfiguredTelemetry::new();
        let types = fake_types();
        let root = RootId::for_test(99);
        let source = ProductKey::AbiExecutable(fake_executable_with_function(root, 990));
        let intermediate = ProductKey::AbiExecutable(fake_executable_with_function(root, 991));
        let pending = ProductKey::AbiExecutable(fake_executable_with_function(root, 992));
        let settled = ProductKey::AbiExecutable(fake_executable_with_function(root, 993));
        let mut memo = ProductMemo::default();
        finish_test_product(&mut memo, &source, ProductValue::Unit, []);
        finish_test_product(&mut memo, &intermediate, ProductValue::Unit, [source.clone()]);
        memo.unblock(
            &pending,
            ProductDependencies {
                products: HashMap::from([(intermediate.clone(), Some(1))]),
                facts: HashMap::new(),
            },
        );
        finish_test_product(&mut memo, &settled, ProductValue::Unit, [intermediate.clone()]);

        memo.remove(&tel, &source, &types);

        assert!(!memo.pending_dependencies.contains_key(&pending));
        assert!(memo.get(&settled).is_some());
        assert!(memo.dirty_descendants.contains(&intermediate));
        assert!(memo.dirty_descendants.contains(&settled));
    }

    #[derive(Default)]
    struct FakeProducers {
        types: super::super::Types,
        produced: HashSet<ProductKey>,
        calls: Vec<ProductKey>,
        self_wait: Option<ProductKey>,
        root_entry: Option<ExecutableKey>,
        root_prerequisites: Vec<ProductKey>,
        root_recursive_prerequisite: Option<ProductKey>,
        recursive_telemetry: Option<Rc<ConfiguredTelemetry>>,
        facts: HashMap<FactKey, FactState>,
        runtime_fact: Option<FactUse<FactKey>>,
        runtime_value: Option<ProductValue>,
        runtime_children: HashMap<ProductKey, ProductKey>,
        materialized_value: Option<ProductValue>,
        backend_fact: Option<FactUse<FactKey>>,
        backend_value: Option<ProductValue>,
        fact_state_reads: usize,
        fail_native_once: bool,
        native_fact: Option<FactUse<FactKey>>,
    }

    impl FakeProducers {
        fn fact_state(&mut self, fact: &FactUse<FactKey>) -> FactState {
            self.fact_state_reads += 1;
            self.facts.get(fact.fact()).copied().unwrap_or(FactState {
                revision: None,
                settled: false,
            })
        }

        fn produce_unit(&mut self, key: ProductKey) -> PullOutcome {
            self.calls.push(key.clone());
            self.produced.insert(key);
            PullOutcome::Produced(ProductValue::Unit)
        }
    }

    impl ProductProducers for FakeProducers {
        fn product_types(&self) -> &super::super::Types {
            &self.types
        }

        fn produce(&mut self, context: &mut ProductReadContext<'_>, key: &ProductKey) -> PullOutcome {
            if self.self_wait.as_ref() == Some(key) {
                self.calls.push(key.clone());
                return PullOutcome::wait_on_product(key.clone());
            }
            match key {
                ProductKey::RootBackendProduct(root) => {
                    let tel = ConfiguredTelemetry::new();
                    self.calls.push(key.clone());
                    let mut waits = self
                        .root_prerequisites
                        .iter()
                        .filter(|prerequisite| {
                            context
                                .read_product_entry(&tel, (*prerequisite).clone(), &self.types)
                                .is_none()
                        })
                        .cloned()
                        .map(PullWait::Product)
                        .collect::<Vec<_>>();
                    if let Some(prerequisite) = self.root_recursive_prerequisite.clone() {
                        let telemetry = self
                            .recursive_telemetry
                            .as_ref()
                            .expect("a recursive fake producer needs its driver telemetry");
                        if matches!(
                            context.read_recursive_product(telemetry.as_ref(), prerequisite.clone(), key, &self.types,),
                            RecursiveProductRead::Waiting
                        ) {
                            waits.push(PullWait::Product(prerequisite));
                        }
                    }
                    if !waits.is_empty() {
                        return PullOutcome::Waiting(waits);
                    }
                    let prerequisite =
                        ProductKey::AbiExecutable(self.root_entry.clone().expect("fake root entry should be set"));
                    if context
                        .read_product_entry(&tel, prerequisite.clone(), &self.types)
                        .is_some()
                    {
                        self.produced.insert(ProductKey::RootBackendProduct(*root));
                        PullOutcome::Produced(ProductValue::Unit)
                    } else {
                        PullOutcome::wait_on_product(prerequisite)
                    }
                }
                ProductKey::NativeProgram(_) => {
                    self.calls.push(key.clone());
                    if let Some(fact) = self.native_fact.clone() {
                        let state = self.fact_state(&fact);
                        context.record_fact_state(fact.clone(), state);
                        if !state.settled {
                            return PullOutcome::wait_on_fact(fact);
                        }
                    }
                    if std::mem::take(&mut self.fail_native_once) {
                        PullOutcome::Failed(ProductFailure::NativeLowering)
                    } else {
                        PullOutcome::Produced(ProductValue::Unit)
                    }
                }
                ProductKey::BackendExecutable(_) => {
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
                    } else if self.backend_value.is_none() {
                        return PullOutcome::wait_on_fact(FactUse::current(FactKey::CodeIndexed(
                            super::super::CodeId::ZERO,
                        )));
                    }
                    self.produced.insert(key.clone());
                    PullOutcome::Produced(self.backend_value.clone().unwrap_or(ProductValue::Unit))
                }
                ProductKey::MaterializedExecutable(_) => {
                    self.calls.push(key.clone());
                    self.produced.insert(key.clone());
                    PullOutcome::Produced(self.materialized_value.clone().unwrap_or(ProductValue::Unit))
                }
                ProductKey::AbiExecutable(_) => {
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
                    if let Some(child) = self.runtime_children.get(key).cloned()
                        && context
                            .read_product_entry(&ConfiguredTelemetry::new(), child.clone(), &self.types)
                            .is_none()
                    {
                        return PullOutcome::wait_on_product(child);
                    }
                    self.produced.insert(key.clone());
                    PullOutcome::Produced(self.runtime_value.clone().unwrap_or(ProductValue::Unit))
                }
                _ => self.produce_unit(key.clone()),
            }
        }
    }

    #[test]
    fn failed_product_is_not_memoized_and_can_be_retried() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(0);
        let key = ProductKey::NativeProgram(root);
        let prerequisite = FactUse::settled(FactKey::RootEntry(root));
        let mut producers = FakeProducers {
            fail_native_once: true,
            native_fact: Some(prerequisite.clone()),
            ..FakeProducers::default()
        };
        let mut driver = ProductDriver::new(&tel, root);

        assert_eq!(
            driver.pull(&mut producers, key.clone()),
            PullOutcome::wait_on_fact(prerequisite.clone())
        );
        assert!(driver.session().memo.pending_product_dependencies(&key).is_some());
        producers.facts.insert(
            prerequisite.fact().clone(),
            FactState {
                revision: Some(1),
                settled: true,
            },
        );
        assert_eq!(
            driver.pull(&mut producers, key.clone()),
            PullOutcome::Failed(ProductFailure::NativeLowering)
        );
        assert!(!driver.session().memo.contains_in_progress(&key));
        assert!(driver.session().memo.pending_product_dependencies(&key).is_none());
        assert_eq!(driver.session().memo.get(&key), None);
        assert_eq!(driver.session().memo.generation(&key), None);

        assert_eq!(
            driver.pull(&mut producers, key.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(driver.session().memo.generation(&key), Some(1));
    }

    #[test]
    fn transport_only_root_movement_stops_at_equal_backend_content() {
        let root = RootId::for_test(0);
        let root_key = ProductKey::RootBackendProduct(root);
        let content_key = ProductKey::RootBackendContent(root);
        let native_key = ProductKey::NativeProgram(root);
        let backend = Rc::new(super::super::artifact::BackendProgram::empty_for_test());
        let answer = |entry, program| {
            ProductValue::RootBackendProduct(RootBackendProductAnswer {
                program,
                transport: Rc::new(super::super::artifact::MaterializedTransportPlan {
                    entry,
                    executable_membership: Box::default(),
                    position_layouts: Vec::new(),
                    callable_boundaries: Vec::new(),
                    boundary_ids: Vec::new(),
                    codegen_seam_facts: Box::default(),
                    callable_owners: Box::default(),
                    callable_facts: HashMap::new(),
                    boundary_facts: HashMap::new(),
                }),
            })
        };
        let mut memo = ProductMemo::default();

        finish_test_product(
            &mut memo,
            &root_key,
            answer(
                executable_symbol_for_test(&fake_executable_with_function(root, 1)),
                Rc::clone(&backend),
            ),
            [],
        );
        finish_test_product(
            &mut memo,
            &content_key,
            ProductValue::RootBackendContent(Rc::clone(&backend)),
            [root_key.clone()],
        );
        finish_test_product(&mut memo, &native_key, ProductValue::Unit, [content_key.clone()]);
        let content_generation = memo.generation(&content_key);
        let native_generation = memo.generation(&native_key);

        finish_test_product(
            &mut memo,
            &root_key,
            answer(
                executable_symbol_for_test(&fake_executable_with_function(root, 2)),
                Rc::new((*backend).clone()),
            ),
            [],
        );
        let Some(ProductValue::RootBackendProduct(reproduced)) = memo.get(&root_key) else {
            panic!("root reproduction must retain its answer");
        };
        assert!(
            Rc::ptr_eq(&backend, &reproduced.program),
            "the memo owns equal backend retention even when transport moves"
        );
        let reproduced_program = Rc::clone(&reproduced.program);
        finish_test_product(
            &mut memo,
            &content_key,
            ProductValue::RootBackendContent(reproduced_program),
            [root_key],
        );

        assert_eq!(memo.generation(&content_key), content_generation);
        assert_eq!(memo.generation(&native_key), native_generation);
        assert!(memo.get(&native_key).is_some());
    }

    #[test]
    fn equal_native_reproduction_retains_allocation_and_generation() {
        let root = RootId::for_test(0);
        let key = ProductKey::NativeProgram(root);
        let native = || NativeProgram {
            entry: crate::fz_ir::FnId(0),
            module: crate::fz_ir::Module::default(),
            executable_entries: Vec::new(),
            bodies: Vec::new(),
            callable_boundaries: Vec::new(),
        };
        let original = Rc::new(native());
        let mut memo = ProductMemo::default();

        finish_test_product(&mut memo, &key, ProductValue::NativeProgram(Rc::clone(&original)), []);
        let generation = memo.generation(&key);
        finish_test_product(&mut memo, &key, ProductValue::NativeProgram(Rc::new(native())), []);

        let Some(ProductValue::NativeProgram(retained)) = memo.get(&key) else {
            panic!("native program must remain settled");
        };
        assert!(Rc::ptr_eq(retained, &original));
        assert_eq!(memo.generation(&key), generation);
    }

    #[test]
    fn product_driver_names_prerequisites_without_follow_up_jobs() {
        let tel = ConfiguredTelemetry::new();
        let capture = ProductTelemetryCapture::install(&tel);
        let root = RootId::for_test(0);
        let executable = fake_executable(root);
        let root_key = ProductKey::RootBackendProduct(root);
        let prerequisite = ProductKey::AbiExecutable(executable.clone());
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
    fn product_driver_correlates_waiting_producer_runs_and_cache_hits() {
        let tel = Rc::new(ConfiguredTelemetry::new());
        let (buf, writer) = crate::telemetry::capture::vec_writer();
        JsonlBackend::new_writer(writer).install(tel.as_ref());
        let root = RootId::for_test(90);
        let root_key = ProductKey::RootBackendProduct(root);
        let dependency = ProductKey::AbiExecutable(fake_executable_with_function(root, 901));
        let dependency_child = ProductKey::AbiExecutable(fake_executable_with_function(root, 902));
        let moved = ProductKey::AbiExecutable(fake_executable_with_function(root, 903));
        let mut producers = FakeProducers {
            root_entry: match &dependency {
                ProductKey::AbiExecutable(executable) => Some(executable.clone()),
                _ => unreachable!(),
            },
            root_prerequisites: vec![moved.clone()],
            root_recursive_prerequisite: Some(dependency.clone()),
            recursive_telemetry: Some(Rc::clone(&tel)),
            runtime_children: HashMap::from([(dependency.clone(), dependency_child.clone())]),
            ..FakeProducers::default()
        };
        let mut driver = ProductDriver::new(tel.as_ref(), root);

        assert_eq!(
            driver.pull(&mut producers, dependency.clone()),
            PullOutcome::wait_on_product(dependency_child.clone())
        );
        assert_eq!(
            driver.pull(&mut producers, root_key.clone()),
            PullOutcome::Waiting(vec![
                PullWait::Product(moved.clone()),
                PullWait::Product(dependency.clone())
            ])
        );
        assert_eq!(
            driver.pull(&mut producers, moved),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(
            driver.pull(&mut producers, root_key.clone()),
            PullOutcome::wait_on_product(dependency.clone())
        );
        assert_eq!(
            driver.pull(&mut producers, dependency_child),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(
            driver.pull(&mut producers, dependency),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(
            driver.pull(&mut producers, root_key.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(
            driver.pull(&mut producers, root_key),
            PullOutcome::Produced(ProductValue::Unit)
        );
        driver.finish_session();

        let events = parse_public_trace(&buf.borrow());
        let requested_name = ["fz", "compiler2", "pull", "product", "requested"].map(str::to_string);
        let evaluated_name = ["fz", "compiler2", "pull", "product", "evaluated"].map(str::to_string);
        let settled_name = ["fz", "compiler2", "pull", "product", "settled"].map(str::to_string);
        let normalized_product = |event: &crate::telemetry::causal::PublicEvent| {
            let mut product = event.metadata["product"].clone();
            product
                .as_object_mut()
                .expect("product identity is an object")
                .remove("opaque_type");
            product
        };
        let is_root = |event: &&crate::telemetry::causal::PublicEvent| {
            event.metadata["product"]["kind"] == "root_backend_product"
                && event.metadata["product"]["root_id"] == u64::from(root.as_u32())
        };
        let all_requests = events
            .iter()
            .filter(|event| event.name == requested_name)
            .map(|event| event.metadata["request_id"].as_u64().expect("request identity"))
            .collect::<Vec<_>>();
        let all_evaluations = events
            .iter()
            .filter(|event| event.name == evaluated_name)
            .map(|event| event.metadata["request_id"].as_u64().expect("evaluation identity"))
            .collect::<Vec<_>>();
        assert_eq!(all_requests, (1..=8).collect::<Vec<_>>());
        assert_eq!(all_evaluations, (1..=7).collect::<Vec<_>>());
        let requests = events
            .iter()
            .filter(|event| event.name == requested_name && is_root(event))
            .map(|event| event.metadata["request_id"].as_u64().expect("request identity"))
            .collect::<Vec<_>>();
        let evaluations = events
            .iter()
            .filter(|event| event.name == evaluated_name && is_root(event))
            .map(|event| event.metadata["request_id"].as_u64().expect("evaluation identity"))
            .collect::<Vec<_>>();
        assert_eq!(requests, [2, 4, 7, 8]);
        assert_eq!(evaluations, [2, 4, 7]);

        let (moved_position, moved_event) = events
            .iter()
            .enumerate()
            .find(|(_, event)| event.name == settled_name && event.metadata["product"]["function_id"] == 903)
            .expect("the exact moved dependency settlement");
        let moved_product = normalized_product(moved_event);
        let dependency_product = events
            .iter()
            .find(|event| event.name == requested_name && event.metadata["request_id"] == 1)
            .map(normalized_product)
            .expect("the recursive dependency request");
        let request_position = events
            .iter()
            .position(|event| event.name == requested_name && event.metadata["request_id"] == 4)
            .expect("the moved producer request");

        let report = CausalReport::derive(&events);
        let initial_evaluation = report
            .product_evaluations
            .iter()
            .find(|evaluation| evaluation.request == 2)
            .expect("initial root producer run");
        let moved_evaluation = report
            .product_evaluations
            .iter()
            .find(|evaluation| evaluation.request == 4)
            .expect("producer run after dependency movement");
        assert_eq!(moved_evaluation.prior_evaluation, Some(initial_evaluation.position));
        assert_eq!(moved_evaluation.cause, ProductEvaluationCause::ProductMovement);
        assert_eq!(moved_evaluation.prior_waits.len(), 2);
        assert!(matches!(
            &moved_evaluation.prior_waits[0],
            ProductEvaluationWait::Product(product) if product.raw == moved_product
        ));
        assert!(matches!(
            &moved_evaluation.prior_waits[1],
            ProductEvaluationWait::Product(product) if product.raw == dependency_product
        ));
        assert_eq!(moved_evaluation.triggers.len(), 1);
        let trigger = &moved_evaluation.triggers[0];
        assert_eq!(trigger.position, moved_position);
        assert_eq!(trigger.kind, ProductEvaluationTriggerKind::ProductSettlement);
        assert!(matches!(
            &trigger.dependency,
            ProductEvaluationWait::Product(product) if product.raw == moved_product
        ));
        let search = report
            .recursive_searches
            .iter()
            .find(|search| search.request == Some(4) && search.product == moved_evaluation.product)
            .expect("recursive search inside the moved producer run");
        assert_eq!(search.session, moved_evaluation.session);
        assert_eq!(search.dependency.raw, dependency_product);
        assert_eq!(search.cause, Some(ProductEvaluationCause::ProductMovement));
        assert!(
            initial_evaluation.position < moved_position
                && moved_position < request_position
                && request_position < search.position
                && search.position < moved_evaluation.position
        );
    }

    #[test]
    fn product_driver_refreshes_deepest_stale_child_without_waking_equal_value_readers() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(7);
        let executable = fake_executable(root);
        let parent = ProductKey::RootBackendProduct(root);
        let child = ProductKey::AbiExecutable(executable.clone());
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
        let key = ProductKey::AbiExecutable(fake_executable(root));
        let mut driver = ProductDriver::new(&tel, root);
        finish_test_entry(
            &mut driver.session_mut().memo,
            &tel,
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
            &fake_types(),
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
        let key = ProductKey::AbiExecutable(fake_executable(root));
        let mut driver = ProductDriver::new(&tel, root);
        finish_test_entry(
            &mut driver.session_mut().memo,
            &tel,
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
            &fake_types(),
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
        let key = ProductKey::AbiExecutable(fake_executable(root));
        let mut driver = ProductDriver::new(&tel, root);
        finish_test_entry(
            &mut driver.session_mut().memo,
            &tel,
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
            &fake_types(),
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
    fn equal_parent_reproduction_does_not_invalidate_its_grandparent() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(17);
        let executable = fake_executable(root);
        let grandparent = ProductKey::RootBackendProduct(root);
        let parent = ProductKey::AbiExecutable(executable.clone());
        let child = ProductKey::BackendExecutable(executable);
        let fact = FactUse::current(FactKey::CodeIndexed(super::super::CodeId::ZERO));
        let mut producers = FakeProducers {
            root_entry: match &parent {
                ProductKey::AbiExecutable(executable) => Some(executable.clone()),
                _ => unreachable!(),
            },
            runtime_children: HashMap::from([(parent.clone(), child.clone())]),
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
    fn product_driver_rejects_an_in_progress_key_before_request_telemetry() {
        let tel = ConfiguredTelemetry::new();
        let requests = Rc::new(Cell::new(0));
        let observed = Rc::clone(&requests);
        tel.attach_raw_event2::<ProductKey, ProductRequestId, _>(PRODUCT_REQUESTED_EVENT, move |_, _, _, _, _| {
            observed.set(observed.get() + 1)
        });
        let root = RootId::for_test(2);
        let executable = fake_executable(root);
        let key = ProductKey::ExecutableEffects(executable);
        let mut driver = ProductDriver::new(&tel, root);
        let mut producers = FakeProducers::default();

        assert!(driver.session_mut().memo.begin(key.clone()));
        assert!(catch_unwind(AssertUnwindSafe(|| driver.pull(&mut producers, key.clone()))).is_err());
        assert_eq!(requests.get(), 0);
        assert_eq!(driver.session().request_ids.next, NonZeroU64::new(1));
        assert!(driver.session().memo.contains_in_progress(&key));
        assert!(producers.calls.is_empty());
    }

    #[test]
    fn executable_effects_reads_only_its_local_projection_and_direct_callee_products() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(79);
        let caller = fake_executable_with_function(root, 790);
        let callee = fake_executable_with_function(root, 791);
        let leaf = fake_executable_with_function(root, 792);
        let mut driver = ProductDriver::new(&tel, root);
        record_effect_product(&mut driver.session_mut(), &caller, &[&callee], false);
        record_effect_product(&mut driver.session_mut(), &callee, &[&leaf], false);
        record_effect_product(&mut driver.session_mut(), &leaf, &[], true);
        let mut world = World::new();
        let caller_effects = ProductKey::ExecutableEffects(caller.clone());
        let callee_effects = ProductKey::ExecutableEffects(callee);
        let caller_materialized = ProductKey::MaterializedExecutable(caller);

        let outcome = {
            let mut producers = WorldProductProducers::new(&mut world, &tel);
            driver.pull(&mut producers, caller_effects.clone())
        };

        assert_eq!(outcome, PullOutcome::wait_on_product(callee_effects.clone()));
        let dependencies = driver
            .session()
            .memo()
            .dependency_edges()
            .filter(|(reader, _)| *reader == &caller_effects)
            .map(|(_, dependency)| dependency.clone())
            .collect::<HashSet<_>>();
        assert_eq!(dependencies, HashSet::from([caller_materialized, callee_effects]));
    }

    #[test]
    fn executable_effects_product_settles_symbolic_mutual_recursion_without_root_loop() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(8);
        let first = fake_executable_with_function(root, 80);
        let second = fake_executable_with_function(root, 81);
        let leaf = fake_executable_with_function(root, 82);
        let mut driver = ProductDriver::new(&tel, root);
        record_effect_product(&mut driver.session_mut(), &first, &[&second], false);
        record_effect_product(&mut driver.session_mut(), &second, &[&first, &leaf], false);
        record_effect_product(&mut driver.session_mut(), &leaf, &[], true);
        let mut world = World::new();
        let effects = pull_effects_until_produced(&mut driver, &mut world, &second);
        assert!(effects.allocates, "effects should propagate through mutual recursion");
        assert!(memo_effects(&driver.session(), &first).is_some_and(|effects| effects.allocates));
        assert!(memo_effects(&driver.session(), &second).is_some_and(|effects| effects.allocates));
        let expected_dependencies = HashSet::from([
            ProductKey::MaterializedExecutable(first.clone()),
            ProductKey::MaterializedExecutable(second.clone()),
            ProductKey::ExecutableEffects(leaf),
        ]);
        for member in [&first, &second] {
            let dependencies = driver
                .session()
                .memo()
                .product_dependencies(&ProductKey::ExecutableEffects(member.clone()))
                .expect("every recursive member has a dependency snapshot")
                .keys()
                .cloned()
                .collect::<HashSet<_>>();
            assert_eq!(
                dependencies, expected_dependencies,
                "the group retains exactly the external inputs of its member formulas"
            );
        }
        assert_eq!(driver.session().producer_pokes(), 0);
    }

    #[test]
    fn executable_effects_selects_the_group_after_all_direct_reads() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(88);
        let anchor = fake_executable_with_function(root, 880);
        let first = fake_executable_with_function(root, 881);
        let second = fake_executable_with_function(root, 882);
        let mut driver = ProductDriver::new(&tel, root);
        record_effect_product(&mut driver.session_mut(), &anchor, &[&first, &second], false);
        record_effect_product(&mut driver.session_mut(), &first, &[&anchor], false);
        record_effect_product(&mut driver.session_mut(), &second, &[&anchor], true);
        let mut world = World::new();
        for member in [&first, &second] {
            let outcome = {
                let mut producers = WorldProductProducers::new(&mut world, &tel);
                driver.pull(&mut producers, ProductKey::ExecutableEffects(member.clone()))
            };
            assert_eq!(
                outcome,
                PullOutcome::wait_on_product(ProductKey::ExecutableEffects(anchor.clone()))
            );
        }

        let effects = pull_effects_until_produced(&mut driver, &mut world, &anchor);

        assert!(effects.allocates);
        let expected_dependencies = HashSet::from([
            ProductKey::MaterializedExecutable(anchor.clone()),
            ProductKey::MaterializedExecutable(first.clone()),
            ProductKey::MaterializedExecutable(second.clone()),
        ]);
        for member in [&anchor, &first, &second] {
            assert_eq!(
                driver
                    .session()
                    .memo()
                    .product_dependencies(&ProductKey::ExecutableEffects(member.clone()))
                    .expect("every member of the complete group must settle")
                    .keys()
                    .cloned()
                    .collect::<HashSet<_>>(),
                expected_dependencies
            );
            assert!(memo_effects(&driver.session(), member).is_some_and(|effects| effects.allocates));
        }
    }

    #[test]
    fn executable_effects_self_cycle_uses_the_generic_recursive_group() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(89);
        let executable = fake_executable_with_function(root, 890);
        let mut driver = ProductDriver::new(&tel, root);
        record_effect_product(&mut driver.session_mut(), &executable, &[&executable], true);
        let mut world = World::new();

        assert_eq!(
            pull_effects_until_produced(&mut driver, &mut world, &executable),
            EffectSummary {
                allocates: true,
                ..EffectSummary::default()
            }
        );
        assert_eq!(
            driver
                .session()
                .memo()
                .product_dependencies(&ProductKey::ExecutableEffects(executable.clone()))
                .expect("self-recursive effects settle with one external dependency snapshot")
                .keys()
                .cloned()
                .collect::<HashSet<_>>(),
            HashSet::from([ProductKey::MaterializedExecutable(executable)])
        );
    }

    #[test]
    fn unchanged_local_effect_reproduces_once_without_waking_its_caller() {
        let tel = ConfiguredTelemetry::new();
        let evaluations = capture_product_evaluations(&tel);
        let root = RootId::for_test(90);
        let caller = fake_executable_with_function(root, 90);
        let callee = fake_executable_with_function(root, 91);
        let mut driver = ProductDriver::new(&tel, root);
        record_effect_product(&mut driver.session_mut(), &caller, &[&callee], false);
        let callee_materialized = fake_effect_materialized(&callee, &[], false);
        record_materialized_product(&mut driver.session_mut(), callee.clone(), callee_materialized.clone());
        let mut world = World::new();
        assert_eq!(
            pull_effects_until_produced(&mut driver, &mut world, &caller),
            EffectSummary::default()
        );
        let callee_generation = driver
            .session()
            .memo()
            .generation(&ProductKey::ExecutableEffects(callee.clone()));
        let caller_generation = driver
            .session()
            .memo()
            .generation(&ProductKey::ExecutableEffects(caller.clone()));
        evaluations.borrow_mut().clear();

        let mut changed_materialized = callee_materialized;
        changed_materialized.original_entry_ids = vec![ControlEntryId::from_u32(17)];
        record_materialized_product(&mut driver.session_mut(), callee.clone(), changed_materialized);

        assert_eq!(
            pull_effects_until_produced(&mut driver, &mut world, &caller),
            EffectSummary::default()
        );
        assert_eq!(
            evaluations.borrow().as_slice(),
            &[ProductKey::ExecutableEffects(callee.clone())],
            "the moved local product must re-evaluate its formula without re-evaluating an unchanged dependent"
        );
        assert_eq!(
            driver
                .session()
                .memo()
                .generation(&ProductKey::ExecutableEffects(callee)),
            callee_generation,
            "equal effect reproduction preserves its generation"
        );
        assert_eq!(
            driver
                .session()
                .memo()
                .generation(&ProductKey::ExecutableEffects(caller)),
            caller_generation
        );
    }

    #[test]
    fn effect_dependencies_follow_edge_add_remove_and_changed_leaf_exactly() {
        let tel = ConfiguredTelemetry::new();
        let evaluations = capture_product_evaluations(&tel);
        let root = RootId::for_test(93);
        let grand = fake_executable_with_function(root, 93);
        let caller = fake_executable_with_function(root, 94);
        let callee = fake_executable_with_function(root, 95);
        let unreachable = fake_executable_with_function(root, 96);
        let mut driver = ProductDriver::new(&tel, root);
        record_effect_product(&mut driver.session_mut(), &grand, &[&caller], false);
        record_effect_product(&mut driver.session_mut(), &caller, &[], false);
        record_effect_product(&mut driver.session_mut(), &callee, &[], false);
        record_effect_product(&mut driver.session_mut(), &unreachable, &[], false);
        let mut world = World::new();
        for executable in [&grand, &callee, &unreachable] {
            assert_eq!(
                pull_effects_until_produced(&mut driver, &mut world, executable),
                EffectSummary::default()
            );
        }

        evaluations.borrow_mut().clear();
        record_effect_product(&mut driver.session_mut(), &caller, &[&callee], false);
        assert_eq!(
            pull_effects_until_produced(&mut driver, &mut world, &grand),
            EffectSummary::default()
        );
        assert_eq!(
            evaluations.borrow().as_slice(),
            &[ProductKey::ExecutableEffects(caller.clone())],
            "adding an effect-free edge re-evaluates its owner, while equal retention keeps its caller quiet"
        );

        evaluations.borrow_mut().clear();
        record_effect_product(&mut driver.session_mut(), &callee, &[], true);
        let allocating = EffectSummary {
            allocates: true,
            ..EffectSummary::default()
        };
        assert_eq!(pull_effects_until_produced(&mut driver, &mut world, &grand), allocating);
        assert_eq!(
            evaluations.borrow().as_slice(),
            &[
                ProductKey::ExecutableEffects(callee.clone()),
                ProductKey::ExecutableEffects(caller.clone()),
                ProductKey::ExecutableEffects(grand.clone()),
            ],
            "a changed leaf re-evaluates only the exact reverse dependents"
        );

        evaluations.borrow_mut().clear();
        record_effect_product(&mut driver.session_mut(), &caller, &[], false);
        assert_eq!(
            pull_effects_until_produced(&mut driver, &mut world, &grand),
            EffectSummary::default()
        );
        assert_eq!(
            evaluations.borrow().as_slice(),
            &[
                ProductKey::ExecutableEffects(caller),
                ProductKey::ExecutableEffects(grand.clone()),
            ],
            "removing the edge re-evaluates its owner and the dependent whose answer changes"
        );

        evaluations.borrow_mut().clear();
        record_effect_product(&mut driver.session_mut(), &callee, &[], false);
        assert_eq!(
            pull_effects_until_produced(&mut driver, &mut world, &callee),
            EffectSummary::default()
        );
        assert_eq!(
            pull_effects_until_produced(&mut driver, &mut world, &grand),
            EffectSummary::default()
        );
        assert_eq!(
            pull_effects_until_produced(&mut driver, &mut world, &unreachable),
            EffectSummary::default()
        );
        assert_eq!(
            evaluations.borrow().as_slice(),
            &[ProductKey::ExecutableEffects(callee)],
            "after edge removal, neither former dependents nor unreachable products re-evaluate"
        );
    }

    #[test]
    fn displaced_effect_dependencies_cannot_close_a_reversed_edge_cycle() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(97);
        let first = fake_executable_with_function(root, 970);
        let second = fake_executable_with_function(root, 971);
        let mut driver = ProductDriver::new(&tel, root);
        record_effect_product(&mut driver.session_mut(), &first, &[], true);
        record_effect_product(&mut driver.session_mut(), &second, &[&first], false);
        let mut world = World::new();
        assert!(pull_effects_until_produced(&mut driver, &mut world, &second).allocates);

        record_effect_product(&mut driver.session_mut(), &first, &[&second], true);
        record_effect_product(&mut driver.session_mut(), &second, &[], false);

        assert!(pull_effects_until_produced(&mut driver, &mut world, &first).allocates);
        assert_eq!(
            memo_effects(&driver.session(), &second),
            Some(EffectSummary::default()),
            "the displaced second formula's retired edge must not make it a member of the reversed dependency"
        );
        assert_eq!(
            driver
                .session()
                .memo()
                .product_dependencies(&ProductKey::ExecutableEffects(second.clone()))
                .expect("the second effects formula must settle independently")
                .keys()
                .cloned()
                .collect::<HashSet<_>>(),
            HashSet::from([ProductKey::MaterializedExecutable(second.clone())])
        );
        assert_eq!(
            driver
                .session()
                .memo()
                .product_dependencies(&ProductKey::ExecutableEffects(first.clone()))
                .expect("the first effects formula must retain its new edge")
                .keys()
                .cloned()
                .collect::<HashSet<_>>(),
            HashSet::from([
                ProductKey::MaterializedExecutable(first),
                ProductKey::ExecutableEffects(second),
            ])
        );
    }

    #[test]
    fn dirty_external_chain_retracts_a_pending_effect_group_snapshot() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(98);
        let leaf = fake_executable_with_function(root, 980);
        let external = fake_executable_with_function(root, 981);
        let anchor = fake_executable_with_function(root, 982);
        let peer = fake_executable_with_function(root, 983);
        let mut driver = ProductDriver::new(&tel, root);
        record_effect_product(&mut driver.session_mut(), &leaf, &[], true);
        record_effect_product(&mut driver.session_mut(), &external, &[&leaf], false);
        record_effect_product(&mut driver.session_mut(), &anchor, &[&peer], false);
        record_effect_product(&mut driver.session_mut(), &peer, &[&external, &anchor], false);
        let mut world = World::new();
        assert!(pull_effects_until_produced(&mut driver, &mut world, &external).allocates);
        let pending = {
            let mut producers = WorldProductProducers::new(&mut world, &tel);
            driver.pull(&mut producers, ProductKey::ExecutableEffects(peer.clone()))
        };
        assert_eq!(
            pending,
            PullOutcome::wait_on_product(ProductKey::ExecutableEffects(anchor.clone()))
        );

        record_effect_product(&mut driver.session_mut(), &leaf, &[], false);

        assert_eq!(
            pull_effects_until_produced(&mut driver, &mut world, &anchor),
            EffectSummary::default(),
            "the group must wait for the dirty external chain instead of publishing its stale effect"
        );
        assert_eq!(
            driver
                .session()
                .memo()
                .generation(&ProductKey::ExecutableEffects(leaf.clone())),
            Some(2)
        );
        assert_eq!(
            driver
                .session()
                .memo()
                .generation(&ProductKey::ExecutableEffects(external.clone())),
            Some(2)
        );
        let session = driver.session();
        let group_dependencies = session
            .memo()
            .product_dependencies(&ProductKey::ExecutableEffects(anchor.clone()))
            .expect("the refreshed group must settle");
        assert_eq!(
            group_dependencies.keys().cloned().collect::<HashSet<_>>(),
            HashSet::from([
                ProductKey::MaterializedExecutable(anchor),
                ProductKey::MaterializedExecutable(peer),
                ProductKey::ExecutableEffects(external.clone()),
            ])
        );
        assert_eq!(
            group_dependencies.get(&ProductKey::ExecutableEffects(external.clone())),
            Some(&Some(2))
        );
        assert_eq!(
            driver
                .session()
                .memo()
                .product_dependencies(&ProductKey::ExecutableEffects(external))
                .expect("the external formula must refresh after its leaf")
                .get(&ProductKey::ExecutableEffects(leaf)),
            Some(&Some(2))
        );
    }

    #[test]
    fn pull_session_lifecycle_finishes_on_drop_and_reports_producer_pokes() {
        let tel = ConfiguredTelemetry::new();
        let observed = Rc::new(Cell::new(None));
        let sink = Rc::clone(&observed);
        tel.attach_raw_event1::<PullSession, _>(
            &["fz", "compiler2", "pull", "session", "finished"],
            move |_, _, _, session| {
                sink.set(Some((
                    session.id().expect("emitted sessions have identities"),
                    session.demanded_executables.len(),
                    session.producer_pokes,
                )));
            },
        );
        let root = RootId::for_test(5);
        let executable = fake_executable(root);
        let mut driver = ProductDriver::new(&tel, root);
        let mut producers = FakeProducers::default();

        assert_eq!(
            driver.pull(&mut producers, ProductKey::AbiExecutable(executable)),
            PullOutcome::Produced(ProductValue::Unit)
        );
        driver.session_mut().record_producer_pokes(2);
        let session_id = driver.session().id().expect("enabled session telemetry");
        drop(driver);

        assert_eq!(observed.get(), Some((session_id, 1, 2)));
        let second = ProductDriver::new(&tel, RootId::for_test(6));
        let second_id = second.session().id().expect("enabled session telemetry");
        drop(second);
        assert_ne!(second_id, session_id);
    }

    #[test]
    fn pull_session_id_exhaustion_never_wraps_or_emits_a_reserved_identity() {
        let counter = AtomicU64::new(u64::MAX - 1);
        assert_eq!(allocate_pull_session_id(&counter).get(), u64::MAX - 1);
        assert_eq!(allocate_pull_session_id(&counter).get(), u64::MAX);
        assert_eq!(counter.load(Ordering::Relaxed), 0);
        assert!(catch_unwind(|| allocate_pull_session_id(&counter)).is_err());
        assert_eq!(counter.load(Ordering::Relaxed), 0, "exhaustion must be permanent");

        let tel = ConfiguredTelemetry::new();
        let starts = Rc::new(Cell::new(0));
        let observed = Rc::clone(&starts);
        tel.attach_raw_event1::<PullSessionId, _>(SESSION_STARTED_EVENT, move |_, _, _, _| {
            observed.set(observed.get() + 1);
        });
        let result = catch_unwind(AssertUnwindSafe(|| {
            ProductDriver::with_session_id_source(&tel, PullSession::new(RootId::for_test(8)), || {
                panic!("pull session identity exhausted")
            })
        }));
        assert!(result.is_err());
        assert_eq!(starts.get(), 0, "identity exhaustion must precede session telemetry");
    }

    #[test]
    fn product_request_id_exhaustion_precedes_telemetry_and_cannot_reuse_zero() {
        let tel = ConfiguredTelemetry::new();
        let requests = Rc::new(RefCell::new(Vec::new()));
        let observed = Rc::clone(&requests);
        tel.attach_raw_event2::<ProductKey, ProductRequestId, _>(
            PRODUCT_REQUESTED_EVENT,
            move |_, _, _, _, request| observed.borrow_mut().push(*request),
        );
        let root = RootId::for_test(9);
        let key = ProductKey::AbiExecutable(fake_executable(root));
        let mut driver = ProductDriver::new(&tel, root);
        driver.session_mut().request_ids.next = NonZeroU64::new(u64::MAX);
        let mut producers = FakeProducers::default();

        assert_eq!(
            driver.pull(&mut producers, key.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(
            requests
                .borrow()
                .iter()
                .map(|request| request.get())
                .collect::<Vec<_>>(),
            [u64::MAX]
        );
        assert!(
            catch_unwind(AssertUnwindSafe(|| driver.pull(&mut producers, key))).is_err(),
            "the request after the last nonzero identity must fail"
        );
        assert_eq!(
            requests
                .borrow()
                .iter()
                .map(|request| request.get())
                .collect::<Vec<_>>(),
            [u64::MAX],
            "exhaustion must happen before a request event"
        );
        assert!(
            driver.session().request_ids.next.is_none(),
            "exhaustion must be permanent"
        );
    }

    #[test]
    fn disabled_telemetry_does_not_mint_a_session_identity() {
        let driver = ProductDriver::new(&crate::telemetry::sink::NullTelemetry, RootId::for_test(5));
        assert_eq!(driver.session().id(), None);

        let configured = ConfiguredTelemetry::new();
        let driver = ProductDriver::new(&configured, RootId::for_test(5));
        assert_eq!(driver.session().id(), None);
    }

    fn fake_executable(root: RootId) -> ExecutableKey {
        fake_executable_with_function(root, root.as_u32() + 10)
    }

    fn fake_executable_with_function(root: RootId, function: u32) -> ExecutableKey {
        let mut types = super::super::Types::new();
        fake_executable_in(&mut types, root, function)
    }

    fn fake_executable_in(types: &mut super::super::Types, root: RootId, function: u32) -> ExecutableKey {
        let function = super::super::FunctionId::for_test(function);
        let activation = super::super::ActivationKey::from_inputs(root, function, &[], types);
        ExecutableKey {
            activation,
            need: super::super::ExecutableNeed::Value,
        }
    }

    fn fake_types() -> super::super::Types {
        let mut types = super::super::Types::new();
        let _ = super::super::ActivationKey::from_inputs(
            RootId::for_test(0),
            super::super::FunctionId::for_test(0),
            &[],
            &mut types,
        );
        types
    }

    fn record_materialized_product(
        session: &mut PullSession,
        executable: ExecutableKey,
        materialized: MaterializedExecutable,
    ) {
        let tel = ConfiguredTelemetry::new();
        finish_test_entry(
            &mut session.memo,
            &tel,
            &ProductKey::MaterializedExecutable(executable),
            ProductValue::MaterializedExecutable(Rc::new(materialized)),
            ProductDependencies::default(),
            &fake_types(),
        );
    }

    fn record_effect_product(
        session: &mut PullSession,
        executable: &ExecutableKey,
        callees: &[&ExecutableKey],
        allocates: bool,
    ) {
        record_materialized_product(
            session,
            executable.clone(),
            fake_effect_materialized(executable, callees, allocates),
        );
    }

    fn memo_effects(session: &PullSession, executable: &ExecutableKey) -> Option<EffectSummary> {
        match session.memo().get(&ProductKey::ExecutableEffects(executable.clone())) {
            Some(ProductValue::ExecutableEffects(effects)) => Some(*effects),
            _ => None,
        }
    }

    fn pull_effects_until_produced(
        driver: &mut ProductDriver<'_, ConfiguredTelemetry>,
        world: &mut World,
        executable: &ExecutableKey,
    ) -> EffectSummary {
        let requested = ProductKey::ExecutableEffects(executable.clone());
        let mut stack = vec![requested.clone()];
        while let Some(key) = stack.pop() {
            let outcome = {
                let mut producers = WorldProductProducers::new(world, driver.telemetry());
                driver.pull(&mut producers, key.clone())
            };
            match outcome {
                PullOutcome::Produced(ProductValue::ExecutableEffects(effects)) if key == requested => {
                    return effects;
                }
                PullOutcome::Produced(ProductValue::ExecutableEffects(_)) => {}
                PullOutcome::Produced(other) => panic!("effect pull produced unexpected value {other:?}"),
                PullOutcome::Waiting(waits) => {
                    stack.push(key);
                    for wait in waits.into_iter().rev() {
                        match wait {
                            PullWait::Product(product) => stack.push(product),
                            PullWait::Fact(fact) => panic!("effect-only fixture unexpectedly waited on {fact:?}"),
                        }
                    }
                }
                PullOutcome::Failed(failure) => panic!("effect product failed: {failure:?}"),
            }
        }
        unreachable!("the requested effects product remains on the work stack until it settles")
    }

    fn capture_product_evaluations(tel: &ConfiguredTelemetry) -> Rc<RefCell<Vec<ProductKey>>> {
        let evaluations = Rc::new(RefCell::new(Vec::new()));
        let sink = Rc::clone(&evaluations);
        tel.attach_raw_event3::<ProductKey, ProductRequestId, PullOutcome, _>(
            PRODUCT_EVALUATED_EVENT,
            move |_, _, _, product, _, _| sink.borrow_mut().push(product.clone()),
        );
        evaluations
    }

    /// Build production-consistent effect inputs: the stored projection and
    /// the body from which the effect product derives it always agree.
    fn fake_effect_materialized(
        executable: &ExecutableKey,
        callees: &[&ExecutableKey],
        allocates: bool,
    ) -> MaterializedExecutable {
        let executable = executable_symbol_for_test(executable);
        let effects = EffectSummary {
            allocates,
            ..EffectSummary::default()
        };
        let projections = if allocates {
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
            return_ty: effect_test_ty(),
            runtime_demand: Rc::new(ExecutableRuntimeDemand::default()),
            transport: MaterializedExecutableTransport {
                executable: executable.clone(),
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
            struct_modules: Box::default(),
            body: super::super::LoweredBody::Clauses {
                clauses: vec![LoweredClause {
                    span: crate::source::Span::DUMMY,
                    params: Vec::new(),
                    projections,
                    entry: ControlEntryId::from_u32(0),
                }],
                entries: vec![LoweredEntry {
                    span: crate::source::Span::DUMMY,
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
            call_edges: callees
                .iter()
                .enumerate()
                .map(|(index, callee)| {
                    (
                        CallSiteId::from_u32(index as u32),
                        fake_effect_edge(
                            (*callee).clone(),
                            executable.clone(),
                            executable_symbol_for_test(callee),
                        ),
                    )
                })
                .collect(),
        }
    }

    fn fake_effect_edge(
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
            return_ty: effect_test_ty(),
        }
    }

    fn effect_test_ty() -> super::super::Ty {
        let mut types = super::super::Types::new();
        types.none()
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
        ProductValue::CallableConstruction(Rc::new(CallableConstructionOwner {
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
        ProductValue::CallableConstruction(Rc::new(CallableConstructionOwner {
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
        let tel = ConfiguredTelemetry::new();
        assert!(memo.begin(key.clone()));
        let products = dependencies
            .into_iter()
            .map(|dependency| {
                let generation = memo.generation(&dependency);
                (dependency, generation)
            })
            .collect();
        assert!(finish_test_entry(
            memo,
            &tel,
            key,
            value,
            ProductDependencies {
                products,
                facts: HashMap::new(),
            },
            &fake_types(),
        ));
    }

    #[test]
    fn callable_owner_products_aggregate_order_free_and_retract_independently() {
        let types = fake_types();
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
            capture_layouts: Box::default(),
        });
        let boundary = BoundaryId::for_test(8);
        let layout = TransportLayout::structural(ShapeId::for_test(9));
        let left_key = ProductKey::CallableConstruction(left_position.clone());
        let right_key = ProductKey::CallableConstruction(right_position.clone());
        let left_abi = ProductKey::AbiExecutable(fake_executable_with_function(root, 350));
        let right_abi = ProductKey::AbiExecutable(fake_executable_with_function(root, 351));
        let root_key = ProductKey::RootBackendProduct(root);
        let mut memo = ProductMemo::default();
        let tel = ConfiguredTelemetry::new();

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
            ProductValue::RootBackendProduct(RootBackendProductAnswer {
                program: Rc::new(super::super::artifact::BackendProgram::empty_for_test()),
                transport: Rc::new(super::super::artifact::MaterializedTransportPlan {
                    entry: left_resolution.clone(),
                    executable_membership: Box::default(),
                    position_layouts: Vec::new(),
                    callable_boundaries: Vec::new(),
                    boundary_ids: Vec::new(),
                    codegen_seam_facts: Box::default(),
                    callable_owners: Box::default(),
                    callable_facts: HashMap::new(),
                    boundary_facts: HashMap::new(),
                }),
            }),
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
        memo.remove(&tel, &left_key, &types);
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
        assert!(memo.stale_dependency(&left_abi, &types).is_some());
        assert!(memo.stale_dependency(&right_abi, &types).is_none());
        assert!(memo.stale_dependency(&root_key, &types).is_some());

        let reproduced = memo.get(&left_key).cloned().expect("replaced owner product");
        memo.remove(&tel, &left_key, &types);
        finish_test_product(&mut memo, &left_key, reproduced, []);
        assert_eq!(memo.generation(&left_key), replaced_generation);
        assert_eq!(memo.generation(&right_key), right_generation);

        memo.remove(&tel, &left_key, &types);
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
            ProductValue::CallableConstruction(Rc::new(CallableConstructionOwner {
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
        let tel = ConfiguredTelemetry::new();
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
        assert!(finish_test_group(
            memo,
            &tel,
            keys.first().expect("owner group is non-empty"),
            entries,
            &fake_types(),
        ));
    }

    #[test]
    fn transport_shape_group_retains_every_external_dependency_for_every_member() {
        let types = fake_types();
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
        let external = ProductKey::TransportShape(TransportPosition::ExecutableReturn {
            executable: executable_symbol_for_test(&fake_executable_with_function(root, 381)),
        });
        let left_reader = ProductKey::AbiExecutable(fake_executable_with_function(root, 382));
        let right_reader = ProductKey::AbiExecutable(fake_executable_with_function(root, 383));
        let unrelated = ProductKey::AbiExecutable(fake_executable_with_function(root, 384));
        let first_layout = TransportLayout::structural(ShapeId::for_test(110));
        let second_layout = TransportLayout::structural(ShapeId::for_test(111));
        let external_value = |shape| {
            ProductValue::TransportShape(TransportShapeFact::Layout(TransportLayout::structural(
                ShapeId::for_test(shape),
            )))
        };

        for reverse in [false, true] {
            let mut memo = ProductMemo::default();
            let tel = ConfiguredTelemetry::new();
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
            assert!(finish_test_group(&mut memo, &tel, &left, entries, &types));
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

            memo.remove(&tel, &external, &types);
            finish_test_product(&mut memo, &external, external_value(386), []);
            assert!(memo.get(&left).is_none());
            assert!(memo.get(&right).is_none());
            assert!(memo.get(&unrelated).is_some());

            for key in [&left, &right] {
                assert!(memo.begin(key.clone()));
            }
            let left_generation = memo.generation(&left);
            let right_generation = memo.generation(&right);
            let external_generation = memo.generation(&external);
            assert!(finish_test_group(
                &mut memo,
                &tel,
                &left,
                vec![
                    (
                        left.clone(),
                        ProductValue::TransportShape(TransportShapeFact::Layout(second_layout)),
                        ProductDependencies {
                            products: HashMap::from([
                                (right.clone(), right_generation),
                                (external.clone(), external_generation),
                            ]),
                            facts: HashMap::new(),
                        },
                    ),
                    (
                        right.clone(),
                        ProductValue::TransportShape(TransportShapeFact::Layout(second_layout)),
                        ProductDependencies {
                            products: HashMap::from([(left.clone(), left_generation)]),
                            facts: HashMap::new(),
                        },
                    ),
                ],
                &types,
            ));
            assert_eq!(memo.generation(&left), Some(2));
            assert_eq!(memo.generation(&right), Some(2));
            assert!(memo.get(&left_reader).is_none());
            assert!(memo.get(&right_reader).is_none());
            assert_eq!(memo.generation(&unrelated), unrelated_generation);
        }
    }

    /// fz-kdt.34.4 TDD 4: a group settle must emit one `pull.product.settled`
    /// event PER MEMBER (not just the anchor `finish_completion` was called for),
    /// each carrying its own generation and changed flag, all sharing one
    /// `group` id -- and a second, independent group settle must get a
    /// DIFFERENT group id. Red before fz-kdt.34.4: only the driver's single
    /// anchor-keyed event existed, and it carried no generation/changed/group
    /// at all.
    #[test]
    fn group_settle_emits_one_settled_event_per_member_with_shared_generation_and_group() {
        let tel = ConfiguredTelemetry::new();
        let events: Rc<RefCell<Vec<(ProductKey, ProductValue, ProductSettlement)>>> = Rc::new(RefCell::new(Vec::new()));
        let sink = Rc::clone(&events);
        tel.attach_raw_event3::<ProductKey, ProductValue, ProductSettlement, _>(
            &["fz", "compiler2", "pull", "product", "settled"],
            move |_, _, _, key, value, settlement| {
                sink.borrow_mut().push((key.clone(), value.clone(), *settlement));
            },
        );

        let root = RootId::for_test(60);
        let left = ProductKey::AbiExecutable(fake_executable_with_function(root, 600));
        let right = ProductKey::AbiExecutable(fake_executable_with_function(root, 601));
        let mut memo = ProductMemo::default();

        let first_value = ProductValue::ExecutableEffects(EffectSummary::default());
        let second_value = ProductValue::ExecutableEffects(EffectSummary {
            allocates: true,
            ..EffectSummary::default()
        });

        for key in [&left, &right] {
            assert!(memo.begin(key.clone()));
        }
        assert!(finish_test_group(
            &mut memo,
            &tel,
            &left,
            vec![
                (left.clone(), first_value.clone(), ProductDependencies::default()),
                (right.clone(), first_value.clone(), ProductDependencies::default()),
            ],
            &fake_types(),
        ));

        let first_group_events = events.borrow().clone();
        assert_eq!(
            first_group_events.len(),
            2,
            "a group settle must emit one settled event per member, not just the anchor"
        );
        let first_group_id = first_group_events[0]
            .2
            .group
            .expect("group settlement carries a group id");
        for (key, value, settlement) in &first_group_events {
            assert!(*key == left || *key == right);
            assert_eq!(*value, first_value);
            assert_eq!(settlement.generation, 1, "a first-time settle starts at generation 1");
            assert!(settlement.changed, "a first-time settle is always a change");
            assert_eq!(settlement.group, Some(first_group_id));
        }

        events.borrow_mut().clear();

        for key in [&left, &right] {
            assert!(memo.begin(key.clone()));
        }
        assert!(finish_test_group(
            &mut memo,
            &tel,
            &left,
            vec![
                (left.clone(), first_value, ProductDependencies::default()),
                (right.clone(), second_value, ProductDependencies::default()),
            ],
            &fake_types(),
        ));

        let second_group_events = events.borrow().clone();
        assert_eq!(second_group_events.len(), 2);
        let second_group_id = second_group_events[0]
            .2
            .group
            .expect("group settlement carries a group id");
        assert_ne!(
            second_group_id, first_group_id,
            "a second, independent group settle must get a distinct group id"
        );
        let left_settlement = &second_group_events
            .iter()
            .find(|(key, _, _)| *key == left)
            .expect("left member should have settled")
            .2;
        let right_settlement = &second_group_events
            .iter()
            .find(|(key, _, _)| *key == right)
            .expect("right member should have settled")
            .2;
        assert_eq!(
            left_settlement.generation, 1,
            "a reproduced-unchanged member keeps its prior generation"
        );
        assert!(
            !left_settlement.changed,
            "a reproduced-unchanged member's changed flag is false"
        );
        assert_eq!(right_settlement.generation, 2, "a changed member's generation advances");
        assert!(right_settlement.changed, "a changed member's changed flag is true");
        assert_eq!(left_settlement.group, Some(second_group_id));
        assert_eq!(right_settlement.group, Some(second_group_id));
    }

    #[test]
    fn recursive_group_members_share_one_dependency_snapshot() {
        let tel = ConfiguredTelemetry::new();
        let types = fake_types();
        let root = RootId::for_test(61);
        let left = ProductKey::AbiExecutable(fake_executable_with_function(root, 610));
        let right = ProductKey::AbiExecutable(fake_executable_with_function(root, 611));
        let external = ProductKey::AbiExecutable(fake_executable_with_function(root, 612));
        let dependencies = ProductDependencies {
            products: HashMap::from([(external, Some(7))]),
            facts: HashMap::new(),
        };
        let mut memo = ProductMemo::default();
        assert!(memo.begin(left.clone()));
        assert!(memo.begin(right.clone()));
        assert!(finish_test_group(
            &mut memo,
            &tel,
            &left,
            vec![
                (left.clone(), ProductValue::Unit, dependencies.clone()),
                (right.clone(), ProductValue::Unit, dependencies),
            ],
            &types,
        ));
        let left_dependencies = &memo.produced[&left].dependencies;
        let right_dependencies = &memo.produced[&right].dependencies;
        assert!(
            Rc::ptr_eq(left_dependencies, right_dependencies),
            "one recursive publication must retain one shared dependency snapshot",
        );
    }

    #[test]
    fn changed_product_authority_discards_pending_reader_snapshots_before_group_settlement() {
        let types = fake_types();
        let root = RootId::for_test(39);
        let external = ProductKey::AbiExecutable(fake_executable_with_function(root, 390));
        let left = ProductKey::AbiExecutable(fake_executable_with_function(root, 391));
        let right = ProductKey::AbiExecutable(fake_executable_with_function(root, 392));
        let unrelated = ProductKey::AbiExecutable(fake_executable_with_function(root, 393));
        let first = ProductValue::ExecutableEffects(EffectSummary::default());
        let second = ProductValue::ExecutableEffects(EffectSummary {
            allocates: true,
            ..EffectSummary::default()
        });

        for reverse in [false, true] {
            let mut memo = ProductMemo::default();
            let tel = ConfiguredTelemetry::new();
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

            memo.remove(&tel, &external, &types);
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
            assert!(finish_test_group(&mut memo, &tel, &left, entries, &types));
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
        let types = fake_types();
        let root = RootId::for_test(40);
        let reader = ProductKey::AbiExecutable(fake_executable_with_function(root, 400));
        let unrelated = ProductKey::AbiExecutable(fake_executable_with_function(root, 401));
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
        let tel = ConfiguredTelemetry::new();
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

        memo.reconcile_fact_movements(&tel, &HashMap::from([(fact.fact().clone(), first)]), &types);
        assert!(memo.pending_dependencies.contains_key(&reader));
        memo.reconcile_fact_movements(&tel, &HashMap::from([(fact.fact().clone(), second)]), &types);

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
        let left = ProductKey::AbiExecutable(fake_executable_with_function(root, 410));
        let right = ProductKey::AbiExecutable(fake_executable_with_function(root, 411));
        let external = ProductKey::AbiExecutable(fake_executable_with_function(root, 412));
        let unrelated = ProductKey::AbiExecutable(fake_executable_with_function(root, 413));
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
                let tel = ConfiguredTelemetry::new();
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

                assert!(!finish_test_group(&mut memo, &tel, &left, entries, &fake_types()));
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
                assert!(finish_test_group(
                    &mut memo,
                    &tel,
                    &left,
                    vec![
                        (left.clone(), ProductValue::Unit, concordant.clone()),
                        (right.clone(), ProductValue::Unit, concordant),
                    ],
                    &fake_types(),
                ));
            }
        }
    }

    #[test]
    fn rejected_group_retries_without_displaced_dependency_snapshots() {
        let types = fake_types();
        let root = RootId::for_test(42);
        let left = ProductKey::AbiExecutable(fake_executable_with_function(root, 420));
        let right = ProductKey::AbiExecutable(fake_executable_with_function(root, 421));
        let external = ProductKey::AbiExecutable(fake_executable_with_function(root, 422));

        for reverse in [false, true] {
            let mut memo = ProductMemo::default();
            let tel = ConfiguredTelemetry::new();
            for key in [&left, &right] {
                assert!(memo.begin(key.clone()));
            }
            let first = ProductDependencies {
                products: HashMap::from([(external.clone(), Some(1))]),
                facts: HashMap::new(),
            };
            assert!(finish_test_group(
                &mut memo,
                &tel,
                &left,
                vec![
                    (left.clone(), ProductValue::Unit, first.clone()),
                    (right.clone(), ProductValue::Unit, first),
                ],
                &types,
            ));
            for key in [&left, &right] {
                memo.remove(&tel, key, &types);
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
                (left.clone(), ProductValue::Unit, stale.as_ref().clone()),
                (right.clone(), ProductValue::Unit, current.clone()),
            ];
            if reverse {
                entries.reverse();
            }
            assert!(!finish_test_group(&mut memo, &tel, &left, entries, &types));

            for key in [&left, &right] {
                let displaced = memo
                    .displaced
                    .get(key)
                    .expect("rejected member should retain its prior value and generation");
                assert_eq!(displaced.generation, 1);
                assert_eq!(displaced.dependencies.as_ref(), &ProductDependencies::default());
                assert!(memo.begin(key.clone()));
            }
            assert!(finish_test_group(
                &mut memo,
                &tel,
                &left,
                vec![
                    (left.clone(), ProductValue::Unit, current.clone()),
                    (right.clone(), ProductValue::Unit, current),
                ],
                &types,
            ));
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
            carrier: TransportCarrier::ValueRef(LaneId::for_test(0)),
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
            capture_layouts: Box::default(),
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
        let types = fake_types();
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
        let slot = ProductKey::TransportShape(x_position.clone());
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
            capture_layouts: Box::default(),
        });
        let boundary = BoundaryId::for_test(10);
        let layout = TransportLayout {
            structural: ShapeId::for_test(101),
            carrier: TransportCarrier::ValueRef(LaneId::for_test(0)),
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
        let slot_value = ProductValue::TransportShape(TransportShapeFact::Layout(layout));

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
        let tel = ConfiguredTelemetry::new();
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
            memo.remove(&tel, key, &types);
        }
        finish_owner_group(&mut memo, &keys, &first_answers, &external, callable, boundary, true);
        assert_eq!(keys.clone().map(|key| memo.generation(&key)), generations);

        let replacement_position = TransportPosition::Value {
            executable: executable_symbol_for_test(&fake_executable_with_function(root, 371)),
            value: ValueId::from_u32(2),
        };
        memo.remove(&tel, &terminal, &types);
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
        assert!(memo.stale_dependency(&parent, &types).is_some());
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

        memo.remove(&tel, &terminal, &types);
        finish_test_product(
            &mut memo,
            &terminal,
            callable_owner_answer(layout, replacement_position, callable, boundary, second_resolution),
            [],
        );
        assert!(keys.iter().all(|key| memo.generation(key) == Some(2)));

        memo.remove(&tel, &terminal, &types);
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

        memo.remove(&tel, &slot, &types);
        finish_test_product(
            &mut memo,
            &slot,
            ProductValue::TransportShape(TransportShapeFact::Layout(TransportLayout {
                structural: ShapeId::for_test(102),
                ..layout
            })),
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
