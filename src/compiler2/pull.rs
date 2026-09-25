//! Product-keyed pull substrate for compiler2 artifacts.
//!
//! This module is intentionally separate from the existing job scheduler. A
//! product producer answers one named demand and can only return a value or
//! explicit waits. It does not enqueue jobs, schedule follow-up work, or scan a
//! root frontier.

mod rooted;

use indexmap::IndexMap;

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
};
use super::drive::{DependencyKey, FactKey, ProductAddress};
use super::executable_facts::ExecutableFacts;
use super::facts::{FactChange, FactMovement, FactState, FactUse};
use super::identity::{ExecutableKey, ModuleId, RootId};
use super::ordered_worklist::OrderedWorklist;
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
const RECURSIVE_GROUP_PUBLISHED_EVENT: &[&str] = &["fz", "compiler2", "pull", "recursive_group", "published"];

fn causal_product_events_enabled(tel: &impl Telemetry) -> bool {
    [
        PRODUCT_REQUESTED_EVENT,
        PRODUCT_EVALUATED_EVENT,
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
    NativeProgram(RootId),
    BackendExecutable(ExecutableKey),
    AbiExecutable(ExecutableKey),
    MaterializedExecutable(ExecutableKey),
    ExecutableEffects(ExecutableKey),
    TransportShape(TransportPosition),
    CallableConstruction(TransportPosition),
    StructSchema(ModuleId),
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
                | (Self::NativeProgram(left), Self::NativeProgram(right)) => left.cmp(right),
                (Self::StructSchema(left), Self::StructSchema(right)) => left.cmp(right),
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
        ProductKey::NativeProgram(_) => 11,
        ProductKey::TransportShape(_) => 12,
        ProductKey::StructSchema(_) => 13,
    }
}

impl ProductKey {
    pub fn kind(&self) -> &'static str {
        match self {
            Self::RootBackendProduct(_) => "root_backend_product",
            Self::NativeProgram(_) => "native_program",
            Self::BackendExecutable(_) => "backend_executable",
            Self::AbiExecutable(_) => "abi_executable",
            Self::MaterializedExecutable(_) => "materialized_executable",
            Self::ExecutableEffects(_) => "executable_effects",
            Self::TransportShape(_) => "transport_shape",
            Self::CallableConstruction(_) => "callable_construction",
            Self::StructSchema(_) => "struct_schema",
        }
    }

    fn executable(&self) -> Option<&ExecutableKey> {
        match self {
            Self::BackendExecutable(executable)
            | Self::AbiExecutable(executable)
            | Self::MaterializedExecutable(executable)
            | Self::ExecutableEffects(executable) => Some(executable),
            Self::RootBackendProduct(_)
            | Self::NativeProgram(_)
            | Self::TransportShape(_)
            | Self::CallableConstruction(_) => None,
            Self::StructSchema(_) => None,
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
    RootBackendProduct(Rc<BackendProgram>),
    NativeProgram(Rc<NativeProgram>),
    BackendExecutable(Rc<BackendExecutable>),
    AbiExecutable(Rc<AbiReadyExecutable>),
    MaterializedExecutable(Rc<MaterializedExecutable>),
    ExecutableEffects(EffectSummary),
    TransportShape(TransportShapeFact),
    CallableConstruction(Rc<CallableConstructionOwner>),
    StructSchema(Rc<super::backend_program::BackendSchema>),
}

fn same_product_value(left: &ProductValue, right: &ProductValue) -> bool {
    match (left, right) {
        (ProductValue::RootBackendProduct(left), ProductValue::RootBackendProduct(right)) => {
            Rc::ptr_eq(left, right) || left == right
        }
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
    /// A producer reached a program it cannot lower and said why through a
    /// diagnostic before returning. The root stops on that diagnostic, and
    /// the drive boundary above forwards the failure without restating it —
    /// the same contract `FatalError` carries.
    Failed,
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
    pending_dependencies: HashMap<ProductKey, PendingProduct>,
    canceled_wait_frame: Option<(usize, ProductRequestId)>,
    wait_frame_exposures: Vec<WaitFrameExposure>,
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
    rooted: HashMap<ProductKey, rooted::RootedProducts>,
    membership_readers: HashMap<ProductKey, HashSet<ProductKey>>,
    rooted_readers: HashMap<ProductKey, HashSet<ProductKey>>,
}

type ProductCommitMember = (ProductKey, ProductValue, ProductDependencies);

#[derive(Debug)]
struct PendingProduct {
    dependencies: ProductDependencies,
    request: ProductRequestId,
    waiting_frame: Option<usize>,
}

#[derive(Debug)]
struct WaitFrameExposure {
    reader: ProductKey,
    request: ProductRequestId,
    position: usize,
    branch: ProductKey,
    reparented: bool,
}

enum ProductCompletion {
    Single(ProductValue, ProductDependencies),
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

enum MutationAdmissions<K> {
    Empty,
    One(K, u8),
    Many(HashMap<K, u8>),
}

impl<K: Eq + std::hash::Hash + Clone> MutationAdmissions<K> {
    fn admit(&mut self, mutation: ReaderMutation, key: &K) -> bool {
        let bit = 1 << mutation.rank();
        match self {
            Self::Empty => *self = Self::One(key.clone(), bit),
            Self::One(first, mask) if first == key => return Self::include(mask, bit),
            Self::One(_, _) => {
                let Self::One(first, mask) = std::mem::replace(self, Self::Empty) else {
                    unreachable!()
                };
                *self = Self::Many(HashMap::from([(first, mask), (key.clone(), bit)]));
            }
            Self::Many(keys) => {
                if let Some(mask) = keys.get_mut(key) {
                    return Self::include(mask, bit);
                }
                keys.insert(key.clone(), bit);
            }
        }
        true
    }

    fn include(mask: &mut u8, bit: u8) -> bool {
        if *mask & bit != 0 {
            return false;
        }
        *mask |= bit;
        true
    }
}

struct ProductMutationWave {
    pending: OrderedWorklist<(ReaderMutation, ProductKey)>,
    admissions: MutationAdmissions<ProductKey>,
    work: ProductValidation,
}

impl ProductMutationWave {
    fn new(mut seeds: Vec<(ReaderMutation, ProductKey)>, types: &super::types::Types) -> Self {
        let mut admissions = MutationAdmissions::Empty;
        let mut work = ProductValidation::default();
        seeds.retain(|(mutation, key)| {
            work.mutation_admissions += 1;
            admissions.admit(*mutation, key)
        });
        seeds.sort_unstable_by(|left, right| Self::compare(left, right, types, &mut work));
        Self {
            pending: OrderedWorklist::from_sorted(seeds),
            admissions,
            work,
        }
    }

    fn compare(
        left: &(ReaderMutation, ProductKey),
        right: &(ReaderMutation, ProductKey),
        types: &super::types::Types,
        work: &mut ProductValidation,
    ) -> std::cmp::Ordering {
        work.ordering_comparisons += 1;
        let order = left.1.semantic_cmp(&right.1, types);
        debug_assert!(
            order != std::cmp::Ordering::Equal || left.1 == right.1,
            "distinct products must not share a semantic order identity"
        );
        order.then_with(|| left.0.rank().cmp(&right.0.rank()))
    }

    fn admit(&mut self, mutation: ReaderMutation, key: &ProductKey) -> bool {
        self.work.mutation_admissions += 1;
        self.admissions.admit(mutation, key)
    }

    fn push(&mut self, mutation: ReaderMutation, key: ProductKey, types: &super::types::Types) -> Option<ProductKey> {
        if self.admit(mutation, &key) {
            self.pending.push((mutation, key), |left, right| {
                Self::compare(left, right, types, &mut self.work)
            });
            None
        } else {
            Some(key)
        }
    }

    fn push_borrowed(&mut self, mutation: ReaderMutation, key: &ProductKey, types: &super::types::Types) {
        if self.admit(mutation, key) {
            self.pending.push((mutation, key.clone()), |left, right| {
                Self::compare(left, right, types, &mut self.work)
            });
        }
    }

    fn readers(
        &mut self,
        mutation: ReaderMutation,
        readers: Option<&HashSet<ProductKey>>,
        types: &super::types::Types,
    ) {
        for reader in readers.into_iter().flatten() {
            self.work.mutation_edges += 1;
            self.push_borrowed(mutation, reader, types);
        }
    }

    fn pop(&mut self, types: &super::types::Types) -> Option<(ReaderMutation, ProductKey)> {
        let selected = self
            .pending
            .pop(|left, right| Self::compare(left, right, types, &mut self.work))?;
        self.work.mutation_pops += 1;
        Some(selected)
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

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ProductValidation {
    pub vertex_visits: u64,
    pub edge_scans: u64,
    pub witness_visits: u64,
    pub witness_updates: u64,
    pub cursor_rewinds: u64,
    pub mutation_admissions: u64,
    pub mutation_pops: u64,
    pub mutation_edges: u64,
    pub reparent_candidates: u64,
    pub reparent_proof_nodes: u64,
    pub ordering_comparisons: u64,
}

#[derive(Default)]
struct ProductValidationWalk {
    checked: HashSet<ProductKey>,
    work: ProductValidation,
}

impl ProductValidation {
    fn include(&mut self, work: Self) {
        self.vertex_visits += work.vertex_visits;
        self.edge_scans += work.edge_scans;
        self.witness_visits += work.witness_visits;
        self.witness_updates += work.witness_updates;
        self.cursor_rewinds += work.cursor_rewinds;
        self.mutation_admissions += work.mutation_admissions;
        self.mutation_pops += work.mutation_pops;
        self.mutation_edges += work.mutation_edges;
        self.reparent_candidates += work.reparent_candidates;
        self.reparent_proof_nodes += work.reparent_proof_nodes;
        self.ordering_comparisons += work.ordering_comparisons;
    }

    pub(super) fn report(&self, tel: &impl Telemetry, key: &ProductKey) {
        if *self != Self::default() {
            tel.raw_event2(&["fz", "compiler2", "pull", "product", "validation"], key, self);
        }
    }
}

#[derive(Debug, PartialEq)]
struct ProductEntry {
    value: ProductValue,
    generation: u64,
    dependencies: Rc<ProductDependencies>,
    membership: HashSet<ProductKey>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ProductDependencies {
    products: IndexMap<ProductKey, Option<u64>>,
    rooted_read: Option<RootedRead>,
    facts: HashMap<FactUse<FactKey>, FactState>,
    membership: HashSet<ProductKey>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RootedRead {
    position: usize,
    delivered: bool,
    controls_delivered: bool,
}

impl ProductMemo {
    fn has_unsettled_inputs(&self, key: &ProductKey) -> bool {
        self.displaced.contains_key(key)
            || self.fact_stale_dependencies.contains_key(key)
            || self.dirty_descendants.contains(key)
    }

    fn dependencies_are_unsettled(&self, key: &ProductKey, work: &mut ProductValidation) -> bool {
        self.rooted.get(key).is_some_and(|rooted| !rooted.dirty.is_empty())
            || self.produced.get(key).is_some_and(|entry| {
                entry.dependencies.products.keys().any(|dependency| {
                    work.mutation_edges += 1;
                    self.has_unsettled_inputs(dependency)
                })
            })
    }

    fn external_state(&self, key: &ProductKey) -> FactState {
        FactState {
            revision: self
                .produced
                .get(key)
                .or_else(|| self.displaced.get(key))
                .map(|entry| entry.generation),
            settled: self.produced.contains_key(key) && !self.has_unsettled_inputs(key),
        }
    }

    fn record_external_change(&mut self, key: &ProductKey, before: FactState) {
        if self.observed_products.contains(key) {
            let after = self.external_state(key);
            if before != after {
                self.external_changes.push(FactChange::replacing(
                    key.clone(),
                    before.revision,
                    after.revision,
                    before.settled,
                    after.settled,
                ));
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
    pub(crate) fn product_dependencies(&self, key: &ProductKey) -> Option<&IndexMap<ProductKey, Option<u64>>> {
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
            .map(|(key, pending)| (key, &pending.dependencies))
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
        self.pending_dependencies.get(key).map(|pending| &pending.dependencies)
    }

    fn begin(&mut self, key: ProductKey) -> bool {
        self.in_progress.insert(key)
    }

    fn finish_completion(
        &mut self,
        tel: &impl Telemetry,
        emit_causal: bool,
        requested: &ProductKey,
        completion: ProductCompletion,
        types: &super::types::Types,
    ) -> bool {
        match completion {
            ProductCompletion::Single(value, dependencies) => {
                if self.invalidated_in_progress.remove(requested) {
                    self.in_progress.remove(requested);
                    self.produced.remove(requested);
                    return false;
                }
                self.commit_members(
                    tel,
                    emit_causal,
                    requested,
                    std::iter::once((requested.clone(), value, dependencies)),
                    None,
                    types,
                );
            }
            ProductCompletion::RecursiveGroup(mut members) => {
                members.sort_by(|(left, _, _), (right, _, _)| left.semantic_cmp(right, types));
                assert!(
                    members.iter().any(|(key, _, _)| key == requested),
                    "a recursive completion must include its actual owner"
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
                let member_keys = members.iter().map(|(key, _, _)| key.clone()).collect::<HashSet<_>>();
                if member_keys.iter().any(|key| self.invalidated_in_progress.contains(key)) {
                    self.reject_group(tel, &member_keys, types);
                    return false;
                }
                let mut product_observations = HashMap::new();
                let mut fact_observations = HashMap::new();
                for (_, _, dependencies) in &members {
                    for (dependency, generation) in &dependencies.products {
                        if member_keys.contains(dependency) {
                            continue;
                        }
                        if product_observations
                            .insert(dependency, generation)
                            .is_some_and(|recorded| recorded != generation)
                        {
                            self.reject_group(tel, &member_keys, types);
                            return false;
                        }
                    }
                    for (fact, state) in &dependencies.facts {
                        if fact_observations
                            .insert(fact, state)
                            .is_some_and(|recorded| recorded != state)
                        {
                            self.reject_group(tel, &member_keys, types);
                            return false;
                        }
                    }
                }
                self.next_group_id += 1;
                let group_id = self.next_group_id;
                self.commit_members(tel, emit_causal, requested, members.into_iter(), Some(group_id), types);
            }
        }
        true
    }

    fn commit_members(
        &mut self,
        tel: &impl Telemetry,
        emit_causal: bool,
        requested: &ProductKey,
        members: impl ExactSizeIterator<Item = ProductCommitMember>,
        group: Option<u64>,
        types: &super::types::Types,
    ) {
        let mut prepared = Vec::with_capacity(members.len());
        let mut external_before = Vec::new();
        for (key, value, mut dependencies) in members {
            if self.observed_products.contains(&key) {
                external_before.push((key.clone(), self.external_state(&key)));
            }
            self.in_progress.remove(&key);
            let previous = self.produced.remove(&key).or_else(|| self.displaced.remove(&key));
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
            let membership = std::mem::take(&mut dependencies.membership);
            let previous_membership = previous.map(|entry| entry.membership).unwrap_or_default();
            prepared.push((
                key,
                value,
                dependencies,
                generation,
                changed,
                membership,
                previous_membership,
            ));
        }

        let group_generations = group.map(|_| {
            prepared
                .iter()
                .map(|(key, _, _, generation, _, _, _)| (key.clone(), *generation))
                .collect::<HashMap<_, _>>()
        });
        if let Some(generations) = &group_generations {
            for (_, _, dependencies, _, _, _, _) in &mut prepared {
                for (dependency, generation) in &mut dependencies.products {
                    if let Some(settled) = generations.get(dependency) {
                        *generation = Some(*settled);
                    }
                }
            }
        }

        for (key, value, dependencies, generation, changed, membership, _) in &mut prepared {
            if dependencies.rooted_read.is_none() {
                self.retire_rooted(key).report(tel, key);
            }
            if dependencies.rooted_read.is_some_and(|read| read.delivered) {
                self.rooted
                    .get_mut(key)
                    .expect("delivered rooted observation")
                    .changes
                    .clear();
            }
            self.install_reader_dependencies(key, dependencies);
            self.fact_stale_dependencies.remove(key);
            self.dirty_descendants.remove(key);
            self.produced.insert(
                key.clone(),
                ProductEntry {
                    value: value.clone(),
                    generation: *generation,
                    dependencies: Rc::new(std::mem::take(dependencies)),
                    membership: std::mem::take(membership),
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
            }
        }
        for (key, before) in external_before {
            self.record_external_change(&key, before);
        }
        for (key, _, _, _, _, _, previous) in &prepared {
            self.replace_membership_readers(key, previous);
        }
        let mut rooted_mutations = Vec::new();
        for (key, _, _, _, changed, _, previous) in &prepared {
            rooted_mutations.extend(self.committed_rooted_member(tel, key, previous, *changed, types));
        }
        let mutations = prepared.iter().flat_map(|(key, _, _, _, changed, _, _)| {
            self.reader_mutations(
                key,
                if *changed {
                    ReaderMutation::Invalidate
                } else {
                    ReaderMutation::Refresh
                },
            )
        });
        let mutations = mutations
            .filter(|(_, reader)| {
                group_generations
                    .as_ref()
                    .is_none_or(|members| !members.contains_key(reader))
            })
            .chain(rooted_mutations)
            .collect();
        self.mutate_product_wave(tel, mutations, types);
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
                entry.dependencies = Rc::default();
            }
        }
        self.mutate_product_wave(tel, mutations, types);
    }

    fn unblock(&mut self, request: ProductRequestId, key: &ProductKey, dependencies: ProductDependencies) {
        self.in_progress.remove(key);
        self.invalidated_in_progress.remove(key);
        self.take_pending_dependencies(key);
        self.install_reader_dependencies(key, &dependencies);
        self.pending_dependencies.insert(
            key.clone(),
            PendingProduct {
                dependencies,
                request,
                waiting_frame: None,
            },
        );
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
        if let Some(PendingProduct {
            waiting_frame: Some(position),
            request,
            ..
        }) = &pending
            && self
                .canceled_wait_frame
                .is_none_or(|(previous, _)| *position < previous)
        {
            self.canceled_wait_frame = Some((*position, *request));
        }
        self.remove_reader_dependencies(reader, pending.as_ref().map(|pending| &pending.dependencies));
        pending.map(|pending| pending.dependencies)
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
        pending: Vec<(ReaderMutation, ProductKey)>,
        types: &super::types::Types,
    ) {
        let mut wave = ProductMutationWave::new(pending, types);
        let mut last_reader = None;
        while let Some((mutation, reader)) = wave.pop(types) {
            let external_before = self
                .observed_products
                .contains(&reader)
                .then(|| self.external_state(&reader));
            match mutation {
                ReaderMutation::Invalidate => {
                    for root in self.rooted_member_dirty(&reader, &mut wave.work) {
                        let _ = wave.push(ReaderMutation::Dirty, root, types);
                    }
                    let (was_pending, was_produced) = self.displace_for_reproduction_shallow(tel, &reader);
                    let next = if was_pending {
                        Some(ReaderMutation::Invalidate)
                    } else if was_produced {
                        Some(ReaderMutation::Dirty)
                    } else {
                        None
                    };
                    if let Some(next) = next {
                        wave.readers(next, self.product_readers.get(&reader), types);
                    }
                }
                ReaderMutation::Dirty => {
                    for root in self.rooted_member_dirty(&reader, &mut wave.work) {
                        let _ = wave.push(ReaderMutation::Dirty, root, types);
                    }
                    if self.pending_dependencies.contains_key(&reader) {
                        if let Some(rejected) = wave.push(ReaderMutation::Invalidate, reader, types) {
                            last_reader = Some(rejected);
                        }
                        continue;
                    }
                    if self.dirty_descendants.insert(reader.clone()) {
                        wave.readers(ReaderMutation::Dirty, self.product_readers.get(&reader), types);
                    }
                }
                ReaderMutation::Refresh => {
                    let dirty = self.dependencies_are_unsettled(&reader, &mut wave.work);
                    if dirty {
                        self.dirty_descendants.insert(reader.clone());
                    } else if self.dirty_descendants.remove(&reader) {
                        wave.readers(ReaderMutation::Refresh, self.product_readers.get(&reader), types);
                    }
                    for root in self.rooted_member_refresh(&reader, &mut wave.work) {
                        let _ = wave.push(ReaderMutation::Refresh, root, types);
                    }
                }
            }
            if let Some(before) = external_before {
                self.record_external_change(&reader, before);
            }
            last_reader = Some(reader);
        }
        if let Some(reader) = last_reader {
            wave.work.report(tel, &reader);
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
                let pending_stale = self.pending_dependencies.get(&reader).is_some_and(|pending| {
                    pending
                        .dependencies
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

    fn stale_dependency(
        &mut self,
        tel: &impl Telemetry,
        key: &ProductKey,
        types: &super::types::Types,
    ) -> Option<ProductKey> {
        let mut walk = ProductValidationWalk::default();
        let resumable = self.pending_dependencies.get(key).is_some_and(|pending| {
            pending
                .dependencies
                .rooted_read
                .is_some_and(|read| !read.delivered && read.controls_delivered)
                && !self.fact_stale_dependencies.contains_key(key)
        });
        let stale = if resumable {
            self.rooted_stale_dependency(tel, key, &mut walk, types, false)
                .or_else(|| Some(key.clone()))
        } else {
            self.stale_dependency_inner(tel, key, &mut walk, types, false)
        };
        self.finish_validation(tel, walk, stale.is_none(), None, types)
            .report(tel, key);
        stale
    }

    fn finish_validation(
        &mut self,
        tel: &impl Telemetry,
        walk: ProductValidationWalk,
        valid: bool,
        active_reader: Option<&ProductKey>,
        types: &super::types::Types,
    ) -> ProductValidation {
        let ProductValidationWalk { checked, mut work } = walk;
        if valid && !checked.is_empty() {
            let external_before = checked
                .iter()
                .filter(|key| self.observed_products.contains(*key))
                .map(|key| (key.clone(), self.external_state(key)))
                .collect::<Vec<_>>();
            for key in &checked {
                self.dirty_descendants.remove(key);
                if let Some(rooted) = self.rooted.get_mut(key) {
                    rooted.dirty.clear();
                    rooted.collect_maintenance(&mut work);
                }
            }
            let mut mutations = Vec::new();
            for key in &checked {
                mutations.extend(
                    self.reader_mutations(key, ReaderMutation::Refresh)
                        .filter(|(_, reader)| !checked.contains(reader) && active_reader != Some(reader)),
                );
                mutations.extend(
                    self.rooted_member_refresh(key, &mut work)
                        .into_iter()
                        .filter(|root| active_reader != Some(root))
                        .map(|root| (ReaderMutation::Refresh, root)),
                );
            }
            self.mutate_product_wave(tel, mutations, types);
            for (key, before) in external_before {
                self.record_external_change(&key, before);
            }
        }
        work
    }

    fn stale_dependency_inner(
        &mut self,
        tel: &impl Telemetry,
        key: &ProductKey,
        visiting: &mut ProductValidationWalk,
        types: &super::types::Types,
        complete: bool,
    ) -> Option<ProductKey> {
        if self.fact_stale_dependencies.contains_key(key) {
            return Some(key.clone());
        }
        if self.displaced.contains_key(key) {
            return Some(key.clone());
        }
        if !self.dirty_descendants.contains(key) && self.rooted.get(key).is_none_or(|rooted| rooted.dirty.is_empty()) {
            return None;
        }
        if !self.produced.contains_key(key) {
            return None;
        }
        if !visiting.checked.insert(key.clone()) {
            return None;
        }
        visiting.work.vertex_visits += 1;
        self.stale_observation(tel, key, visiting, types, complete)
    }

    fn stale_observation(
        &mut self,
        tel: &impl Telemetry,
        key: &ProductKey,
        visiting: &mut ProductValidationWalk,
        types: &super::types::Types,
        complete: bool,
    ) -> Option<ProductKey> {
        let dependencies = Rc::clone(&self.produced[key].dependencies);
        let count = dependencies.products.len();
        let rooted_read = dependencies.rooted_read;
        for index in 0..count {
            if let Some(read) = rooted_read.filter(|read| read.position == index) {
                if let Some(stale) = self.rooted_stale_dependency(tel, key, visiting, types, complete) {
                    return Some(stale);
                }
                if !read.delivered {
                    return Some(key.clone());
                }
            }
            let (dependency, generation) = dependencies.products.get_index(index).expect("observation index");
            visiting.work.edge_scans += 1;
            let current = self.produced.get(dependency).map(|entry| entry.generation);
            if current != *generation {
                return Some(if current.is_none() {
                    dependency.clone()
                } else {
                    key.clone()
                });
            }
            if generation.is_some()
                && let Some(stale) = self.stale_dependency_inner(tel, dependency, visiting, types, complete)
            {
                return Some(stale);
            }
        }
        if let Some(read) = rooted_read.filter(|read| read.position == count) {
            return self
                .rooted_stale_dependency(tel, key, visiting, types, complete)
                .or_else(|| (!read.delivered).then(|| key.clone()));
        }
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
            .map(|change| {
                FactChange::replacing(
                    DependencyKey::Product(ProductAddress { root, key: change.key }),
                    change.old_revision,
                    change.new_revision,
                    change.old_settled,
                    change.new_settled,
                )
            })
            .filter(|change| change.content_changed() || change.readiness_changed())
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
                FactChange::replacing(
                    DependencyKey::Product(ProductAddress { root, key: key.clone() }),
                    before.revision,
                    None,
                    before.settled,
                    false,
                )
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
    product_reads_delivered: bool,
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
            product_reads_delivered: true,
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
            self.product_reads_delivered = false;
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
        if let Some(stale) = self.session.memo.stale_dependency(tel, &key, types) {
            self.product_reads_delivered = false;
            self.session.memo.prepare_stale_for_reproduction(tel, &stale, types);
            let generation = self.session.memo.generation(&key);
            self.dependencies.products.insert(key.clone(), generation);
            return None;
        }
        let generation = self.session.memo.generation(&key);
        self.product_reads_delivered &= generation.is_some();
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

    fn into_completion(self) -> (ProductDependencies, Option<Vec<ProductCommitMember>>) {
        (self.dependencies, self.recursive_group)
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
            ProductKey::StructSchema(module) => {
                super::jobs::backend::produce_struct_schema(self.world, context, *module)
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

    pub(super) fn reconcile_wait_frames(&mut self, types: &super::types::Types) -> Option<(usize, ProductRequestId)> {
        self.wait_frames_canceled(types);
        self.session_mut().memo.canceled_wait_frame.take()
    }

    pub(super) fn wait_frames_canceled(&mut self, types: &super::types::Types) -> bool {
        let tel = self.tel;
        let mut session = self.session_mut();
        session.reconcile_fact_movements(tel, types);
        session.memo.canceled_wait_frame.is_some()
    }

    pub(super) fn register_wait_frame(&mut self, key: &ProductKey, position: usize) -> Option<ProductRequestId> {
        let mut session = self.session_mut();
        let pending = session.memo.pending_dependencies.get_mut(key)?;
        pending.dependencies.rooted_read?;
        let newly_registered = pending.waiting_frame.is_none();
        pending.waiting_frame.get_or_insert(position);
        let request = pending.request;
        if newly_registered {
            session.memo.begin_wait_frame_admissions(key);
        }
        Some(request)
    }

    pub(super) fn unregister_wait_frame(&mut self, key: &ProductKey, request: ProductRequestId, position: usize) {
        let mut session = self.session_mut();
        if let Some(pending) = session.memo.pending_dependencies.get_mut(key)
            && pending.request == request
            && pending.waiting_frame == Some(position)
        {
            pending.waiting_frame = None;
        }
    }

    pub(super) fn admit_wait_frame_product(
        &mut self,
        reader: &ProductKey,
        request: ProductRequestId,
        product: &ProductKey,
    ) {
        self.session_mut()
            .memo
            .admit_wait_frame_product(reader, request, product);
    }

    pub(super) fn release_wait_frame_product(
        &mut self,
        reader: &ProductKey,
        request: ProductRequestId,
        product: &ProductKey,
    ) {
        self.session_mut()
            .memo
            .release_wait_frame_product(reader, request, product);
    }

    pub(super) fn next_wait_frame_admission(
        &mut self,
        work: &mut ProductValidation,
    ) -> Option<(usize, ProductRequestId, ProductKey)> {
        self.session_mut().memo.next_wait_frame_admission(work)
    }

    pub(super) fn product_is_current(&self, key: &ProductKey) -> bool {
        let session = self.session();
        session.memo.get(key).is_some()
            && !session.memo.has_unsettled_inputs(key)
            && session.memo.rooted.get(key).is_none_or(|root| root.dirty.is_empty())
    }

    pub(super) fn collect_wait_frame_work(&self, reader: &ProductKey, work: &mut ProductValidation) {
        if let Some(rooted) = self.session().memo.rooted.get(reader) {
            rooted.collect_maintenance(work);
        }
    }

    pub(super) fn finish_wait_frames(&mut self) {
        self.session_mut().memo.wait_frame_exposures.clear();
    }

    pub fn pull(
        &mut self,
        producers: &mut impl ProductProducers,
        key: impl std::borrow::Borrow<ProductKey>,
    ) -> PullOutcome {
        let key = key.borrow();
        let tel = self.tel;
        let emit_causal_products = self.emit_causal_products;
        assert!(
            !self.session().memo.contains_in_progress(key),
            "safe product producers cannot recursively enter ProductDriver::pull"
        );
        let request = self.session_mut().request_ids.allocate();
        if self.emit_causal_products {
            tel.raw_event2(PRODUCT_REQUESTED_EVENT, key, &request);
        }
        self.session_mut()
            .reconcile_fact_movements(tel, producers.product_types());
        self.session_mut().note_product_request(key);
        let stale = self
            .session_mut()
            .memo
            .stale_dependency(tel, key, producers.product_types());
        if let Some(stale) = stale {
            self.session_mut()
                .memo
                .prepare_stale_for_reproduction(tel, &stale, producers.product_types());
            if &stale != key {
                return PullOutcome::wait_on_product(stale);
            }
        }
        if let Some(value) = self.session().memo.get(key) {
            self.emit("cache_hit", key);
            return PullOutcome::Produced(value.clone());
        }
        assert!(
            self.session_mut().memo.begin(key.clone()),
            "safe product producers cannot recursively enter ProductDriver::pull"
        );

        let (outcome, dependencies, recursive_group) = {
            let mut session = self.session_mut();
            let mut context = ProductReadContext::new(&mut session);
            let outcome = producers.produce(&mut context, key);
            let (dependencies, recursive_group) = context.into_completion();
            (outcome, dependencies, recursive_group)
        };
        if self.emit_causal_products {
            tel.raw_event3(PRODUCT_EVALUATED_EVENT, key, &request, &outcome);
        }

        match outcome {
            PullOutcome::Produced(value) => {
                let completion = if let Some(members) = recursive_group {
                    ProductCompletion::RecursiveGroup(members)
                } else {
                    ProductCompletion::Single(value, dependencies)
                };
                let settled = self.session_mut().memo.finish_completion(
                    tel,
                    emit_causal_products,
                    key,
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
                            .get(key)
                            .expect("settled completion must install its requested product")
                            .clone(),
                    )
                }
            }
            PullOutcome::Waiting(waits) => {
                self.session_mut().memo.unblock(request, key, dependencies);
                PullOutcome::Waiting(waits)
            }
            PullOutcome::Failed => {
                assert!(
                    recursive_group.is_none(),
                    "a failed product cannot publish a recursive group"
                );
                self.session_mut().memo.abort(key);
                PullOutcome::Failed
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
#[path = "pull_test.rs"]
mod pull_test;
