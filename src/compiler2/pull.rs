//! Product-keyed pull substrate for compiler2 artifacts.
//!
//! This module is intentionally separate from the existing job scheduler. A
//! product producer answers one named demand and can only return a value or
//! explicit waits. It does not enqueue jobs, schedule follow-up work, or scan a
//! root frontier.

use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::num::NonZeroU64;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::telemetry::{Telemetry, TelemetryExt as _};

use super::artifact::{
    AbiReadyExecutable, BackendCallArg, BackendReceive, BackendStep, CallEdge, CallReturnFlow, EffectSummary,
    MaterializedExecutable, ReusableConsCapture, RootBackendProductAnswer,
};
use super::body::{
    CallSiteId, ControlDestination, ControlDispatch, ControlEntryId, DispatchBindings, LoweredExtern, ValueId,
};
use super::drive::FactKey;
use super::executable_facts::ExecutableFacts;
use super::facts::{FactMovement, FactState, FactUse};
use super::identity::{ExecutableKey, RootId};
use super::scheduler::WorkStartTally;
use super::semantic::{CallableFlowEdge, CallableSurface, ExecutableRuntimeDemand, RuntimeDemand, SemanticOrd};
use super::transport::{CallableConstructionOwner, ShapeId, TransportPosition};
pub use super::transport::{TransportCarrier, TransportLayout};
use super::world::World;

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
pub struct InputSlot {
    pub executable: ExecutableKey,
    pub semantic_index: usize,
}

/// Exact resolved edge for a local callable producer and canonical surface.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CallableResolutionKey {
    pub executable: ExecutableKey,
    pub value: ValueId,
    pub surface: CallableSurface,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ProductKey {
    RootBackendProduct(RootId),
    BackendExecutable(ExecutableKey),
    AbiExecutable(ExecutableKey),
    MaterializedExecutable(ExecutableKey),
    ExecutableEffects(ExecutableKey),
    RuntimeDemand(ExecutableKey),
    CallableResolution(CallableResolutionKey),
    OutgoingEdgeFrontier(RootId),
    OutgoingInputEdges(ExecutableKey),
    IncomingInputRelations(RootId),
    IncomingInputSlot(InputSlot),
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
                | (Self::ExecutableEffects(left), Self::ExecutableEffects(right))
                | (Self::RuntimeDemand(left), Self::RuntimeDemand(right))
                | (Self::OutgoingInputEdges(left), Self::OutgoingInputEdges(right)) => left.semantic_cmp(right, types),
                (Self::RootBackendProduct(left), Self::RootBackendProduct(right))
                | (Self::OutgoingEdgeFrontier(left), Self::OutgoingEdgeFrontier(right))
                | (Self::IncomingInputRelations(left), Self::IncomingInputRelations(right)) => left.cmp(right),
                (Self::CallableResolution(left), Self::CallableResolution(right)) => left
                    .executable
                    .semantic_cmp(&right.executable, types)
                    .then_with(|| left.value.cmp(&right.value))
                    .then_with(|| types.cmp_activation_tys(&left.surface.inputs, &right.surface.inputs)),
                (Self::IncomingInputSlot(left), Self::IncomingInputSlot(right)) => left
                    .executable
                    .semantic_cmp(&right.executable, types)
                    .then_with(|| left.semantic_index.cmp(&right.semantic_index)),
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
        ProductKey::CallableResolution(_) => 3,
        ProductKey::ExecutableEffects(_) => 4,
        ProductKey::IncomingInputRelations(_) => 5,
        ProductKey::IncomingInputSlot(_) => 6,
        ProductKey::MaterializedExecutable(_) => 7,
        ProductKey::OutgoingEdgeFrontier(_) => 8,
        ProductKey::OutgoingInputEdges(_) => 9,
        ProductKey::RootBackendProduct(_) => 10,
        ProductKey::RuntimeDemand(_) => 11,
        ProductKey::TransportShape(_) => 12,
    }
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
            Self::CallableResolution(_) => "callable_resolution",
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
            | Self::RuntimeDemand(executable)
            | Self::OutgoingInputEdges(executable) => Some(executable),
            Self::CallableResolution(key) => Some(&key.executable),
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
    RootBackendProduct(Rc<RootBackendProductAnswer>),
    BackendExecutable(Rc<SymbolicBackendExecutable>),
    AbiExecutable(Rc<AbiReadyExecutable>),
    MaterializedExecutable(Rc<MaterializedExecutable>),
    ExecutableEffects(EffectSummary),
    RuntimeDemand(Rc<ExecutableRuntimeDemand>),
    CallableResolution(CallableFlowEdge),
    OutgoingEdgeFrontier(Rc<[ExecutableKey]>),
    OutgoingInputEdges(Rc<OrderedIncomingInputs>),
    IncomingInputRelations(Rc<OrderedIncomingInputs>),
    IncomingInputSlot(Rc<[IncomingInputSource]>),
    TransportShape(TransportShapeFact),
    CallableConstruction(Rc<CallableConstructionOwner>),
}

fn same_product_value(left: &ProductValue, right: &ProductValue) -> bool {
    match (left, right) {
        (ProductValue::RootBackendProduct(left), ProductValue::RootBackendProduct(right)) => {
            Rc::ptr_eq(left, right) || left == right
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
        (ProductValue::RuntimeDemand(left), ProductValue::RuntimeDemand(right)) => {
            Rc::ptr_eq(left, right) || left == right
        }
        (ProductValue::CallableConstruction(left), ProductValue::CallableConstruction(right)) => {
            Rc::ptr_eq(left, right) || left == right
        }
        (ProductValue::OutgoingEdgeFrontier(left), ProductValue::OutgoingEdgeFrontier(right)) => {
            Rc::ptr_eq(left, right) || left == right
        }
        (ProductValue::OutgoingInputEdges(left), ProductValue::OutgoingInputEdges(right))
        | (ProductValue::IncomingInputRelations(left), ProductValue::IncomingInputRelations(right)) => {
            Rc::ptr_eq(left, right) || left == right
        }
        (ProductValue::IncomingInputSlot(left), ProductValue::IncomingInputSlot(right)) => {
            Rc::ptr_eq(left, right) || left == right
        }
        _ => left == right,
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct OrderedIncomingInputs(Box<[(InputSlot, Rc<[IncomingInputSource]>)]>);

impl OrderedIncomingInputs {
    pub(crate) fn from_unordered(
        inputs: HashMap<InputSlot, HashSet<IncomingInputSource>>,
        types: &super::types::Types,
    ) -> Self {
        let mut inputs = inputs
            .into_iter()
            .map(|(slot, sources)| {
                let mut sources = sources.into_iter().collect::<Vec<_>>();
                sources.sort_by(|left, right| compare_incoming_input_sources(left, right, types));
                (slot, Rc::from(sources))
            })
            .collect::<Vec<_>>();
        inputs.sort_by(|(left, _), (right, _)| compare_input_slots(left, right, types));
        Self(inputs.into_boxed_slice())
    }

    fn iter(&self) -> impl Iterator<Item = (&InputSlot, &[IncomingInputSource])> {
        self.0.iter().map(|(slot, sources)| (slot, sources.as_ref()))
    }

    fn get(&self, slot: &InputSlot) -> Option<Rc<[IncomingInputSource]>> {
        self.0
            .iter()
            .find_map(|(candidate, sources)| (candidate == slot).then(|| Rc::clone(sources)))
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
}

#[cfg_attr(test, derive(Clone))]
#[derive(Debug, PartialEq)]
pub struct SymbolicBackendExecutable {
    pub key: ExecutableKey,
    pub abi: Rc<AbiReadyExecutable>,
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
    /// Monotone counter stamping each settled group with a distinct id. The
    /// first group settled gets id 1 (the field itself starts at the
    /// `Default` zero and is pre-incremented before use).
    next_group_id: u64,
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
        if dependency != current && memo.unsettled_product_dependencies(dependency).is_none() {
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
            memo.unsettled_product_dependencies(key)
        };
        if dependencies.is_some() && key.kind() == current.kind() {
            self.candidate_inventory += 1;
        }
        for dependency in dependencies
            .into_iter()
            .flat_map(|dependencies| dependencies.products.keys())
        {
            if dependency != current && memo.unsettled_product_dependencies(dependency).is_none() {
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
    fn retain_equal_value(&self, key: &ProductKey, candidate: ProductValue) -> ProductValue {
        self.produced
            .get(key)
            .or_else(|| self.displaced.get(key))
            .filter(|entry| same_product_value(&entry.value, &candidate))
            .map_or(candidate, |entry| entry.value.clone())
    }

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

    fn product_dependencies_for_group(&self, key: &ProductKey) -> Option<&ProductDependencies> {
        self.pending_dependencies
            .get(key)
            .or_else(|| self.produced.get(key).map(|entry| entry.dependencies.as_ref()))
            .or_else(|| self.displaced.get(key).map(|entry| entry.dependencies.as_ref()))
    }

    /// The dependencies of `key` if `key` has not settled: either it is in
    /// flight and has recorded some, or it was displaced and is waiting to be
    /// produced again. A settled product is deliberately absent -- see
    /// no pending wait chain can pass through it.
    fn unsettled_product_dependencies(&self, key: &ProductKey) -> Option<&ProductDependencies> {
        self.pending_dependencies
            .get(key)
            .or_else(|| self.displaced.get(key).map(|entry| entry.dependencies.as_ref()))
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
                | ProductValue::CallableResolution(_)
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
        for (key, value, dependencies) in members {
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
        let mut mutations = Vec::new();
        for (fact_key, final_state) in facts {
            let readers = self.fact_readers.get(fact_key).cloned().unwrap_or_default();
            for reader in readers {
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

fn compare_input_slots(left: &InputSlot, right: &InputSlot, types: &super::types::Types) -> std::cmp::Ordering {
    left.executable
        .semantic_cmp(&right.executable, types)
        .then_with(|| left.semantic_index.cmp(&right.semantic_index))
}

fn compare_incoming_input_sources(
    left: &IncomingInputSource,
    right: &IncomingInputSource,
    types: &super::types::Types,
) -> std::cmp::Ordering {
    left.producer
        .semantic_cmp(&right.producer, types)
        .then_with(|| left.value.as_u32().cmp(&right.value.as_u32()))
        .then_with(|| incoming_input_role_key(left.role).cmp(&incoming_input_role_key(right.role)))
}

fn ordered_executable_frontier(
    executables: &HashSet<ExecutableKey>,
    types: &super::types::Types,
) -> Rc<[ExecutableKey]> {
    let mut executables = executables.iter().cloned().collect::<Vec<_>>();
    executables.sort_by(|left, right| left.semantic_cmp(right, types));
    Rc::from(executables)
}

fn incoming_input_role_key(role: IncomingInputRole) -> (u8, u32, usize) {
    match role {
        IncomingInputRole::CallArgument => (0, 0, 0),
        IncomingInputRole::CallableCapture {
            construction,
            capture_index,
        } => (1, construction.as_u32(), capture_index),
    }
}

type DemandContributionTransaction = (
    ExecutableKey,
    HashMap<ExecutableKey, RuntimeDemand>,
    HashMap<ExecutableKey, HashMap<usize, RuntimeDemand>>,
);

#[derive(Debug)]
pub struct PullSession {
    id: Option<PullSessionId>,
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
    materialized_executables: HashMap<ExecutableKey, Rc<MaterializedExecutable>>,
    executable_effects: HashMap<ExecutableKey, EffectSummary>,
    abi_executables: HashMap<ExecutableKey, Rc<AbiReadyExecutable>>,
    backend_executables: HashMap<ExecutableKey, Rc<SymbolicBackendExecutable>>,
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
            id: None,
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

    pub fn id(&self) -> Option<PullSessionId> {
        self.id
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
    pub fn record_settled_runtime_demand(
        &mut self,
        tel: &impl Telemetry,
        executable: ExecutableKey,
        demand: ExecutableRuntimeDemand,
        types: &super::types::Types,
    ) {
        let key = ProductKey::RuntimeDemand(executable.clone());
        let previous = match self.memo.produced.get(&key).or_else(|| self.memo.displaced.get(&key)) {
            Some(ProductEntry {
                value: ProductValue::RuntimeDemand(previous),
                ..
            }) => Some(previous.as_ref().clone()),
            _ => None,
        };
        let changed = previous.is_some_and(|previous| previous != demand);
        self.memo.finish_completion(
            tel,
            causal_product_events_enabled(tel),
            &key,
            ProductCompletion::Batch(vec![(
                key.clone(),
                ProductValue::RuntimeDemand(Rc::new(demand)),
                ProductDependencies::default(),
            )]),
            types,
        );
        if changed {
            self.invalidate_artifact_products(tel, &executable, types);
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
        types: &super::types::Types,
    ) -> Option<RuntimeDemand> {
        let mut contributors = self
            .return_demand_contributors
            .get(target)
            .into_iter()
            .flatten()
            .filter(|contributor| !members.contains(*contributor))
            .cloned()
            .collect::<Vec<_>>();
        contributors.sort_by(|left, right| left.semantic_cmp(right, types));
        contributors
            .iter()
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
        types: &super::types::Types,
    ) -> HashMap<usize, RuntimeDemand> {
        let mut joined: HashMap<usize, RuntimeDemand> = HashMap::new();
        let mut contributors = self
            .input_demand_contributors
            .get(target)
            .into_iter()
            .flatten()
            .cloned()
            .collect::<Vec<_>>();
        contributors.sort_by(|left, right| left.semantic_cmp(right, types));
        for contributor in &contributors {
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
        self.materialized_executables.get(executable).map(Rc::as_ref)
    }

    pub fn invalidate_artifact_products_for(
        &mut self,
        tel: &impl Telemetry,
        executable: &ExecutableKey,
        types: &super::types::Types,
    ) {
        self.invalidate_artifact_products(tel, executable, types);
    }

    pub fn materialized_executables(&self) -> &HashMap<ExecutableKey, Rc<MaterializedExecutable>> {
        &self.materialized_executables
    }

    pub fn executable_effects(&self, executable: &ExecutableKey) -> Option<EffectSummary> {
        self.executable_effects.get(executable).copied()
    }

    pub fn executable_effects_inventory(&self) -> &HashMap<ExecutableKey, EffectSummary> {
        &self.executable_effects
    }

    pub fn abi_executable(&self, executable: &ExecutableKey) -> Option<&AbiReadyExecutable> {
        self.abi_executables.get(executable).map(Rc::as_ref)
    }

    pub fn abi_executables(&self) -> &HashMap<ExecutableKey, Rc<AbiReadyExecutable>> {
        &self.abi_executables
    }

    pub fn backend_executable(&self, executable: &ExecutableKey) -> Option<&SymbolicBackendExecutable> {
        self.backend_executables.get(executable).map(Rc::as_ref)
    }

    pub fn backend_executables(&self) -> &HashMap<ExecutableKey, Rc<SymbolicBackendExecutable>> {
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
    #[cfg(test)]
    pub fn replace_settled_return_demand_contributions(
        &mut self,
        tel: &impl Telemetry,
        caller: ExecutableKey,
        contributions: HashMap<ExecutableKey, RuntimeDemand>,
        settled_members: &HashSet<ExecutableKey>,
        types: &super::types::Types,
    ) -> HashSet<ExecutableKey> {
        self.replace_settled_demand_contributions(
            tel,
            vec![(caller, contributions, HashMap::new())],
            settled_members,
            types,
        )
    }

    pub fn replace_settled_demand_contributions(
        &mut self,
        tel: &impl Telemetry,
        mut transactions: Vec<DemandContributionTransaction>,
        settled_members: &HashSet<ExecutableKey>,
        types: &super::types::Types,
    ) -> HashSet<ExecutableKey> {
        transactions.sort_by(|(left, _, _), (right, _, _)| left.semantic_cmp(right, types));
        let mut affected_returns = HashSet::new();
        let mut affected_inputs = HashSet::new();
        for (caller, returns, inputs) in transactions {
            self.replace_return_demand_contributions(caller.clone(), returns, &mut affected_returns);
            self.replace_input_demand_contributions(caller, inputs, &mut affected_inputs);
        }
        let mut affected = affected_returns.union(&affected_inputs).cloned().collect::<Vec<_>>();
        affected.sort_by(|left, right| left.semantic_cmp(right, types));
        let mut displaced = HashSet::new();
        for target in affected {
            if affected_returns.contains(&target) {
                displaced.extend(self.recompute_return_demand(tel, &target, settled_members, types));
            }
            if affected_inputs.contains(&target) {
                displaced.extend(self.recompute_input_demand(tel, &target, settled_members, types));
            }
        }
        displaced
    }

    fn replace_return_demand_contributions(
        &mut self,
        caller: ExecutableKey,
        contributions: HashMap<ExecutableKey, RuntimeDemand>,
        affected: &mut HashSet<ExecutableKey>,
    ) {
        let previous = self.return_demand_contributions.remove(&caller).unwrap_or_default();
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
    }

    fn recompute_return_demand(
        &mut self,
        tel: &impl Telemetry,
        target: &ExecutableKey,
        settled_members: &HashSet<ExecutableKey>,
        types: &super::types::Types,
    ) -> HashSet<ExecutableKey> {
        let mut contributors = self
            .return_demand_contributors
            .get(target)
            .into_iter()
            .flatten()
            .cloned()
            .collect::<Vec<_>>();
        contributors.sort_by(|left, right| left.semantic_cmp(right, types));
        let joined = contributors
            .iter()
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
            self.invalidate_demand_derived_products(tel, target, types)
        } else {
            HashSet::new()
        }
    }

    /// The INPUT-side sibling of [`Self::replace_settled_return_demand_contributions`]:
    /// replace `caller`'s full set of SETTLED boundary input-demand pins
    /// (target -> position -> demand). Same OBSERVED/retraction semantics —
    /// a re-settled caller whose pin drops retracts cleanly because each
    /// target's joined positions are rebuilt from current contributors.
    #[cfg(test)]
    pub fn replace_settled_input_demand_contributions(
        &mut self,
        tel: &impl Telemetry,
        caller: ExecutableKey,
        contributions: HashMap<ExecutableKey, HashMap<usize, RuntimeDemand>>,
        settled_members: &HashSet<ExecutableKey>,
        types: &super::types::Types,
    ) -> HashSet<ExecutableKey> {
        self.replace_settled_demand_contributions(
            tel,
            vec![(caller, HashMap::new(), contributions)],
            settled_members,
            types,
        )
    }

    fn replace_input_demand_contributions(
        &mut self,
        caller: ExecutableKey,
        contributions: HashMap<ExecutableKey, HashMap<usize, RuntimeDemand>>,
        affected: &mut HashSet<ExecutableKey>,
    ) {
        let previous = self.input_demand_contributions.remove(&caller).unwrap_or_default();
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
    }

    fn recompute_input_demand(
        &mut self,
        tel: &impl Telemetry,
        target: &ExecutableKey,
        settled_members: &HashSet<ExecutableKey>,
        types: &super::types::Types,
    ) -> HashSet<ExecutableKey> {
        let mut joined: HashMap<usize, RuntimeDemand> = HashMap::new();
        let mut contributors = self
            .input_demand_contributors
            .get(target)
            .into_iter()
            .flatten()
            .cloned()
            .collect::<Vec<_>>();
        contributors.sort_by(|left, right| left.semantic_cmp(right, types));
        for contributor in &contributors {
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
            self.invalidate_demand_derived_products(tel, target, types)
        } else {
            HashSet::new()
        }
    }

    pub fn record_materialized_executable(
        &mut self,
        tel: &impl Telemetry,
        executable: ExecutableKey,
        materialized: Rc<MaterializedExecutable>,
        types: &super::types::Types,
    ) {
        let key = ProductKey::MaterializedExecutable(executable.clone());
        let ProductValue::MaterializedExecutable(materialized) = self
            .memo
            .retain_equal_value(&key, ProductValue::MaterializedExecutable(materialized))
        else {
            unreachable!("materialized retention preserves the product variant")
        };
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
                self.invalidate_demand_derived_products(tel, &executable, types);
            }
        }
        let effect_inputs = effect_relevant_inputs(&materialized);
        let effect_inputs_changed = self.latest_effect_inputs.get(&executable) != Some(&effect_inputs);
        let previous = self.latest_effect_inputs.insert(executable.clone(), effect_inputs);
        self.replace_effect_dependent_edges(&executable, previous.map(|(_, callees)| callees));
        self.materialized_executables.insert(executable.clone(), materialized);
        if effect_inputs_changed {
            self.invalidate_effect_cone(tel, &executable, types);
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

    pub fn record_abi_executable(&mut self, executable: ExecutableKey, abi: Rc<AbiReadyExecutable>) {
        let key = ProductKey::AbiExecutable(executable.clone());
        let ProductValue::AbiExecutable(abi) = self.memo.retain_equal_value(&key, ProductValue::AbiExecutable(abi))
        else {
            unreachable!("ABI retention preserves the product variant")
        };
        self.demanded_executables.insert(executable.clone());
        self.abi_executables.insert(executable, abi);
    }

    pub fn record_backend_executable(&mut self, executable: ExecutableKey, backend: Rc<SymbolicBackendExecutable>) {
        let key = ProductKey::BackendExecutable(executable.clone());
        let ProductValue::BackendExecutable(backend) = self
            .memo
            .retain_equal_value(&key, ProductValue::BackendExecutable(backend))
        else {
            unreachable!("backend retention preserves the product variant")
        };
        self.demanded_executables.insert(executable.clone());
        self.backend_executables.insert(executable, backend);
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

    pub fn assign_executable_index(&mut self, executable: ExecutableKey, index: usize) {
        self.demanded_executables.insert(executable.clone());
        self.executable_index.insert(executable, index);
    }

    /// The demand EPOCH wipe: settled demand retracts only here. Walks the
    /// demand-read dependents (callers) transitively, displacing each member's
    /// RuntimeDemand memo plus the transport/artifact products derived from it,
    /// so the next demand pull re-settles the affected cone against the new
    /// call graph. Returns the displaced executables.
    fn invalidate_demand_derived_products(
        &mut self,
        tel: &impl Telemetry,
        executable: &ExecutableKey,
        types: &super::types::Types,
    ) -> HashSet<ExecutableKey> {
        let mut stack = vec![executable.clone()];
        let mut seen = HashSet::new();
        let mut products = Vec::new();
        while let Some(current) = stack.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            products.push(ProductKey::RuntimeDemand(current.clone()));
            products.extend(artifact_product_keys(&current));
            stack.extend(
                self.runtime_demand_dependents
                    .get(&current)
                    .into_iter()
                    .flatten()
                    .chain(self.demand_flow_dependents.get(&current).into_iter().flatten())
                    .cloned(),
            );
        }
        self.memo.invalidate_products(tel, products, types);
        for current in &seen {
            self.materialized_executables.remove(current);
            self.abi_executables.remove(current);
            self.backend_executables.remove(current);
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
            | ProductKey::RuntimeDemand(_)
            | ProductKey::CallableResolution(_)
            | ProductKey::OutgoingEdgeFrontier(_)
            | ProductKey::OutgoingInputEdges(_)
            | ProductKey::IncomingInputRelations(_)
            | ProductKey::IncomingInputSlot(_)
            | ProductKey::CallableConstruction(_) => {}
        }
    }

    fn invalidate_artifact_products(
        &mut self,
        tel: &impl Telemetry,
        executable: &ExecutableKey,
        types: &super::types::Types,
    ) {
        self.memo
            .invalidate_products(tel, artifact_product_keys(executable), types);
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
    fn invalidate_effect_cone(
        &mut self,
        tel: &impl Telemetry,
        executable: &ExecutableKey,
        types: &super::types::Types,
    ) {
        let mut stack = vec![executable.clone()];
        let mut seen = HashSet::new();
        let mut products = Vec::new();
        while let Some(current) = stack.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            products.push(ProductKey::ExecutableEffects(current.clone()));
            stack.extend(self.effect_dependents.get(&current).into_iter().flatten().cloned());
        }
        self.memo.invalidate_products(tel, products, types);
        for current in seen {
            self.executable_effects.remove(&current);
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

    fn note_product_request(&mut self, tel: &impl Telemetry, key: &ProductKey, types: &super::types::Types) {
        if let ProductKey::OutgoingInputEdges(executable) = key
            && self.outgoing_edge_request_set.insert(executable.clone())
        {
            self.memo
                .remove(tel, &ProductKey::OutgoingEdgeFrontier(self.root), types);
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

fn artifact_product_keys(executable: &ExecutableKey) -> [ProductKey; 3] {
    [
        ProductKey::MaterializedExecutable(executable.clone()),
        ProductKey::AbiExecutable(executable.clone()),
        ProductKey::BackendExecutable(executable.clone()),
    ]
}

pub struct ProductReadContext<'s> {
    session: &'s mut PullSession,
    dependencies: ProductDependencies,
    staged: Vec<ProductCommitMember>,
    recursive_group: Option<Vec<ProductCommitMember>>,
    #[cfg(test)]
    product_reads: Vec<ProductReadObservation>,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProductReadObservation {
    pub(crate) key: ProductKey,
    pub(crate) hit: bool,
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
            #[cfg(test)]
            product_reads: Vec::new(),
        }
    }

    #[cfg(test)]
    pub(crate) fn product_read_checkpoint(&self) -> usize {
        self.product_reads.len()
    }

    #[cfg(test)]
    pub(crate) fn product_reads_since(&self, checkpoint: usize) -> Vec<ProductReadObservation> {
        self.product_reads[checkpoint..].to_vec()
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
    /// traversal that decides whether it closes a recursive group. Discovery
    /// must precede stale-read normalization: the pending edges are the
    /// evidence that the products are waiting on one another.
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
            let _ = self.read_product_entry(tel, dependency, types);
            return RecursiveProductRead::Group(members);
        }
        match self.read_product_entry(tel, dependency, types) {
            Some(value) => RecursiveProductRead::Ready(value),
            None => RecursiveProductRead::Waiting,
        }
    }

    pub(crate) fn recursive_group_callable_owners(
        &self,
        members: &[ProductKey],
        types: &super::types::Types,
    ) -> Vec<Rc<CallableConstructionOwner>> {
        let member_set = members.iter().collect::<HashSet<_>>();
        let mut dependencies = members
            .iter()
            .flat_map(|member| {
                self.session
                    .memo
                    .product_dependencies_for_group(member)
                    .into_iter()
                    .flat_map(|dependencies| dependencies.products.keys())
            })
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

    /// A group member's settled runtime demand, read without adding a second
    /// dependency after each member already recorded its own ordinary read.
    pub(crate) fn settled_runtime_demand(&self, executable: &ExecutableKey) -> Option<&ExecutableRuntimeDemand> {
        self.session.memo.runtime_demand(executable)
    }

    pub(crate) fn stage_callable_construction_group(
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
        assert!(
            self.recursive_group.replace(entries).is_none(),
            "one producer staged two recursive completions"
        );
        current_value
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
            #[cfg(test)]
            self.product_reads.push(ProductReadObservation {
                key: key.clone(),
                hit: false,
            });
            return None;
        }
        let generation = self.session.memo.generation(&key);
        self.dependencies.products.insert(key.clone(), generation);
        #[cfg(test)]
        self.product_reads.push(ProductReadObservation {
            key: key.clone(),
            hit: self.session.memo.get(&key).is_some(),
        });
        self.session.memo.get(&key)
    }

    pub fn read_runtime_demand(
        &mut self,
        tel: &impl Telemetry,
        executable: &ExecutableKey,
        types: &super::types::Types,
    ) -> Option<Rc<ExecutableRuntimeDemand>> {
        match self.read_product(tel, ProductKey::RuntimeDemand(executable.clone()), types) {
            Some(ProductValue::RuntimeDemand(demand)) => Some(Rc::clone(demand)),
            Some(other) => panic!("runtime demand product produced unexpected value {other:?}"),
            None => None,
        }
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

    pub(crate) fn publish_product(&mut self, key: ProductKey, value: ProductValue) {
        self.staged.push((key, value, self.dependencies.clone()));
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
    fn produce_runtime_demand(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome;
    fn produce_callable_resolution(
        &mut self,
        _context: &mut ProductReadContext<'_>,
        _key: &CallableResolutionKey,
    ) -> PullOutcome {
        panic!("callable resolution producer is not installed")
    }
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
    fn product_types(&self) -> &super::types::Types {
        self.world.types()
    }

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
        super::jobs::artifact::produce_executable_effects_product(
            self.telemetry,
            context,
            executable,
            self.world.types(),
        )
    }

    fn produce_runtime_demand(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome {
        super::jobs::runtime_demand::produce_runtime_demand_product(self.world, self.telemetry, context, executable)
    }

    fn produce_callable_resolution(
        &mut self,
        context: &mut ProductReadContext<'_>,
        key: &CallableResolutionKey,
    ) -> PullOutcome {
        super::jobs::runtime_demand::produce_callable_resolution_product(self.world, self.telemetry, context, key)
    }

    fn produce_outgoing_edge_frontier(&mut self, context: &mut ProductReadContext<'_>, _root: RootId) -> PullOutcome {
        PullOutcome::Produced(ProductValue::OutgoingEdgeFrontier(ordered_executable_frontier(
            context.session().outgoing_edge_requests(),
            self.world.types(),
        )))
    }

    fn produce_outgoing_input_edges(
        &mut self,
        context: &mut ProductReadContext<'_>,
        executable: &ExecutableKey,
    ) -> PullOutcome {
        super::jobs::runtime_demand::produce_outgoing_input_edges_product(
            self.world,
            self.telemetry,
            context,
            executable,
        )
    }

    fn produce_incoming_input_relations(&mut self, context: &mut ProductReadContext<'_>, root: RootId) -> PullOutcome {
        let frontier_key = ProductKey::OutgoingEdgeFrontier(root);
        let publishers = match context.read_product(self.telemetry, frontier_key.clone(), self.world.types()) {
            Some(ProductValue::OutgoingEdgeFrontier(publishers)) => Rc::clone(publishers),
            Some(value) => panic!("outgoing edge frontier produced unexpected value {value:?}"),
            None => return PullOutcome::wait_on_product(frontier_key),
        };
        let mut slots: HashMap<InputSlot, HashSet<IncomingInputSource>> = HashMap::new();
        let mut waits = Vec::new();
        for publisher in publishers.iter() {
            let key = ProductKey::OutgoingInputEdges(publisher.clone());
            match context.read_product(self.telemetry, key.clone(), self.world.types()) {
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
            PullOutcome::Produced(ProductValue::IncomingInputRelations(Rc::new(
                OrderedIncomingInputs::from_unordered(slots, self.world.types()),
            )))
        } else {
            PullOutcome::Waiting(waits)
        }
    }

    fn produce_incoming_input_slot(&mut self, context: &mut ProductReadContext<'_>, slot: &InputSlot) -> PullOutcome {
        let relations_key = ProductKey::IncomingInputRelations(context.session().root());
        match context.read_product(self.telemetry, relations_key.clone(), self.world.types()) {
            Some(ProductValue::IncomingInputRelations(relations)) => PullOutcome::Produced(
                ProductValue::IncomingInputSlot(relations.get(slot).unwrap_or_else(|| Rc::from([]))),
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
        super::jobs::transport::produce_transport_shape_product(self.world, self.telemetry, context, position)
    }

    fn produce_callable_construction(
        &mut self,
        context: &mut ProductReadContext<'_>,
        position: &TransportPosition,
    ) -> PullOutcome {
        super::jobs::transport::produce_callable_construction_product(self.world, self.telemetry, context, position)
    }
}

pub struct ProductDriver<'a, T: Telemetry> {
    tel: &'a T,
    session: PullSession,
    emit_causal_products: bool,
    emit_session_lifecycle: bool,
    request_ids: ProductRequestIds,
    finished: Cell<bool>,
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
        Self::with_session_id_source(tel, session, || allocate_pull_session_id(&NEXT_PULL_SESSION_ID))
    }

    fn with_session_id_source(
        tel: &'a T,
        mut session: PullSession,
        allocate_session_id: impl FnOnce() -> PullSessionId,
    ) -> Self {
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
        Self {
            tel,
            session,
            emit_causal_products: causal_product_events_enabled(tel),
            emit_session_lifecycle,
            request_ids: ProductRequestIds::new(),
            finished: Cell::new(false),
        }
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
        self.emit_finished_once();
    }

    pub(crate) fn apply_fact_movements(&mut self, movements: &[FactMovement<FactKey>]) {
        self.session.apply_fact_movements(movements);
    }

    pub fn pull(&mut self, producers: &mut impl ProductProducers, key: ProductKey) -> PullOutcome {
        assert!(
            !self.session.memo.contains_in_progress(&key),
            "safe product producers cannot recursively enter ProductDriver::pull"
        );
        let request = self.request_ids.allocate();
        if self.emit_causal_products {
            self.tel.raw_event2(PRODUCT_REQUESTED_EVENT, &key, &request);
        }
        self.session
            .reconcile_fact_movements(self.tel, producers.product_types());
        self.session
            .note_product_request(self.tel, &key, producers.product_types());
        if let Some(stale) = self.session.memo.stale_dependency(&key, producers.product_types()) {
            self.session
                .memo
                .prepare_stale_for_reproduction(self.tel, &stale, producers.product_types());
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
        assert!(
            self.session.memo.begin(key.clone()),
            "safe product producers cannot recursively enter ProductDriver::pull"
        );

        let mut context = ProductReadContext::new(&mut self.session);
        let outcome = match &key {
            ProductKey::RootBackendProduct(root) => producers.produce_root_backend_product(&mut context, *root),
            ProductKey::BackendExecutable(executable) => producers.produce_backend_executable(&mut context, executable),
            ProductKey::AbiExecutable(executable) => producers.produce_abi_executable(&mut context, executable),
            ProductKey::MaterializedExecutable(executable) => {
                producers.produce_materialized_executable(&mut context, executable)
            }
            ProductKey::ExecutableEffects(executable) => producers.produce_executable_effects(&mut context, executable),
            ProductKey::RuntimeDemand(executable) => producers.produce_runtime_demand(&mut context, executable),
            ProductKey::CallableResolution(key) => producers.produce_callable_resolution(&mut context, key),
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
        let (dependencies, mut staged, recursive_group) = context.into_completion();
        if self.emit_causal_products {
            self.tel.raw_event3(PRODUCT_EVALUATED_EVENT, &key, &request, &outcome);
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
                let settled = self.session.memo.finish_completion(
                    self.tel,
                    self.emit_causal_products,
                    &key,
                    completion,
                    producers.product_types(),
                );
                if !settled {
                    self.session.discard_product_side_effects(&key);
                    let waits = vec![PullWait::Product(key.clone())];
                    PullOutcome::Waiting(waits)
                } else {
                    PullOutcome::Produced(
                        self.session
                            .memo
                            .get(&key)
                            .expect("settled completion must install its requested product")
                            .clone(),
                    )
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

    fn emit_finished_once(&self) {
        if self.emit_session_lifecycle && !self.finished.replace(true) {
            self.session.emit_finished(self.tel);
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
        let current = ProductKey::RuntimeDemand(fake_executable_with_function(root, 840));
        let dependency = ProductKey::RuntimeDemand(fake_executable_with_function(root, 841));
        let peer = ProductKey::RuntimeDemand(fake_executable_with_function(root, 842));
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
        let current = ProductKey::RuntimeDemand(fake_executable_with_function(root, 850));
        let missing = ProductKey::RuntimeDemand(fake_executable_with_function(root, 851));
        let ready = ProductKey::RuntimeDemand(fake_executable_with_function(root, 852));
        let cyclic = ProductKey::RuntimeDemand(fake_executable_with_function(root, 853));
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
            [860, 861, 862].map(|function| ProductKey::RuntimeDemand(fake_executable_in(&mut types, root, function)));
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
            [880, 881, 882].map(|function| ProductKey::RuntimeDemand(fake_executable_in(&mut types, root, function)));
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
            .map(|function| ProductKey::RuntimeDemand(fake_executable_in(&mut types, root, function)));
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
            let replacement = ProductValue::OutgoingEdgeFrontier(ordered_frontier([]));
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
    fn incoming_input_values_hide_frontier_slot_and_source_insertion_order() {
        let root = RootId::for_test(90);
        let mut types = super::super::Types::new();
        let [producer_a, producer_b, callee_a, callee_b] =
            [900, 901, 902, 903].map(|function| fake_executable_in(&mut types, root, function));
        let slot_a = InputSlot {
            executable: callee_a,
            semantic_index: 1,
        };
        let slot_b = InputSlot {
            executable: callee_b,
            semantic_index: 0,
        };
        let source_a = IncomingInputSource {
            producer: producer_a.clone(),
            value: ValueId::from_u32(2),
            role: IncomingInputRole::CallArgument,
        };
        let source_b = IncomingInputSource {
            producer: producer_b.clone(),
            value: ValueId::from_u32(1),
            role: IncomingInputRole::CallableCapture {
                construction: ValueId::from_u32(3),
                capture_index: 0,
            },
        };

        let forward_frontier = HashSet::from([producer_a.clone(), producer_b.clone()]);
        let reverse_frontier = [producer_b, producer_a].into_iter().collect();
        assert_eq!(
            ordered_executable_frontier(&forward_frontier, &types),
            ordered_executable_frontier(&reverse_frontier, &types)
        );

        let forward = OrderedIncomingInputs::from_unordered(
            HashMap::from([
                (slot_a.clone(), HashSet::from([source_a.clone(), source_b.clone()])),
                (slot_b.clone(), HashSet::from([source_b.clone(), source_a.clone()])),
            ]),
            &types,
        );
        let reverse = OrderedIncomingInputs::from_unordered(
            [
                (slot_b, [source_a.clone(), source_b.clone()].into_iter().collect()),
                (
                    slot_a.clone(),
                    [source_b.clone(), source_a.clone()].into_iter().collect(),
                ),
            ]
            .into_iter()
            .collect(),
            &types,
        );
        assert_eq!(forward, reverse);
        assert_eq!(forward.get(&slot_a), reverse.get(&slot_a));
        let mut expected_sources = vec![source_a, source_b];
        expected_sources.sort_by(|left, right| compare_incoming_input_sources(left, right, &types));
        assert_eq!(forward.get(&slot_a).expect("slot a").as_ref(), expected_sources);
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
            if self.self_wait.as_ref() == Some(&key) {
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
        fn product_types(&self) -> &super::super::Types {
            &self.types
        }

        fn produce_root_backend_product(&mut self, context: &mut ProductReadContext<'_>, root: RootId) -> PullOutcome {
            let tel = ConfiguredTelemetry::new();
            let key = ProductKey::RootBackendProduct(root);
            self.calls.push(key.clone());
            let mut waits = if self.root_prerequisites.is_empty() {
                Vec::new()
            } else {
                self.root_prerequisites
                    .iter()
                    .filter(|prerequisite| {
                        context
                            .read_product_entry(&tel, (*prerequisite).clone(), &self.types)
                            .is_none()
                    })
                    .cloned()
                    .map(PullWait::Product)
                    .collect::<Vec<_>>()
            };
            if let Some(prerequisite) = self.root_recursive_prerequisite.clone() {
                let telemetry = self
                    .recursive_telemetry
                    .as_ref()
                    .expect("a recursive fake producer needs its driver telemetry");
                if matches!(
                    context.read_recursive_product(telemetry.as_ref(), prerequisite.clone(), &key, &self.types),
                    RecursiveProductRead::Waiting
                ) {
                    waits.push(PullWait::Product(prerequisite));
                }
            }
            if !waits.is_empty() {
                return PullOutcome::Waiting(waits);
            }
            let prerequisite =
                ProductKey::RuntimeDemand(self.root_entry.clone().expect("fake root entry should be set"));
            if context
                .read_product_entry(&tel, prerequisite.clone(), &self.types)
                .is_some()
            {
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
            if let Some(child) = self.runtime_children.get(&key).cloned()
                && context
                    .read_product_entry(&ConfiguredTelemetry::new(), child.clone(), &self.types)
                    .is_none()
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
    fn unchanged_reproduction_returns_the_canonical_memo_handle() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(63);
        let key = ProductKey::RuntimeDemand(fake_executable_with_function(root, 630));
        let first = Rc::new(ExecutableRuntimeDemand::default());
        let equal_but_distinct = Rc::new(ExecutableRuntimeDemand::default());
        let mut producers = FakeProducers {
            runtime_value: Some(ProductValue::RuntimeDemand(Rc::clone(&first))),
            ..FakeProducers::default()
        };
        let mut driver = ProductDriver::new(&tel, root);

        match driver.pull(&mut producers, key.clone()) {
            PullOutcome::Produced(ProductValue::RuntimeDemand(value)) => assert!(Rc::ptr_eq(&value, &first)),
            other => panic!("expected first runtime demand, got {other:?}"),
        }
        driver
            .session
            .memo
            .prepare_stale_for_reproduction(&tel, &key, &producers.types);
        producers.runtime_value = Some(ProductValue::RuntimeDemand(equal_but_distinct));

        match driver.pull(&mut producers, key.clone()) {
            PullOutcome::Produced(ProductValue::RuntimeDemand(value)) => assert!(
                Rc::ptr_eq(&value, &first),
                "an unchanged producer run must return the memo's retained allocation",
            ),
            other => panic!("expected reproduced runtime demand, got {other:?}"),
        }
        match driver.session.memo.get(&key) {
            Some(ProductValue::RuntimeDemand(value)) => assert!(Rc::ptr_eq(value, &first)),
            other => panic!("expected canonical memoized runtime demand, got {other:?}"),
        }
    }

    #[test]
    fn product_driver_correlates_waiting_producer_runs_and_cache_hits() {
        let tel = Rc::new(ConfiguredTelemetry::new());
        let (buf, writer) = crate::telemetry::capture::vec_writer();
        JsonlBackend::new_writer(writer).install(tel.as_ref());
        let root = RootId::for_test(90);
        let root_key = ProductKey::RootBackendProduct(root);
        let dependency = ProductKey::RuntimeDemand(fake_executable_with_function(root, 901));
        let dependency_child = ProductKey::RuntimeDemand(fake_executable_with_function(root, 902));
        let moved = ProductKey::RuntimeDemand(fake_executable_with_function(root, 903));
        let mut producers = FakeProducers {
            root_entry: match &dependency {
                ProductKey::RuntimeDemand(executable) => Some(executable.clone()),
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
        let key = ProductKey::RuntimeDemand(fake_executable(root));
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
        let key = ProductKey::RuntimeDemand(fake_executable(root));
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
        let parent = ProductKey::RuntimeDemand(executable.clone());
        let child = ProductKey::BackendExecutable(executable);
        let fact = FactUse::current(FactKey::CodeIndexed(super::super::CodeId::ZERO));
        let mut producers = FakeProducers {
            root_entry: match &parent {
                ProductKey::RuntimeDemand(executable) => Some(executable.clone()),
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

        assert!(driver.session.memo.begin(key.clone()));
        assert!(catch_unwind(AssertUnwindSafe(|| driver.pull(&mut producers, key.clone()))).is_err());
        assert_eq!(requests.get(), 0);
        assert_eq!(driver.request_ids.next, NonZeroU64::new(1));
        assert!(driver.session.memo.contains_in_progress(&key));
        assert!(producers.calls.is_empty());
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
            PullOutcome::Produced(ProductValue::OutgoingEdgeFrontier(ordered_frontier([first.clone(),])))
        );
        let first_generation = driver.session().memo().generation(&frontier);

        driver.pull(&mut fake, ProductKey::OutgoingInputEdges(first.clone()));
        driver.pull(&mut fake, ProductKey::BackendExecutable(first.clone()));
        assert_eq!(driver.session().memo().generation(&frontier), first_generation);

        fake.self_wait = Some(ProductKey::OutgoingInputEdges(second.clone()));
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
            PullOutcome::Produced(ProductValue::OutgoingEdgeFrontier(ordered_frontier([first, second])))
        );
        assert_ne!(driver.session().memo().generation(&frontier), first_generation);
    }

    #[test]
    fn pull_session_invalidates_runtime_demand_when_return_demand_grows() {
        let tel = ConfiguredTelemetry::new();
        let types = fake_types();
        let caller = fake_executable(RootId::for_test(5));
        let callee = fake_executable(RootId::for_test(5));
        let mut session = PullSession::new(RootId::for_test(5));
        finish_test_entry(
            &mut session.memo,
            &tel,
            &ProductKey::RuntimeDemand(callee.clone()),
            ProductValue::RuntimeDemand(Rc::default()),
            ProductDependencies::default(),
            &types,
        );

        session.replace_settled_return_demand_contributions(
            &tel,
            caller,
            HashMap::from([(callee.clone(), RuntimeDemand::whole())]),
            &HashSet::new(),
            &types,
        );

        assert_eq!(
            session.external_return_demand(&callee, &HashSet::new(), &types),
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
        let tel = ConfiguredTelemetry::new();
        let types = fake_types();
        let caller = fake_executable(RootId::for_test(7));
        let callee = fake_executable(RootId::for_test(7));
        let mut session = PullSession::new(RootId::for_test(7));

        session.replace_settled_return_demand_contributions(
            &tel,
            caller.clone(),
            HashMap::from([(callee.clone(), RuntimeDemand::whole())]),
            &HashSet::new(),
            &types,
        );
        assert_eq!(
            session.external_return_demand(&callee, &HashSet::new(), &types),
            Some(RuntimeDemand::whole())
        );

        finish_test_entry(
            &mut session.memo,
            &tel,
            &ProductKey::RuntimeDemand(callee.clone()),
            ProductValue::RuntimeDemand(Rc::default()),
            ProductDependencies::default(),
            &types,
        );
        session.replace_settled_return_demand_contributions(
            &tel,
            caller.clone(),
            HashMap::from([(callee.clone(), RuntimeDemand::ignore())]),
            &HashSet::new(),
            &types,
        );

        assert_eq!(
            session.external_return_demand(&callee, &HashSet::new(), &types),
            Some(RuntimeDemand::ignore()),
            "a collapsed caller retracts its callee's whole demand down to the observed discard"
        );
        assert!(
            session.memo().get(&ProductKey::RuntimeDemand(callee.clone())).is_none(),
            "retracting a non-member callee's return demand re-settles its runtime demand"
        );

        session.replace_settled_return_demand_contributions(&tel, caller, HashMap::new(), &HashSet::new(), &types);
        assert_eq!(
            session.external_return_demand(&callee, &HashSet::new(), &types),
            None,
            "withdrawing the last contributor leaves the callee not-yet-observed (distinct from an observed discard)"
        );
    }

    #[test]
    fn pull_session_invalidates_runtime_demand_when_input_demand_grows() {
        let tel = ConfiguredTelemetry::new();
        let types = fake_types();
        let caller = fake_executable(RootId::for_test(9));
        let callee = fake_executable(RootId::for_test(9));
        let mut session = PullSession::new(RootId::for_test(9));
        finish_test_entry(
            &mut session.memo,
            &tel,
            &ProductKey::RuntimeDemand(callee.clone()),
            ProductValue::RuntimeDemand(Rc::default()),
            ProductDependencies::default(),
            &types,
        );

        session.replace_settled_input_demand_contributions(
            &tel,
            caller,
            HashMap::from([(callee.clone(), HashMap::from([(0, RuntimeDemand::whole())]))]),
            &HashSet::new(),
            &types,
        );

        assert_eq!(
            session.external_input_demand(&callee, &HashSet::new(), &types),
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
        let tel = ConfiguredTelemetry::new();
        let types = fake_types();
        let caller = fake_executable(RootId::for_test(11));
        let callee = fake_executable(RootId::for_test(11));
        let mut session = PullSession::new(RootId::for_test(11));

        session.replace_settled_input_demand_contributions(
            &tel,
            caller.clone(),
            HashMap::from([(callee.clone(), HashMap::from([(0, RuntimeDemand::whole())]))]),
            &HashSet::new(),
            &types,
        );
        assert_eq!(
            session.external_input_demand(&callee, &HashSet::new(), &types),
            HashMap::from([(0, RuntimeDemand::whole())])
        );

        finish_test_entry(
            &mut session.memo,
            &tel,
            &ProductKey::RuntimeDemand(callee.clone()),
            ProductValue::RuntimeDemand(Rc::default()),
            ProductDependencies::default(),
            &types,
        );
        session.replace_settled_input_demand_contributions(
            &tel,
            caller.clone(),
            HashMap::from([(callee.clone(), HashMap::from([(0, RuntimeDemand::ignore())]))]),
            &HashSet::new(),
            &types,
        );

        assert_eq!(
            session.external_input_demand(&callee, &HashSet::new(), &types),
            HashMap::from([(0, RuntimeDemand::ignore())]),
            "a collapsed caller retracts its callee's whole position demand down to the observed discard"
        );
        assert!(
            session.memo().get(&ProductKey::RuntimeDemand(callee.clone())).is_none(),
            "retracting a non-member callee's input demand re-settles its runtime demand"
        );

        session.replace_settled_input_demand_contributions(&tel, caller, HashMap::new(), &HashSet::new(), &types);
        assert_eq!(
            session.external_input_demand(&callee, &HashSet::new(), &types),
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
    fn contribution_transaction_is_canonical_across_callers_targets_and_contributors() {
        let root = RootId::for_test(89);
        let mut types = super::super::Types::new();
        let [caller_a, caller_b, target_a, target_b] =
            [890, 891, 892, 893].map(|function| fake_executable_in(&mut types, root, function));
        let mut expected_displaced = vec![
            ProductKey::RuntimeDemand(target_a.clone()),
            ProductKey::RuntimeDemand(target_b.clone()),
        ];
        sort_product_keys(&mut expected_displaced, &types);

        for reverse in [false, true] {
            let tel = ConfiguredTelemetry::new();
            let mut session = PullSession::new(root);
            for key in &expected_displaced {
                finish_test_product(&mut session.memo, key, ProductValue::Unit, []);
            }
            let displaced = Rc::new(RefCell::new(Vec::new()));
            let sink = Rc::clone(&displaced);
            tel.attach_raw_event1::<ProductKey, _>(
                &["fz", "compiler2", "pull", "product", "displaced"],
                move |_, _, _, key| sink.borrow_mut().push(key.clone()),
            );
            let mut transactions = vec![
                (
                    caller_a.clone(),
                    HashMap::from([(target_b.clone(), RuntimeDemand::whole())]),
                    HashMap::from([(target_a.clone(), HashMap::from([(0, RuntimeDemand::whole())]))]),
                ),
                (
                    caller_b.clone(),
                    HashMap::from([(target_a.clone(), RuntimeDemand::ignore())]),
                    HashMap::from([(target_b.clone(), HashMap::from([(1, RuntimeDemand::whole())]))]),
                ),
            ];
            if reverse {
                transactions.reverse();
            }
            let changed = session.replace_settled_demand_contributions(&tel, transactions, &HashSet::new(), &types);

            assert_eq!(*displaced.borrow(), expected_displaced);
            assert_eq!(changed, HashSet::from([target_a.clone(), target_b.clone()]));
            assert_eq!(
                session.external_return_demand(&target_a, &HashSet::new(), &types),
                Some(RuntimeDemand::ignore())
            );
            assert_eq!(
                session.external_return_demand(&target_b, &HashSet::new(), &types),
                Some(RuntimeDemand::whole())
            );
            assert_eq!(
                session.external_input_demand(&target_a, &HashSet::new(), &types),
                HashMap::from([(0, RuntimeDemand::whole())])
            );
            assert_eq!(
                session.external_input_demand(&target_b, &HashSet::new(), &types),
                HashMap::from([(1, RuntimeDemand::whole())])
            );
        }
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
        driver.session.memo.remove(&tel, &caller_key, &fake.types);
        finish_test_entry(
            &mut driver.session.memo,
            &tel,
            &caller_key,
            ProductValue::OutgoingInputEdges(ordered_inputs(HashMap::from([(
                slot.clone(),
                HashSet::from([source.clone()]),
            )]))),
            ProductDependencies::default(),
            &fake.types,
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
                PullOutcome::Produced(ProductValue::IncomingInputSlot(ordered_sources([source.clone()])))
            );
        }
        let source_generation = driver.session.memo.generation(&incoming_key);
        let relations_generation = driver.session.memo.generation(&relations_key);

        let unrelated_key = ProductKey::OutgoingInputEdges(unrelated);
        driver.pull(&mut fake, unrelated_key.clone());
        driver.session.memo.remove(&tel, &unrelated_key, &fake.types);
        finish_test_entry(
            &mut driver.session.memo,
            &tel,
            &unrelated_key,
            ProductValue::OutgoingInputEdges(ordered_inputs(HashMap::new())),
            ProductDependencies::default(),
            &fake.types,
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
                PullOutcome::Produced(ProductValue::IncomingInputSlot(ordered_sources([source])))
            );
        }
        assert_eq!(driver.session.memo.generation(&incoming_key), source_generation);
        assert_eq!(driver.session.memo.generation(&relations_key), relations_generation);

        driver.session.memo.remove(&tel, &caller_key, &fake.types);
        finish_test_entry(
            &mut driver.session.memo,
            &tel,
            &caller_key,
            ProductValue::OutgoingInputEdges(ordered_inputs(HashMap::new())),
            ProductDependencies::default(),
            &fake.types,
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
            PullOutcome::Produced(ProductValue::IncomingInputSlot(ordered_sources([])))
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
                runtime_demand: Rc::new(ExecutableRuntimeDemand::default()),
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
                runtime_demand: Rc::new(ExecutableRuntimeDemand::default()),
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
                runtime_demand: Rc::new(ExecutableRuntimeDemand::default()),
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
            driver.pull(&mut producers, ProductKey::RuntimeDemand(executable)),
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
        let key = ProductKey::RuntimeDemand(fake_executable(root));
        let mut driver = ProductDriver::new(&tel, root);
        driver.request_ids.next = NonZeroU64::new(u64::MAX);
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
        assert!(driver.request_ids.next.is_none(), "exhaustion must be permanent");
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

    fn ordered_frontier(values: impl IntoIterator<Item = ExecutableKey>) -> Rc<[ExecutableKey]> {
        let types = fake_types();
        let mut values = values.into_iter().collect::<Vec<_>>();
        values.sort_by(|left, right| left.semantic_cmp(right, &types));
        values.dedup();
        Rc::from(values)
    }

    fn ordered_inputs(values: HashMap<InputSlot, HashSet<IncomingInputSource>>) -> Rc<OrderedIncomingInputs> {
        Rc::new(OrderedIncomingInputs::from_unordered(values, &fake_types()))
    }

    fn ordered_sources(values: impl IntoIterator<Item = IncomingInputSource>) -> Rc<[IncomingInputSource]> {
        let types = fake_types();
        let mut values = values.into_iter().collect::<Vec<_>>();
        values.sort_by(|left, right| compare_incoming_input_sources(left, right, &types));
        values.dedup();
        Rc::from(values)
    }

    fn record_materialized_product(
        session: &mut PullSession,
        executable: ExecutableKey,
        materialized: MaterializedExecutable,
    ) {
        let tel = ConfiguredTelemetry::new();
        session.record_materialized_executable(
            &tel,
            executable.clone(),
            Rc::new(materialized.clone()),
            &super::super::Types::new(),
        );
        finish_test_entry(
            &mut session.memo,
            &tel,
            &ProductKey::MaterializedExecutable(executable),
            ProductValue::MaterializedExecutable(Rc::new(materialized)),
            ProductDependencies::default(),
            &fake_types(),
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
            ProductValue::RootBackendProduct(Rc::new(RootBackendProductAnswer {
                program: Rc::new(super::super::artifact::BackendProgram {
                    entry: 0,
                    atom_names: Vec::new(),
                    struct_schemas: Default::default(),
                    executables: Vec::new(),
                    construction_wrappers: Vec::new(),
                }),
                transport: super::super::artifact::MaterializedTransportPlan {
                    entry: left_resolution.clone(),
                    executable_membership: Box::default(),
                    position_layouts: Vec::new(),
                    callable_boundaries: Vec::new(),
                    boundary_ids: Vec::new(),
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
            ProductValue::IncomingInputSlot(ordered_sources([IncomingInputSource {
                producer: fake_executable_with_function(root, producer),
                value: ValueId::from_u32(1),
                role: IncomingInputRole::CallArgument,
            }]))
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
    /// event PER MEMBER (not just the anchor `finish_group` was called for),
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
        let left = ProductKey::RuntimeDemand(fake_executable_with_function(root, 600));
        let right = ProductKey::RuntimeDemand(fake_executable_with_function(root, 601));
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
        let left = ProductKey::RuntimeDemand(fake_executable_with_function(root, 610));
        let right = ProductKey::RuntimeDemand(fake_executable_with_function(root, 611));
        let external = ProductKey::RuntimeDemand(fake_executable_with_function(root, 612));
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
    fn shared_payloads_keep_structural_generation_semantics() {
        let tel = ConfiguredTelemetry::new();
        let types = fake_types();
        let key = ProductKey::RuntimeDemand(fake_executable_with_function(RootId::for_test(62), 620));
        let first = Rc::new(ExecutableRuntimeDemand::default());
        let retained = Rc::clone(&first);
        let same = Rc::clone(&first);
        let equal_but_distinct = Rc::new(ExecutableRuntimeDemand::default());
        assert!(!Rc::ptr_eq(&first, &equal_but_distinct));

        let mut memo = ProductMemo::default();
        assert!(finish_test_entry(
            &mut memo,
            &tel,
            &key,
            ProductValue::RuntimeDemand(first),
            ProductDependencies::default(),
            &types,
        ));
        assert!(finish_test_entry(
            &mut memo,
            &tel,
            &key,
            ProductValue::RuntimeDemand(same),
            ProductDependencies::default(),
            &types,
        ));
        assert_eq!(memo.generation(&key), Some(1));
        assert!(finish_test_entry(
            &mut memo,
            &tel,
            &key,
            ProductValue::RuntimeDemand(equal_but_distinct),
            ProductDependencies::default(),
            &types,
        ));
        assert_eq!(memo.generation(&key), Some(1));
        match memo.get(&key) {
            Some(ProductValue::RuntimeDemand(current)) => assert!(
                Rc::ptr_eq(current, &retained),
                "an equal settlement must retain the already-memoized allocation",
            ),
            other => panic!("expected memoized runtime demand, got {other:?}"),
        }

        let changed = ExecutableRuntimeDemand {
            return_demand: RuntimeDemand::whole(),
            ..ExecutableRuntimeDemand::default()
        };
        assert!(finish_test_entry(
            &mut memo,
            &tel,
            &key,
            ProductValue::RuntimeDemand(Rc::new(changed)),
            ProductDependencies::default(),
            &types,
        ));
        assert_eq!(memo.generation(&key), Some(2));
    }

    #[test]
    fn changed_product_authority_discards_pending_reader_snapshots_before_group_settlement() {
        let types = fake_types();
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
        let left = ProductKey::RuntimeDemand(fake_executable_with_function(root, 420));
        let right = ProductKey::RuntimeDemand(fake_executable_with_function(root, 421));
        let external = ProductKey::RuntimeDemand(fake_executable_with_function(root, 422));

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
        let slot_value = ProductValue::IncomingInputSlot(ordered_sources([IncomingInputSource {
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
            ProductValue::IncomingInputSlot(ordered_sources([
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
