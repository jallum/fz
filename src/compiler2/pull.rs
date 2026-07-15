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
    AbiReadyExecutable, BackendCallArg, BackendProgram, BackendReceive, BackendStep, CallEdge, CallReturnFlow,
    EffectSummary, MaterializedExecutable, ReusableConsCapture,
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
use super::transport::{
    BoundaryFacts, BoundaryId, CallableConstructionFact, CallableFacts, CallableId, CodegenSeamFact, ExecutableSymbol,
    ShapeId, TransportPosition,
};
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
    TransportComponent(TransportPosition),
    CallableFacts(CallableId),
    BoundaryFacts(BoundaryId),
    /// The session's published codegen seam facts, over every boundary
    /// recorded in `PullSession::boundary_facts_inventory` so far. Computed
    /// once per root per invalidation epoch (see `record_boundary_facts`),
    /// not once per executable production: both
    /// `produce_materialized_executable_product` and
    /// `produce_abi_executable_product` pull this instead of rebuilding and
    /// sorting the full seam-fact set on every call.
    CodegenSeamFacts(RootId),
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
            Self::TransportComponent(_) => "transport_component",
            Self::CallableFacts(_) => "callable_facts",
            Self::BoundaryFacts(_) => "boundary_facts",
            Self::CodegenSeamFacts(_) => "codegen_seam_facts",
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
            | Self::TransportComponent(_)
            | Self::CallableFacts(_)
            | Self::BoundaryFacts(_)
            | Self::CodegenSeamFacts(_) => None,
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
    Layout(TransportLayout),
    AbsentForClosure(u64),
}

impl TransportShapeFact {
    pub fn shape(&self) -> Option<ShapeId> {
        match self {
            Self::Layout(layout) => Some(layout.structural),
            Self::AbsentForClosure(_) => None,
        }
    }

    pub fn layout(&self) -> Option<TransportLayout> {
        match self {
            Self::Layout(layout) => Some(*layout),
            Self::AbsentForClosure(_) => None,
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
    ExecutableFacts(Rc<ExecutableFacts>),
    RuntimeDemand(Box<ExecutableRuntimeDemand>),
    OutgoingEdgeFrontier(Rc<HashSet<ExecutableKey>>),
    OutgoingInputEdges(Rc<HashMap<InputSlot, HashSet<IncomingInputSource>>>),
    IncomingInputRelations(Rc<HashMap<InputSlot, HashSet<IncomingInputSource>>>),
    IncomingInputSlot(HashSet<IncomingInputSource>),
    TransportShape(TransportShapeFact),
    TransportComponent(TransportComponentInventory),
    CallableFacts(Option<CallableFacts>),
    BoundaryFacts(Option<BoundaryFacts>),
    CodegenSeamFacts(Box<[CodegenSeamFact]>),
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

    pub fn contains_in_progress(&self, key: &ProductKey) -> bool {
        self.in_progress.contains(key)
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
                | ProductValue::TransportComponent(_)
                | ProductValue::CallableFacts(_)
                | ProductValue::BoundaryFacts(_)
                | ProductValue::CodegenSeamFacts(_),
            )
            | None => None,
        }
    }

    /// The session-wide codegen seam facts, once settled for the current
    /// invalidation epoch. `None` means the product has not been produced
    /// yet (or was displaced by `record_boundary_facts` observing a changed
    /// boundary) -- the caller should wait on
    /// `ProductKey::CodegenSeamFacts(root)`, exactly like `runtime_demand`
    /// above.
    pub fn codegen_seam_facts(&self, root: RootId) -> Option<&[CodegenSeamFact]> {
        match self.get(&ProductKey::CodegenSeamFacts(root)) {
            Some(ProductValue::CodegenSeamFacts(facts)) => Some(facts.as_ref()),
            Some(
                ProductValue::Unit
                | ProductValue::RootBackendProduct(_)
                | ProductValue::BackendExecutable(_)
                | ProductValue::AbiExecutable(_)
                | ProductValue::MaterializedExecutable(_)
                | ProductValue::ExecutableEffects(_)
                | ProductValue::ExecutableFacts(_)
                | ProductValue::RuntimeDemand(_)
                | ProductValue::OutgoingEdgeFrontier(_)
                | ProductValue::OutgoingInputEdges(_)
                | ProductValue::IncomingInputRelations(_)
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

    fn finish(&mut self, key: &ProductKey, value: ProductValue, dependencies: ProductDependencies) -> bool {
        self.in_progress.remove(key);
        if self.invalidated_in_progress.remove(key) {
            self.produced.remove(key);
            return false;
        }
        let previous = self.produced.remove(key).or_else(|| self.displaced.remove(key));
        self.remove_reader_dependencies(key, previous.as_ref().map(|entry| &entry.dependencies));
        let pending = self.pending_dependencies.remove(key);
        self.remove_reader_dependencies(key, pending.as_ref());
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

    fn unblock(&mut self, key: &ProductKey, dependencies: ProductDependencies) {
        self.in_progress.remove(key);
        self.invalidated_in_progress.remove(key);
        let previous = self.pending_dependencies.remove(key).unwrap_or_default();
        self.remove_reader_dependencies(key, Some(&previous));
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
        if let Some(entry) = self.produced.remove(key) {
            self.remove_reader_dependencies(key, Some(&entry.dependencies));
            self.displaced.insert(key.clone(), entry);
            self.mark_readers_dirty(key);
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TransportComponentInventory {
    /// The canonical component representative: the running-min member position
    /// under the structural position order. Every member's pull materializes
    /// an inventory carrying this same representative and membership.
    pub representative: TransportPosition,
    pub positions: Vec<TransportPosition>,
}

/// One connected component of a solved transport shape-constraint closure: its
/// canonical representative, every member position, and the component's agreed
/// shape (`None` when no anchor grounded the component).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolvedTransportComponent {
    pub representative: TransportPosition,
    pub positions: Vec<TransportPosition>,
    pub shape: Option<ShapeId>,
}

/// The full result of ONE shape-constraint solve over a settled executable
/// closure: every connected component indexed by member position, the exact
/// boundary-publication positions it derived, and the executable cover it
/// projected. A position of a covered executable that is absent from
/// `component_of` was proven unconstrained by this same solve -- it needs a
/// singleton component, not a re-solve.
#[derive(Debug, Default)]
pub struct SolvedTransportClosure {
    pub executables: HashSet<ExecutableKey>,
    pub component_of: HashMap<TransportPosition, usize>,
    pub components: Vec<SolvedTransportComponent>,
    pub(crate) boundary_publications: HashSet<TransportPosition>,
    /// Settled world facts consumed by the solve at their exact states.
    pub consumed_fact_states: HashMap<FactKey, FactState>,
    /// Session-product owners consulted while discovering the closure.
    pub consulted: HashSet<ExecutableKey>,
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
    demanded_transport_positions: HashSet<TransportPosition>,
    // By-symbol view of the EntryCapture/ResumePayload members of
    // `demanded_transport_positions` -- the only variants
    // `session_materialized_executable_transport` reads from the demanded
    // set. The demanded set is monotone (positions are never retracted), so
    // this index needs no invalidation story: it grows in lockstep inside
    // `note_demanded_transport_position`, the single insertion point.
    demanded_capture_resume_positions: HashMap<ExecutableSymbol, HashSet<TransportPosition>>,
    transport_shape_facts: HashMap<TransportPosition, TransportShapeFact>,
    transport_layouts: HashMap<TransportPosition, TransportLayout>,
    // `transport_shapes` and `transport_shapes_by_symbol` are one fact in two
    // keyings: the flat position->shape map, and the per-owning-executable
    // index `session_materialized_executable_transport` consumes instead of
    // filter-scanning the whole inventory per production. They mutate ONLY
    // through `insert_transport_shape`/`remove_transport_shape`, so the index
    // lives and dies with the map by construction -- including the epoch
    // removals in `invalidate_transport_products` and the displaced-product
    // removals in `discard_product_side_effects`.
    transport_shapes: HashMap<TransportPosition, ShapeId>,
    transport_shapes_by_symbol: HashMap<ExecutableSymbol, HashSet<TransportPosition>>,
    transport_components: HashMap<TransportPosition, TransportComponentInventory>,
    // Live solved closures and the exact reverse indexes for their member,
    // world-fact, and session-product ownership.
    solved_transport_closures: HashMap<u64, SolvedTransportClosure>,
    transport_closure_cover: HashMap<ExecutableKey, u64>,
    transport_closure_fact_dependents: HashMap<FactKey, HashSet<u64>>,
    transport_closure_counter: u64,
    // Session-product owner -> covered members. Entries are installed and
    // retracted with the closure that owns them.
    transport_closure_consult_dependents: HashMap<ExecutableKey, HashSet<ExecutableKey>>,
    transport_positions_by_executable: HashMap<ExecutableKey, HashSet<TransportPosition>>,
    callable_facts: HashMap<CallableId, CallableFacts>,
    callable_constructions: HashMap<TransportPosition, CallableConstructionFact>,
    boundary_facts: HashMap<BoundaryId, BoundaryFacts>,
    demanded_callables: HashSet<CallableId>,
    demanded_boundaries: HashSet<BoundaryId>,
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
            demanded_transport_positions: HashSet::new(),
            demanded_capture_resume_positions: HashMap::new(),
            transport_shape_facts: HashMap::new(),
            transport_shapes: HashMap::new(),
            transport_layouts: HashMap::new(),
            transport_shapes_by_symbol: HashMap::new(),
            transport_components: HashMap::new(),
            solved_transport_closures: HashMap::new(),
            transport_closure_cover: HashMap::new(),
            transport_closure_fact_dependents: HashMap::new(),
            transport_closure_counter: 0,
            transport_closure_consult_dependents: HashMap::new(),
            transport_positions_by_executable: HashMap::new(),
            callable_facts: HashMap::new(),
            callable_constructions: HashMap::new(),
            boundary_facts: HashMap::new(),
            demanded_callables: HashSet::new(),
            demanded_boundaries: HashSet::new(),
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
            // Artifact products displace inside the transport walk
            // (`invalidate_transport_products` owns them for every reached
            // executable, root included) -- no second call here.
            self.invalidate_transport_products(&executable);
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

    pub fn demanded_transport_positions(&self) -> &HashSet<TransportPosition> {
        &self.demanded_transport_positions
    }

    pub fn transport_shape(&self, position: &TransportPosition) -> Option<ShapeId> {
        self.transport_layout(position).map(|layout| layout.structural)
    }

    pub fn transport_layout(&self, position: &TransportPosition) -> Option<TransportLayout> {
        self.transport_layouts.get(position).copied()
    }

    pub fn transport_shape_fact(&self, position: &TransportPosition) -> Option<&TransportShapeFact> {
        self.transport_shape_facts.get(position)
    }

    pub fn transport_shapes(&self) -> &HashMap<TransportPosition, ShapeId> {
        &self.transport_shapes
    }

    pub fn transport_layouts(&self) -> &HashMap<TransportPosition, TransportLayout> {
        &self.transport_layouts
    }

    /// Every position with a recorded shape whose OWNING executable is
    /// `symbol` -- the keyed view maintained in lockstep with
    /// `transport_shapes`, avoiding a per-production filter-scan of the
    /// whole inventory.
    pub fn transport_shape_positions_for(&self, symbol: &ExecutableSymbol) -> impl Iterator<Item = &TransportPosition> {
        self.transport_shapes_by_symbol.get(symbol).into_iter().flatten()
    }

    /// Every demanded EntryCapture/ResumePayload position owned by `symbol`.
    /// Monotone alongside `demanded_transport_positions`; see the field
    /// comment.
    pub fn demanded_capture_resume_positions_for(
        &self,
        symbol: &ExecutableSymbol,
    ) -> impl Iterator<Item = &TransportPosition> {
        self.demanded_capture_resume_positions.get(symbol).into_iter().flatten()
    }

    pub fn transport_component(&self, position: &TransportPosition) -> Option<&TransportComponentInventory> {
        self.transport_components.get(position)
    }

    /// Whether `executable` was projected by a still-valid shape-constraint
    /// solve. A covered executable's positions never re-solve: they read the
    /// recorded solve (or are proven unconstrained by it).
    pub fn transport_closure_covers(&self, executable: &ExecutableKey) -> bool {
        self.transport_closure_cover.contains_key(executable)
    }

    /// The solved component holding `position`, from the closure covering
    /// `executable`. `None` under a valid cover means the solve proved the
    /// position unconstrained (singleton component).
    pub fn solved_transport_component(
        &self,
        executable: &ExecutableKey,
        position: &TransportPosition,
    ) -> Option<&SolvedTransportComponent> {
        let id = self.transport_closure_cover.get(executable)?;
        let closure = &self.solved_transport_closures[id];
        closure
            .component_of
            .get(position)
            .map(|index| &closure.components[*index])
    }

    pub(crate) fn solved_transport_closure_publishes(
        &self,
        executable: &ExecutableKey,
        position: &TransportPosition,
    ) -> bool {
        self.transport_closure_cover
            .get(executable)
            .and_then(|id| self.solved_transport_closures.get(id))
            .is_some_and(|closure| closure.boundary_publications.contains(position))
    }

    pub fn callable_facts(&self, callable: CallableId) -> Option<&CallableFacts> {
        self.callable_facts.get(&callable)
    }

    pub fn callable_facts_inventory(&self) -> &HashMap<CallableId, CallableFacts> {
        &self.callable_facts
    }

    pub fn callable_constructions(&self) -> &HashMap<TransportPosition, CallableConstructionFact> {
        &self.callable_constructions
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

    /// Record the component inventory a position's pull materialized. The key
    /// is the PULLED position (the product identity); the value carries the
    /// component's canonical representative and full membership from the
    /// covering solve.
    pub fn record_transport_component(&mut self, position: TransportPosition, component: TransportComponentInventory) {
        self.note_demanded_transport_position(&position);
        for member in &component.positions {
            self.note_demanded_transport_position(member);
        }
        self.transport_components.insert(position, component);
    }

    /// Total `(consulted, member)` edge count currently live in
    /// `transport_closure_consult_dependents` -- test/telemetry
    /// observability for the ledger's lockstep pruning: bounded by the
    /// LIVE closures' membership, never by the session's full solve
    /// history.
    #[cfg(test)]
    pub(crate) fn transport_closure_consult_edge_count(&self) -> usize {
        self.transport_closure_consult_dependents
            .values()
            .map(HashSet::len)
            .sum()
    }

    /// Install the dense consult product `closure.consulted x
    /// closure.executables` into `transport_closure_consult_dependents`:
    /// every `(consulted, member)` pair the closure's solve read while
    /// discovering its membership. The mirror of
    /// `remove_transport_closure_consult_edges` -- called only from
    /// `record_solved_transport_closure`, so the two stay in lockstep by
    /// construction (one call site installs, one call site retracts, both
    /// keyed off the SAME closure value).
    fn insert_transport_closure_consult_edges(&mut self, closure: &SolvedTransportClosure) {
        for consulted in &closure.consulted {
            let dependents = self
                .transport_closure_consult_dependents
                .entry(consulted.clone())
                .or_default();
            for member in &closure.executables {
                if member != consulted {
                    dependents.insert(member.clone());
                }
            }
            if dependents.is_empty() {
                self.transport_closure_consult_dependents.remove(consulted);
            }
        }
    }

    /// Retract exactly the edges `insert_transport_closure_consult_edges`
    /// installed for this closure. Since closures are kept disjoint (a
    /// member belongs to at most one recorded closure at a time), this
    /// closure owns these `(consulted, member)` pairs outright -- no other
    /// live closure can have contributed the same edge, so removal is safe
    /// without a reference count.
    fn remove_transport_closure_consult_edges(&mut self, closure: &SolvedTransportClosure) {
        for consulted in &closure.consulted {
            let Some(dependents) = self.transport_closure_consult_dependents.get_mut(consulted) else {
                continue;
            };
            for member in &closure.executables {
                dependents.remove(member);
            }
            if dependents.is_empty() {
                self.transport_closure_consult_dependents.remove(consulted);
            }
        }
    }

    /// Record the full result of one shape-constraint solve. While live,
    /// closures stay disjoint by construction: any prior closure sharing a
    /// member executable is dropped whole -- cover AND consult edges -- before
    /// the new cover and its own consult edges are installed.
    pub fn record_solved_transport_closure(&mut self, closure: SolvedTransportClosure) {
        let displaced = closure
            .executables
            .iter()
            .filter_map(|member| self.transport_closure_cover.get(member).copied())
            .collect::<HashSet<u64>>();
        for id in displaced {
            self.drop_solved_transport_closure(id);
        }
        let id = self.transport_closure_counter;
        self.transport_closure_counter += 1;
        for member in &closure.executables {
            self.transport_closure_cover.insert(member.clone(), id);
        }
        for fact in closure.consumed_fact_states.keys() {
            self.transport_closure_fact_dependents
                .entry(fact.clone())
                .or_default()
                .insert(id);
        }
        self.insert_transport_closure_consult_edges(&closure);
        self.solved_transport_closures.insert(id, closure);
    }

    fn drop_solved_transport_closure(&mut self, id: u64) {
        let Some(closure) = self.solved_transport_closures.remove(&id) else {
            return;
        };
        for member in &closure.executables {
            if self.transport_closure_cover.get(member) == Some(&id) {
                self.transport_closure_cover.remove(member);
            }
        }
        for fact in closure.consumed_fact_states.keys() {
            let remove_entry = self
                .transport_closure_fact_dependents
                .get_mut(fact)
                .is_some_and(|closures| {
                    closures.remove(&id);
                    closures.is_empty()
                });
            if remove_entry {
                self.transport_closure_fact_dependents.remove(fact);
            }
        }
        self.remove_transport_closure_consult_edges(&closure);
    }

    pub fn record_transport_shape(&mut self, position: TransportPosition, shape: ShapeId) {
        self.record_transport_layout(position, TransportLayout::structural(shape));
    }

    pub fn record_transport_layout(&mut self, position: TransportPosition, layout: TransportLayout) {
        self.note_demanded_transport_position(&position);
        self.transport_shape_facts
            .insert(position.clone(), TransportShapeFact::Layout(layout));
        self.insert_transport_layout(position, layout);
    }

    pub fn record_transport_shape_for(
        &mut self,
        executable: &ExecutableKey,
        position: TransportPosition,
        shape: ShapeId,
    ) {
        self.record_transport_layout_for(executable, position, TransportLayout::structural(shape));
    }

    pub fn record_transport_layout_for(
        &mut self,
        executable: &ExecutableKey,
        position: TransportPosition,
        layout: TransportLayout,
    ) {
        self.note_demanded_transport_position(&position);
        self.transport_positions_by_executable
            .entry(executable.clone())
            .or_default()
            .insert(position.clone());
        self.transport_shape_facts
            .insert(position.clone(), TransportShapeFact::Layout(layout));
        let changed = self.insert_transport_layout(position, layout);
        if changed {
            self.invalidate_artifact_products(executable);
        }
    }

    /// Record a provisional absence: `position` has no grounded shape under
    /// the closure solve identified by `closure` (the id
    /// `transport_closure_id_covering` returned for `position`'s owning
    /// executable at the time of the query). The verdict stands only until
    /// that closure is displaced -- see `TransportShapeFact::AbsentForClosure`.
    pub fn record_absent_transport_shape_for(
        &mut self,
        executable: &ExecutableKey,
        position: TransportPosition,
        closure: u64,
    ) {
        self.note_demanded_transport_position(&position);
        self.transport_positions_by_executable
            .entry(executable.clone())
            .or_default()
            .insert(position.clone());
        let fact = TransportShapeFact::AbsentForClosure(closure);
        let changed = self.transport_shape_facts.insert(position.clone(), fact.clone()) != Some(fact);
        self.remove_transport_shape(&position);
        if changed {
            self.invalidate_artifact_products(executable);
        }
    }

    /// The closure id covering `executable`, if any -- the provenance a
    /// caller records into `TransportShapeFact::AbsentForClosure` when this
    /// solve fails to ground one of `executable`'s positions.
    pub fn transport_closure_id_covering(&self, executable: &ExecutableKey) -> Option<u64> {
        self.transport_closure_cover.get(executable).copied()
    }

    /// Displace the transport products derived from the (stale) solve
    /// covering `executable`: the full invalidation walk, so every member the
    /// solve consulted loses its shape/component/artifact products and the
    /// next pull re-solves against the moved facts. Over-reaching is
    /// conservative-correct; a member left standing is the stale-verdict bug.
    pub(crate) fn displace_transport_closure_for(&mut self, executable: &ExecutableKey) {
        self.invalidate_transport_products(executable);
    }

    fn apply_fact_movements(&mut self, movements: &[FactMovement<FactKey>]) {
        for movement in movements {
            self.pending_fact_states.insert(movement.key.clone(), movement.state);
        }
    }

    fn reconcile_fact_movements(&mut self) {
        let pending = std::mem::take(&mut self.pending_fact_states);
        let mut stale_closures = HashSet::new();
        for (fact, state) in &pending {
            let Some(dependents) = self.transport_closure_fact_dependents.get(fact) else {
                continue;
            };
            for id in dependents {
                let consumed = self
                    .solved_transport_closures
                    .get(id)
                    .and_then(|closure| closure.consumed_fact_states.get(fact))
                    .copied();
                if consumed != Some(*state) {
                    stale_closures.insert(*id);
                }
            }
        }
        let stale_transport = stale_closures
            .iter()
            .filter_map(|id| self.solved_transport_closures.get(id))
            .filter_map(|closure| closure.executables.iter().next().cloned())
            .collect::<Vec<_>>();
        for executable in stale_transport {
            self.displace_transport_closure_for(&executable);
        }
        self.memo.reconcile_fact_movements(&pending);
    }

    /// The SOLE insertion point into `transport_shapes`: keeps the by-symbol
    /// index in lockstep. Returns whether the recorded shape changed.
    fn insert_transport_layout(&mut self, position: TransportPosition, layout: TransportLayout) -> bool {
        self.transport_shapes_by_symbol
            .entry(position.executable().clone())
            .or_default()
            .insert(position.clone());
        self.transport_shapes.insert(position.clone(), layout.structural);
        self.transport_layouts.insert(position, layout) != Some(layout)
    }

    /// The SOLE removal point from `transport_shapes`: keeps the by-symbol
    /// index in lockstep.
    fn remove_transport_shape(&mut self, position: &TransportPosition) {
        self.transport_shapes.remove(position);
        self.transport_layouts.remove(position);
        if let Some(positions) = self.transport_shapes_by_symbol.get_mut(position.executable()) {
            positions.remove(position);
            if positions.is_empty() {
                self.transport_shapes_by_symbol.remove(position.executable());
            }
        }
    }

    /// The SOLE insertion point into `demanded_transport_positions`: keeps the
    /// by-symbol EntryCapture/ResumePayload index in lockstep. Both sets are
    /// monotone, so lockstep insertion is the whole coherence story.
    fn note_demanded_transport_position(&mut self, position: &TransportPosition) {
        if !self.demanded_transport_positions.insert(position.clone()) {
            return;
        }
        if matches!(
            position,
            TransportPosition::EntryCapture { .. } | TransportPosition::ResumePayload { .. }
        ) {
            self.demanded_capture_resume_positions
                .entry(position.executable().clone())
                .or_default()
                .insert(position.clone());
        }
    }

    pub fn record_callable_facts(&mut self, callable: CallableId, facts: CallableFacts) {
        self.demanded_callables.insert(callable);
        self.callable_facts.insert(callable, facts);
    }

    pub fn record_callable_construction(&mut self, construction: CallableConstructionFact) {
        self.callable_constructions
            .insert(construction.producer.clone(), construction);
    }

    pub fn record_boundary_facts(&mut self, boundary: BoundaryId, facts: BoundaryFacts) {
        self.demanded_boundaries.insert(boundary);
        let changed = self.boundary_facts.insert(boundary, facts.clone()).as_ref() != Some(&facts);
        // `session_codegen_publication_seam_facts` is the ONLY reader of
        // `boundary_facts_inventory`/`boundary_facts` behind
        // `ProductKey::CodegenSeamFacts`: a boundary whose recorded facts
        // actually moved (a new boundary, or a re-solved closure whose
        // publications changed) invalidates that memo so the next pull
        // re-derives the seam-fact set instead of serving a snapshot that
        // predates this boundary. An unchanged re-record (the common case:
        // a shared boundary re-confirmed by another executable's closure
        // solve) leaves the memo standing.
        if changed {
            self.memo.remove(&ProductKey::CodegenSeamFacts(self.root));
        }
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
            // The transport walk artifact-invalidates every node it reaches,
            // `current` included -- no separate artifact wipe is needed here.
            self.invalidate_transport_products(&current);
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
            ProductKey::TransportShape(position) => {
                if matches!(
                    self.transport_shape_facts.get(position),
                    Some(TransportShapeFact::AbsentForClosure(_))
                ) {
                    self.transport_shape_facts.remove(position);
                }
            }
            ProductKey::TransportComponent(position) => {
                self.transport_components.remove(position);
            }
            ProductKey::RootBackendProduct(_)
            | ProductKey::ExecutableFacts(_)
            | ProductKey::RuntimeDemand(_)
            | ProductKey::OutgoingEdgeFrontier(_)
            | ProductKey::OutgoingInputEdges(_)
            | ProductKey::IncomingInputRelations(_)
            | ProductKey::IncomingInputSlot(_)
            | ProductKey::CallableFacts(_)
            | ProductKey::BoundaryFacts(_)
            | ProductKey::CodegenSeamFacts(_) => {}
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

    fn invalidate_transport_products(&mut self, executable: &ExecutableKey) {
        let mut stack = vec![executable.clone()];
        let mut seen = HashSet::new();
        while let Some(current) = stack.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            let mut closure_ids = HashSet::new();
            if let Some(id) = self.transport_closure_cover.get(&current) {
                closure_ids.insert(*id);
            }
            if let Some(dependents) = self.transport_closure_consult_dependents.get(&current) {
                closure_ids.extend(
                    dependents
                        .iter()
                        .filter_map(|dependent| self.transport_closure_cover.get(dependent).copied()),
                );
            }
            let displaced_members = closure_ids
                .iter()
                .filter_map(|id| self.solved_transport_closures.get(id))
                .flat_map(|closure| closure.executables.iter().cloned())
                .collect::<HashSet<_>>();
            for id in closure_ids {
                self.drop_solved_transport_closure(id);
            }
            stack.extend(displaced_members);
            self.invalidate_transport_products_for_one(&current);
            self.invalidate_artifact_products(&current);
        }
    }

    fn invalidate_transport_products_for_one(&mut self, executable: &ExecutableKey) {
        let Some(positions) = self.transport_positions_by_executable.remove(executable) else {
            return;
        };
        for position in &positions {
            self.transport_shape_facts.remove(position);
            self.remove_transport_shape(position);
            self.transport_components.remove(position);
            self.memo.remove(&ProductKey::TransportShape(position.clone()));
            self.memo.remove(&ProductKey::TransportComponent(position.clone()));
        }

        let stale_components = self
            .transport_components
            .iter()
            .filter_map(|(member, component)| {
                component
                    .positions
                    .iter()
                    .any(|position| positions.contains(position))
                    .then_some(member.clone())
            })
            .collect::<Vec<_>>();
        for member in stale_components {
            self.transport_components.remove(&member);
            self.memo.remove(&ProductKey::TransportComponent(member));
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
        if let Some(position) = key.transport_position() {
            self.note_demanded_transport_position(position);
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
}

impl<'s> ProductReadContext<'s> {
    pub(crate) fn new(session: &'s mut PullSession) -> Self {
        Self {
            session,
            dependencies: ProductDependencies::default(),
        }
    }

    pub fn read_product(&mut self, key: ProductKey) -> Option<&ProductValue> {
        self.read_product_entry(key)
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

    pub fn read_codegen_seam_facts(&mut self, root: RootId) -> Option<Box<[CodegenSeamFact]>> {
        match self.read_product(ProductKey::CodegenSeamFacts(root)) {
            Some(ProductValue::CodegenSeamFacts(facts)) => Some(facts.clone()),
            Some(other) => panic!("codegen seam facts product produced unexpected value {other:?}"),
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

    fn into_dependencies(self) -> ProductDependencies {
        self.dependencies
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
    fn produce_transport_component(
        &mut self,
        context: &mut ProductReadContext<'_>,
        position: &TransportPosition,
    ) -> PullOutcome;
    fn produce_callable_facts(&mut self, context: &mut ProductReadContext<'_>, callable: CallableId) -> PullOutcome;
    fn produce_boundary_facts(&mut self, context: &mut ProductReadContext<'_>, boundary: BoundaryId) -> PullOutcome;
    fn produce_codegen_seam_facts(&mut self, context: &mut ProductReadContext<'_>, root: RootId) -> PullOutcome;
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
        super::jobs::transport::produce_transport_shape_product(context, position)
    }

    fn produce_transport_component(
        &mut self,
        context: &mut ProductReadContext<'_>,
        position: &TransportPosition,
    ) -> PullOutcome {
        super::jobs::transport::produce_transport_component_product(self.world, self.telemetry, context, position)
    }

    fn produce_callable_facts(&mut self, context: &mut ProductReadContext<'_>, callable: CallableId) -> PullOutcome {
        PullOutcome::Produced(ProductValue::CallableFacts(
            context.session().callable_facts(callable).cloned(),
        ))
    }

    fn produce_boundary_facts(&mut self, context: &mut ProductReadContext<'_>, boundary: BoundaryId) -> PullOutcome {
        PullOutcome::Produced(ProductValue::BoundaryFacts(
            context.session().boundary_facts(boundary).cloned(),
        ))
    }

    fn produce_codegen_seam_facts(&mut self, context: &mut ProductReadContext<'_>, root: RootId) -> PullOutcome {
        super::jobs::artifact::produce_codegen_seam_facts_product(self.world, self.telemetry, context, root)
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
            ProductKey::TransportComponent(position) => producers.produce_transport_component(&mut context, position),
            ProductKey::CallableFacts(callable) => producers.produce_callable_facts(&mut context, *callable),
            ProductKey::BoundaryFacts(boundary) => producers.produce_boundary_facts(&mut context, *boundary),
            ProductKey::CodegenSeamFacts(root) => producers.produce_codegen_seam_facts(&mut context, *root),
        };
        let dependencies = context.into_dependencies();
        if let PullOutcome::Waiting(waits) = &outcome {
            for wait in waits {
                if let PullWait::Product(product) = wait {
                    self.session.note_product_request(product);
                }
            }
        }

        match outcome {
            PullOutcome::Produced(value) => {
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
    use std::collections::HashSet;
    use std::rc::Rc;

    use crate::telemetry::ConfiguredTelemetry;

    use super::super::facts::FactReadiness;
    use super::super::identity::{ExecutableNeed, FunctionId};
    use super::super::transport::{ActivationSymbol, ExecutableSymbol};
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

        fn produce_transport_component(
            &mut self,
            _context: &mut ProductReadContext<'_>,
            position: &TransportPosition,
        ) -> PullOutcome {
            self.produce(ProductKey::TransportComponent(position.clone()))
        }

        fn produce_callable_facts(
            &mut self,
            _context: &mut ProductReadContext<'_>,
            callable: CallableId,
        ) -> PullOutcome {
            self.produce(ProductKey::CallableFacts(callable))
        }

        fn produce_boundary_facts(
            &mut self,
            _context: &mut ProductReadContext<'_>,
            boundary: BoundaryId,
        ) -> PullOutcome {
            self.produce(ProductKey::BoundaryFacts(boundary))
        }

        fn produce_codegen_seam_facts(&mut self, _context: &mut ProductReadContext<'_>, root: RootId) -> PullOutcome {
            self.produce(ProductKey::CodegenSeamFacts(root))
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
        producers.runtime_value = Some(ProductValue::CallableFacts(None));
        assert_eq!(
            driver.pull(&mut producers, parent.clone()),
            PullOutcome::wait_on_product(child.clone())
        );
        assert_eq!(
            driver.pull(&mut producers, child.clone()),
            PullOutcome::Produced(ProductValue::CallableFacts(None))
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
        producers.backend_value = Some(ProductValue::CallableFacts(None));
        driver.apply_fact_movements(&[fact_movement(fact.fact().clone(), Some(2), false)]);
        assert_eq!(
            driver.pull(&mut producers, grandparent.clone()),
            PullOutcome::wait_on_product(child.clone())
        );
        assert_eq!(driver.session().memo().generation(&grandparent), Some(1));
        assert_eq!(driver.session().memo().generation(&parent), Some(1));
        assert_eq!(
            driver.pull(&mut producers, child),
            PullOutcome::Produced(ProductValue::CallableFacts(None))
        );
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
    fn first_pull_of_an_absent_product_does_not_discard_session_side_effects() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(18);
        let position = TransportPosition::ExecutableReturn {
            executable: executable_symbol_for_test(&fake_executable(root)),
        };
        let shape = ShapeId::for_test(0);
        let key = ProductKey::TransportShape(position.clone());
        let mut session = PullSession::new(root);
        session.record_transport_shape(position.clone(), shape);
        let mut driver = ProductDriver::with_session(&tel, session);
        let mut producers = FakeProducers::default();

        assert_eq!(
            driver.pull(&mut producers, key),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert_eq!(
            driver.session().transport_shape_fact(&position),
            Some(&TransportShapeFact::Layout(TransportLayout::structural(shape)))
        );
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
    fn pull_session_leaves_codegen_seam_facts_standing_across_an_unchanged_boundary_rerecord() {
        // The common case: a boundary shared by several executables' transport
        // closures is re-confirmed (same value) each time its closure re-solves.
        // `record_boundary_facts` must not treat this as a movement of the data
        // `session_codegen_publication_seam_facts` reads.
        let mut session = PullSession::new(RootId::for_test(9));
        let boundary = BoundaryId::for_test(0);
        let facts = BoundaryFacts {
            publications: Box::default(),
            resolutions: Box::default(),
        };
        session.record_boundary_facts(boundary, facts.clone());
        session.memo.finish(
            &ProductKey::CodegenSeamFacts(session.root()),
            ProductValue::CodegenSeamFacts(Box::default()),
            ProductDependencies::default(),
        );

        session.record_boundary_facts(boundary, facts);

        assert!(
            session.memo().codegen_seam_facts(session.root()).is_some(),
            "an unchanged re-record of the same boundary facts must leave the codegen seam facts memo standing"
        );
    }

    #[test]
    fn pull_session_invalidates_codegen_seam_facts_when_a_boundary_actually_changes() {
        // The hard case this ticket is about: `session_codegen_publication_seam_facts`
        // is memoized behind `ProductKey::CodegenSeamFacts`, but it is still
        // derived from `boundary_facts_inventory` -- a boundary whose recorded
        // facts move (a brand-new boundary, or a re-solved closure whose
        // publications changed) must displace the memo, or a later production
        // would read a snapshot that predates the boundary it needs.
        let mut session = PullSession::new(RootId::for_test(9));
        let boundary_a = BoundaryId::for_test(0);
        let boundary_b = BoundaryId::for_test(1);
        let empty_facts = BoundaryFacts {
            publications: Box::default(),
            resolutions: Box::default(),
        };
        session.record_boundary_facts(boundary_a, empty_facts.clone());
        session.memo.finish(
            &ProductKey::CodegenSeamFacts(session.root()),
            ProductValue::CodegenSeamFacts(Box::default()),
            ProductDependencies::default(),
        );
        assert!(session.memo().codegen_seam_facts(session.root()).is_some());

        // A brand-new boundary appearing in the inventory changes the set
        // `session_codegen_publication_seam_facts` iterates over.
        session.record_boundary_facts(boundary_b, empty_facts);
        assert!(
            session.memo().codegen_seam_facts(session.root()).is_none(),
            "a newly recorded boundary must invalidate the memoized codegen seam facts product"
        );

        // Re-settle the memo, then re-solve `boundary_a` with DIFFERENT facts
        // (e.g. its closure re-solved with a new publication) -- the value at
        // an already-known key moving must invalidate too, not just new keys.
        session.memo.finish(
            &ProductKey::CodegenSeamFacts(session.root()),
            ProductValue::CodegenSeamFacts(Box::default()),
            ProductDependencies::default(),
        );
        let mut world = crate::compiler2::World::new();
        let arrow = world.types_mut().any();
        let publication = TransportPosition::Value {
            executable: ExecutableSymbol {
                activation: ActivationSymbol {
                    function: FunctionId::for_test(1),
                    arrow,
                    input: Box::default(),
                },
                need: ExecutableNeed::Value,
            },
            value: ValueId::from_u32(0),
        };
        let changed_facts = BoundaryFacts {
            publications: Box::from([publication]),
            resolutions: Box::default(),
        };
        session.record_boundary_facts(boundary_a, changed_facts);
        assert!(
            session.memo().codegen_seam_facts(session.root()).is_none(),
            "a boundary whose recorded facts changed must invalidate the memoized codegen seam facts product"
        );
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
    fn world_product_transport_shape_waits_for_component_inventory() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(63);
        let position = TransportPosition::ExecutableReturn {
            executable: executable_symbol_for_test(&fake_executable(root)),
        };
        let mut driver = ProductDriver::new(&tel, root);
        let mut world = World::new();
        let mut producers = WorldProductProducers::new(&mut world, &tel);

        let outcome = driver.pull(&mut producers, ProductKey::TransportShape(position.clone()));

        assert_eq!(
            outcome,
            PullOutcome::wait_on_product(ProductKey::TransportComponent(position))
        );
    }

    #[test]
    fn world_product_transport_shape_projects_layout_owned_by_a_live_cover() {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(64);
        let executable = fake_executable(root);
        let position = TransportPosition::ExecutableReturn {
            executable: executable_symbol_for_test(&executable),
        };
        let mut world = World::new();
        let shape = ShapeId::for_test(0);
        let mut driver = ProductDriver::new(&tel, root);
        driver
            .session_mut()
            .record_solved_transport_closure(SolvedTransportClosure {
                executables: HashSet::from([executable.clone()]),
                component_of: HashMap::from([(position.clone(), 0)]),
                components: vec![SolvedTransportComponent {
                    representative: position.clone(),
                    positions: vec![position.clone()],
                    shape: Some(shape),
                }],
                boundary_publications: HashSet::new(),
                consumed_fact_states: HashMap::new(),
                consulted: HashSet::new(),
            });
        driver.session_mut().record_transport_layout_for(
            &executable,
            position.clone(),
            TransportLayout::structural(shape),
        );
        let mut producers = WorldProductProducers::new(&mut world, &tel);

        assert_eq!(
            driver.pull(&mut producers, ProductKey::TransportShape(position.clone())),
            PullOutcome::Produced(ProductValue::TransportShape(TransportShapeFact::Layout(
                TransportLayout::structural(shape),
            )))
        );
        assert!(
            driver
                .session()
                .memo()
                .get(&ProductKey::TransportComponent(position))
                .is_none()
        );
    }

    #[test]
    fn world_product_transport_artifacts_require_product_entries_not_only_session_inventory() {
        use super::super::transport::{
            ActivationSymbol, CallableDescr, CallableFacts, ExecutableSymbol, LaneDescr, ShapeDescr, TransportClass,
        };

        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(7);
        let executable = fake_executable(root);
        let mut world = World::new();
        let int = world.types_mut().int();
        let lane = world.intern_lane(LaneDescr {
            ty: int,
            class: TransportClass::Value,
        });
        let shape = world.intern_shape(ShapeDescr::Lane(lane));
        let callable = world.intern_callable(CallableDescr {
            function: Some(executable.activation.function),
            capture_tys: Box::default(),
            capture_shapes: Box::default(),
            capture_lanes: Box::default(),
        });
        let callable_facts = CallableFacts {
            resolutions: Box::new([ExecutableSymbol {
                activation: ActivationSymbol {
                    function: executable.activation.function,
                    arrow: executable.activation.arrow,
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
        let component = TransportComponentInventory {
            representative: position.clone(),
            positions: vec![position.clone()],
        };
        driver
            .session_mut()
            .record_transport_component(position.clone(), component.clone());
        driver
            .session_mut()
            .record_callable_facts(callable, callable_facts.clone());
        let mut producers = WorldProductProducers::new(&mut world, &tel);

        assert_eq!(
            driver.pull(&mut producers, ProductKey::TransportShape(position.clone())),
            PullOutcome::wait_on_product(ProductKey::TransportComponent(position.clone()))
        );
        driver.session_mut().memo.finish(
            &ProductKey::TransportComponent(position.clone()),
            ProductValue::TransportComponent(component.clone()),
            ProductDependencies::default(),
        );
        assert_eq!(
            driver.pull(&mut producers, ProductKey::TransportShape(position.clone())),
            PullOutcome::Produced(ProductValue::TransportShape(TransportShapeFact::Layout(
                TransportLayout::structural(shape),
            )))
        );
        assert_eq!(
            driver.pull(&mut producers, ProductKey::TransportComponent(position)),
            PullOutcome::Produced(ProductValue::TransportComponent(component))
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

    /// INTENT: a recorded solve serves EVERY member position of EVERY
    /// component -- any member's lookup through the executable cover reaches
    /// its component (with the canonical representative), and a covered
    /// position absent from the solve is proven unconstrained (`None`), so no
    /// pull path ever needs a second solve without an input movement.
    #[test]
    fn solved_transport_closure_serves_every_member_position() {
        let root = RootId::for_test(21);
        let executable = fake_executable(root);
        let symbol = executable_symbol_for_test(&executable);
        let representative = TransportPosition::ExecutableInput {
            executable: symbol.clone(),
            semantic_index: 0,
        };
        let member = TransportPosition::ExecutableReturn {
            executable: symbol.clone(),
        };
        let unconstrained = TransportPosition::Value {
            executable: symbol,
            value: ValueId::from_u32(7),
        };
        let mut closure = SolvedTransportClosure::default();
        closure.executables.insert(executable.clone());
        closure.components.push(SolvedTransportComponent {
            representative: representative.clone(),
            positions: vec![representative.clone(), member.clone()],
            shape: None,
        });
        closure.component_of.insert(representative.clone(), 0);
        closure.component_of.insert(member.clone(), 0);
        let mut session = PullSession::new(root);

        session.record_solved_transport_closure(closure);

        assert!(session.transport_closure_covers(&executable));
        let by_member = session
            .solved_transport_component(&executable, &member)
            .expect("a member position's lookup should reach its solved component");
        assert_eq!(by_member.representative, representative);
        assert_eq!(
            session.solved_transport_component(&executable, &representative),
            session.solved_transport_component(&executable, &member),
            "every member should read the one solved component"
        );
        assert!(
            session
                .solved_transport_component(&executable, &unconstrained)
                .is_none(),
            "a covered position outside the solve is proven unconstrained, not unsolved"
        );
    }

    /// A demand movement on one member retracts its owning closure for every member.
    #[test]
    fn member_demand_movement_retracts_its_owning_transport_closure() {
        let root = RootId::for_test(22);
        let first = fake_executable_with_function(root, 220);
        let second = fake_executable_with_function(root, 221);
        let position = TransportPosition::ExecutableReturn {
            executable: executable_symbol_for_test(&second),
        };
        let mut closure = SolvedTransportClosure::default();
        closure.executables.insert(first.clone());
        closure.executables.insert(second.clone());
        closure.components.push(SolvedTransportComponent {
            representative: position.clone(),
            positions: vec![position.clone()],
            shape: None,
        });
        closure.component_of.insert(position.clone(), 0);
        let mut session = PullSession::new(root);
        session.record_solved_transport_closure(closure);
        assert!(session.transport_closure_covers(&first));
        assert!(session.transport_closure_covers(&second));
        assert!(session.solved_transport_component(&second, &position).is_some());

        let settled = ExecutableRuntimeDemand::default();
        let mut moved = ExecutableRuntimeDemand::default();
        moved.input_demands.push(RuntimeDemand::default());
        session.record_settled_runtime_demand(first.clone(), settled);
        session.record_settled_runtime_demand(first.clone(), moved);

        assert!(
            !session.transport_closure_covers(&first),
            "the moved member's cover must drop"
        );
        assert!(
            !session.transport_closure_covers(&second),
            "the whole closure must drop with it -- no member may serve the displaced solve"
        );
        assert!(session.solved_transport_component(&second, &position).is_none());
    }

    /// INTENT: closures stay disjoint -- recording a solve that absorbs a
    /// member of an older solve displaces the older solve entirely, so a
    /// single cover always answers for an executable.
    #[test]
    fn solved_transport_closure_recording_displaces_overlapping_closures() {
        let root = RootId::for_test(23);
        let shared = fake_executable_with_function(root, 230);
        let old_only = fake_executable_with_function(root, 231);
        let mut old = SolvedTransportClosure::default();
        old.executables.insert(shared.clone());
        old.executables.insert(old_only.clone());
        let mut new = SolvedTransportClosure::default();
        new.executables.insert(shared.clone());
        let mut session = PullSession::new(root);

        session.record_solved_transport_closure(old);
        session.record_solved_transport_closure(new);

        assert!(session.transport_closure_covers(&shared));
        assert!(
            !session.transport_closure_covers(&old_only),
            "the displaced closure's other members must not keep a stale cover"
        );
    }

    /// INTENT (fz-go4.18.28.13): a re-solve that shares a member with an
    /// older closure but has DIFFERENT overall membership must displace the
    /// older closure's consult edges along with its cover -- precisely,
    /// leaving an unrelated LIVE closure's own edges untouched. Before this
    /// fix, `record_transport_closure_consult` only ever grew the ledger:
    /// `drop_solved_transport_closure` evicted the cover but never the
    /// consult edges the dropped closure had installed, so a fact only the
    /// old, now-gone membership ever consulted kept a dangling edge forever.
    #[test]
    fn transport_closure_consult_ledger_prunes_displaced_closure_on_resolve() {
        let root = RootId::for_test(24);
        let consulted_only_by_old = fake_executable_with_function(root, 240);
        let shared_consulted = fake_executable_with_function(root, 241);
        let shared_member = fake_executable_with_function(root, 242);
        let old_only_member = fake_executable_with_function(root, 243);
        let new_only_member = fake_executable_with_function(root, 244);
        let untouched_member = fake_executable_with_function(root, 245);
        let mut session = PullSession::new(root);

        // An unrelated live closure elsewhere in the session -- shares no
        // member with `old`, so `record_solved_transport_closure`'s
        // disjointness rule must never touch it.
        let mut untouched = SolvedTransportClosure::default();
        untouched.executables.insert(untouched_member.clone());
        untouched.consulted.insert(shared_consulted.clone());
        session.record_solved_transport_closure(untouched);

        // The old closure: two members, consulted by both
        // `consulted_only_by_old` (exclusively) and `shared_consulted`.
        let mut old = SolvedTransportClosure::default();
        old.executables.insert(shared_member.clone());
        old.executables.insert(old_only_member.clone());
        old.consulted.insert(consulted_only_by_old);
        old.consulted.insert(shared_consulted.clone());
        session.record_solved_transport_closure(old);

        assert_eq!(
            session.transport_closure_consult_edge_count(),
            5,
            "untouched(1 consulted x 1 member) + old(2 consulted x 2 members) = 5 live edges"
        );

        // Re-solve `shared_member` with DIFFERENT membership: `old_only_member`
        // drops out, `new_only_member` joins, and this closure was only ever
        // consulted through `shared_consulted` -- `consulted_only_by_old` was
        // never read by this solve. This is exactly the re-solve
        // `jobs::transport::solve_transport_closure` performs: same
        // `record_solved_transport_closure` call, sharing `shared_member`
        // with the prior cover so the disjointness rule displaces `old`.
        let mut new = SolvedTransportClosure::default();
        new.executables.insert(shared_member.clone());
        new.executables.insert(new_only_member.clone());
        new.consulted.insert(shared_consulted);
        session.record_solved_transport_closure(new);

        assert!(session.transport_closure_covers(&shared_member));
        assert!(session.transport_closure_covers(&new_only_member));
        assert!(
            !session.transport_closure_covers(&old_only_member),
            "the displaced closure's dropped-out member must not keep a stale cover"
        );
        assert!(
            session.transport_closure_covers(&untouched_member),
            "the unrelated live closure must survive a disjoint re-solve"
        );

        assert_eq!(
            session.transport_closure_consult_edge_count(),
            3,
            "untouched(1) + new(1 consulted x 2 members) = 3 live edges -- `old`'s edges from \
             `consulted_only_by_old` (exclusive to the dropped membership) and its stale \
             `shared_consulted -> old_only_member` edge must both be gone, not accumulated on \
             top of `new`'s edges"
        );
    }

    #[test]
    fn transport_invalidation_retracts_only_closures_that_own_the_moved_input() {
        let root = RootId::for_test(25);
        let consulted = fake_executable_with_function(root, 250);
        let member = fake_executable_with_function(root, 251);
        let unrelated = fake_executable_with_function(root, 252);
        let mut closure = SolvedTransportClosure::default();
        closure.executables.insert(member.clone());
        closure.consulted.insert(consulted);
        let mut unrelated_closure = SolvedTransportClosure::default();
        unrelated_closure.executables.insert(unrelated.clone());
        let mut session = PullSession::new(root);
        session.record_solved_transport_closure(closure);
        session.record_solved_transport_closure(unrelated_closure);
        assert_eq!(session.transport_closure_consult_edge_count(), 1);

        let settled = ExecutableRuntimeDemand::default();
        let mut moved = ExecutableRuntimeDemand::default();
        moved.input_demands.push(RuntimeDemand::default());
        session.record_settled_runtime_demand(member.clone(), settled);
        session.record_settled_runtime_demand(member.clone(), moved);

        assert_eq!(
            session.transport_closure_consult_edge_count(),
            0,
            "the displaced closure must retract the consult edge it owned"
        );
        assert!(!session.transport_closure_covers(&member));
        assert!(
            session.transport_closure_covers(&unrelated),
            "a movement cannot retract a closure that neither covers nor consulted the moved executable"
        );
    }

    #[test]
    fn fact_movement_batch_retracts_every_affected_transport_closure() {
        let root = RootId::for_test(26);
        let first = fake_executable_with_function(root, 260);
        let second = fake_executable_with_function(root, 261);
        let untouched = fake_executable_with_function(root, 262);
        let first_fact = FactKey::LoweredBody(FunctionId::for_test(260));
        let second_fact = FactKey::LoweredBody(FunctionId::for_test(261));
        let mut session = PullSession::new(root);
        for (executable, consumed) in [
            (
                first.clone(),
                HashMap::from([(
                    first_fact.clone(),
                    FactState {
                        revision: Some(1),
                        settled: true,
                    },
                )]),
            ),
            (
                second.clone(),
                HashMap::from([(
                    second_fact.clone(),
                    FactState {
                        revision: Some(4),
                        settled: true,
                    },
                )]),
            ),
            (untouched.clone(), HashMap::new()),
        ] {
            session.record_solved_transport_closure(SolvedTransportClosure {
                executables: HashSet::from([executable]),
                consumed_fact_states: consumed,
                ..Default::default()
            });
        }

        session.apply_fact_movements(&[
            fact_movement(first_fact, Some(2), true),
            fact_movement(second_fact, Some(5), true),
        ]);
        session.reconcile_fact_movements();

        assert!(!session.transport_closure_covers(&first));
        assert!(!session.transport_closure_covers(&second));
        assert!(session.transport_closure_covers(&untouched));
    }

    #[test]
    fn same_revision_dirty_fact_movement_retracts_cover_and_component_product() {
        let root = RootId::for_test(28);
        let executable = fake_executable_with_function(root, 280);
        let fact = FactKey::LoweredBody(FunctionId::for_test(280));
        let position = TransportPosition::ExecutableReturn {
            executable: executable_symbol_for_test(&executable),
        };
        let component = TransportComponentInventory {
            representative: position.clone(),
            positions: vec![position.clone()],
        };
        let key = ProductKey::TransportComponent(position.clone());
        let mut session = PullSession::new(root);
        session.record_solved_transport_closure(SolvedTransportClosure {
            executables: HashSet::from([executable.clone()]),
            consumed_fact_states: HashMap::from([(
                fact.clone(),
                FactState {
                    revision: Some(1),
                    settled: true,
                },
            )]),
            ..Default::default()
        });
        session.record_transport_shape_for(&executable, position.clone(), ShapeId::for_test(0));
        session.record_transport_component(position, component.clone());
        session.memo.finish(
            &key,
            ProductValue::TransportComponent(component),
            ProductDependencies::default(),
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
            HashSet::from([FactUse::current(FactKey::RootEntry(root))]),
            vec![fact],
            Vec::new(),
        );
        assert_eq!(blocked.movements.len(), 1);
        assert_eq!(blocked.movements[0].state.revision, Some(1));
        assert!(!blocked.movements[0].state.settled);

        session.apply_fact_movements(&blocked.movements);
        session.reconcile_fact_movements();

        assert!(!session.transport_closure_covers(&executable));
        assert!(session.memo().get(&key).is_none());
    }

    /// INTENT: the by-symbol transport-shape index is a second KEYING of
    /// `transport_shapes`, not a cache -- a symbol's lookup returns exactly
    /// the recorded positions the old whole-inventory filter-scan would have
    /// found for it, and nothing from any other executable.
    #[test]
    fn transport_shape_index_serves_exactly_the_owning_symbol() {
        let root = RootId::for_test(31);
        let first = fake_executable_with_function(root, 310);
        let second = fake_executable_with_function(root, 311);
        let first_position = TransportPosition::ExecutableReturn {
            executable: executable_symbol_for_test(&first),
        };
        let second_position = TransportPosition::ExecutableReturn {
            executable: executable_symbol_for_test(&second),
        };
        let shape = ShapeId::for_test(0);
        let mut session = PullSession::new(root);

        session.record_transport_shape_for(&first, first_position.clone(), shape);
        session.record_transport_shape_for(&second, second_position.clone(), shape);

        assert_eq!(
            session
                .transport_shape_positions_for(&executable_symbol_for_test(&first))
                .collect::<Vec<_>>(),
            vec![&first_position]
        );
        assert_eq!(
            session
                .transport_shape_positions_for(&executable_symbol_for_test(&second))
                .collect::<Vec<_>>(),
            vec![&second_position]
        );
    }

    /// INTENT: the index lives and dies with `transport_shapes` across the
    /// transport EPOCH boundary. Invalidation is keyed by the RECORDING
    /// executable (`transport_positions_by_executable`), while the index is
    /// keyed by each position's OWNING symbol -- a position recorded FOR one
    /// executable but owned by another's symbol must still leave the index
    /// when its recorder's epoch ends, and positions recorded by an
    /// untouched executable must keep standing.
    #[test]
    fn transport_shape_index_dies_with_its_owning_closure() {
        let root = RootId::for_test(32);
        let invalidated = fake_executable_with_function(root, 320);
        let untouched = fake_executable_with_function(root, 321);
        let invalidated_symbol = executable_symbol_for_test(&invalidated);
        let untouched_symbol = executable_symbol_for_test(&untouched);
        let own_position = TransportPosition::ExecutableReturn {
            executable: invalidated_symbol.clone(),
        };
        // Recorded FOR `invalidated`, but OWNED by `untouched`'s symbol --
        // e.g. a CallArg on the caller solved by the callee's closure.
        let cross_position = TransportPosition::CallArg {
            executable: untouched_symbol.clone(),
            callsite: CallSiteId::from_u32(0),
            semantic_index: 0,
        };
        let standing_position = TransportPosition::ExecutableReturn {
            executable: untouched_symbol.clone(),
        };
        let shape = ShapeId::for_test(0);
        let mut session = PullSession::new(root);
        session.record_transport_shape_for(&invalidated, own_position.clone(), shape);
        session.record_transport_shape_for(&invalidated, cross_position.clone(), shape);
        session.record_transport_shape_for(&untouched, standing_position.clone(), shape);

        // Settled demand for `invalidated` moves.
        let settled = ExecutableRuntimeDemand::default();
        let mut moved = ExecutableRuntimeDemand::default();
        moved.input_demands.push(RuntimeDemand::default());
        session.record_settled_runtime_demand(invalidated.clone(), settled);
        session.record_settled_runtime_demand(invalidated.clone(), moved);

        assert!(session.transport_shape(&own_position).is_none());
        assert!(session.transport_shape(&cross_position).is_none());
        assert_eq!(
            session
                .transport_shape_positions_for(&invalidated_symbol)
                .collect::<Vec<_>>(),
            Vec::<&TransportPosition>::new(),
            "the invalidated recorder's own position must leave the index with the map"
        );
        assert_eq!(
            session
                .transport_shape_positions_for(&untouched_symbol)
                .collect::<Vec<_>>(),
            vec![&standing_position],
            "the cross-recorded position must leave the index, while the untouched recorder's position stands"
        );
    }

    /// INTENT: a position re-recorded as ABSENT leaves `transport_shapes` and
    /// must leave the index with it -- the artifact consumer packages only
    /// positions that currently have a shape.
    #[test]
    fn transport_shape_index_drops_positions_rerecorded_absent() {
        let root = RootId::for_test(33);
        let executable = fake_executable_with_function(root, 330);
        let symbol = executable_symbol_for_test(&executable);
        let position = TransportPosition::ExecutableReturn {
            executable: symbol.clone(),
        };
        let mut session = PullSession::new(root);
        session.record_transport_shape_for(&executable, position.clone(), ShapeId::for_test(0));
        assert_eq!(session.transport_shape_positions_for(&symbol).count(), 1);

        session.record_absent_transport_shape_for(&executable, position.clone(), 0);

        assert!(session.transport_shape(&position).is_none());
        assert_eq!(
            session.transport_shape_positions_for(&symbol).count(),
            0,
            "an absent re-record must remove the position from the by-symbol index"
        );
    }

    /// INTENT: the demanded-position index carries exactly the
    /// EntryCapture/ResumePayload variants the artifact consumer reads from
    /// the demanded set, keyed by each position's own symbol; other variants
    /// join the demanded set without joining the index.
    #[test]
    fn demanded_capture_resume_index_tracks_only_those_variants() {
        let root = RootId::for_test(34);
        let executable = fake_executable_with_function(root, 340);
        let symbol = executable_symbol_for_test(&executable);
        let capture = TransportPosition::EntryCapture {
            executable: symbol.clone(),
            entry: ControlEntryId::from_u32(0),
            capture_index: 0,
        };
        let resume = TransportPosition::ResumePayload {
            executable: symbol.clone(),
            callsite: None,
            entry: ControlEntryId::from_u32(1),
        };
        let input = TransportPosition::ExecutableInput {
            executable: symbol.clone(),
            semantic_index: 0,
        };
        let mut session = PullSession::new(root);
        session.record_transport_component(
            input.clone(),
            TransportComponentInventory {
                representative: input.clone(),
                positions: vec![input.clone(), capture.clone(), resume.clone()],
            },
        );

        assert!(session.demanded_transport_positions().contains(&input));
        let mut indexed = session
            .demanded_capture_resume_positions_for(&symbol)
            .cloned()
            .collect::<Vec<_>>();
        indexed.sort_by_key(|position| match position {
            TransportPosition::EntryCapture { .. } => 0,
            _ => 1,
        });
        assert_eq!(indexed, vec![capture, resume]);
    }
}
