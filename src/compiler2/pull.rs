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
use super::transport::{
    BoundaryFacts, BoundaryId, CallableFacts, CallableId, CodegenSeamFact, ShapeId, TransportPosition,
};
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
            Self::RuntimeDemand(_) => "runtime_demand",
            Self::OutgoingInputEdges(_) => "outgoing_input_edges",
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
            | Self::RuntimeDemand(executable)
            | Self::OutgoingInputEdges(executable) => Some(executable),
            Self::IncomingInputSlot(slot) => Some(&slot.executable),
            Self::RootBackendProduct(_)
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
    // Last value each invalidated key held, kept (moved, not cloned) until the
    // key re-produces. Lets the driver report whether a re-production was
    // byte-identical to the value the invalidation displaced -- the minimality
    // signal for invalidation hygiene.
    displaced: HashMap<ProductKey, ProductValue>,
    in_progress: HashSet<ProductKey>,
    invalidated_in_progress: HashSet<ProductKey>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ProductFinish {
    settled: bool,
    identical: bool,
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
        match self.produced.get(&ProductKey::CodegenSeamFacts(root)) {
            Some(ProductValue::CodegenSeamFacts(facts)) => Some(facts.as_ref()),
            Some(
                ProductValue::Unit
                | ProductValue::RootBackendProduct(_)
                | ProductValue::BackendExecutable(_)
                | ProductValue::AbiExecutable(_)
                | ProductValue::MaterializedExecutable(_)
                | ProductValue::ExecutableEffects(_)
                | ProductValue::RuntimeDemand(_)
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

    fn finish(&mut self, key: &ProductKey, value: ProductValue) -> ProductFinish {
        self.in_progress.remove(key);
        if self.invalidated_in_progress.remove(key) {
            self.produced.remove(key);
            return ProductFinish {
                settled: false,
                identical: false,
            };
        }
        let displaced = self.displaced.remove(key);
        let identical = self.produced.get(key) == Some(&value) || displaced.as_ref() == Some(&value);
        self.produced.insert(key.clone(), value);
        ProductFinish {
            settled: true,
            identical,
        }
    }

    fn unblock(&mut self, key: &ProductKey) {
        self.in_progress.remove(key);
        self.invalidated_in_progress.remove(key);
    }

    fn remove(&mut self, key: &ProductKey) {
        if self.in_progress.contains(key) {
            self.invalidated_in_progress.insert(key.clone());
        }
        if let Some(value) = self.produced.remove(key) {
            self.displaced.insert(key.clone(), value);
        }
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
/// closure: every connected component, indexed by member position, plus the
/// executable cover the solve projected. A position of a covered executable
/// that is absent from `component_of` was proven unconstrained by this same
/// solve -- it needs a singleton component, not a re-solve.
#[derive(Debug, Default)]
pub struct SolvedTransportClosure {
    pub executables: HashSet<ExecutableKey>,
    pub component_of: HashMap<TransportPosition, usize>,
    pub components: Vec<SolvedTransportComponent>,
}

#[derive(Debug)]
pub struct PullSession {
    root: RootId,
    memo: ProductMemo,
    demanded_executables: HashSet<ExecutableKey>,
    call_edges: HashMap<ExecutableKey, Vec<DemandedCallEdge>>,
    incoming_inputs: HashMap<InputSlot, Vec<IncomingInputSource>>,
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
    materialized_executables: HashMap<ExecutableKey, MaterializedExecutable>,
    executable_effects: HashMap<ExecutableKey, EffectSummary>,
    abi_executables: HashMap<ExecutableKey, AbiReadyExecutable>,
    backend_executables: HashMap<ExecutableKey, SymbolicBackendExecutable>,
    demanded_transport_positions: HashSet<TransportPosition>,
    transport_shape_facts: HashMap<TransportPosition, TransportShapeFact>,
    transport_shapes: HashMap<TransportPosition, ShapeId>,
    transport_components: HashMap<TransportPosition, TransportComponentInventory>,
    // Solved-closure inventory: each shape-constraint solve records every
    // component it computed, keyed by a session-unique closure id, with
    // `transport_closure_cover` mapping each projected executable to the solve
    // that covered it. Closures are valid for exactly one transport-graph
    // EPOCH: any transport invalidation (a settled-demand change, a new
    // incoming call edge) clears the whole inventory, so a cover can never
    // answer from a graph the movement outgrew -- the same events that
    // displaced per-anchor memos before, now displacing the shared solve.
    // Within an epoch closures are kept disjoint: recording a solve drops any
    // prior solve sharing a member.
    solved_transport_closures: HashMap<u64, SolvedTransportClosure>,
    transport_closure_cover: HashMap<ExecutableKey, u64>,
    transport_closure_counter: u64,
    transport_positions_by_executable: HashMap<ExecutableKey, HashSet<TransportPosition>>,
    callable_facts: HashMap<CallableId, CallableFacts>,
    boundary_facts: HashMap<BoundaryId, BoundaryFacts>,
    demanded_callables: HashSet<CallableId>,
    demanded_boundaries: HashSet<BoundaryId>,
    executable_index: HashMap<ExecutableKey, usize>,
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
            demand_flow_dependents: HashMap::new(),
            settled_demand_callees: HashMap::new(),
            latest_effect_inputs: HashMap::new(),
            effect_dependents: HashMap::new(),
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
            solved_transport_closures: HashMap::new(),
            transport_closure_cover: HashMap::new(),
            transport_closure_counter: 0,
            transport_positions_by_executable: HashMap::new(),
            callable_facts: HashMap::new(),
            boundary_facts: HashMap::new(),
            demanded_callables: HashSet::new(),
            demanded_boundaries: HashSet::new(),
            executable_index: HashMap::new(),
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
    pub fn record_settled_runtime_demand(&mut self, executable: ExecutableKey, demand: ExecutableRuntimeDemand) {
        let key = ProductKey::RuntimeDemand(executable.clone());
        let previous = match self.memo.produced.get(&key).or_else(|| self.memo.displaced.get(&key)) {
            Some(ProductValue::RuntimeDemand(previous)) => Some(previous.as_ref().clone()),
            _ => None,
        };
        let changed = previous.is_some_and(|previous| previous != demand);
        self.memo.displaced.remove(&key);
        self.memo
            .produced
            .insert(key, ProductValue::RuntimeDemand(Box::new(demand)));
        if changed {
            self.invalidate_transport_products(&executable);
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
            // A new incoming edge feeds the callee's input SLOTS -- a transport
            // input, not a demand input (the demand cone derives its edges from
            // settled facts, not from this session inventory), so settled
            // demand stands and only shape-consuming products re-derive.
            self.invalidate_edge_derived_products(&edge.callee);
        }
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
        self.demanded_transport_positions.insert(position.clone());
        self.demanded_transport_positions
            .extend(component.positions.iter().cloned());
        self.transport_components.insert(position, component);
    }

    /// Record the full result of one shape-constraint solve. Within the epoch,
    /// closures stay disjoint by construction: any prior closure sharing a
    /// member executable is dropped whole before the new cover is installed.
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
    }

    /// The transport-graph EPOCH boundary: a solve input moved somewhere, so
    /// every recorded solve is displaced at once. Product-visible inventories
    /// (shapes, produced components) stand -- exactly the products the
    /// pre-movement graph already answered -- and are displaced separately by
    /// the targeted product invalidation walks.
    fn clear_solved_transport_closures(&mut self) {
        self.solved_transport_closures.clear();
        self.transport_closure_cover.clear();
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
            self.invalidate_transport_products(&current);
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

    /// New incoming call edges change transport inputs, never settled demand:
    /// wipe the shape/artifact products of the callee and its transitive
    /// demand readers, leaving every RuntimeDemand memo standing.
    fn invalidate_edge_derived_products(&mut self, executable: &ExecutableKey) {
        let mut stack = vec![executable.clone()];
        let mut seen = HashSet::new();
        while let Some(current) = stack.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            self.invalidate_transport_products(&current);
            self.invalidate_artifact_products(&current);
            if let Some(dependents) = self.runtime_demand_dependents.get(&current).cloned() {
                stack.extend(dependents);
            }
        }
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
        // Transport invalidation is only ever rooted at a solve-input movement
        // (settled-demand change, new incoming edge), so it is an epoch
        // boundary: every recorded solve is displaced, and the next component
        // pull re-solves against the moved graph.
        self.clear_solved_transport_closures();
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

fn effect_relevant_inputs(materialized: &MaterializedExecutable) -> (EffectSummary, HashSet<ExecutableKey>) {
    let callees = materialized
        .call_edges
        .values()
        .flat_map(|edge| edge.target.local_callees())
        .cloned()
        .collect();
    (materialized.effects, callees)
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
    fn produce_codegen_seam_facts(&mut self, session: &mut PullSession, root: RootId) -> PullOutcome;
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

    fn produce_codegen_seam_facts(&mut self, session: &mut PullSession, root: RootId) -> PullOutcome {
        super::jobs::artifact::produce_codegen_seam_facts_product(self.world, session, root)
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
        #[cfg(debug_assertions)]
        self.session.assert_executable_effects_fresh();
        self.session.emit_finished(self.tel);
    }

    pub fn pull(&mut self, producers: &mut impl ProductProducers, key: ProductKey) -> PullOutcome {
        self.emit("requested", &key, 0);
        self.session.note_product_request(&key);
        if let Some(value) = self.session.memo.get(&key) {
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
            ProductKey::CodegenSeamFacts(root) => producers.produce_codegen_seam_facts(&mut self.session, *root),
        };

        match outcome {
            PullOutcome::Produced(value) => {
                let finish = self.session.memo.finish(&key, value.clone());
                if !finish.settled {
                    self.session.discard_product_side_effects(&key);
                    let waits = vec![PullWait::Product(key.clone())];
                    self.emit_waited(&key, &waits);
                    return PullOutcome::Waiting(waits);
                }
                self.emit_produced(&key, finish.identical);
                PullOutcome::Produced(value)
            }
            PullOutcome::Waiting(waits) => {
                self.session.memo.unblock(&key);
                self.emit_waited(&key, &waits);
                PullOutcome::Waiting(waits)
            }
        }
    }

    fn emit_produced(&self, key: &ProductKey, identical: bool) {
        self.tel.execute(
            &["fz", "compiler2", "pull", "product", "produced"],
            &measurements! {
                wait_count: 0_usize,
                identical: identical,
            },
            &metadata! {
                kind: key.kind(),
                product: opaque_debug(key),
            },
        );
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

    use super::super::identity::{ExecutableNeed, FunctionId};
    use super::super::transport::{ActivationSymbol, ExecutableSymbol};
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

        fn produce_codegen_seam_facts(&mut self, _session: &mut PullSession, root: RootId) -> PullOutcome {
            self.produce(ProductKey::CodegenSeamFacts(root))
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
            session.memo().get(&ProductKey::RuntimeDemand(callee)).is_some(),
            "recording an incoming edge feeds transport input slots and must leave settled demand standing"
        );
        assert_eq!(session.producer_pokes(), 0);
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
        );
        let publication = TransportPosition::Value {
            executable: ExecutableSymbol {
                activation: ActivationSymbol {
                    function: FunctionId::for_test(1),
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
        driver.session_mut().record_transport_component(
            position.clone(),
            TransportComponentInventory {
                representative: position.clone(),
                positions: vec![position.clone()],
            },
        );
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
                representative: position.clone(),
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
        let capture = Capture::new();
        tel.attach(&[], capture.handler());
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
        driver.session_mut().record_materialized_executable(
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
        driver
            .session_mut()
            .record_materialized_executable(callee.clone(), callee_materialized.clone());
        let mut world = World::new(&tel);
        let mut producers = WorldProductProducers::new(&mut world);
        assert!(matches!(
            driver.pull(&mut producers, effects_key.clone()),
            PullOutcome::Produced(ProductValue::ExecutableEffects(_))
        ));
        let produced_after_settle = capture.count(&["fz", "compiler2", "pull", "product", "produced"]);

        driver
            .session_mut()
            .record_materialized_executable(callee.clone(), callee_materialized.clone());

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
            capture.count(&["fz", "compiler2", "pull", "product", "produced"]),
            produced_after_settle,
            "an unchanged effect projection must not re-produce the effects product"
        );

        let mut changed = callee_materialized;
        changed.effects = EffectSummary {
            scheduler_visible: true,
            ..EffectSummary::default()
        };
        driver
            .session_mut()
            .record_materialized_executable(callee.clone(), changed);

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
            capture.count(&["fz", "compiler2", "pull", "product", "produced"]) > produced_after_settle,
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
                        callee_return: TransportPosition::ExecutableReturn {
                            executable: callee_symbol,
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
        driver.session_mut().record_materialized_executable(
            grand.clone(),
            fake_materialized(
                grand_symbol.clone(),
                Some(fake_edge(caller.clone(), grand_symbol, caller_symbol.clone())),
                EffectSummary::default(),
            ),
        );
        driver.session_mut().record_materialized_executable(
            caller.clone(),
            fake_materialized(
                caller_symbol.clone(),
                Some(fake_edge(callee.clone(), caller_symbol, callee_symbol.clone())),
                EffectSummary::default(),
            ),
        );
        driver.session_mut().record_materialized_executable(
            callee.clone(),
            fake_materialized(callee_symbol, None, EffectSummary::default()),
        );
        let mut world = World::new(&tel);
        let mut producers = WorldProductProducers::new(&mut world);
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
        driver
            .session_mut()
            .record_materialized_executable(callee.clone(), changed);

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
                        callee_return: TransportPosition::ExecutableReturn {
                            executable: callee_symbol,
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
    fn product_memo_finish_classifies_identical_vs_changed_reproductions() {
        // The displaced value an invalidation removes is kept so the next
        // production of the same key can be classified byte-identical vs
        // changed -- the minimality signal for invalidation hygiene.
        let key = ProductKey::RuntimeDemand(fake_executable(RootId::for_test(92)));
        let mut memo = ProductMemo::default();

        memo.begin(key.clone());
        assert_eq!(
            memo.finish(&key, ProductValue::Unit),
            ProductFinish {
                settled: true,
                identical: false,
            },
            "a first production has nothing to be identical to"
        );

        memo.remove(&key);
        memo.begin(key.clone());
        assert_eq!(
            memo.finish(&key, ProductValue::Unit),
            ProductFinish {
                settled: true,
                identical: true,
            },
            "re-producing the displaced value after invalidation is identical"
        );

        memo.remove(&key);
        memo.begin(key.clone());
        assert_eq!(
            memo.finish(&key, ProductValue::RuntimeDemand(Box::default())),
            ProductFinish {
                settled: true,
                identical: false,
            },
            "re-producing a different value after invalidation is a change"
        );
    }

    #[test]
    fn produced_telemetry_measures_identical_reproductions() {
        let tel = ConfiguredTelemetry::new();
        let capture = Capture::new();
        tel.attach(&[], capture.handler());
        let root = RootId::for_test(93);
        let key = ProductKey::OutgoingInputEdges(fake_executable(root));
        let mut driver = ProductDriver::new(&tel, root);
        let mut producers = FakeProducers::default();

        assert_eq!(
            driver.pull(&mut producers, key.clone()),
            PullOutcome::Produced(ProductValue::Unit)
        );
        let first = capture
            .last(&["fz", "compiler2", "pull", "product", "produced"])
            .expect("first production should emit produced telemetry");
        assert!(
            !measurement_bool(&first, "identical"),
            "a first production carries identical=false"
        );

        driver.session.memo.remove(&key);
        assert_eq!(
            driver.pull(&mut producers, key),
            PullOutcome::Produced(ProductValue::Unit)
        );
        let second = capture
            .last(&["fz", "compiler2", "pull", "product", "produced"])
            .expect("re-production should emit produced telemetry");
        assert!(
            measurement_bool(&second, "identical"),
            "an invalidation that re-produces the displaced value carries identical=true"
        );
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

    /// INTENT: a recorded solve serves EVERY member position of EVERY
    /// component -- any member's lookup through the executable cover reaches
    /// its component (with the canonical representative), and a covered
    /// position absent from the solve is proven unconstrained (`None`), so no
    /// pull path ever needs a second solve within the epoch.
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

    /// INTENT: the SOLVE is the coherent epoch unit. A settled-demand change on
    /// ANY member executable drops the whole recorded closure, so no other
    /// member keeps answering component pulls from the displaced solve.
    #[test]
    fn solved_transport_closure_drops_whole_on_any_member_epoch_event() {
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
            "the epoch member's cover must drop"
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

    fn measurement_u64(event: &crate::telemetry::capture::OwnedEvent, key: &str) -> u64 {
        match event.measurements.get(key) {
            Some(crate::telemetry::Value::U64(value)) => *value,
            other => panic!("expected u64 measurement {key}, got {other:?}"),
        }
    }

    fn measurement_bool(event: &crate::telemetry::capture::OwnedEvent, key: &str) -> bool {
        match event.measurements.get(key) {
            Some(crate::telemetry::Value::Bool(value)) => *value,
            other => panic!("expected bool measurement {key}, got {other:?}"),
        }
    }
}
