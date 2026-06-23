//! Shared transport descriptor vocabulary.
//!
//! This module is deliberately below any root-scoped `TransportPlan`: it owns
//! immutable descriptor interners and root-independent symbols only. Positions
//! may mention semantic body evidence, but descriptor keys must not.

use std::collections::HashMap;
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::Range;

use super::body::{CallSiteId, ControlEntryId, ValueId};
use super::identity::{ExecutableNeed, FunctionId, RootId};
use super::types::Ty;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ShapeId(u32);

impl ShapeId {
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LaneId(u32);

impl LaneId {
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CallableId(u32);

impl CallableId {
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BoundaryId(u32);

impl BoundaryId {
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

trait InternedId: Copy {
    fn from_u32(raw: u32) -> Self;
    fn as_usize(self) -> usize;
}

impl InternedId for ShapeId {
    fn from_u32(raw: u32) -> Self {
        Self(raw)
    }

    fn as_usize(self) -> usize {
        self.0 as usize
    }
}

impl InternedId for LaneId {
    fn from_u32(raw: u32) -> Self {
        Self(raw)
    }

    fn as_usize(self) -> usize {
        self.0 as usize
    }
}

impl InternedId for CallableId {
    fn from_u32(raw: u32) -> Self {
        Self(raw)
    }

    fn as_usize(self) -> usize {
        self.0 as usize
    }
}

impl InternedId for BoundaryId {
    fn from_u32(raw: u32) -> Self {
        Self(raw)
    }

    fn as_usize(self) -> usize {
        self.0 as usize
    }
}

/// The cross-executable agreement state for one input position's transport
/// shape. Each caller contributes the [`ShapeId`] it sends across the call
/// edge; the join answers a single question: "do all callers agree on one
/// physical layout?".
///
/// Sticky three-state join-semilattice, height `<= 2`, strictly monotone, so it
/// needs no widening budget:
///
/// - `Unbound` — bottom: no caller has contributed yet.
/// - `Agreed(shape)` — every caller seen so far carries exactly this layout.
/// - `Conflicted` — two distinct layouts seen; collapses to top and stays there.
///
/// `Unbound` is deliberately distinct from `Conflicted`: "no caller yet" is not
/// "callers disagree". Conflating them would let an empty caller set masquerade
/// as a resolved single shape (the unknown-is-not-none rule).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShapeAgreement {
    Unbound,
    Agreed(ShapeId),
    Conflicted,
}

impl ShapeAgreement {
    /// The least element: zero contributors.
    pub const BOTTOM: Self = ShapeAgreement::Unbound;

    /// A single caller's contribution of `shape`.
    pub fn of(shape: ShapeId) -> Self {
        ShapeAgreement::Agreed(shape)
    }

    /// The agreed shape iff every contributor so far carries one layout.
    /// `None` for both `Unbound` (nobody yet) and `Conflicted` (disagreement).
    pub fn agreed(self) -> Option<ShapeId> {
        match self {
            ShapeAgreement::Agreed(shape) => Some(shape),
            ShapeAgreement::Unbound | ShapeAgreement::Conflicted => None,
        }
    }

    pub fn is_conflicted(self) -> bool {
        matches!(self, ShapeAgreement::Conflicted)
    }

    /// Monotone join: `self ⊔ other`. Commutative, idempotent, with a sticky
    /// top — once `Conflicted`, always `Conflicted`.
    pub fn join(self, other: Self) -> Self {
        use ShapeAgreement::{Agreed, Conflicted, Unbound};
        match (self, other) {
            (Unbound, rhs) => rhs,
            (lhs, Unbound) => lhs,
            (Conflicted, _) | (_, Conflicted) => Conflicted,
            (Agreed(left), Agreed(right)) if left == right => Agreed(left),
            (Agreed(_), Agreed(_)) => Conflicted,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ShapeDescr {
    Nothing,
    Lane(LaneId),
    Tuple(Box<[ShapeId]>),
    Callable(CallableId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TransportValue<Lane> {
    Absent,
    Runtime(Lane),
    Transport { shape: ShapeId, lanes: Vec<Lane> },
}

impl<Lane: Copy> TransportValue<Lane> {
    pub fn runtime_lane(&self) -> Option<Lane> {
        match self {
            Self::Runtime(lane) => Some(*lane),
            Self::Absent | Self::Transport { .. } => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TransportClass {
    Value,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LaneDescr {
    pub ty: Ty,
    pub class: TransportClass,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ActivationSymbol {
    pub function: FunctionId,
    pub input: Box<[Ty]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExecutableSymbol {
    pub activation: ActivationSymbol,
    pub need: ExecutableNeed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CodegenLaneRepr {
    ValueRef,
    RawInt,
    RawF64,
    RawAtom,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CodegenSeam {
    FunctionEntry {
        executable: ExecutableSymbol,
        semantic_index: usize,
    },
    BlockParam {
        executable: ExecutableSymbol,
        entry: ControlEntryId,
    },
    ReturnDelivery {
        executable: ExecutableSymbol,
    },
    ContinuationEntry {
        executable: ExecutableSymbol,
        callsite: CallSiteId,
        entry: ControlEntryId,
    },
    ReturnContinuation {
        executable: ExecutableSymbol,
        callsite: CallSiteId,
    },
    TailCall {
        executable: ExecutableSymbol,
        callsite: CallSiteId,
    },
    CallableBoundary {
        boundary: BoundaryId,
    },
    ExternBoundary {
        executable: ExecutableSymbol,
    },
    FirstClassPublication {
        boundary: BoundaryId,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CodegenSeamFact {
    pub seam: CodegenSeam,
    pub shape: Option<ShapeId>,
    pub lane: LaneId,
    pub repr: CodegenLaneRepr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CallableDescr {
    pub function: Option<FunctionId>,
    pub capture_shapes: Box<[ShapeId]>,
    pub capture_lanes: Box<[LaneId]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallableFacts {
    pub resolutions: Box<[ExecutableSymbol]>,
    pub direct_surfaces: Box<[Box<[ShapeId]>]>,
    pub direct_edges: Box<[CallableDirectEdge]>,
    pub boundary_ids: Box<[BoundaryId]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CallableDirectEdge {
    pub surface_inputs: Box<[Ty]>,
    pub surface_arg_shapes: Box<[ShapeId]>,
    pub resolution: ExecutableSymbol,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BoundaryDescr {
    pub callable: CallableId,
    pub surface_arg_shapes: Box<[ShapeId]>,
    pub published_value_lane: LaneId,
    pub published_capture_lanes: Box<[LaneId]>,
    pub published_arg_lanes: Box<[LaneId]>,
    pub published_return_shape: ShapeId,
    pub published_return_lanes: Box<[LaneId]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundaryFacts {
    pub publications: Box<[TransportPosition]>,
    pub resolutions: Box<[ExecutableSymbol]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TransportPosition {
    ExecutableInput {
        executable: ExecutableSymbol,
        semantic_index: usize,
    },
    ExecutableReturn {
        executable: ExecutableSymbol,
    },
    ResumePayload {
        executable: ExecutableSymbol,
        callsite: Option<CallSiteId>,
        entry: ControlEntryId,
    },
    ReturnPayload {
        executable: ExecutableSymbol,
        callsite: CallSiteId,
    },
    CallArg {
        executable: ExecutableSymbol,
        callsite: CallSiteId,
        semantic_index: usize,
    },
    EntryCapture {
        executable: ExecutableSymbol,
        entry: ControlEntryId,
        capture_index: usize,
    },
    Value {
        executable: ExecutableSymbol,
        value: ValueId,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TransportPlan {
    pub entry: ExecutableSymbol,
    pub executable_membership: Box<[ExecutableSymbol]>,
    pub positions: HashMap<TransportPosition, ShapeId>,
    pub callables: HashMap<CallableId, CallableFacts>,
    pub boundaries: HashMap<BoundaryId, BoundaryFacts>,
    pub codegen_seam_facts: Box<[CodegenSeamFact]>,
}

#[derive(Debug, Default)]
pub struct TransportStore {
    interners: TransportInterners,
    plans: TransportPlanMap,
}

impl TransportStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn interners(&self) -> &TransportInterners {
        &self.interners
    }

    pub fn interners_mut(&mut self) -> &mut TransportInterners {
        &mut self.interners
    }

    pub fn plans(&self) -> &TransportPlanMap {
        &self.plans
    }

    pub fn plans_mut(&mut self) -> &mut TransportPlanMap {
        &mut self.plans
    }
}

#[derive(Debug, Default)]
pub struct TransportInterners {
    shapes: Interner<ShapeDescr, ShapeId>,
    lanes: Interner<LaneDescr, LaneId>,
    callables: Interner<CallableDescr, CallableId>,
    boundaries: Interner<BoundaryDescr, BoundaryId>,
}

impl TransportInterners {
    pub fn intern_shape(&mut self, descr: ShapeDescr) -> ShapeId {
        self.shapes.intern(descr)
    }

    pub fn shape(&self, id: ShapeId) -> &ShapeDescr {
        self.shapes.get(id)
    }

    pub fn shape_width(&self, shape: ShapeId) -> usize {
        self.shape_lane_ids(shape).len()
    }

    pub fn shape_lane_ids(&self, shape: ShapeId) -> Vec<LaneId> {
        match self.shape(shape) {
            ShapeDescr::Nothing => Vec::new(),
            ShapeDescr::Lane(lane) => vec![*lane],
            ShapeDescr::Tuple(fields) => fields
                .iter()
                .copied()
                .flat_map(|field| self.shape_lane_ids(field))
                .collect(),
            ShapeDescr::Callable(callable) => self.callable(*callable).capture_lanes.to_vec(),
        }
    }

    pub fn shape_leaf_lanes(&self, shape: ShapeId) -> Vec<(ShapeId, LaneId)> {
        match self.shape(shape) {
            ShapeDescr::Nothing => Vec::new(),
            ShapeDescr::Lane(lane) => vec![(shape, *lane)],
            ShapeDescr::Tuple(fields) => fields
                .iter()
                .copied()
                .flat_map(|field| self.shape_leaf_lanes(field))
                .collect(),
            ShapeDescr::Callable(callable) => self
                .callable(*callable)
                .capture_lanes
                .iter()
                .copied()
                .map(|lane| (shape, lane))
                .collect(),
        }
    }

    pub fn tuple_field_spans(&self, shape: ShapeId) -> Option<Vec<(ShapeId, Range<usize>)>> {
        let ShapeDescr::Tuple(fields) = self.shape(shape) else {
            return None;
        };
        let mut offset = 0_usize;
        let mut spans = Vec::with_capacity(fields.len());
        for field in fields.iter().copied() {
            let width = self.shape_width(field);
            let end = offset
                .checked_add(width)
                .expect("transport tuple field lane span overflow");
            spans.push((field, offset..end));
            offset = end;
        }
        Some(spans)
    }

    pub fn shape_count(&self) -> usize {
        self.shapes.len()
    }

    pub fn intern_lane(&mut self, descr: LaneDescr) -> LaneId {
        self.lanes.intern(descr)
    }

    pub fn lane(&self, id: LaneId) -> &LaneDescr {
        self.lanes.get(id)
    }

    pub fn lane_count(&self) -> usize {
        self.lanes.len()
    }

    pub fn intern_callable(&mut self, descr: CallableDescr) -> CallableId {
        self.callables.intern(descr)
    }

    pub fn callable(&self, id: CallableId) -> &CallableDescr {
        self.callables.get(id)
    }

    pub fn callable_count(&self) -> usize {
        self.callables.len()
    }

    pub fn intern_boundary(&mut self, descr: BoundaryDescr) -> BoundaryId {
        self.boundaries.intern(descr)
    }

    pub fn boundary(&self, id: BoundaryId) -> &BoundaryDescr {
        self.boundaries.get(id)
    }

    pub fn boundary_count(&self) -> usize {
        self.boundaries.len()
    }

    pub fn shapes(&self) -> impl Iterator<Item = (ShapeId, &ShapeDescr)> + '_ {
        self.shapes.iter()
    }

    pub fn lanes(&self) -> impl Iterator<Item = (LaneId, &LaneDescr)> + '_ {
        self.lanes.iter()
    }

    pub fn callables(&self) -> impl Iterator<Item = (CallableId, &CallableDescr)> + '_ {
        self.callables.iter()
    }

    pub fn boundaries(&self) -> impl Iterator<Item = (BoundaryId, &BoundaryDescr)> + '_ {
        self.boundaries.iter()
    }
}

#[derive(Debug)]
struct Interner<D, I> {
    arena: Vec<D>,
    index: HashMap<D, I>,
    id: PhantomData<I>,
}

impl<D, I> Default for Interner<D, I> {
    fn default() -> Self {
        Self {
            arena: Vec::new(),
            index: HashMap::new(),
            id: PhantomData,
        }
    }
}

impl<D, I> Interner<D, I>
where
    D: Clone + Eq + Hash,
    I: InternedId + Eq + Hash,
{
    fn intern(&mut self, descr: D) -> I {
        if let Some(id) = self.index.get(&descr) {
            return *id;
        }
        let raw = self.arena.len();
        assert!(u32::try_from(raw).is_ok(), "transport interner exhausted ids");
        let id = I::from_u32(raw as u32);
        self.arena.push(descr.clone());
        self.index.insert(descr, id);
        id
    }

    fn get(&self, id: I) -> &D {
        self.arena
            .get(id.as_usize())
            .unwrap_or_else(|| panic!("unknown transport descriptor id {}", id.as_usize()))
    }

    fn len(&self) -> usize {
        self.arena.len()
    }

    fn iter(&self) -> impl Iterator<Item = (I, &D)> + '_ {
        self.arena
            .iter()
            .enumerate()
            .map(|(index, descr)| (I::from_u32(index as u32), descr))
    }
}

#[derive(Debug, Default)]
pub struct TransportPlanMap {
    slots: Vec<Option<TransportPlan>>,
}

impl TransportPlanMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, root: RootId, plan: TransportPlan) -> bool {
        self.ensure(root);
        let slot = &mut self.slots[root.as_u32() as usize];
        let changed = !matches!(slot, Some(existing) if existing == &plan);
        *slot = Some(plan);
        changed
    }

    pub fn get(&self, root: RootId) -> Option<&TransportPlan> {
        self.slots.get(root.as_u32() as usize).and_then(|slot| slot.as_ref())
    }

    pub fn remove(&mut self, root: RootId) -> Option<TransportPlan> {
        self.slots.get_mut(root.as_u32() as usize).and_then(Option::take)
    }

    fn ensure(&mut self, root: RootId) {
        let needed = root.as_u32() as usize + 1;
        if self.slots.len() < needed {
            self.slots.resize_with(needed, || None);
        }
    }
}
