//! Shared transport descriptor vocabulary.
//!
//! This module is deliberately below the root-scoped `MaterializedTransportPlan`
//! (`artifact.rs`): it owns immutable descriptor interners and root-independent
//! symbols only. Positions may mention semantic body evidence, but descriptor
//! keys must not.

use std::collections::HashMap;
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::Range;

use super::body::{CallSiteId, ControlEntryId, ValueId};
use super::identity::{ExecutableNeed, FunctionId};
use super::semantic::SemanticOrd;
use super::types::{Ty, Types};
use crate::dispatch_matrix::pattern::PatternDispatchPlan;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ShapeId(u32);

impl ShapeId {
    pub fn as_u32(self) -> u32 {
        self.0
    }

    #[cfg(test)]
    pub(crate) fn for_test(raw: u32) -> Self {
        Self(raw)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TransportCarrier {
    Absent,
    ValueRef,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TransportLayout {
    pub structural: ShapeId,
    pub carrier: TransportCarrier,
}

impl TransportLayout {
    pub const fn structural(structural: ShapeId) -> Self {
        Self {
            structural,
            carrier: TransportCarrier::Absent,
        }
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

    #[cfg(test)]
    pub(crate) fn for_test(raw: u32) -> Self {
        Self(raw)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BoundaryId(u32);

impl BoundaryId {
    pub fn as_u32(self) -> u32 {
        self.0
    }

    #[cfg(test)]
    pub(crate) fn for_test(raw: u32) -> Self {
        Self(raw)
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
    pub arrow: Ty,
    pub input: Box<[Ty]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExecutableSymbol {
    pub activation: ActivationSymbol,
    pub need: ExecutableNeed,
}

impl SemanticOrd<Types> for ExecutableSymbol {
    fn semantic_cmp(&self, other: &Self, types: &Types) -> std::cmp::Ordering {
        self.activation
            .function
            .cmp(&other.activation.function)
            .then_with(|| types.cmp_activation_ty(self.activation.arrow, other.activation.arrow))
            .then_with(|| types.cmp_activation_tys(&self.activation.input, &other.activation.input))
            .then_with(|| self.need.cmp(&other.need))
    }
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
    EntryCapture {
        executable: ExecutableSymbol,
        entry: ControlEntryId,
        capture_index: usize,
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

impl CodegenSeam {
    #[cfg(test)]
    pub(crate) fn executable(&self) -> Option<&ExecutableSymbol> {
        match self {
            Self::FunctionEntry { executable, .. }
            | Self::BlockParam { executable, .. }
            | Self::EntryCapture { executable, .. }
            | Self::ReturnDelivery { executable }
            | Self::ContinuationEntry { executable, .. }
            | Self::ReturnContinuation { executable, .. }
            | Self::TailCall { executable, .. }
            | Self::ExternBoundary { executable } => Some(executable),
            Self::CallableBoundary { .. } | Self::FirstClassPublication { .. } => None,
        }
    }
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
    /// The callable's user-visible parameter count — what a rendered fun
    /// reports (`#fn<id/arity>`, Elixir's `#Function<.../arity>`). It is fixed
    /// by the source, unlike the capture lanes below, which demand may elide
    /// to nothing. Functionally determined by `function`, so it never splits
    /// an interner pool (fz-gk4).
    pub arity: u16,
    /// The settled types of the closure's lexical captures. They remain part
    /// of callable identity even when demand elides every physical capture
    /// lane, preventing distinct groundings from pooling at the interner.
    pub capture_tys: Box<[Ty]>,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallableConstructionFact {
    pub callable: CallableId,
    pub producer: TransportPosition,
    pub captures: Box<[CallableConstructionCapture]>,
    pub members: Box<[CallableConstructionMember]>,
    pub(crate) selection: Option<PatternDispatchPlan<Ty>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallableConstructionOwner {
    pub layout: TransportLayout,
    pub construction: Option<CallableConstructionFact>,
    pub callable_facts: HashMap<CallableId, CallableFacts>,
    pub boundary_facts: HashMap<BoundaryId, BoundaryFacts>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallableConstructionCapture {
    pub source: TransportPosition,
    pub layout: TransportLayout,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallableConstructionMember {
    pub boundary: BoundaryId,
    pub surface_inputs: Box<[Ty]>,
    pub surface_arg_shapes: Box<[ShapeId]>,
    pub resolution: ExecutableSymbol,
    pub capture_semantic_inputs: Box<[usize]>,
    pub surface_semantic_inputs: Box<[usize]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CallableDirectEdge {
    pub surface_inputs: Box<[Ty]>,
    pub surface_arg_shapes: Box<[ShapeId]>,
    pub resolution: ExecutableSymbol,
    pub capture_semantic_inputs: Box<[usize]>,
    pub surface_semantic_inputs: Box<[usize]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BoundaryDescr {
    pub callable: CallableId,
    pub surface_arg_shapes: Box<[ShapeId]>,
    pub published_value_lane: LaneId,
    pub published_capture_lanes: Box<[LaneId]>,
    pub published_arg_lanes: Box<[LaneId]>,
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

impl TransportPosition {
    /// The executable that owns this position.
    pub fn executable(&self) -> &ExecutableSymbol {
        match self {
            Self::ExecutableInput { executable, .. }
            | Self::ExecutableReturn { executable }
            | Self::ResumePayload { executable, .. }
            | Self::ReturnPayload { executable, .. }
            | Self::CallArg { executable, .. }
            | Self::EntryCapture { executable, .. }
            | Self::Value { executable, .. } => executable,
        }
    }
}

impl SemanticOrd<Types> for TransportPosition {
    fn semantic_cmp(&self, other: &Self, types: &Types) -> std::cmp::Ordering {
        transport_position_rank(self)
            .cmp(&transport_position_rank(other))
            .then_with(|| self.executable().semantic_cmp(other.executable(), types))
            .then_with(|| match (self, other) {
                (
                    Self::ExecutableInput {
                        semantic_index: left, ..
                    },
                    Self::ExecutableInput {
                        semantic_index: right, ..
                    },
                ) => left.cmp(right),
                (
                    Self::ResumePayload {
                        callsite: left_callsite,
                        entry: left_entry,
                        ..
                    },
                    Self::ResumePayload {
                        callsite: right_callsite,
                        entry: right_entry,
                        ..
                    },
                ) => left_callsite
                    .cmp(right_callsite)
                    .then_with(|| left_entry.as_u32().cmp(&right_entry.as_u32())),
                (Self::ReturnPayload { callsite: left, .. }, Self::ReturnPayload { callsite: right, .. }) => {
                    left.cmp(right)
                }
                (
                    Self::CallArg {
                        callsite: left_callsite,
                        semantic_index: left_index,
                        ..
                    },
                    Self::CallArg {
                        callsite: right_callsite,
                        semantic_index: right_index,
                        ..
                    },
                ) => left_callsite
                    .cmp(right_callsite)
                    .then_with(|| left_index.cmp(right_index)),
                (
                    Self::EntryCapture {
                        entry: left_entry,
                        capture_index: left_index,
                        ..
                    },
                    Self::EntryCapture {
                        entry: right_entry,
                        capture_index: right_index,
                        ..
                    },
                ) => left_entry
                    .as_u32()
                    .cmp(&right_entry.as_u32())
                    .then_with(|| left_index.cmp(right_index)),
                (Self::Value { value: left, .. }, Self::Value { value: right, .. }) => left.cmp(right),
                _ => std::cmp::Ordering::Equal,
            })
    }
}

fn transport_position_rank(position: &TransportPosition) -> u8 {
    match position {
        TransportPosition::CallArg { .. } => 0,
        TransportPosition::EntryCapture { .. } => 1,
        TransportPosition::ExecutableInput { .. } => 2,
        TransportPosition::ExecutableReturn { .. } => 3,
        TransportPosition::ResumePayload { .. } => 4,
        TransportPosition::ReturnPayload { .. } => 5,
        TransportPosition::Value { .. } => 6,
    }
}

#[derive(Debug, Default)]
pub struct TransportStore {
    interners: TransportInterners,
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
