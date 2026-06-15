//! Shared transport descriptor vocabulary.
//!
//! This module is deliberately below any root-scoped `TransportPlan`: it owns
//! immutable descriptor interners and root-independent symbols only. Positions
//! may mention semantic body evidence, but descriptor keys must not.

use std::collections::HashMap;
use std::hash::Hash;
use std::marker::PhantomData;

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ShapeDescr {
    Nothing,
    Lane(LaneId),
    Tuple(Box<[ShapeId]>),
    Callable(CallableId),
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CallableDescr {
    pub function: Option<FunctionId>,
    pub capture_shapes: Box<[ShapeId]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CallableMaterializationKind {
    DirectOnly,
    FirstClass,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallableFacts {
    pub resolutions: Box<[ExecutableSymbol]>,
    pub direct_surfaces: Box<[Box<[ShapeId]>]>,
    pub capture_lanes: Box<[LaneId]>,
    pub materialization: CallableMaterializationKind,
    pub boundary_ids: Box<[BoundaryId]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BoundaryReturnDescr {
    Nothing,
    Value(LaneId),
    Tuple(Box<[LaneId]>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BoundaryDescr {
    pub callable: CallableId,
    pub surface_arg_shapes: Box<[ShapeId]>,
    pub published_capture_lanes: Box<[LaneId]>,
    pub published_arg_lanes: Box<[LaneId]>,
    pub published_return: BoundaryReturnDescr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundaryFacts {
    pub publications: Box<[TransportPosition]>,
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
        callsite: CallSiteId,
        entry: ControlEntryId,
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
    Boundary {
        boundary: BoundaryId,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TransportPlan {
    pub entry: ExecutableSymbol,
    pub executable_membership: Box<[ExecutableSymbol]>,
    pub positions: HashMap<TransportPosition, ShapeId>,
    pub callables: HashMap<CallableId, CallableFacts>,
    pub boundaries: HashMap<BoundaryId, BoundaryFacts>,
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

    fn ensure(&mut self, root: RootId) {
        let needed = root.as_u32() as usize + 1;
        if self.slots.len() < needed {
            self.slots.resize_with(needed, || None);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler2::identity::{FunctionMap, ModuleId};
    use crate::compiler2::types::Types;

    #[test]
    fn transport_shape_interner_hashes_recursive_children_by_id() {
        let mut types = Types::new();
        let int = types.int();
        let mut interners = TransportInterners::default();

        let lane = interners.intern_lane(LaneDescr {
            ty: int,
            class: TransportClass::Value,
        });
        let scalar = interners.intern_shape(ShapeDescr::Lane(lane));
        let tuple = interners.intern_shape(ShapeDescr::Tuple(vec![scalar].into_boxed_slice()));
        let tuple_again = interners.intern_shape(ShapeDescr::Tuple(vec![scalar].into_boxed_slice()));
        let nested = interners.intern_shape(ShapeDescr::Tuple(vec![tuple].into_boxed_slice()));

        assert_eq!(lane.as_u32(), 0);
        assert_eq!(scalar.as_u32(), 0);
        assert_eq!(tuple, tuple_again);
        assert_ne!(tuple, nested);
        assert_eq!(interners.shape_count(), 3);
        assert_eq!(
            interners.shape(tuple),
            &ShapeDescr::Tuple(vec![scalar].into_boxed_slice()),
            "tuple descriptors store child ShapeIds, not child descriptors"
        );
    }

    #[test]
    fn transport_descriptors_share_across_root_positions() {
        let mut types = Types::new();
        let int = types.int();
        let mut functions = FunctionMap::new();
        let add = functions.reference(ModuleId::GLOBAL, "add", 2);
        let mut store = TransportStore::new();
        let interners = store.interners_mut();

        let lane = interners.intern_lane(LaneDescr {
            ty: int,
            class: TransportClass::Value,
        });
        let shape = interners.intern_shape(ShapeDescr::Lane(lane));
        let executable = ExecutableSymbol {
            activation: ActivationSymbol {
                function: add,
                input: vec![int, int].into_boxed_slice(),
            },
            need: ExecutableNeed::Value,
        };
        let first_position = TransportPosition::ExecutableInput {
            executable: executable.clone(),
            semantic_index: 0,
        };
        let second_position = TransportPosition::Value {
            executable,
            value: ValueId::from_u32(7),
        };
        let callable = interners.intern_callable(CallableDescr {
            function: Some(add),
            capture_shapes: vec![shape].into_boxed_slice(),
        });
        let same_callable = interners.intern_callable(CallableDescr {
            function: Some(add),
            capture_shapes: vec![shape].into_boxed_slice(),
        });
        let callable_shape = interners.intern_shape(ShapeDescr::Callable(callable));
        let same_callable_shape = interners.intern_shape(ShapeDescr::Callable(same_callable));

        assert_ne!(first_position, second_position);
        assert_eq!(callable, same_callable);
        assert_eq!(callable_shape, same_callable_shape);
        assert_eq!(interners.callable_count(), 1);
        assert_eq!(interners.shape_count(), 2);
        assert_eq!(
            interners.callable(callable),
            &CallableDescr {
                function: Some(add),
                capture_shapes: vec![shape].into_boxed_slice(),
            },
            "callable descriptors are independent of root-scoped positions"
        );
    }

    #[test]
    fn transport_boundary_descriptors_are_interned_contracts() {
        let mut types = Types::new();
        let int = types.int();
        let mut functions = FunctionMap::new();
        let add = functions.reference(ModuleId::GLOBAL, "add", 2);
        let mut interners = TransportInterners::default();

        let lane = interners.intern_lane(LaneDescr {
            ty: int,
            class: TransportClass::Value,
        });
        let shape = interners.intern_shape(ShapeDescr::Lane(lane));
        let callable = interners.intern_callable(CallableDescr {
            function: Some(add),
            capture_shapes: vec![shape].into_boxed_slice(),
        });
        let boundary = BoundaryDescr {
            callable,
            surface_arg_shapes: vec![shape].into_boxed_slice(),
            published_capture_lanes: vec![lane].into_boxed_slice(),
            published_arg_lanes: vec![lane].into_boxed_slice(),
            published_return: BoundaryReturnDescr::Value(lane),
        };

        let first = interners.intern_boundary(boundary.clone());
        let second = interners.intern_boundary(boundary.clone());

        assert_eq!(first, second);
        assert_eq!(interners.boundary_count(), 1);
        assert_eq!(interners.boundary(first), &boundary);
    }
}
