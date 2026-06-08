//! Compiler2's artifact-side program projections.
//!
//! `MaterializedProgram` is the first backend-owned snapshot for one closed
//! root. `AbiReadyProgram` is the next projection above it: the same closed
//! executable frontier with ABI lanes and return contracts made explicit.

use std::collections::HashMap;

use crate::fz_ir::ExternTy;

use super::body::{CallSiteId, LoweredBody, ValueId};
use super::identity::{ExecutableKey, RootId};
use super::types::Ty;

#[derive(Debug, Clone, PartialEq)]
pub struct MaterializedProgram {
    pub semantic_revision: u64,
    pub entry: ExecutableKey,
    pub executables: HashMap<ExecutableKey, MaterializedExecutable>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MaterializedExecutable {
    pub return_ty: Ty,
    pub value_types: HashMap<ValueId, Ty>,
    pub effects: EffectSummary,
    pub body: LoweredBody,
    pub call_edges: HashMap<CallSiteId, MaterializedCallEdge>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaterializedCallEdge {
    pub callee: ExecutableKey,
    pub return_ty: Ty,
    pub extern_marshals: Option<Vec<ExternTy>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AbiReadyProgram {
    pub materialized_revision: u64,
    pub entry: ExecutableKey,
    pub executables: HashMap<ExecutableKey, AbiReadyExecutable>,
    pub callable_entries: Vec<CallableEntry>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AbiReadyExecutable {
    pub return_ty: Ty,
    pub return_abi: ReturnAbi,
    pub param_reprs: Vec<AbiValueRepr>,
    pub value_types: HashMap<ValueId, Ty>,
    pub value_reprs: HashMap<ValueId, AbiValueRepr>,
    pub effects: EffectSummary,
    pub body: LoweredBody,
    pub call_edges: HashMap<CallSiteId, AbiReadyCallEdge>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbiReadyCallEdge {
    pub callee: ExecutableKey,
    pub return_ty: Ty,
    pub return_abi: ReturnAbi,
    pub extern_marshals: Option<Vec<ExternTy>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallableEntry {
    pub target: ExecutableKey,
    pub capture_count: usize,
    pub param_reprs: Vec<AbiValueRepr>,
    pub return_ty: Ty,
    pub return_abi: ReturnAbi,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AbiValueRepr {
    ValueRef,
    RawInt,
    RawF64,
    RawAtom,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReturnAbi {
    Value(AbiValueRepr),
    TupleFields(Vec<AbiValueRepr>),
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct EffectSummary {
    pub allocates: bool,
    pub observable: bool,
    pub reads_allocation_stats: bool,
    pub scheduler_visible: bool,
    pub halts: bool,
    pub calls_opaque: bool,
}

impl EffectSummary {
    pub fn union_with(&mut self, other: EffectSummary) -> bool {
        let before = *self;
        self.allocates |= other.allocates;
        self.observable |= other.observable;
        self.reads_allocation_stats |= other.reads_allocation_stats;
        self.scheduler_visible |= other.scheduler_visible;
        self.halts |= other.halts;
        self.calls_opaque |= other.calls_opaque;
        *self != before
    }
}

#[derive(Debug, Clone)]
struct ProjectionSlot<T> {
    state: ProjectionState<T>,
    revision: u64,
}

#[derive(Debug, Clone)]
enum ProjectionState<T> {
    Placeholder,
    Defined(T),
}

#[derive(Debug)]
struct RootProjectionMap<T> {
    slots: Vec<ProjectionSlot<T>>,
}

#[derive(Debug, Default)]
pub struct MaterializedProgramMap {
    inner: RootProjectionMap<MaterializedProgram>,
}

#[derive(Debug, Default)]
pub struct AbiReadyProgramMap {
    inner: RootProjectionMap<AbiReadyProgram>,
}

impl MaterializedProgramMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, root: RootId, program: MaterializedProgram) -> u64 {
        self.inner.define(root, program)
    }

    pub fn get(&self, root: RootId) -> Option<&MaterializedProgram> {
        self.inner.get(root)
    }
}

impl AbiReadyProgramMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, root: RootId, program: AbiReadyProgram) -> u64 {
        self.inner.define(root, program)
    }

    pub fn get(&self, root: RootId) -> Option<&AbiReadyProgram> {
        self.inner.get(root)
    }
}

impl<T> RootProjectionMap<T>
where
    T: PartialEq,
{
    fn define(&mut self, root: RootId, value: T) -> u64 {
        self.ensure(root);
        let slot = &mut self.slots[root.as_u32() as usize];
        let next = ProjectionState::Defined(value);
        if !slot.state.same_state(&next) {
            slot.state = next;
            slot.revision += 1;
        }
        slot.revision
    }

    fn get(&self, root: RootId) -> Option<&T> {
        match &self.slots.get(root.as_u32() as usize)?.state {
            ProjectionState::Placeholder => None,
            ProjectionState::Defined(value) => Some(value),
        }
    }

    fn ensure(&mut self, root: RootId) {
        let needed = root.as_u32() as usize + 1;
        if self.slots.len() < needed {
            self.slots.resize_with(needed, || ProjectionSlot {
                state: ProjectionState::Placeholder,
                revision: 0,
            });
        }
    }
}

impl<T> Default for RootProjectionMap<T> {
    fn default() -> Self {
        Self { slots: Vec::new() }
    }
}

impl<T> ProjectionState<T>
where
    T: PartialEq,
{
    fn same_state(&self, other: &Self) -> bool {
        match (self, other) {
            (ProjectionState::Placeholder, ProjectionState::Placeholder) => true,
            (ProjectionState::Defined(left), ProjectionState::Defined(right)) => left == right,
            _ => false,
        }
    }
}
