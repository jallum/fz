//! Compiler2's artifact-side program projections.
//!
//! `MaterializedProgram` is the first backend-owned snapshot for one closed
//! root. `AbiReadyProgram` is the next projection above it: the same closed
//! executable frontier with ABI lanes and return contracts made explicit.
//! `EmissionReadyProgram` is the final closed executable inventory before
//! backend lowering. `BackendProgram` is the backend-owned handoff: the same
//! closed inventory with settled clause-entry dispatch, direct executable
//! references, callable-boundary obligations, and concrete extern wire classes
//! attached to structured function bodies.

use std::collections::HashMap;

use crate::ast::{BinOp, UnOp};
use crate::compiler::source::Span;
use crate::dispatch_matrix::pattern::PatternDispatchPlan;
use crate::fz_ir::ExternTy;

use super::body::{CallSiteId, Literal, LoweredBody, LoweredExtern, ValueId};
use super::identity::{ExecutableKey, FunctionId, RootId};
use super::types::Ty;

#[derive(Debug, Clone, PartialEq)]
pub struct MaterializedProgram {
    pub semantic_revision: u64,
    pub entry: ExecutableKey,
    pub executables: HashMap<ExecutableKey, MaterializedExecutable>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MaterializedExecutable {
    pub entry_dispatch: Option<ExecutableDispatch>,
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
pub struct EmissionReadyProgram {
    pub abi_ready_revision: u64,
    pub entry: usize,
    pub executables: Vec<EmissionReadyExecutable>,
    pub callable_entries: Vec<EmissionReadyCallableEntry>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BackendProgram {
    pub emission_ready_revision: u64,
    pub entry: usize,
    pub atom_names: Vec<String>,
    pub executables: Vec<BackendExecutable>,
    pub callable_entries: Vec<BackendCallableEntry>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AbiReadyExecutable {
    pub entry_dispatch: Option<ExecutableDispatch>,
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

#[derive(Debug, Clone, PartialEq)]
pub struct EmissionReadyExecutable {
    pub key: ExecutableKey,
    pub entry_dispatch: Option<ExecutableDispatch>,
    pub return_ty: Ty,
    pub return_abi: ReturnAbi,
    pub param_reprs: Vec<AbiValueRepr>,
    pub value_types: HashMap<ValueId, Ty>,
    pub value_reprs: HashMap<ValueId, AbiValueRepr>,
    pub effects: EffectSummary,
    pub body: LoweredBody,
    pub call_edges: Vec<EmissionReadyCallEdge>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EmissionReadyCallEdge {
    pub callsite: CallSiteId,
    pub callee: usize,
    pub extern_marshals: Option<Vec<ExternTy>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EmissionReadyCallableEntry {
    pub target: usize,
    pub capture_count: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BackendExecutable {
    pub key: ExecutableKey,
    pub entry_dispatch: Option<ExecutableDispatch>,
    pub return_ty: Ty,
    pub return_abi: ReturnAbi,
    pub param_reprs: Vec<AbiValueRepr>,
    pub value_types: HashMap<ValueId, Ty>,
    pub value_reprs: HashMap<ValueId, AbiValueRepr>,
    pub effects: EffectSummary,
    pub body: BackendBody,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BackendCallableEntry {
    pub target: usize,
    pub capture_count: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BackendBody {
    Extern {
        signature: LoweredExtern,
    },
    Clauses {
        clauses: Vec<BackendClause>,
        generated: Vec<FunctionId>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExecutableDispatch {
    plan: PatternDispatchPlan<Ty>,
    clause_ids: Vec<u32>,
}

impl ExecutableDispatch {
    pub(crate) fn new(plan: PatternDispatchPlan<Ty>, clause_ids: Vec<u32>) -> Self {
        Self { plan, clause_ids }
    }

    pub(crate) fn plan(&self) -> &PatternDispatchPlan<Ty> {
        &self.plan
    }

    pub(crate) fn clause_index(&self, body_id: u32) -> Option<usize> {
        self.clause_ids.iter().position(|candidate| *candidate == body_id)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BackendClause {
    pub span: Span,
    pub params: Vec<ValueId>,
    pub projections: Vec<BackendStep>,
    pub body: BackendBlock,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BackendBlock {
    pub span: Span,
    pub steps: Vec<BackendStep>,
    pub result: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BackendCallArg {
    pub value: ValueId,
    pub callable_entries: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BackendStep {
    Const {
        value: ValueId,
        literal: Literal,
    },
    Tuple {
        value: ValueId,
        items: Vec<ValueId>,
    },
    List {
        value: ValueId,
        items: Vec<ValueId>,
        tail: Option<ValueId>,
    },
    FunctionRef {
        value: ValueId,
        function: FunctionId,
    },
    NamedFunctionRef {
        value: ValueId,
        name: String,
        arity: usize,
    },
    DirectCall {
        value: ValueId,
        callsite: CallSiteId,
        callee: usize,
        args: Vec<BackendCallArg>,
        extern_marshals: Option<Vec<ExternTy>>,
    },
    ClosureCall {
        value: ValueId,
        callsite: CallSiteId,
        callee: ValueId,
        target: usize,
        args: Vec<BackendCallArg>,
    },
    Lambda {
        value: ValueId,
        function: FunctionId,
        captures: Vec<ValueId>,
    },
    BinaryOp {
        value: ValueId,
        op: BinOp,
        left: ValueId,
        right: ValueId,
    },
    UnaryOp {
        value: ValueId,
        op: UnOp,
        input: ValueId,
    },
    MapIndex {
        value: ValueId,
        base: ValueId,
        key: ValueId,
    },
    If {
        value: ValueId,
        cond: ValueId,
        then_block: BackendBlock,
        else_block: BackendBlock,
    },
    AssertLiteral {
        source: ValueId,
        literal: Literal,
    },
    AssertTuple {
        source: ValueId,
        arity: usize,
    },
    TupleField {
        value: ValueId,
        source: ValueId,
        index: usize,
    },
    AssertEmptyList {
        source: ValueId,
    },
    AssertSame {
        source: ValueId,
        value: ValueId,
    },
    SplitList {
        source: ValueId,
        head: ValueId,
        tail: ValueId,
    },
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

#[derive(Debug, Default)]
pub struct EmissionReadyProgramMap {
    inner: RootProjectionMap<EmissionReadyProgram>,
}

#[derive(Debug, Default)]
pub struct BackendProgramMap {
    inner: RootProjectionMap<BackendProgram>,
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

impl EmissionReadyProgramMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, root: RootId, program: EmissionReadyProgram) -> u64 {
        self.inner.define(root, program)
    }

    pub fn get(&self, root: RootId) -> Option<&EmissionReadyProgram> {
        self.inner.get(root)
    }
}

impl BackendProgramMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, root: RootId, program: BackendProgram) -> u64 {
        self.inner.define(root, program)
    }

    pub fn get(&self, root: RootId) -> Option<&BackendProgram> {
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
