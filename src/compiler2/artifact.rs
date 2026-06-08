//! Compiler2's artifact-side program projections.
//!
//! `MaterializedProgram` is the first backend-owned snapshot for one closed
//! root. `AbiReadyProgram` is the next projection above it: the same closed
//! executable frontier with ABI lanes and return contracts made explicit.
//! `EmissionReadyProgram` is the final closed executable inventory before
//! backend lowering. `BackendProgram` is the interpreter-ready handoff: the
//! same closed inventory with settled clause-entry dispatch, direct
//! executable references, callable-boundary obligations, and concrete extern
//! wire classes attached to structured function bodies. Native codegen needs
//! one more Compiler2-owned projection above that: `NativeProgram`, a
//! codegen-ready CPS/native handoff that carries only backend-consumption
//! facts and never rebuilds `ModulePlan`, `PlannedProgram`, or `AbiFacts`.

use std::collections::HashMap;

use crate::ast::{BinOp, UnOp};
use crate::compiler::source::Span;
use crate::dispatch_matrix::pattern::PatternDispatchPlan;
use crate::fz_ir::{
    Block as IrBlock, CallsiteId as IrCallsiteId, CallsiteIdent, Cont as IrCont, ExternMarshalSite, ExternTy,
    ExternalCallEdge, FnId, FnIr as IrFn, Module as IrModule, Prim as IrPrim, ReceiveAfter, ReceiveClause,
    Stmt as IrStmt, Term as IrTerm, Var,
};

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

#[derive(Debug, Clone)]
pub(crate) struct NativeProgram {
    /// Revision of the `BackendProgram(root)` snapshot this native handoff
    /// was derived from.
    pub backend_revision: u64,
    /// The CPS/native entry body the shared JIT/AOT pipeline should start at.
    pub entry: FnId,
    /// Compiler2-owned CPS/native module handed to shared codegen. This
    /// replaces the old prepared `Module` input for Compiler2-native runs.
    pub module: IrModule,
    /// Per-body native facts that replace old planner-owned side tables such
    /// as `ModulePlan.effective_returns`, `SpecPlan.vars`, and continuation
    /// classification.
    pub bodies: Vec<NativeBody>,
    /// Closed callable-entry inventory plus callable identity bodies. This
    /// replaces the old planner-side callable-entry lookup surface.
    pub callable_entries: Vec<NativeCallableEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NativeEntryAbi {
    Direct,
    Continuation { extra_params: usize },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NativeBodyOrigin {
    Executable(ExecutableKey),
    Clause { owner: ExecutableKey, index: u32 },
    Continuation { owner: FnId, index: u32 },
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct NativeBody {
    /// Body identity inside `module`.
    pub fn_id: FnId,
    /// Why this CPS/native body exists.
    pub origin: NativeBodyOrigin,
    /// ABI shape at the entry seam.
    pub entry_abi: NativeEntryAbi,
    /// ABI lanes at the entry seam.
    pub param_reprs: Vec<AbiValueRepr>,
    pub return_ty: Ty,
    pub return_abi: ReturnAbi,
    /// Final per-value types after Compiler2 lowering into CPS/native form.
    pub value_types: HashMap<Var, Ty>,
    /// Callable-constructor vars mapped to the closed callable-entry
    /// inventory they may materialize.
    pub callable_constructors: HashMap<Var, Vec<usize>>,
    /// Concrete extern marshal classes keyed by CPS/native extern site.
    pub extern_marshals: HashMap<ExternMarshalSite, ExternTy>,
    pub effects: EffectSummary,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NativeCallableEntry {
    /// Synthetic callable identity used at `MakeFnRef` / `MakeClosure` sites.
    pub identity_fn: FnId,
    /// Direct executable-entry body the callable entry ultimately reaches.
    pub target_fn: FnId,
    pub target: ExecutableKey,
    pub capture_count: usize,
    pub param_reprs: Vec<AbiValueRepr>,
    pub return_ty: Ty,
    pub return_abi: ReturnAbi,
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

#[derive(Debug, Default)]
pub(crate) struct NativeProgramMap {
    slots: Vec<ProjectionSlot<NativeProgram>>,
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

impl NativeProgramMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, root: RootId, program: NativeProgram) -> u64 {
        self.ensure(root);
        let slot = &mut self.slots[root.as_u32() as usize];
        let next = ProjectionState::Defined(program);
        if !native_program_same_state(&slot.state, &next) {
            slot.state = next;
            slot.revision += 1;
        }
        slot.revision
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

fn native_program_same_state(left: &ProjectionState<NativeProgram>, right: &ProjectionState<NativeProgram>) -> bool {
    match (left, right) {
        (ProjectionState::Placeholder, ProjectionState::Placeholder) => true,
        (ProjectionState::Defined(left), ProjectionState::Defined(right)) => native_programs_equal(left, right),
        _ => false,
    }
}

fn native_programs_equal(left: &NativeProgram, right: &NativeProgram) -> bool {
    left.backend_revision == right.backend_revision
        && left.entry == right.entry
        && left.bodies == right.bodies
        && left.callable_entries == right.callable_entries
        && native_modules_equal(&left.module, &right.module)
}

fn native_modules_equal(left: &IrModule, right: &IrModule) -> bool {
    left.module_path == right.module_path
        && left.fns.len() == right.fns.len()
        && left
            .fns
            .iter()
            .zip(right.fns.iter())
            .all(|(left, right)| native_fns_equal(left, right))
        && left.fn_idx == right.fn_idx
        && left.atom_names == right.atom_names
        && left.externs == right.externs
        && left.extern_idx == right.extern_idx
        && left.external_call_edges.len() == right.external_call_edges.len()
        && left
            .external_call_edges
            .iter()
            .zip(right.external_call_edges.iter())
            .all(|(left, right)| native_external_call_edges_equal(left, right))
        && left.protocol_call_targets == right.protocol_call_targets
}

fn native_fns_equal(left: &IrFn, right: &IrFn) -> bool {
    left.id == right.id
        && left.name == right.name
        && left.frame_schema_id == right.frame_schema_id
        && left.entry == right.entry
        && left.category == right.category
        && left.owner_module == right.owner_module
        && left.ignored_entry_params == right.ignored_entry_params
        && left.physical_entry_params == right.physical_entry_params
        && left.physical_capabilities == right.physical_capabilities
        && left.blocks.len() == right.blocks.len()
        && left
            .blocks
            .iter()
            .zip(right.blocks.iter())
            .all(|(left, right)| native_blocks_equal(left, right))
}

fn native_blocks_equal(left: &IrBlock, right: &IrBlock) -> bool {
    left.id == right.id
        && left.params == right.params
        && left.stmts.len() == right.stmts.len()
        && left
            .stmts
            .iter()
            .zip(right.stmts.iter())
            .all(|(left, right)| native_stmts_equal(left, right))
        && native_terms_equal(&left.terminator, &right.terminator)
}

fn native_stmts_equal(left: &IrStmt, right: &IrStmt) -> bool {
    match (left, right) {
        (IrStmt::Let(left_var, left_prim), IrStmt::Let(right_var, right_prim)) => {
            left_var == right_var && native_prims_equal(left_prim, right_prim)
        }
    }
}

fn native_prims_equal(left: &IrPrim, right: &IrPrim) -> bool {
    match (left, right) {
        (IrPrim::Extern(left_ident, left_extern, left_args), IrPrim::Extern(right_ident, right_extern, right_args)) => {
            native_callsite_idents_equal(left_ident, right_ident)
                && left_extern == right_extern
                && left_args == right_args
        }
        (IrPrim::MakeFnRef(left_ident, left_fn), IrPrim::MakeFnRef(right_ident, right_fn)) => {
            native_callsite_idents_equal(left_ident, right_ident) && left_fn == right_fn
        }
        (
            IrPrim::MakeClosure(left_ident, left_fn, left_captured),
            IrPrim::MakeClosure(right_ident, right_fn, right_captured),
        ) => {
            native_callsite_idents_equal(left_ident, right_ident)
                && left_fn == right_fn
                && left_captured == right_captured
        }
        _ => left == right,
    }
}

fn native_terms_equal(left: &IrTerm, right: &IrTerm) -> bool {
    match (left, right) {
        (IrTerm::Goto(left_block, left_args), IrTerm::Goto(right_block, right_args)) => {
            left_block == right_block && left_args == right_args
        }
        (
            IrTerm::If {
                cond: left_cond,
                then_b: left_then,
                else_b: left_else,
                origin: left_origin,
            },
            IrTerm::If {
                cond: right_cond,
                then_b: right_then,
                else_b: right_else,
                origin: right_origin,
            },
        ) => {
            left_cond == right_cond && left_then == right_then && left_else == right_else && left_origin == right_origin
        }
        (
            IrTerm::Call {
                ident: left_ident,
                callee: left_callee,
                args: left_args,
                continuation: left_cont,
            },
            IrTerm::Call {
                ident: right_ident,
                callee: right_callee,
                args: right_args,
                continuation: right_cont,
            },
        ) => {
            native_callsite_idents_equal(left_ident, right_ident)
                && left_callee == right_callee
                && left_args == right_args
                && native_conts_equal(left_cont, right_cont)
        }
        (
            IrTerm::TailCall {
                ident: left_ident,
                callee: left_callee,
                args: left_args,
                is_back_edge: left_back_edge,
            },
            IrTerm::TailCall {
                ident: right_ident,
                callee: right_callee,
                args: right_args,
                is_back_edge: right_back_edge,
            },
        ) => {
            native_callsite_idents_equal(left_ident, right_ident)
                && left_callee == right_callee
                && left_args == right_args
                && left_back_edge == right_back_edge
        }
        (
            IrTerm::CallClosure {
                ident: left_ident,
                closure: left_closure,
                args: left_args,
                continuation: left_cont,
            },
            IrTerm::CallClosure {
                ident: right_ident,
                closure: right_closure,
                args: right_args,
                continuation: right_cont,
            },
        ) => {
            native_callsite_idents_equal(left_ident, right_ident)
                && left_closure == right_closure
                && left_args == right_args
                && native_conts_equal(left_cont, right_cont)
        }
        (
            IrTerm::TailCallClosure {
                ident: left_ident,
                closure: left_closure,
                args: left_args,
            },
            IrTerm::TailCallClosure {
                ident: right_ident,
                closure: right_closure,
                args: right_args,
            },
        ) => {
            native_callsite_idents_equal(left_ident, right_ident)
                && left_closure == right_closure
                && left_args == right_args
        }
        (IrTerm::Return(left_var), IrTerm::Return(right_var)) | (IrTerm::Halt(left_var), IrTerm::Halt(right_var)) => {
            left_var == right_var
        }
        (
            IrTerm::ReceiveMatched {
                ident: left_ident,
                clauses: left_clauses,
                dispatch: left_dispatch,
                after: left_after,
                pinned: left_pinned,
                captures: left_captures,
            },
            IrTerm::ReceiveMatched {
                ident: right_ident,
                clauses: right_clauses,
                dispatch: right_dispatch,
                after: right_after,
                pinned: right_pinned,
                captures: right_captures,
            },
        ) => {
            native_callsite_idents_equal(left_ident, right_ident)
                && left_clauses.len() == right_clauses.len()
                && left_clauses
                    .iter()
                    .zip(right_clauses.iter())
                    .all(|(left, right)| native_receive_clauses_equal(left, right))
                && left_dispatch == right_dispatch
                && native_receive_after_equal(left_after.as_ref(), right_after.as_ref())
                && left_pinned == right_pinned
                && left_captures == right_captures
        }
        _ => false,
    }
}

fn native_conts_equal(left: &IrCont, right: &IrCont) -> bool {
    left.fn_id == right.fn_id && left.captured == right.captured
}

fn native_receive_clauses_equal(left: &ReceiveClause, right: &ReceiveClause) -> bool {
    native_callsite_idents_equal(&left.ident, &right.ident)
        && left.bound_names == right.bound_names
        && left.guard == right.guard
        && left.body == right.body
        && left.span == right.span
}

fn native_receive_after_equal(left: Option<&ReceiveAfter>, right: Option<&ReceiveAfter>) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => {
            native_callsite_idents_equal(&left.ident, &right.ident)
                && left.timeout == right.timeout
                && left.body == right.body
                && left.span == right.span
        }
        _ => false,
    }
}

fn native_external_call_edges_equal(left: &ExternalCallEdge, right: &ExternalCallEdge) -> bool {
    native_callsite_ids_equal(&left.callsite, &right.callsite) && left.target == right.target
}

fn native_callsite_ids_equal(left: &IrCallsiteId, right: &IrCallsiteId) -> bool {
    left.caller == right.caller && left.slot == right.slot && native_callsite_idents_equal(&left.ident, &right.ident)
}

fn native_callsite_idents_equal(left: &CallsiteIdent, right: &CallsiteIdent) -> bool {
    left.span() == right.span()
}
