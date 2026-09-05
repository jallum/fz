//! Compiler2's artifact-side program projections.
//!
//! `BackendProgram` is the interpreter-ready handoff for one root: a pulled
//! executable inventory with settled clause-entry dispatch, direct executable
//! references, callable-boundary obligations, and concrete extern wire classes
//! attached to structured function bodies. Native codegen needs one more
//! Compiler2-owned projection above that: `NativeProgram`, a codegen-ready
//! CPS/native handoff that carries only backend-consumption facts and never
//! rebuilds `ModulePlan`, `PlannedProgram`, or `AbiFacts`.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::rc::Rc;

use crate::ast::{BinOp, UnOp};
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardExpr};
use crate::dispatch_matrix::{
    ComparisonValue, DispatchEdge, DispatchNode, EdgeEvidence, GraphNodeId, PinnedValueId, Region, RegionPredicate,
    SubjectId, SubjectSource,
};
use crate::fz_ir::{
    Block as IrBlock, CallsiteId as IrCallsiteId, CallsiteIdent, Cont as IrCont, ExternMarshalSite, ExternTy,
    ExternalCallEdge, FnId, FnIr as IrFn, Module as IrModule, Prim as IrPrim, ReceiveAfter as IrReceiveAfter,
    ReceiveClause as IrReceiveClause, Stmt as IrStmt, Term as IrTerm, Var,
};
use crate::ground_value::GroundValue;
use crate::runtime_type_predicate::CallableShape;
use crate::source::Span;

pub use super::body::ReusableConsCapture;
use super::body::{
    CallSiteId, ControlDestination, ControlDispatch, ControlEntryId, DispatchBindings, LoweredBitField,
    LoweredBitFieldSpec, LoweredBody, LoweredExtern, ReceiveAfter, ReceiveClause, ValueId,
};
use super::identity::{ExecutableKey, FunctionId, ModuleId};
use super::semantic::ExecutableRuntimeDemand;
use super::transport::{
    BoundaryId, CallableConstructionOwner, CallableId, ExecutableSymbol, ShapeId, TransportCarrier, TransportLayout,
    TransportPosition,
};
use super::types::Ty;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallTarget<T> {
    Local(T),
    ProviderBoundary(FunctionId),
}

impl<T> CallTarget<T> {
    pub fn local(&self) -> Option<&T> {
        match self {
            Self::Local(value) => Some(value),
            Self::ProviderBoundary(_) => None,
        }
    }
}

impl<T: Copy> CallTarget<T> {
    pub fn copied_local(&self) -> Option<T> {
        self.local().copied()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BackendConstructionWrapper {
    pub identity: TransportPosition,
    pub callable: CallableId,
    pub captures: Box<[BackendConstructionCapture]>,
    pub call_arity: usize,
    pub return_form: BackendCallableReturn,
    pub members: Box<[BackendConstructionMemberAdapter]>,
    pub(crate) selection: Option<crate::dispatch_matrix::pattern::PatternDispatchPlan<Ty>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BackendCallableReturn {
    Diverges,
    Absent,
    ValueRef,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BackendConstructionMemberAdapter {
    pub boundary: BoundaryId,
    pub surface_inputs: Box<[Ty]>,
    pub surface_arg_shapes: Box<[ShapeId]>,
    pub target: ExecutableKey,
    pub capture_semantic_inputs: Box<[usize]>,
    pub surface_semantic_inputs: Box<[usize]>,
    pub target_inputs: Box<[BackendSemanticInputLayout]>,
    pub target_return: BackendReturnLayout,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BackendSemanticInputLayout {
    pub semantic_index: usize,
    pub layout: BackendValueLayout,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BackendValueLayout {
    pub structural: ShapeId,
    pub carrier: TransportCarrier,
    pub tys: Box<[Ty]>,
    pub reprs: Box<[AbiValueRepr]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BackendReturnLayout {
    pub layout: BackendValueLayout,
    pub diverges: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BackendConstructionCapture {
    pub layout: BackendValueLayout,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaterializedExecutableTransport {
    pub executable: ExecutableSymbol,
    pub position_layouts: Vec<(TransportPosition, TransportLayout)>,
    pub input_positions: Vec<TransportPosition>,
    pub return_position: TransportPosition,
    pub resume_positions: Vec<TransportPosition>,
    pub return_payload_positions: Vec<TransportPosition>,
    pub entry_capture_positions: Vec<TransportPosition>,
    pub call_arg_positions: Vec<TransportPosition>,
    pub value_positions: Vec<TransportPosition>,
}

impl MaterializedExecutableTransport {
    pub fn layout_at(&self, position: &TransportPosition) -> Option<TransportLayout> {
        self.position_layouts
            .iter()
            .find_map(|(candidate, layout)| (candidate == position).then_some(*layout))
    }
}

#[cfg_attr(test, derive(Clone))]
#[derive(Debug, PartialEq)]
pub struct MaterializedExecutable {
    pub entry_dispatch: Option<ExecutableDispatch>,
    pub return_ty: Ty,
    pub runtime_demand: Rc<ExecutableRuntimeDemand>,
    pub transport: MaterializedExecutableTransport,
    pub original_entry_ids: Vec<ControlEntryId>,
    pub value_types: HashMap<ValueId, Ty>,
    pub effects: EffectSummary,
    /// Struct schemas this pruned executable can construct, test, or name in
    /// its type surface, kept as typed compiler identities until root packaging.
    pub(crate) struct_modules: Box<[ModuleId]>,
    pub body: LoweredBody,
    pub call_edges: HashMap<CallSiteId, MaterializedCallEdge>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaterializedCallEdge {
    pub target: CallEdge<ExecutableKey>,
    pub return_ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallEdge<T, F = CallReturnFlow> {
    Direct(DirectCallEdge<T, F>),
    Dispatch(Box<DispatchCallEdge<T, F>>),
    /// A closure-call site whose positioned callee transport has a public
    /// `ValueRef` carrier. Invocation runs through the callee's runtime identity
    /// even when semantic resolution has one exact target; target cardinality
    /// does not redefine the transported physical representation.
    /// Explicit and settled — distinct from a callsite whose summary fact
    /// has not been computed yet (which stays `Ok(None)` at materialization).
    Indirect(F),
}

impl<T, F> CallEdge<T, F> {
    /// Every local callee the edge can reach: the direct target, or all
    /// dispatch arms. Product formulas use this one projection to name their
    /// exact callee dependencies.
    pub fn local_callees(&self) -> Vec<&T> {
        match self {
            Self::Direct(direct) => direct.callee.local().into_iter().collect(),
            Self::Dispatch(dispatch) => dispatch.arms.iter().filter_map(|arm| arm.callee.local()).collect(),
            Self::Indirect(_) => Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DirectCallEdge<T, F = CallReturnFlow> {
    pub callee: CallTarget<T>,
    pub return_flow: F,
    pub extern_marshals: Option<Vec<ExternTy>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DispatchCallEdge<T, F = CallReturnFlow> {
    pub(crate) plan: PatternDispatchPlan<Ty>,
    pub arms: Vec<DispatchCallArm<T, F>>,
    pub miss: DispatchCallMiss,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DispatchCallArm<T, F = CallReturnFlow> {
    pub body_id: u32,
    pub callee: CallTarget<T>,
    pub return_flow: F,
    pub extern_marshals: Option<Vec<ExternTy>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DispatchCallMiss {
    Unreachable,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallReturnFlow {
    NoReturn {
        local_source: Option<TransportPosition>,
    },
    Tail {
        source: TransportPosition,
        payload: TransportPosition,
        caller_return: TransportPosition,
    },
    Continue {
        source: TransportPosition,
        payload: TransportPosition,
        caller_return: TransportPosition,
    },
    Deliver {
        source: TransportPosition,
        resume: TransportPosition,
        entry: ControlEntryId,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BackendReturnFlow {
    NoReturn,
    Tail,
    Continue {
        source: Box<BackendReturnLayout>,
    },
    Deliver {
        source: Box<BackendReturnLayout>,
        entry: ControlEntryId,
    },
}

pub use super::backend_program::BackendProgram;

#[cfg_attr(test, derive(Clone))]
#[derive(Debug)]
pub(crate) struct NativeProgram {
    /// The CPS/native entry body the shared JIT/AOT pipeline should start at.
    pub entry: FnId,
    /// Compiler2-owned CPS/native module handed to shared codegen. This
    /// replaces the old prepared `Module` input for Compiler2-native runs.
    pub module: IrModule,
    /// Every semantic executable in the closed backend program and the
    /// physical CPS/native entry that implements it. Several semantic keys may
    /// share one entry when their closed native graphs are equivalent.
    pub executable_entries: Vec<NativeExecutableEntry>,
    /// Per-body native facts that replace old planner-owned side tables such
    /// as `ModulePlan.effective_returns`, `SpecPlan.vars`, and continuation
    /// classification.
    pub bodies: Vec<NativeBody>,
    /// Closed callable-boundary inventory plus callable identity bodies. This
    /// replaces the old planner-side callable-entry lookup surface.
    pub callable_boundaries: Vec<NativeCallableBoundary>,
}

impl PartialEq for NativeProgram {
    fn eq(&self, other: &Self) -> bool {
        native_programs_equal(self, other)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct NativeExecutableEntry {
    pub key: ExecutableKey,
    pub fn_id: FnId,
}

impl NativeProgram {
    #[cfg(test)]
    pub(crate) fn executable_fn(&self, key: &ExecutableKey) -> Option<FnId> {
        self.executable_entries
            .iter()
            .find(|entry| &entry.key == key)
            .map(|entry| entry.fn_id)
    }

    #[cfg(test)]
    pub(crate) fn native_graph_fn_ids(&self, key: &ExecutableKey) -> HashSet<FnId> {
        let Some(index) = self.executable_entries.iter().position(|entry| &entry.key == key) else {
            return HashSet::new();
        };
        NativeGraphIndex::new(self).graphs[index]
            .bodies
            .values()
            .copied()
            .collect()
    }

    /// Compare the closed native graph owned by two semantic executables.
    ///
    /// The executable body and every clause/continuation it owns are compared
    /// structurally. Only the graph's own `FnId`s, diagnostic names, and
    /// same-span callsite allocation identities are alpha-renamed. Direct
    /// targets, construction words, ABI facts, effects, capture layouts, and
    /// every codegen-relevant value type remain exact comparands.
    #[cfg(test)]
    pub(crate) fn native_cps_graphs_equivalent(&self, left: &ExecutableKey, right: &ExecutableKey) -> bool {
        let Some(left) = self.executable_entries.iter().position(|entry| &entry.key == left) else {
            return false;
        };
        let Some(right) = self.executable_entries.iter().position(|entry| &entry.key == right) else {
            return false;
        };
        NativeGraphIndex::new(self)
            .mapping(left, right, &mut NativeGraphSharingWork::default())
            .is_some()
    }

    pub(crate) fn deduplicate_equivalent_sibling_graphs(&mut self) -> NativeGraphSharingWork {
        let groups = self.sibling_entry_groups();
        if groups.is_empty() {
            return NativeGraphSharingWork::default();
        }
        let mut work = NativeGraphSharingWork::default();
        while self.deduplicate_equivalent_sibling_graphs_once(&groups, &mut work) {}
        work
    }

    fn sibling_entry_groups(&self) -> Vec<Vec<usize>> {
        let mut groups = BTreeMap::<FunctionId, Vec<usize>>::new();
        for (index, entry) in self.executable_entries.iter().enumerate() {
            groups.entry(entry.key.activation.function).or_default().push(index);
        }
        groups.into_values().filter(|group| group.len() > 1).collect()
    }

    fn deduplicate_equivalent_sibling_graphs_once(
        &mut self,
        groups: &[Vec<usize>],
        work: &mut NativeGraphSharingWork,
    ) -> bool {
        let replacements = {
            let graphs = NativeGraphIndex::new(self);
            #[cfg(test)]
            {
                work.passes += 1;
                work.indexed_bodies += self.bodies.len();
                work.owned_graph_bodies += graphs.graphs.iter().map(|graph| graph.bodies.len()).sum::<usize>();
            }
            graphs.replacements(groups, work)
        };
        if replacements.is_empty() {
            return false;
        }

        self.apply_native_graph_replacements(&replacements);
        true
    }

    fn apply_native_graph_replacements(&mut self, replacements: &HashMap<FnId, FnId>) {
        let remap = |fn_id: &mut FnId| {
            if let Some(representative) = replacements.get(fn_id) {
                *fn_id = *representative;
            }
        };
        remap(&mut self.entry);
        for entry in &mut self.executable_entries {
            remap(&mut entry.fn_id);
        }
        for boundary in &mut self.callable_boundaries {
            for member in &mut boundary.members {
                remap(&mut member.target_fn);
            }
        }
        self.bodies.retain(|body| !replacements.contains_key(&body.fn_id));
        for body in &mut self.bodies {
            if let NativeBodyOrigin::Continuation { owner } = &mut body.origin {
                remap(owner);
            }
        }
        self.module
            .fns
            .retain(|function| !replacements.contains_key(&function.id));
        for function in &mut self.module.fns {
            remap_ir_control_fn_ids(function, replacements);
        }
        self.module.fn_idx = self
            .module
            .fns
            .iter()
            .enumerate()
            .map(|(index, function)| (function.id, index))
            .collect();
    }
}

/// Deterministic cost of finding the physical native graphs a program can
/// share. A pass indexes each remaining body once; comparisons then follow the
/// indexed ownership paths rather than rescanning the body inventory.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub(crate) struct NativeGraphSharingWork {
    #[cfg(test)]
    pub passes: usize,
    #[cfg(test)]
    pub indexed_bodies: usize,
    #[cfg(test)]
    pub owned_graph_bodies: usize,
    #[cfg(test)]
    pub graph_comparisons: usize,
    #[cfg(test)]
    pub body_comparisons: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct NativeGraphRole {
    clause: Option<u32>,
    continuations: Vec<usize>,
}

struct NativeOwnedGraph {
    bodies: BTreeMap<NativeGraphRole, FnId>,
    complete: bool,
}

/// One-pass ownership index for structural graph comparison. Clause indices
/// identify entry roots; completed IR control-edge paths identify continuation
/// roles. Lowering order and allocated function ids are not authorities.
struct NativeGraphIndex<'a> {
    program: &'a NativeProgram,
    bodies: HashMap<FnId, &'a NativeBody>,
    graphs: Vec<NativeOwnedGraph>,
}

impl<'a> NativeGraphIndex<'a> {
    fn new(program: &'a NativeProgram) -> Self {
        let mut bodies = HashMap::new();
        let mut clauses = HashMap::<ExecutableKey, BTreeMap<u32, FnId>>::new();
        let mut continuations = HashMap::<FnId, Vec<FnId>>::new();
        for body in &program.bodies {
            assert!(
                bodies.insert(body.fn_id, body).is_none(),
                "native body {:?} must have one ownership record",
                body.fn_id,
            );
            match &body.origin {
                NativeBodyOrigin::Clause { owner, index } => {
                    assert!(
                        clauses
                            .entry(owner.clone())
                            .or_default()
                            .insert(*index, body.fn_id)
                            .is_none(),
                        "native executable {owner:?} must not own duplicate clause index {index}",
                    );
                }
                NativeBodyOrigin::Continuation { owner } => continuations.entry(*owner).or_default().push(body.fn_id),
                NativeBodyOrigin::Executable(_) | NativeBodyOrigin::CallableWrapper { .. } => {}
            }
        }
        let control_edges = program
            .module
            .fns
            .iter()
            .map(|function| (function.id, ir_control_fn_ids(function)))
            .collect::<HashMap<_, _>>();
        let graphs = program
            .executable_entries
            .iter()
            .map(|entry| NativeOwnedGraph::new(entry, &clauses, &continuations, &control_edges))
            .collect();
        Self {
            program,
            bodies,
            graphs,
        }
    }

    fn replacements(&self, groups: &[Vec<usize>], work: &mut NativeGraphSharingWork) -> HashMap<FnId, FnId> {
        let mut replacements = HashMap::new();
        for group in groups {
            let mut compared_roots = HashSet::new();
            for (offset, &left) in group.iter().enumerate() {
                let left_root = self.program.executable_entries[left].fn_id;
                if replacements.contains_key(&left_root) || !compared_roots.insert(left_root) {
                    continue;
                }
                for &right in &group[offset + 1..] {
                    let right_root = self.program.executable_entries[right].fn_id;
                    if right_root == left_root || replacements.contains_key(&right_root) {
                        continue;
                    }
                    if let Some(mapping) = self.mapping(left, right, work) {
                        replacements.extend(mapping);
                    }
                }
            }
        }
        replacements
    }

    fn mapping(&self, left: usize, right: usize, _work: &mut NativeGraphSharingWork) -> Option<HashMap<FnId, FnId>> {
        #[cfg(test)]
        {
            _work.graph_comparisons += 1;
        }
        let (left, right) = (&self.graphs[left], &self.graphs[right]);
        if !left.complete || !right.complete || !left.bodies.keys().eq(right.bodies.keys()) {
            return None;
        }
        let right_to_left = right
            .bodies
            .values()
            .copied()
            .zip(left.bodies.values().copied())
            .collect::<HashMap<_, _>>();
        for (right_fn, left_fn) in right.bodies.values().zip(left.bodies.values()) {
            #[cfg(test)]
            {
                _work.body_comparisons += 1;
            }
            let (left_body, right_body) = (self.bodies[left_fn], self.bodies[right_fn]);
            let left_ir = self.program.module.fn_by_id(*left_fn);
            let mut normalized_right_ir = self.program.module.fn_by_id(*right_fn).clone();
            normalized_right_ir.id = *left_fn;
            normalized_right_ir.name = left_ir.name.clone();
            remap_ir_control_fn_ids(&mut normalized_right_ir, &right_to_left);
            align_ir_callsite_identities(left_ir, &mut normalized_right_ir);
            if !native_body_facts_equal(left_body, right_body, left_ir, &normalized_right_ir)
                || left_ir != &normalized_right_ir
            {
                return None;
            }
        }
        Some(right_to_left)
    }
}

impl NativeOwnedGraph {
    fn new(
        entry: &NativeExecutableEntry,
        clauses: &HashMap<ExecutableKey, BTreeMap<u32, FnId>>,
        continuations: &HashMap<FnId, Vec<FnId>>,
        control_edges: &HashMap<FnId, Vec<FnId>>,
    ) -> Self {
        let mut roots = vec![(
            NativeGraphRole {
                clause: None,
                continuations: Vec::new(),
            },
            entry.fn_id,
        )];
        roots.extend(clauses.get(&entry.key).into_iter().flatten().map(|(&index, &fn_id)| {
            (
                NativeGraphRole {
                    clause: Some(index),
                    continuations: Vec::new(),
                },
                fn_id,
            )
        }));

        let mut owned = HashSet::new();
        let mut ownership_frontier = roots.iter().map(|(_, fn_id)| *fn_id).collect::<Vec<_>>();
        while let Some(fn_id) = ownership_frontier.pop() {
            if owned.insert(fn_id) {
                ownership_frontier.extend(continuations.get(&fn_id).into_iter().flatten().copied());
            }
        }

        let mut bodies = BTreeMap::new();
        let mut reached = HashSet::new();
        let mut frontier = VecDeque::new();
        for (role, fn_id) in roots {
            assert!(
                bodies.insert(role.clone(), fn_id).is_none(),
                "native graph must not publish duplicate ownership role {role:?}",
            );
            assert!(
                reached.insert(fn_id),
                "native graph must not publish body {fn_id:?} under multiple entry roles",
            );
            frontier.push_back((role, fn_id));
        }
        while let Some((role, fn_id)) = frontier.pop_front() {
            for (index, child) in control_edges.get(&fn_id).into_iter().flatten().enumerate() {
                if !owned.contains(child) || !reached.insert(*child) {
                    continue;
                }
                let mut child_role = role.clone();
                child_role.continuations.push(index);
                assert!(
                    bodies.insert(child_role.clone(), *child).is_none(),
                    "native graph must not publish duplicate structural role {child_role:?}",
                );
                frontier.push_back((child_role, *child));
            }
        }
        Self {
            bodies,
            complete: reached.len() == owned.len(),
        }
    }
}

fn ir_control_fn_ids(function: &IrFn) -> Vec<FnId> {
    let mut fn_ids = Vec::new();
    for block in &function.blocks {
        match &block.terminator {
            IrTerm::Call {
                callee, continuation, ..
            } => {
                if let crate::fz_ir::DirectCallTarget::Local(fn_id) = callee {
                    fn_ids.push(*fn_id);
                }
                fn_ids.push(continuation.fn_id);
            }
            IrTerm::TailCall { callee, .. } => {
                if let crate::fz_ir::DirectCallTarget::Local(fn_id) = callee {
                    fn_ids.push(*fn_id);
                }
            }
            IrTerm::CallClosure { continuation, .. } => fn_ids.push(continuation.fn_id),
            IrTerm::ReceiveMatched { clauses, after, .. } => {
                for clause in clauses {
                    if let Some(guard) = clause.guard {
                        fn_ids.push(guard);
                    }
                    fn_ids.push(clause.body);
                }
                if let Some(after) = after {
                    fn_ids.push(after.body);
                }
            }
            IrTerm::Goto(..)
            | IrTerm::If { .. }
            | IrTerm::TailCallClosure { .. }
            | IrTerm::Return(_)
            | IrTerm::ReturnLanes(_)
            | IrTerm::Halt(_) => {}
        }
    }
    fn_ids
}

fn native_body_facts_equal(left: &NativeBody, right: &NativeBody, left_ir: &IrFn, right_ir: &IrFn) -> bool {
    left.entry_abi == right.entry_abi
        && left.param_reprs == right.param_reprs
        && left.return_ty == right.return_ty
        && left.return_reprs == right.return_reprs
        && left.return_tuple_arity == right.return_tuple_arity
        && left.block_param_reprs == right.block_param_reprs
        && native_value_types_equal(left, right, left_ir, right_ir)
        && left.extern_marshals == right.extern_marshals
        && left.effects == right.effects
}

fn native_value_types_equal(left: &NativeBody, right: &NativeBody, left_ir: &IrFn, right_ir: &IrFn) -> bool {
    if left.value_types.len() != right.value_types.len() {
        return false;
    }
    let left_opaque = indirect_callee_only_vars(left_ir);
    let right_opaque = indirect_callee_only_vars(right_ir);
    left.value_types.iter().all(|(var, left_ty)| {
        right.value_types.get(var).is_some_and(|right_ty| {
            left_ty == right_ty
                || (left_opaque.contains(var)
                    && right_opaque.contains(var)
                    && left.block_param_reprs.get(var) == Some(&AbiValueRepr::ValueRef)
                    && right.block_param_reprs.get(var) == Some(&AbiValueRepr::ValueRef))
        })
    })
}

/// A variable used only as the callee word of an indirect closure call has no
/// type-directed codegen decision below the native handoff. Its representation
/// is already fixed by `block_param_reprs`; arguments, captures, and results
/// remain ordinary typed uses and therefore disqualify it.
pub(crate) fn indirect_callee_only_vars(function: &IrFn) -> HashSet<Var> {
    let mut candidates = HashSet::new();
    let mut other_uses = HashSet::new();
    for block in &function.blocks {
        for IrStmt::Let(_, prim) in &block.stmts {
            prim.collect_used_vars(&mut other_uses);
        }
        match &block.terminator {
            IrTerm::CallClosure {
                closure,
                args,
                continuation,
                ..
            } => {
                candidates.insert(*closure);
                other_uses.extend(args.iter().copied());
                other_uses.extend(continuation.captured.iter().copied());
            }
            IrTerm::TailCallClosure { closure, args, .. } => {
                candidates.insert(*closure);
                other_uses.extend(args.iter().copied());
            }
            IrTerm::Goto(_, args) => other_uses.extend(args.iter().copied()),
            IrTerm::If { cond, .. } => {
                other_uses.insert(*cond);
            }
            IrTerm::Call { args, continuation, .. } => {
                other_uses.extend(args.iter().copied());
                other_uses.extend(continuation.captured.iter().copied());
            }
            IrTerm::TailCall { args, .. } => other_uses.extend(args.iter().copied()),
            IrTerm::Return(var) | IrTerm::Halt(var) => {
                other_uses.insert(*var);
            }
            IrTerm::ReturnLanes(vars) => other_uses.extend(vars.iter().copied()),
            IrTerm::ReceiveMatched {
                pinned,
                captures,
                after,
                ..
            } => {
                other_uses.extend(pinned.iter().map(|(_, var)| *var));
                other_uses.extend(captures.iter().copied());
                if let Some(after) = after {
                    other_uses.insert(after.timeout);
                }
            }
        }
    }
    candidates.retain(|var| !other_uses.contains(var));
    candidates
}

/// Visit CPS control edges, never callable construction words carried by
/// `MakeFnRef`, `MakeClosure`, or `ClosureCapture`.
fn visit_ir_control_fn_ids(function: &mut IrFn, mut visit: impl FnMut(&mut FnId)) {
    for block in &mut function.blocks {
        match &mut block.terminator {
            IrTerm::Call {
                callee, continuation, ..
            } => {
                if let crate::fz_ir::DirectCallTarget::Local(fn_id) = callee {
                    visit(fn_id);
                }
                visit(&mut continuation.fn_id);
            }
            IrTerm::TailCall { callee, .. } => {
                if let crate::fz_ir::DirectCallTarget::Local(fn_id) = callee {
                    visit(fn_id);
                }
            }
            IrTerm::CallClosure { continuation, .. } => visit(&mut continuation.fn_id),
            IrTerm::ReceiveMatched { clauses, after, .. } => {
                for clause in clauses {
                    if let Some(guard) = &mut clause.guard {
                        visit(guard);
                    }
                    visit(&mut clause.body);
                }
                if let Some(after) = after {
                    visit(&mut after.body);
                }
            }
            IrTerm::Goto(..)
            | IrTerm::If { .. }
            | IrTerm::TailCallClosure { .. }
            | IrTerm::Return(_)
            | IrTerm::ReturnLanes(_)
            | IrTerm::Halt(_) => {}
        }
    }
}

fn remap_ir_control_fn_ids(function: &mut IrFn, ids: &HashMap<FnId, FnId>) {
    visit_ir_control_fn_ids(function, |fn_id| {
        if let Some(mapped) = ids.get(fn_id) {
            *fn_id = *mapped;
        }
    });
}

fn align_ir_callsite_identities(left: &IrFn, right: &mut IrFn) {
    let align = |left: &CallsiteIdent, right: &mut CallsiteIdent| {
        if left.span() == right.span() {
            *right = left.clone();
        }
    };
    for (left_block, right_block) in left.blocks.iter().zip(&mut right.blocks) {
        for (left_stmt, right_stmt) in left_block.stmts.iter().zip(&mut right_block.stmts) {
            let (IrStmt::Let(_, left_prim), IrStmt::Let(_, right_prim)) = (left_stmt, right_stmt);
            match (left_prim, right_prim) {
                (IrPrim::Extern(left, ..), IrPrim::Extern(right, ..))
                | (IrPrim::MakeFnRef(left, ..), IrPrim::MakeFnRef(right, ..))
                | (IrPrim::MakeClosure(left, ..), IrPrim::MakeClosure(right, ..)) => align(left, right),
                _ => {}
            }
        }
        match (&left_block.terminator, &mut right_block.terminator) {
            (IrTerm::Call { ident: left, .. }, IrTerm::Call { ident: right, .. })
            | (IrTerm::TailCall { ident: left, .. }, IrTerm::TailCall { ident: right, .. })
            | (IrTerm::CallClosure { ident: left, .. }, IrTerm::CallClosure { ident: right, .. })
            | (IrTerm::TailCallClosure { ident: left, .. }, IrTerm::TailCallClosure { ident: right, .. }) => {
                align(left, right);
            }
            (
                IrTerm::ReceiveMatched {
                    ident: left_ident,
                    clauses: left_clauses,
                    after: left_after,
                    ..
                },
                IrTerm::ReceiveMatched {
                    ident: right_ident,
                    clauses: right_clauses,
                    after: right_after,
                    ..
                },
            ) => {
                align(left_ident, right_ident);
                for (left_clause, right_clause) in left_clauses.iter().zip(right_clauses) {
                    align(&left_clause.ident, &mut right_clause.ident);
                }
                if let (Some(left_after), Some(right_after)) = (left_after, right_after) {
                    align(&left_after.ident, &mut right_after.ident);
                }
            }
            _ => {}
        }
    }
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
    Continuation { owner: FnId },
    CallableWrapper { identity: u32 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct NativeCallableBoundaryId(pub u32);

impl NativeCallableBoundaryId {
    pub(crate) fn as_u32(self) -> u32 {
        self.0
    }
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
    pub return_reprs: Vec<AbiValueRepr>,
    pub return_tuple_arity: Option<usize>,
    pub block_param_reprs: HashMap<Var, AbiValueRepr>,
    /// Final per-value types after Compiler2 lowering into CPS/native form.
    pub value_types: HashMap<Var, Ty>,
    /// Concrete extern marshal classes keyed by CPS/native extern site.
    pub extern_marshals: HashMap<ExternMarshalSite, ExternTy>,
    pub effects: EffectSummary,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NativeCallableBoundary {
    pub id: NativeCallableBoundaryId,
    pub identity_fn: FnId,
    /// The callable LAYOUT this boundary mints: function, capture types and
    /// physical capture lanes. Several boundaries can mint one layout -- one
    /// per construction position -- and each stamps its own `identity_fn`.
    pub callable: CallableId,
    /// The CONSTRUCTION this boundary mints, as a runtime test names it: the
    /// function the lattice's closure literal names, plus the projected
    /// capture types the callable closed over. The runtime word a minted value
    /// carries is `identity_fn`, which is this backend's own numbering; a
    /// dispatch that asks WHICH construction a value is asks in the lattice's
    /// terms, and this is the translation (fz-kdt.125, fz-kdt.127). `None`
    /// where the callable names no function, which no finite test can list.
    pub shape: Option<CallableShape>,
    pub wrapper_fn: FnId,
    pub captures: Box<[BackendConstructionCapture]>,
    pub capture_reprs: Box<[AbiValueRepr]>,
    pub call_arity: usize,
    pub return_form: BackendCallableReturn,
    pub task_halt_repr: Option<AbiValueRepr>,
    pub members: Box<[NativeConstructionMember]>,
    pub(crate) selection: Option<crate::dispatch_matrix::pattern::PatternDispatchPlan<Ty>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NativeConstructionMember {
    pub boundary: BoundaryId,
    pub target_fn: FnId,
    pub target: ExecutableKey,
    pub surface_inputs: Box<[Ty]>,
    pub capture_semantic_inputs: Box<[usize]>,
    pub surface_semantic_inputs: Box<[usize]>,
    pub target_inputs: Box<[BackendSemanticInputLayout]>,
    pub target_return: BackendReturnLayout,
}

impl NativeCallableBoundary {
    pub(crate) fn id(&self) -> NativeCallableBoundaryId {
        self.id
    }
}

#[cfg_attr(test, derive(Clone))]
#[derive(Debug, PartialEq)]
pub struct AbiReadyExecutable {
    pub materialized: Rc<MaterializedExecutable>,
    pub param_reprs: Vec<AbiValueRepr>,
    pub semantic_inputs: Box<[BackendSemanticInputLayout]>,
    pub return_layout: BackendReturnLayout,
    pub return_endpoints: Box<[(TransportPosition, BackendReturnLayout)]>,
    pub transport: MaterializedExecutableTransport,
    pub value_layouts: HashMap<ValueId, BackendValueLayout>,
    pub effects: EffectSummary,
    pub call_edges: HashMap<CallSiteId, AbiReadyCallEdge>,
    pub callable_owners: Box<[PositionedCallableConstructionOwner]>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct PositionedCallableConstructionOwner {
    pub position: TransportPosition,
    pub owner: Rc<CallableConstructionOwner>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbiReadyCallEdge {
    pub target: CallEdge<ExecutableKey>,
    pub return_ty: Ty,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BackendExecutable {
    pub key: ExecutableKey,
    pub abi: Rc<AbiReadyExecutable>,
    pub body: BackendBody,
    pub construction_wrappers: Box<[Rc<BackendConstructionWrapper>]>,
    pub(crate) atom_names: Box<[Rc<String>]>,
    pub(crate) boxed_apply_requirements: Box<[super::backend_program::boxed_contract::BoxedApplyRequirement]>,
}

#[cfg(test)]
impl BackendExecutable {
    pub(crate) fn for_test(key: ExecutableKey, return_ty: Ty, nothing: ShapeId) -> Self {
        let symbol = ExecutableSymbol {
            activation: super::transport::ActivationSymbol {
                function: key.activation.function,
                arrow: key.activation.arrow,
                input: Box::default(),
            },
            need: key.need,
        };
        let transport = MaterializedExecutableTransport {
            executable: symbol.clone(),
            position_layouts: Vec::new(),
            input_positions: Vec::new(),
            return_position: TransportPosition::ExecutableReturn { executable: symbol },
            resume_positions: Vec::new(),
            return_payload_positions: Vec::new(),
            entry_capture_positions: Vec::new(),
            call_arg_positions: Vec::new(),
            value_positions: Vec::new(),
        };
        let materialized = Rc::new(MaterializedExecutable {
            entry_dispatch: None,
            return_ty,
            runtime_demand: Rc::default(),
            transport: transport.clone(),
            original_entry_ids: Vec::new(),
            value_types: HashMap::new(),
            effects: EffectSummary::default(),
            struct_modules: Box::default(),
            body: LoweredBody::Clauses {
                clauses: Vec::new(),
                entries: Vec::new(),
                generated: Vec::new(),
            },
            call_edges: HashMap::new(),
        });
        let abi = Rc::new(AbiReadyExecutable {
            materialized,
            param_reprs: Vec::new(),
            semantic_inputs: Box::default(),
            return_layout: BackendReturnLayout {
                layout: BackendValueLayout {
                    structural: nothing,
                    carrier: TransportCarrier::Absent,
                    tys: Box::default(),
                    reprs: Box::default(),
                },
                diverges: false,
            },
            return_endpoints: Box::default(),
            transport,
            value_layouts: HashMap::new(),
            effects: EffectSummary::default(),
            call_edges: HashMap::new(),
            callable_owners: Box::default(),
        });
        Self {
            key,
            abi,
            body: BackendBody::Clauses {
                clauses: Vec::new(),
                entries: Vec::new(),
                generated: Vec::new(),
            },
            construction_wrappers: Box::default(),
            atom_names: Box::default(),
            boxed_apply_requirements: Box::default(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum BackendBody {
    Extern {
        signature: LoweredExtern,
    },
    Clauses {
        clauses: Vec<BackendClause>,
        entries: Vec<BackendEntry>,
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

    pub(crate) fn clause_ids(&self) -> &[u32] {
        &self.clause_ids
    }

    pub(crate) fn clause_index(&self, body_id: u32) -> Option<usize> {
        self.clause_ids.iter().position(|candidate| *candidate == body_id)
    }

    pub(crate) fn required_input_ordinals(&self) -> HashSet<usize> {
        required_dispatch_input_ordinals(&self.plan)
    }
}

pub(crate) fn required_dispatch_input_ordinals(plan: &PatternDispatchPlan<Ty>) -> HashSet<usize> {
    let mut required = HashSet::new();
    let mut visited = HashSet::new();
    collect_dispatch_node_inputs(plan, plan.graph.root, &mut visited, &mut required);
    required
}

fn collect_dispatch_node_inputs(
    plan: &PatternDispatchPlan<Ty>,
    node_id: GraphNodeId,
    visited: &mut HashSet<GraphNodeId>,
    out: &mut HashSet<usize>,
) {
    if !visited.insert(node_id) {
        return;
    }
    let Some(node) = plan.graph.node(node_id) else {
        return;
    };
    match node {
        DispatchNode::Fail | DispatchNode::Outcome { .. } => {}
        DispatchNode::Test {
            predicate,
            on_match,
            on_miss,
        } => {
            collect_region_predicate_inputs(plan, predicate, out);
            collect_dispatch_edge_inputs(plan, on_match, out);
            collect_dispatch_edge_inputs(plan, on_miss, out);
            collect_dispatch_node_inputs(plan, on_match.target, visited, out);
            collect_dispatch_node_inputs(plan, on_miss.target, visited, out);
        }
    }
}

fn collect_dispatch_edge_inputs(plan: &PatternDispatchPlan<Ty>, edge: &DispatchEdge<Ty>, out: &mut HashSet<usize>) {
    collect_edge_evidence_inputs(plan, &edge.evidence, out);
}

fn collect_edge_evidence_inputs(plan: &PatternDispatchPlan<Ty>, evidence: &EdgeEvidence<Ty>, out: &mut HashSet<usize>) {
    for proof in &evidence.proofs {
        collect_region_predicate_inputs(plan, &proof.predicate, out);
    }
    for projection in &evidence.projections {
        collect_subject_inputs(plan, projection.source, out);
    }
}

fn collect_region_predicate_inputs(
    plan: &PatternDispatchPlan<Ty>,
    predicate: &RegionPredicate<Ty>,
    out: &mut HashSet<usize>,
) {
    collect_subject_inputs(plan, predicate.subject, out);
    match &predicate.region {
        Region::Equal(ComparisonValue::Pinned(pinned)) => collect_pinned_input(plan, *pinned, out),
        Region::Guard(guard_id) => {
            if let Some(guard) = plan.guards.get(guard_id.0 as usize) {
                collect_guard_expr_inputs(plan, guard, out);
            }
        }
        Region::Type(_)
        | Region::Equal(ComparisonValue::Const(_))
        | Region::TupleArity(_)
        | Region::List(_)
        | Region::MapKind
        | Region::MapKeyPresent { .. }
        | Region::Bitstring(_) => {}
    }
}

fn collect_guard_expr_inputs(plan: &PatternDispatchPlan<Ty>, expr: &PatternGuardExpr<Ty>, out: &mut HashSet<usize>) {
    match expr {
        PatternGuardExpr::Const(_) => {}
        PatternGuardExpr::Subject(subject) => collect_subject_inputs(plan, *subject, out),
        PatternGuardExpr::Pinned(pinned) => collect_pinned_input(plan, *pinned, out),
        PatternGuardExpr::Unary { expr, .. } => collect_guard_expr_inputs(plan, expr, out),
        PatternGuardExpr::Binary { lhs, rhs, .. } => {
            collect_guard_expr_inputs(plan, lhs, out);
            collect_guard_expr_inputs(plan, rhs, out);
        }
        PatternGuardExpr::Dispatch { inputs, dispatch } => {
            for input in inputs {
                collect_guard_expr_inputs(plan, input, out);
            }
            for body in &dispatch.bodies {
                collect_guard_expr_inputs(&dispatch.plan, body, out);
            }
            collect_dispatch_node_inputs(&dispatch.plan, dispatch.plan.graph.root, &mut HashSet::new(), out);
        }
    }
}

fn collect_subject_inputs(plan: &PatternDispatchPlan<Ty>, subject: SubjectId, out: &mut HashSet<usize>) {
    let Some(subject_data) = plan.matrix.subjects.get(subject.0 as usize) else {
        return;
    };
    match &subject_data.source {
        SubjectSource::Input { ordinal } => {
            out.insert(*ordinal as usize);
        }
        SubjectSource::Projection(projection) => collect_subject_inputs(plan, projection.source, out),
    }
}

fn collect_pinned_input(plan: &PatternDispatchPlan<Ty>, pinned: PinnedValueId, out: &mut HashSet<usize>) {
    if let Some(input) = plan.pinned.get(pinned.0 as usize).and_then(|pinned| pinned.input) {
        out.insert(input as usize);
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BackendClause {
    pub span: Span,
    pub params: Vec<ValueId>,
    pub projections: Vec<BackendStep>,
    pub entry: ControlEntryId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BackendEntry {
    pub span: Span,
    pub origin: BackendEntryOrigin,
    pub params: Vec<ValueId>,
    pub captures: Vec<BackendEntryCapture>,
    pub reusable_cons_captures: Vec<ReusableConsCapture>,
    pub steps: Vec<BackendStep>,
    pub tail: BackendTail,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BackendEntryCapture {
    pub value: ValueId,
    pub layout: BackendValueLayout,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BackendReceive {
    pub bindings: DispatchBindings,
    pub clauses: Vec<ReceiveClause>,
    pub after: Option<ReceiveAfter>,
    pub dest: ControlDestination,
    pub(crate) dispatch: PatternDispatchPlan<Ty>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BackendEntryOrigin {
    Clause,
    Branch,
    ReceiveOutcome,
    DeliveredResume {
        value: ValueId,
        layout: BackendReturnLayout,
    },
}

impl BackendEntryOrigin {
    pub fn input_value(&self) -> Option<ValueId> {
        match self {
            Self::Clause | Self::Branch | Self::ReceiveOutcome => None,
            Self::DeliveredResume { value, .. } => Some(*value),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BackendCallArg {
    pub value: ValueId,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BackendTail {
    Value {
        value: ValueId,
        dest: ControlDestination,
    },
    DirectCall {
        value: ValueId,
        callsite: CallSiteId,
        target: CallEdge<ExecutableKey, BackendReturnFlow>,
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
        return_flow: Option<BackendReturnFlow>,
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

#[derive(Debug, Clone, PartialEq)]
pub enum BackendStep {
    Omitted {
        value: ValueId,
    },
    Const {
        value: ValueId,
        literal: GroundValue,
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
    Map {
        value: ValueId,
        entries: Vec<(ValueId, ValueId)>,
    },
    MapUpdate {
        value: ValueId,
        base: ValueId,
        entries: Vec<(ValueId, ValueId)>,
    },
    Struct {
        value: ValueId,
        module_name: String,
        fields: Vec<(String, ValueId)>,
    },
    Bitstring {
        value: ValueId,
        fields: Vec<LoweredBitField>,
    },
    FunctionRef {
        value: ValueId,
        function: FunctionId,
        construction: Option<TransportPosition>,
    },
    Lambda {
        value: ValueId,
        function: FunctionId,
        captures: Vec<ValueId>,
        construction: Option<TransportPosition>,
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
    FieldAccess {
        value: ValueId,
        base: ValueId,
        field: String,
    },
    AssertLiteral {
        source: ValueId,
        literal: GroundValue,
    },
    AssertStruct {
        source: ValueId,
        module_name: String,
    },
    RequireMapValue {
        value: ValueId,
        source: ValueId,
        key: GroundValue,
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
    BitstringInit {
        reader: ValueId,
        source: ValueId,
    },
    BitstringRead {
        ok: ValueId,
        value: ValueId,
        next_reader: ValueId,
        reader: ValueId,
        spec: LoweredBitFieldSpec,
        is_last: bool,
    },
    AssertBitstringDone {
        reader: ValueId,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AbiValueRepr {
    ValueRef,
    RawInt,
    RawF64,
    RawAtom,
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

pub(crate) fn native_programs_equal(left: &NativeProgram, right: &NativeProgram) -> bool {
    left.entry == right.entry
        && left.executable_entries == right.executable_entries
        && left.bodies == right.bodies
        && left.callable_boundaries == right.callable_boundaries
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
        && left.struct_schemas == right.struct_schemas
        && left.external_call_edges().len() == right.external_call_edges().len()
        && left
            .external_call_edges()
            .iter()
            .zip(right.external_call_edges().iter())
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
        (IrTerm::ReturnLanes(left_lanes), IrTerm::ReturnLanes(right_lanes)) => left_lanes == right_lanes,
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

fn native_receive_clauses_equal(left: &IrReceiveClause, right: &IrReceiveClause) -> bool {
    native_callsite_idents_equal(&left.ident, &right.ident)
        && left.bound_names == right.bound_names
        && left.guard == right.guard
        && left.body == right.body
        && left.span == right.span
}

fn native_receive_after_equal(left: Option<&IrReceiveAfter>, right: Option<&IrReceiveAfter>) -> bool {
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
