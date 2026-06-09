//! Type inference and specialization over CPS IR
//! (`.agent/docs/type-specialization.md`).
//!
//! The engine computes type facts for reachable function activations. A closure
//! is modeled as a function whose first parameters are its captures, bound at
//! creation to known-typed values, so applying a closure activates its body
//! function with the captures prepended as leading arguments.
//!
//! ## Shape
//!
//! Specialization is a **monotone worklist fixpoint** over the CPS-lowered
//! `Module`. Each reachable call contract gets an activation cell keyed by its
//! `FnId` plus canonical input tuple. `FnId` remains body/callable identity;
//! activations are inference instances. Each activation's return ascends a
//! finite-height refinement lattice (via `refine_widen`), so the fixpoint
//! terminates.
//!
//! The CPS lowering is what makes this clean: recursion, continuations, and
//! closure application are all *separate* `FnIr`s, reached through call-shape
//! terminators (`Call`/`TailCall`/`CallClosure`). So a function's body walk
//! only ever touches its own blocks (a finite intra-fn graph) and makes `call`
//! requests at its edges — every inter-fn edge, including every loop back-edge,
//! flows through the activation table, never through the walk. The recursion
//! fixpoint lives entirely in the worklist.
//!
//! ## Unknown is not `none`
//!
//! The fixpoint distinguishes three non-values (see [`Info`]). The *type* `none`
//! is ⊥ of the value lattice — the empty, uninhabited set ("returns nothing,
//! ever"); it is a fact. [`Info::Pending`] is a worklist dependency that has not
//! produced its first fact yet. [`Info::Unknown`] is a live value the engine
//! cannot prove. [`Info::NoReturn`] is the control-flow join identity for paths
//! that do not produce a value (`Halt`, proved-dead matcher arms). Projecting
//! `Unknown` is `Unknown` (we still know nothing), whereas projecting
//! `Known(none)` is `Known(none)` (a field of an uninhabited value is itself
//! uninhabited). Conflating them lets a not-yet-computed continuation argument
//! project to `any` and poison the fixpoint forever.
//! If a public, type-returning edge still has `Pending` or `Unknown` after the
//! fixpoint, that edge may erase it to `any`; the solver itself must never use
//! `any` as the placeholder for "not proven yet."
//!
//! API entry points return boundary data and a coarse completion status.
//! Activation ids are the production handoff identity: they name one solved
//! activation within an outcome without exposing the private proof lattice.
//! Activation facts, activation-edge callsites, diagnostics, and dead matcher
//! arms are emitted through telemetry so tests and operators observe the same
//! production surface.
use crate::frontend::protocols::{impl_target_type, struct_impl_target_type};
use crate::fz_ir::{
    BinOp, BlockId, CallsiteId, Const, DeadBranch, EmitSlot, ExternArg, ExternId, FnId, Module, Prim, Stmt, Term, UnOp,
    Var,
};
use crate::metadata;
use crate::specs::{SchemeInstantiation, SpecApplicationOutcome, apply_spec_set, instantiate_match};
use crate::telemetry::{Telemetry, Value};
use crate::types::{ClosureTarget, ClosureTypes, MapKey, Nominals, RenderTypes, Ty, Types};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::mem::replace;

type Env = HashMap<Var, Info>;
type PredicateFacts = HashMap<Var, PredicateFact>;

/// Branch-selection proof carried alongside a value type.
///
/// This is not the public type of the value, and it is not a second type
/// lattice. It is a witness in the existing type model that the matcher may use
/// while walking lowered tests and guards. Proof is erased by ordinary type
/// joins unless both sides prove the same fact.
#[derive(Clone, PartialEq, Eq, Hash)]
enum ValueProof {
    /// No proof has been established for this value/field.
    Unproven,
    Exact(Ty),
    /// Field-wise proof. A tuple may have some proven fields and some
    /// `Unproven` fields; it is not a full tuple-literal proof unless every
    /// field has proof.
    TupleFields(Vec<ValueProof>),
    /// Key-wise proof for maps. `complete` means the constructed map had only
    /// these static keys, so an absent key can prove a matcher miss.
    MapFields {
        fields: BTreeMap<MapKey, ValueProof>,
        complete: bool,
    },
    /// Field-wise proof for schema-backed structs. The visible type remains the
    /// existing opaque impl-target type; fields are projected by schema name.
    StructFields {
        module: String,
        fields: BTreeMap<String, ValueProof>,
    },
    /// Private matcher-map sentinel state. This is control proof only: it is
    /// not a public type, and `proof_ty` never turns it into one.
    MatcherMapMiss,
    MatcherMapHit(Box<ValueProof>),
}

impl ValueProof {
    fn join(&self, other: &Self) -> Self {
        if self == other { self.clone() } else { Self::Unproven }
    }

    fn tuple_field(&self, index: usize) -> Self {
        match self {
            Self::TupleFields(fields) => fields.get(index).cloned().unwrap_or(Self::Unproven),
            _ => Self::Unproven,
        }
    }

    fn map_field(&self, key: &MapKey) -> MapFieldProof {
        match self {
            Self::MapFields { fields, complete } => {
                if let Some(field) = fields.get(key) {
                    MapFieldProof::Hit(field.clone())
                } else if *complete {
                    MapFieldProof::Miss
                } else {
                    MapFieldProof::Unknown
                }
            }
            _ => MapFieldProof::Unknown,
        }
    }

    fn struct_field(&self, field: &str) -> Self {
        match self {
            Self::StructFields { fields, .. } => fields.get(field).cloned().unwrap_or(Self::Unproven),
            _ => Self::Unproven,
        }
    }
}

enum MapFieldProof {
    Hit(ValueProof),
    Miss,
    Unknown,
}

/// A known value in the inference cell: the visible type plus proof usable by
/// matcher guards. `ty` is what flows out of inference; `proof` is temporary
/// branch-selection support.
#[derive(Clone)]
struct ValueFact {
    ty: Ty,
    proof: ValueProof,
}

impl ValueFact {
    fn new(ty: Ty) -> Self {
        Self {
            ty,
            proof: ValueProof::Unproven,
        }
    }

    fn with_proof(ty: Ty, proof: ValueProof) -> Self {
        Self { ty, proof }
    }

    fn widen<T: Types<Ty = Ty>>(&self, t: &mut T, other: &Self) -> Self {
        Self {
            ty: t.refine_widen(&self.ty, &other.ty),
            proof: self.proof.join(&other.proof),
        }
    }

    fn equiv<T: Types<Ty = Ty>>(&self, t: &T, other: &Self) -> bool {
        t.is_equivalent(&self.ty, &other.ty) && self.proof == other.proof
    }

    fn map_ty(self, f: impl FnOnce(Ty) -> Ty) -> Self {
        Self::new(f(self.ty))
    }

    fn tuple_field<T: Types<Ty = Ty>>(self, t: &mut T, index: usize) -> Self {
        let ty = t.tuple_field_type(&self.ty, index);
        let proof = self.proof.tuple_field(index);
        Self { ty, proof }
    }
}

/// A cell in the inference fixpoint.
///
/// `Pending` is a not-yet-produced dependency value, `Unknown` is a live value
/// the engine cannot prove, and `NoReturn` is a path that contributes no value.
/// All three are distinct from the *type* `none` (the empty, uninhabited set).
/// Projecting `Unknown` yields `Unknown`; projecting `Known(t)` yields
/// `Known(proj t)`.
#[derive(Clone)]
enum Info {
    Pending,
    Unknown,
    NoReturn,
    Known(ValueFact),
}

impl Info {
    fn known(ty: Ty) -> Self {
        Self::Known(ValueFact::new(ty))
    }

    fn known_with_proof(ty: Ty, proof: ValueProof) -> Self {
        Self::Known(ValueFact::with_proof(ty, proof))
    }

    /// Join two inference cells. `Pending` is the not-yet-initialized return
    /// estimate, `NoReturn` contributes no value, `Unknown` is live uncertainty,
    /// and two `Known`s join through the refinement-lattice widen.
    fn join<T: Types<Ty = Ty>>(&self, t: &mut T, other: &Info) -> Info {
        match (self, other) {
            (Info::Pending, x) | (x, Info::Pending) => x.clone(),
            (Info::Unknown, _) | (_, Info::Unknown) => Info::Unknown,
            (Info::NoReturn, x) | (x, Info::NoReturn) => x.clone(),
            (Info::Known(a), Info::Known(b)) => Info::Known(a.widen(t, b)),
        }
    }

    fn equiv<T: Types<Ty = Ty>>(&self, t: &T, other: &Info) -> bool {
        match (self, other) {
            (Info::Pending, Info::Pending) => true,
            (Info::Unknown, Info::Unknown) => true,
            (Info::NoReturn, Info::NoReturn) => true,
            (Info::Known(a), Info::Known(b)) => a.equiv(t, b),
            _ => false,
        }
    }

    /// Map a known type through `f`; `Unknown` is preserved. The shape of
    /// projection: we cannot project what we do not yet know.
    fn map_known(self, f: impl FnOnce(ValueFact) -> ValueFact) -> Info {
        match self {
            Info::Pending => Info::Pending,
            Info::Unknown => Info::Unknown,
            Info::NoReturn => Info::NoReturn,
            Info::Known(value) => Info::Known(f(value)),
        }
    }
}

/// The visible types of an activation's stored inputs. Stored inputs are
/// always `Known` (an activation cannot form from an unresolved slot), so this
/// yields the full arity vector — the public fact and telemetry read the
/// activation's joined inputs, not the dispatch-only projection key.
fn info_tys(inputs: &[Info]) -> Vec<Ty> {
    inputs
        .iter()
        .filter_map(|info| match info {
            Info::Known(value) => Some(value.ty.clone()),
            _ => None,
        })
        .collect()
}

fn unresolved_inputs(inputs: &[Info]) -> Info {
    if inputs.iter().any(|input| matches!(input, Info::Unknown)) {
        Info::Unknown
    } else if inputs.iter().any(|input| matches!(input, Info::NoReturn)) {
        Info::NoReturn
    } else {
        Info::Pending
    }
}

fn non_known(info: Info) -> Info {
    match info {
        Info::Pending => Info::Pending,
        Info::Unknown => Info::Unknown,
        Info::NoReturn => Info::NoReturn,
        Info::Known(_) => unreachable!("non_known called with Known"),
    }
}

fn non_known_pair(a: Info, b: Info) -> Info {
    match (a, b) {
        (Info::Unknown, _) | (_, Info::Unknown) => Info::Unknown,
        (Info::NoReturn, _) | (_, Info::NoReturn) => Info::NoReturn,
        (Info::Pending, _) | (_, Info::Pending) => Info::Pending,
        (Info::Known(_), Info::Known(_)) => unreachable!("non_known_pair called with two Known"),
    }
}

#[derive(Clone)]
enum PredicateFact {
    Eq(Var, Var),
    Neq(Var, Var),
    IsEmptyList(Var),
    IsListCons(Var),
    IsMatcherMapMiss(Var),
    TypeTest(Var, Ty),
}

/// One monomorphic activation of a function body, identified by its `FnId`
/// plus a per-slot **identity class**: dispatch-subject slots
/// (`FnIr::dispatch_subject_slots`) keep their exact value, while non-dispatch
/// slots are coarsened to their `convergence_class`.
///
/// `FnId` remains the callable/body identity. Two calls of the same recursive
/// fn that agree on every dispatch subject and every non-dispatch *family*
/// share one activation even when their non-dispatch slots differ within that
/// family (e.g. `[]` and `nonempty_list(int)` — both the list class): those
/// slots cannot change which clause runs, so they fold into the activation's
/// joined `inputs` instead of forking a fresh instance. A dispatch subject
/// (`int` vs `:ok`) or a cross-family non-dispatch difference (`int` vs
/// `{:cont, int}`) still keeps activations apart. The class vector is built by
/// `Solver::make_key`, which alone knows the per-fn mask.
#[derive(Clone, PartialEq, Eq, Hash)]
struct ActivationKey {
    fn_id: FnId,
    class_inputs: Vec<ValueKey>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct ValueKey {
    ty: Ty,
    proof: ValueProof,
}

impl ValueKey {
    fn from_fact<T: Types<Ty = Ty>>(t: &mut T, value: &ValueFact) -> Self {
        Self {
            ty: t.widen_for_recursive_spec_key(&value.ty),
            proof: value.proof.clone(),
        }
    }

    fn into_info(self) -> Info {
        Info::Known(ValueFact::with_proof(self.ty, self.proof))
    }
}

/// One function activation's current return estimate.
struct Activation {
    inputs: Vec<Info>,
    ret: Info,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct ActivationEdge {
    caller: ActivationKey,
    callee: ActivationKey,
    callsite: CallsiteId,
}

/// The callable value at a call site before it has been resolved to activation
/// requests. Direct calls include protocol stubs; indirect callable values may
/// be thin function refs or env-carrying closures.
enum CallTarget<'a> {
    Direct(FnId),
    Closure { value: Var, env: &'a Env },
}

/// One activation request selected for a call site. Applying the request means
/// activating `fn_id` with the full inference input vector. For closures that
/// vector is `captures ++ args`; the closure's public callable arity is still
/// only its explicit args.
struct ActivationRequest {
    fn_id: FnId,
    inputs: Vec<Info>,
}

/// The set of activations a call target may request at this call site. Today all
/// resolved call targets are singleton; keeping the set explicit makes union
/// closure targets and overloaded callable specs a data-model extension instead
/// of another call path.
struct ActivationRequestSet {
    requests: Vec<ActivationRequest>,
}

impl ActivationRequestSet {
    fn singleton(fn_id: FnId, inputs: Vec<Info>) -> Self {
        Self {
            requests: vec![ActivationRequest { fn_id, inputs }],
        }
    }
}

fn binop_symbol(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::Eq => "==",
        BinOp::Neq => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::And => "and",
        BinOp::Or => "or",
    }
}

#[derive(Clone)]
struct TypeInferDiagnostic {
    fn_id: FnId,
    block_id: BlockId,
    stmt_index: usize,
    kind: TypeInferDiagnosticKind,
}

#[derive(Clone)]
enum TypeInferDiagnosticKind {
    InvalidOperator { op: BinOp, left: Ty, right: Ty },
}

impl TypeInferDiagnostic {
    fn emit<T: Types<Ty = Ty> + RenderTypes>(&self, t: &mut T, module: &Module, tel: &dyn Telemetry) {
        match &self.kind {
            TypeInferDiagnosticKind::InvalidOperator { op, left, right } => {
                let fn_name = module.fn_by_id(self.fn_id).name.clone();
                tel.event(
                    &["fz", "type_infer", "diagnostic"],
                    metadata! {
                        code: "type/invalid-operator",
                        fn_name: fn_name,
                        block: self.block_id.0 as u64,
                        stmt: self.stmt_index as u64,
                        op: binop_symbol(*op),
                        left: t.display_for_diag(left),
                        right: t.display_for_diag(right),
                    },
                );
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct DeadArmFact {
    activation: ActivationKey,
    fn_id: FnId,
    block_id: BlockId,
    branch: DeadBranch,
}

impl DeadArmFact {
    fn emit(
        &self,
        activation_ids: &HashMap<ActivationKey, TypeInferActivationId>,
        module: &Module,
        tel: &dyn Telemetry,
    ) {
        let fn_name = module.fn_by_id(self.fn_id).name.clone();
        let branch = match self.branch {
            DeadBranch::Then => "then",
            DeadBranch::Else => "else",
        };
        tel.event(
            &["fz", "type_infer", "dead_arm"],
            metadata! {
                activation_id: activation_ids
                    .get(&self.activation)
                    .expect("dead-arm activation id")
                    .0,
                fn_name: fn_name,
                block: self.block_id.0 as u64,
                branch: branch,
            },
        );
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TypeInferStatus {
    Complete,
    Unresolved,
    Invalid,
}

#[derive(Clone, Debug)]
pub(crate) struct TypeInferOutcome {
    pub(crate) status: TypeInferStatus,
    pub(crate) activations: Vec<TypeInferActivationFact>,
    pub(crate) edges: Vec<TypeInferActivationEdgeFact>,
    pub(crate) dead_arms: Vec<TypeInferDeadArmFact>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct TypeInferActivationId(pub(crate) u64);

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TypeInferCallsiteFact {
    pub(crate) callsite: CallsiteId,
    pub(crate) span_start: u64,
    pub(crate) span_end: u64,
}

#[derive(Clone, Debug)]
pub(crate) struct TypeInferActivationFact {
    pub(crate) activation_id: TypeInferActivationId,
    pub(crate) fn_id: FnId,
    pub(crate) input_tys: Vec<Ty>,
    pub(crate) return_state: TypeInferReturnState,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TypeInferActivationEdgeFact {
    pub(crate) caller_activation_id: TypeInferActivationId,
    pub(crate) caller_fn_id: FnId,
    pub(crate) caller_input_tys: Vec<Ty>,
    pub(crate) callee_activation_id: TypeInferActivationId,
    pub(crate) callee_fn_id: FnId,
    pub(crate) callee_input_tys: Vec<Ty>,
    pub(crate) callsite: TypeInferCallsiteFact,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TypeInferDeadArmFact {
    pub(crate) activation_id: TypeInferActivationId,
    pub(crate) fn_id: FnId,
    pub(crate) block_id: BlockId,
    pub(crate) branch: DeadBranch,
}

/// Boundary return state for a reached activation.
///
/// This is a production data-transfer shape, not the solver lattice. The
/// private [`Info`] cell remains the only place that owns refinement behavior.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TypeInferReturnState {
    Pending,
    Unknown,
    NoReturn,
    Known(Ty),
}

impl TypeInferReturnState {
    fn from_info(info: &Info) -> Self {
        match info {
            Info::Pending => Self::Pending,
            Info::Unknown => Self::Unknown,
            Info::NoReturn => Self::NoReturn,
            Info::Known(value) => Self::Known(value.ty.clone()),
        }
    }
}

fn info_state(info: &Info) -> &'static str {
    match info {
        Info::Pending => "pending",
        Info::Unknown => "unknown",
        Info::NoReturn => "no_return",
        Info::Known(_) => "known",
    }
}

fn emit_slot_name(slot: EmitSlot) -> &'static str {
    match slot {
        EmitSlot::Direct => "direct",
        EmitSlot::Cont => "cont",
        EmitSlot::ClosureCall => "closure_call",
        EmitSlot::CallableBoundary => "callable_boundary",
    }
}

fn dead_branch_name(branch: DeadBranch) -> &'static str {
    match branch {
        DeadBranch::Then => "then",
        DeadBranch::Else => "else",
    }
}

fn render_info<T: Types<Ty = Ty> + RenderTypes>(t: &mut T, info: &Info) -> String {
    match info {
        Info::Known(value) => t.display_for_diag(&value.ty),
        Info::Pending | Info::Unknown | Info::NoReturn => String::new(),
    }
}

/// The monotone worklist solver. Drives every reachable `(fn, inputs)` to a
/// joint fixpoint of input- and return-type estimates.
struct Solver<'m> {
    module: &'m Module,
    activations: HashMap<ActivationKey, Activation>,
    /// `callee activation -> caller activations whose return estimate read
    /// callee's ret`. When a callee's ret ascends, its callers are re-enqueued.
    deps: HashMap<ActivationKey, HashSet<ActivationKey>>,
    edges: HashSet<ActivationEdge>,
    queue: VecDeque<ActivationKey>,
    queued: HashSet<ActivationKey>,
    diagnostics: Vec<TypeInferDiagnostic>,
    diagnostic_sites: HashSet<(FnId, BlockId, usize)>,
    dead_arms: Vec<DeadArmFact>,
    dead_arm_sites: HashSet<DeadArmFact>,
    /// Per-`FnId` dispatch-subject mask (`true` = the slot drives clause/branch
    /// selection and must stay precise). Computed once from the module body;
    /// `make_key` keeps masked slots in the activation identity and folds the
    /// rest into a joined `Activation.inputs`.
    dispatch_masks: HashMap<FnId, Vec<bool>>,
    /// Fns that participate in recursion. Non-dispatch slot convergence applies
    /// only to these: the accumulator balloon is a recursive fixpoint artifact,
    /// whereas a non-recursive fn's distinct call sites are genuine per-callsite
    /// polymorphism that must keep separate activations (and returns).
    recursive_fns: HashSet<FnId>,
}

impl<'m> Solver<'m> {
    fn new(module: &'m Module) -> Self {
        let dispatch_masks = module.fns.iter().map(|f| (f.id, f.dispatch_subject_slots())).collect();
        let recursive_fns = module.recursive_fns();
        Self {
            module,
            activations: HashMap::new(),
            deps: HashMap::new(),
            edges: HashSet::new(),
            queue: VecDeque::new(),
            queued: HashSet::new(),
            diagnostics: Vec::new(),
            diagnostic_sites: HashSet::new(),
            dead_arms: Vec::new(),
            dead_arm_sites: HashSet::new(),
            dispatch_masks,
            recursive_fns,
        }
    }

    /// Whether entry-param `slot` of `fn_id` must stay precise in the
    /// activation identity. Always precise for non-recursive fns (their call
    /// sites are genuine per-callsite polymorphism). For recursive fns, precise
    /// exactly on the dispatch-subject slots; the complement converges. Unknown
    /// fns and out-of-range slots default to precise, so convergence is a
    /// strict opt-in earned by both recursion and a proven mask.
    fn is_dispatch_slot(&self, fn_id: FnId, slot: usize) -> bool {
        if !self.recursive_fns.contains(&fn_id) {
            return true;
        }
        self.dispatch_masks
            .get(&fn_id)
            .and_then(|mask| mask.get(slot).copied())
            .unwrap_or(true)
    }

    /// Build the activation identity for a call and the full canonical input
    /// vector to store on the activation. Returns `None` if any slot is not a
    /// known value (an unresolved call cannot activate). Each key slot is the
    /// canonicalized value for a dispatch subject and its `convergence_class`
    /// otherwise; the returned `Vec<Info>` is every slot canonicalized exactly
    /// (recursive-key widen per slot) so same-class non-dispatch slots fold
    /// together via the `refine_widen` join of the stored inputs.
    fn make_key<T: Types<Ty = Ty>>(
        &self,
        t: &mut T,
        fn_id: FnId,
        inputs: &[Info],
    ) -> Option<(ActivationKey, Vec<Info>)> {
        let mut full = Vec::with_capacity(inputs.len());
        let mut class_inputs = Vec::with_capacity(inputs.len());
        for (slot, input) in inputs.iter().enumerate() {
            let Info::Known(value) = input else {
                return None;
            };
            let canonical = ValueKey::from_fact(t, value);
            class_inputs.push(if self.is_dispatch_slot(fn_id, slot) {
                canonical.clone()
            } else {
                ValueKey {
                    ty: t.convergence_class(&canonical.ty),
                    proof: ValueProof::Unproven,
                }
            });
            full.push(canonical.into_info());
        }
        Some((ActivationKey { fn_id, class_inputs }, full))
    }

    /// Fold a fresh call's canonical inputs into an existing activation's
    /// stored inputs by joining slot-wise through the refinement lattice.
    /// Dispatch slots are equal by construction (they keyed the same
    /// activation), so only non-dispatch slots can widen. Returns the joined
    /// vector and whether anything changed (which means the body must re-run).
    fn join_inputs<T: Types<Ty = Ty>>(&self, t: &mut T, stored: &[Info], incoming: &[Info]) -> (Vec<Info>, bool) {
        let mut changed = false;
        let joined = stored
            .iter()
            .zip(incoming)
            .map(|(old, new)| {
                // Idempotent by construction: equal slots stay byte-identical.
                // `refine_widen` does not preserve closure-literal identity even
                // when both sides are the same closure (it reconstructs a bare
                // arrow), so widening an unchanged callable slot would erase the
                // identity its apply site needs. Only genuinely differing slots
                // ascend the lattice.
                if old.equiv(t, new) {
                    return old.clone();
                }
                changed = true;
                old.join(t, new)
            })
            .collect();
        (joined, changed)
    }

    fn enqueue(&mut self, key: ActivationKey) {
        if self.queued.insert(key.clone()) {
            self.queue.push_back(key);
        }
    }

    fn pop(&mut self) -> Option<ActivationKey> {
        let key = self.queue.pop_front()?;
        self.queued.remove(&key);
        Some(key)
    }

    /// Seed an entry point with its known input types and schedule it.
    fn seed<T: Types<Ty = Ty>>(&mut self, t: &mut T, fn_id: FnId, inputs: Vec<Info>) -> ActivationKey {
        let (key, canonical) = self
            .make_key(t, fn_id, &inputs)
            .expect("entry activations must be seeded with known inputs");
        self.activations.insert(
            key.clone(),
            Activation {
                inputs: canonical,
                ret: Info::Pending,
            },
        );
        self.enqueue(key.clone());
        key
    }

    /// `caller` applies `target` to `args`. The target first resolves to an
    /// activation request set (direct fn, protocol impl, or closure body with
    /// captures prepended), then every selected request activates through the
    /// same path.
    fn call_target<T: Types<Ty = Ty> + ClosureTypes>(
        &mut self,
        t: &mut T,
        caller: &ActivationKey,
        callsite: CallsiteId,
        target: CallTarget<'_>,
        args: Vec<Info>,
    ) -> Info {
        let requests = match self.activation_requests(t, target, args) {
            Ok(requests) => requests,
            Err(info) => return info,
        };
        self.apply_requests(t, caller, callsite, requests)
    }

    fn seed_callable_boundary<T: Types<Ty = Ty> + ClosureTypes>(
        &mut self,
        t: &mut T,
        caller: &ActivationKey,
        callsite: CallsiteId,
        callable: Var,
        env: &Env,
    ) {
        let Some(requests) = self.boundary_requests(t, callable, env) else {
            return;
        };
        for request in requests.requests {
            self.activate_boundary_request(t, caller, callsite.clone(), request);
        }
    }

    fn activation_requests<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        target: CallTarget<'_>,
        args: Vec<Info>,
    ) -> Result<ActivationRequestSet, Info> {
        match target {
            CallTarget::Direct(callee) => self.direct_requests(t, callee, args),
            CallTarget::Closure { value, env } => self.closure_requests(t, value, args, env),
        }
    }

    /// Direct calls include protocol-dispatch stubs. A stub resolves to the
    /// concrete impl selected by the receiver type; ordinary fns pass through.
    fn direct_requests<T: Types<Ty = Ty>>(
        &self,
        t: &mut T,
        callee: FnId,
        args: Vec<Info>,
    ) -> Result<ActivationRequestSet, Info> {
        if self.module.protocol_call_targets.contains_key(&callee) {
            // A protocol call resolves to a concrete impl chosen by the
            // receiver type. A pending receiver waits for a later fixpoint
            // iteration; a live unknown receiver remains unknown.
            match args.first() {
                Some(Info::Pending) => return Err(Info::Pending),
                Some(Info::Unknown) => return Err(Info::Unknown),
                Some(Info::NoReturn) | None => return Err(Info::NoReturn),
                Some(Info::Known(_)) => {}
            }
            return self
                .resolve_protocol(t, callee, &args)
                .map(|impl_fn| ActivationRequestSet::singleton(impl_fn, args))
                .ok_or(Info::Unknown);
        }
        Ok(ActivationRequestSet::singleton(callee, args))
    }

    fn operator_spec_result<T: Types<Ty = Ty> + ClosureTypes>(&self, t: &mut T, op: BinOp, inputs: &[Info]) -> Info {
        let name = format!("Kernel.{}", binop_symbol(op));
        let Some(f) = self
            .module
            .fns
            .iter()
            .find(|f| f.name == name && f.block(f.entry).params.len() == inputs.len())
        else {
            return unresolved_inputs(inputs);
        };
        self.declared_spec_result(t, f.id, inputs)
            .unwrap_or_else(|| unresolved_inputs(inputs))
    }

    /// Resolve a closure application to its body activation request. `Pending` waits;
    /// `Unknown` stays `Unknown`; a known value that cannot be resolved to a
    /// single closure target is still not proven callable, so it stays
    /// `Unknown` until a final boundary decides how to erase it.
    fn closure_requests<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        closure: Var,
        arg_infos: Vec<Info>,
        env: &Env,
    ) -> Result<ActivationRequestSet, Info> {
        let clo = env.get(&closure).cloned().unwrap_or(Info::Pending);
        let clo_ty = match clo {
            Info::Pending => return Err(Info::Pending),
            Info::Unknown => return Err(Info::Unknown),
            Info::NoReturn => return Err(Info::NoReturn),
            Info::Known(value) => value.ty,
        };
        match t.closure_lit_parts(&clo_ty) {
            Some(parts) => {
                let target: FnId = parts.target.into();
                let mut inputs: Vec<Info> = parts.captures.into_iter().map(Info::known).collect();
                inputs.extend(arg_infos);
                Ok(ActivationRequestSet::singleton(target, inputs))
            }
            // Couldn't resolve a single closure target ⇒ undetermined, not
            // `any` (which would assert "dynamic" as a fact). `any` is earned.
            None => Err(Info::Unknown),
        }
    }

    fn boundary_requests<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        closure: Var,
        env: &Env,
    ) -> Option<ActivationRequestSet> {
        let clo_ty = match env.get(&closure).cloned().unwrap_or(Info::Pending) {
            Info::Known(value) => value.ty,
            Info::Pending | Info::Unknown | Info::NoReturn => return None,
        };
        let clauses = t.callable_clauses(&clo_ty)?;
        let mut requests = Vec::new();
        for clause in clauses {
            let Some(closure) = clause.closure else {
                continue;
            };
            let mut inputs: Vec<Info> = closure.captures.into_iter().map(Info::known).collect();
            inputs.extend(clause.args.into_iter().map(Info::known));
            requests.push(ActivationRequest {
                fn_id: closure.target.into(),
                inputs,
            });
        }
        if requests.is_empty() {
            None
        } else {
            Some(ActivationRequestSet { requests })
        }
    }

    /// Resolve a protocol-dispatch stub to the concrete implementation fn for
    /// its receiver type, mirroring `ir_planner::walk::protocol_dispatch_key`:
    /// the single impl whose target type the receiver is a subtype of. `None`
    /// when the receiver is not yet `Known` or no impl matches.
    fn resolve_protocol<T: Types<Ty = Ty>>(&self, t: &mut T, callee: FnId, args: &[Info]) -> Option<FnId> {
        let target = self.module.protocol_call_targets.get(&callee)?;
        let receiver_ty = match args.first()? {
            Info::Known(value) => value.ty.clone(),
            Info::Pending | Info::Unknown | Info::NoReturn => return None,
        };
        let mut matches: Vec<_> = self
            .module
            .protocol_registry
            .impls
            .values()
            .filter(|fact| fact.protocol == target.protocol)
            .filter(|fact| {
                let target_ty = impl_target_type(t, &fact.target);
                t.is_subtype(&receiver_ty, &target_ty)
            })
            .filter_map(|fact| fact.callbacks.get(&(target.callback.clone(), target.arity)).cloned())
            .collect();
        matches.sort();
        matches.dedup();
        let export = matches.into_iter().next()?;
        let fn_name = format!("{}.{}", export.module, export.name);
        self.module.fn_by_name(&fn_name).map(|f| f.id)
    }

    fn apply_requests<T: Types<Ty = Ty>>(
        &mut self,
        t: &mut T,
        caller: &ActivationKey,
        callsite: CallsiteId,
        requests: ActivationRequestSet,
    ) -> Info {
        let mut out: Option<Info> = None;
        for request in requests.requests {
            let ret = self.activate_request(t, caller, callsite.clone(), request);
            out = Some(match out {
                Some(prev) => prev.join(t, &ret),
                None => ret,
            });
        }
        out.unwrap_or(Info::Unknown)
    }

    /// Record the dependency, ensure the request target activation exists, and
    /// hand back its current return estimate (`Pending` for a callee not yet
    /// processed).
    fn activate_request<T: Types<Ty = Ty>>(
        &mut self,
        t: &mut T,
        caller: &ActivationKey,
        callsite: CallsiteId,
        request: ActivationRequest,
    ) -> Info {
        let Some((key, canonical)) = self.make_key(t, request.fn_id, &request.inputs) else {
            return unresolved_inputs(&request.inputs);
        };
        self.edges.insert(ActivationEdge {
            caller: caller.clone(),
            callee: key.clone(),
            callsite,
        });
        self.deps.entry(key.clone()).or_default().insert(caller.clone());
        self.merge_activation_inputs(t, &key, canonical);
        self.activations
            .get(&key)
            .map(|s| s.ret.clone())
            .unwrap_or(Info::Pending)
    }

    /// Create the activation if new, or fold the call's non-dispatch inputs
    /// into the existing one. A widened input means the body must re-run with
    /// the broader fact, so the activation is re-enqueued — the same monotone
    /// re-evaluation the return-estimate fixpoint already relies on.
    fn merge_activation_inputs<T: Types<Ty = Ty>>(&mut self, t: &mut T, key: &ActivationKey, canonical: Vec<Info>) {
        match self.activations.get(key) {
            None => {
                self.activations.insert(
                    key.clone(),
                    Activation {
                        inputs: canonical,
                        ret: Info::Pending,
                    },
                );
                self.enqueue(key.clone());
            }
            Some(existing) => {
                let (joined, changed) = self.join_inputs(t, &existing.inputs, &canonical);
                if changed {
                    self.activations.get_mut(key).unwrap().inputs = joined;
                    self.enqueue(key.clone());
                }
            }
        }
    }

    fn activate_boundary_request<T: Types<Ty = Ty>>(
        &mut self,
        t: &mut T,
        caller: &ActivationKey,
        callsite: CallsiteId,
        request: ActivationRequest,
    ) {
        let Some((key, canonical)) = self.make_key(t, request.fn_id, &request.inputs) else {
            return;
        };
        self.edges.insert(ActivationEdge {
            caller: caller.clone(),
            callee: key.clone(),
            callsite,
        });
        self.merge_activation_inputs(t, &key, canonical);
    }

    /// Apply `f`'s declared arrow set to this concrete inference input.
    ///
    /// A known matching arrow is a fact. An underconstrained arrow is still
    /// live uncertainty. Known inputs outside every arrow are a contradiction:
    /// the declared callable cannot accept that activation.
    fn declared_spec_result<T: Types<Ty = Ty> + ClosureTypes>(
        &self,
        t: &mut T,
        f: FnId,
        inputs: &[Info],
    ) -> Option<Info> {
        let spec_set = self.module.declared_specs.get(&f)?;
        let mut arg_tys = Vec::with_capacity(inputs.len());
        for i in inputs {
            match i {
                Info::Known(value) => arg_tys.push(value.ty.clone()),
                Info::Pending | Info::Unknown | Info::NoReturn => {
                    return Some(unresolved_inputs(inputs));
                }
            }
        }
        let has_underconstrained_args = arg_tys.iter().any(|ty| t.has_vars(ty));
        match apply_spec_set::<_, (), _>(t, spec_set, &arg_tys, |_t, _query| None) {
            SpecApplicationOutcome::Known(application) => Some(Info::known(application.result)),
            SpecApplicationOutcome::Underconstrained(_) => Some(Info::Unknown),
            SpecApplicationOutcome::NoMatch if has_underconstrained_args => Some(Info::Unknown),
            SpecApplicationOutcome::NoMatch => Some(Info::known(t.none())),
        }
    }

    fn run<T: Types<Ty = Ty> + ClosureTypes>(&mut self, t: &mut T) {
        while let Some(key) = self.pop() {
            let inputs = self.activations[&key].inputs.clone();
            let body_ret = self.walk_fn(t, &key, &inputs);
            // A declared `@spec` is a backstop for a body the engine cannot
            // infer (e.g. an extern-forwarding builtin like `dbg`):
            // only when body inference is `Unknown` do we fall back to the spec
            // instantiated against the inputs. An inferable body keeps its
            // inferred (usually tighter) type, so the spec never blunts a
            // function the engine can read for itself — and a spec the
            // instantiator can't match (e.g. a protocol-typed param) can't
            // turn a precise body into `none`.
            let ret = match body_ret {
                Info::Unknown => self
                    .declared_spec_result(t, key.fn_id, &inputs)
                    .unwrap_or(Info::Unknown),
                known => known,
            };
            let old = self.activations[&key].ret.clone();
            let new = old.join(t, &ret);
            if !new.equiv(t, &old) {
                self.activations.get_mut(&key).unwrap().ret = new;
                if let Some(callers) = self.deps.get(&key).cloned() {
                    for c in callers {
                        self.enqueue(c);
                    }
                }
            }
        }
    }

    fn activation_facts(&self) -> Vec<TypeInferActivationFact> {
        let activation_ids = self.activation_ids();
        let mut facts: Vec<_> = self
            .activations
            .iter()
            .map(|(key, activation)| TypeInferActivationFact {
                activation_id: *activation_ids.get(key).expect("activation id"),
                fn_id: key.fn_id,
                input_tys: info_tys(&activation.inputs),
                return_state: TypeInferReturnState::from_info(&activation.ret),
            })
            .collect();
        facts.sort_by(|a, b| {
            a.activation_id.cmp(&b.activation_id).then_with(|| {
                a.fn_id
                    .cmp(&b.fn_id)
                    .then_with(|| a.input_tys.len().cmp(&b.input_tys.len()))
                    .then_with(|| format!("{:?}", a.input_tys).cmp(&format!("{:?}", b.input_tys)))
                    .then_with(|| format!("{:?}", a.return_state).cmp(&format!("{:?}", b.return_state)))
            })
        });
        facts
    }

    fn activation_ids(&self) -> HashMap<ActivationKey, TypeInferActivationId> {
        let input_tys = |key: &ActivationKey| {
            self.activations
                .get(key)
                .map(|a| info_tys(&a.inputs))
                .unwrap_or_default()
        };
        let mut keys: Vec<_> = self.activations.keys().cloned().collect();
        keys.sort_by(|a, b| {
            let (a_tys, b_tys) = (input_tys(a), input_tys(b));
            a.fn_id
                .cmp(&b.fn_id)
                .then_with(|| a_tys.len().cmp(&b_tys.len()))
                .then_with(|| format!("{a_tys:?}").cmp(&format!("{b_tys:?}")))
        });
        keys.into_iter()
            .enumerate()
            .map(|(index, key)| (key, TypeInferActivationId(index as u64)))
            .collect()
    }

    fn activation_edge_facts(&self) -> Vec<TypeInferActivationEdgeFact> {
        let activation_ids = self.activation_ids();
        let input_tys = |key: &ActivationKey| {
            self.activations
                .get(key)
                .map(|a| info_tys(&a.inputs))
                .unwrap_or_default()
        };
        let mut facts: Vec<_> = self
            .edges
            .iter()
            .map(|edge| TypeInferActivationEdgeFact {
                caller_activation_id: *activation_ids.get(&edge.caller).expect("caller activation id"),
                caller_fn_id: edge.caller.fn_id,
                caller_input_tys: input_tys(&edge.caller),
                callee_activation_id: *activation_ids.get(&edge.callee).expect("callee activation id"),
                callee_fn_id: edge.callee.fn_id,
                callee_input_tys: input_tys(&edge.callee),
                callsite: TypeInferCallsiteFact {
                    callsite: edge.callsite.clone(),
                    span_start: edge.callsite.ident.span().start as u64,
                    span_end: edge.callsite.ident.span().end as u64,
                },
            })
            .collect();
        facts.sort_by(|a, b| {
            a.caller_activation_id
                .cmp(&b.caller_activation_id)
                .then_with(|| a.callee_activation_id.cmp(&b.callee_activation_id))
                .then_with(|| a.caller_fn_id.cmp(&b.caller_fn_id))
                .then_with(|| a.callee_fn_id.cmp(&b.callee_fn_id))
                .then_with(|| format!("{:?}", a.caller_input_tys).cmp(&format!("{:?}", b.caller_input_tys)))
                .then_with(|| format!("{:?}", a.callee_input_tys).cmp(&format!("{:?}", b.callee_input_tys)))
        });
        facts
    }

    fn dead_arm_facts(&self) -> Vec<TypeInferDeadArmFact> {
        let activation_ids = self.activation_ids();
        let mut facts: Vec<_> = self
            .dead_arms
            .iter()
            .map(|dead_arm| TypeInferDeadArmFact {
                activation_id: *activation_ids
                    .get(&dead_arm.activation)
                    .expect("dead-arm activation id"),
                fn_id: dead_arm.fn_id,
                block_id: dead_arm.block_id,
                branch: dead_arm.branch,
            })
            .collect();
        facts.sort_by(|a, b| {
            a.activation_id
                .cmp(&b.activation_id)
                .then_with(|| a.fn_id.cmp(&b.fn_id))
                .then_with(|| a.block_id.0.cmp(&b.block_id.0))
                .then_with(|| dead_branch_name(a.branch).cmp(dead_branch_name(b.branch)))
        });
        facts
    }

    fn outcome(&self) -> TypeInferOutcome {
        TypeInferOutcome {
            status: self.status(),
            activations: self.activation_facts(),
            edges: self.activation_edge_facts(),
            dead_arms: self.dead_arm_facts(),
        }
    }

    fn status(&self) -> TypeInferStatus {
        if !self.diagnostics.is_empty() {
            return TypeInferStatus::Invalid;
        }
        if self
            .activations
            .values()
            .any(|activation| matches!(activation.ret, Info::Pending | Info::Unknown))
        {
            return TypeInferStatus::Unresolved;
        }
        TypeInferStatus::Complete
    }

    fn emit_telemetry<T: Types<Ty = Ty> + RenderTypes>(&self, t: &mut T, tel: &dyn Telemetry) {
        let activation_ids = self.activation_ids();
        self.emit_activation_facts(t, tel);
        self.emit_activation_edge_facts(t, tel);
        self.emit_dispatch_mask_facts(tel);
        self.emit_fn_return_facts(t, tel);
        for diagnostic in &self.diagnostics {
            diagnostic.emit(t, self.module, tel);
        }
        for dead_arm in &self.dead_arms {
            dead_arm.emit(&activation_ids, self.module, tel);
        }
    }

    fn emit_activation_facts<T: Types<Ty = Ty> + RenderTypes>(&self, t: &mut T, tel: &dyn Telemetry) {
        let mut facts: Vec<_> = self.activations.iter().collect();
        facts.sort_by_key(|(key, activation)| (key.fn_id, activation.inputs.len()));
        let activation_ids = self.activation_ids();
        for (key, activation) in facts {
            let fn_name = self.module.fn_by_id(key.fn_id).name.clone();
            let return_ty = render_info(t, &activation.ret);
            let input_tys = activation
                .inputs
                .iter()
                .map(|input| render_info(t, input))
                .collect::<Vec<_>>();
            let mut metadata = metadata! {
                activation_id: activation_ids.get(key).expect("activation id").0,
                fn_name: fn_name,
                fn_id: key.fn_id.0 as u64,
                input_count: activation.inputs.len() as u64,
                input_tys: input_tys,
                state: info_state(&activation.ret),
                return_ty: return_ty,
            };
            if let Info::Known(value) = &activation.ret {
                metadata.0.push(("return_ty_data", Value::opaque(&value.ty)));
            }
            tel.event(&["fz", "type_infer", "activation"], metadata);
        }
    }

    fn emit_activation_edge_facts<T: Types<Ty = Ty> + RenderTypes>(&self, t: &mut T, tel: &dyn Telemetry) {
        let mut facts: Vec<_> = self.edges.iter().collect();
        facts.sort_by(|a, b| {
            (
                a.caller.fn_id,
                a.callee.fn_id,
                emit_slot_name(a.callsite.slot),
                a.callsite.ident.span().start,
                a.callsite.ident.span().end,
            )
                .cmp(&(
                    b.caller.fn_id,
                    b.callee.fn_id,
                    emit_slot_name(b.callsite.slot),
                    b.callsite.ident.span().start,
                    b.callsite.ident.span().end,
                ))
        });
        let activation_ids = self.activation_ids();
        for edge in facts {
            let caller_name = self.module.fn_by_id(edge.caller.fn_id).name.clone();
            let callee_name = self.module.fn_by_id(edge.callee.fn_id).name.clone();
            let edge_input_tys = |key: &ActivationKey| {
                self.activations
                    .get(key)
                    .map(|a| info_tys(&a.inputs))
                    .unwrap_or_default()
                    .iter()
                    .map(|ty| t.display_for_diag(ty))
                    .collect::<Vec<_>>()
            };
            let caller_input_tys = edge_input_tys(&edge.caller);
            let callee_input_tys = edge_input_tys(&edge.callee);
            tel.event(
                &["fz", "type_infer", "activation_edge"],
                metadata! {
                    caller_activation_id: activation_ids
                        .get(&edge.caller)
                        .expect("caller activation id")
                        .0,
                    caller_fn_name: caller_name,
                    caller_fn_id: edge.caller.fn_id.0 as u64,
                    caller_input_tys: caller_input_tys,
                    callee_activation_id: activation_ids
                        .get(&edge.callee)
                        .expect("callee activation id")
                        .0,
                    callee_fn_name: callee_name,
                    callee_fn_id: edge.callee.fn_id.0 as u64,
                    callee_input_tys: callee_input_tys,
                    callsite_slot: emit_slot_name(edge.callsite.slot),
                    callsite_span_start: edge.callsite.ident.span().start as u64,
                    callsite_span_end: edge.callsite.ident.span().end as u64,
                },
            );
        }
    }

    /// fz-y6w.2 — surface each activated fn's dispatch-subject mask. The
    /// `dispatch_slots` are the entry-param indices that drive clause/branch
    /// selection (kept precise); the complement is convergeable. Emitted only
    /// for fns that actually activated, so the inventory mirrors the work done.
    fn emit_dispatch_mask_facts(&self, tel: &dyn Telemetry) {
        let mut fns: Vec<FnId> = self.activations.keys().map(|key| key.fn_id).collect();
        fns.sort();
        fns.dedup();
        for fn_id in fns {
            let mask = match self.dispatch_masks.get(&fn_id) {
                Some(mask) => mask,
                None => continue,
            };
            let dispatch_slots: Vec<String> = mask
                .iter()
                .enumerate()
                .filter(|&(_, is_dispatch)| *is_dispatch)
                .map(|(slot, _)| slot.to_string())
                .collect();
            tel.event(
                &["fz", "type_infer", "dispatch_mask"],
                metadata! {
                    fn_name: self.module.fn_by_id(fn_id).name.clone(),
                    fn_id: fn_id.0 as u64,
                    arity: mask.len() as u64,
                    dispatch_slots: dispatch_slots,
                },
            );
        }
    }

    fn emit_fn_return_facts<T: Types<Ty = Ty> + RenderTypes>(&self, t: &mut T, tel: &dyn Telemetry) {
        let mut by_fn: BTreeMap<FnId, (Option<Ty>, bool, bool)> = BTreeMap::new();
        for (key, activation) in &self.activations {
            let (known_ret, unsettled, no_return) = by_fn.entry(key.fn_id).or_default();
            match &activation.ret {
                Info::Known(value) => {
                    *known_ret = Some(match known_ret.take() {
                        Some(prev) => t.union(prev, value.ty.clone()),
                        None => value.ty.clone(),
                    });
                }
                Info::Pending | Info::Unknown => *unsettled = true,
                Info::NoReturn => *no_return = true,
            }
        }
        for (fn_id, (known_ret, unsettled, no_return)) in by_fn {
            let fn_name = self.module.fn_by_id(fn_id).name.clone();
            let state = if unsettled {
                "unsettled"
            } else if known_ret.is_some() {
                "known"
            } else if no_return {
                "no_return"
            } else {
                "unreached"
            };
            let return_ty = known_ret.as_ref().map(|ty| t.display_for_diag(ty)).unwrap_or_default();
            let mut metadata = metadata! {
                fn_name: fn_name,
                fn_id: fn_id.0 as u64,
                state: state,
                return_ty: return_ty,
            };
            if let Some(ty) = &known_ret {
                metadata.0.push(("return_ty_data", Value::opaque(ty)));
            }
            tel.event(&["fz", "type_infer", "fn_return"], metadata);
        }
    }

    /// The return estimate `f` hands to its continuation, given its inputs.
    fn walk_fn<T: Types<Ty = Ty> + ClosureTypes>(&mut self, t: &mut T, key: &ActivationKey, inputs: &[Info]) -> Info {
        let f = key.fn_id;
        let fnir = self.module.fn_by_id(f);
        let mut env: Env = HashMap::new();
        for (param, info) in fnir.block(fnir.entry).params.iter().zip(inputs) {
            env.insert(*param, info.clone());
        }
        let mut predicates = HashMap::new();
        let mut visited = HashSet::new();
        self.walk_block(t, key, fnir.entry, &mut env, &mut predicates, &mut visited)
    }

    /// Walk one block of `f`. Intra-fn control (`Goto`/`If`) recurses here;
    /// inter-fn edges route through [`Solver::call`]. Returns the value `f`
    /// hands to its continuation along this path (`NoReturn` for non-returning
    /// `Halt` paths — they contribute no value to the control-flow join).
    fn walk_block<T: Types<Ty = Ty> + ClosureTypes>(
        &mut self,
        t: &mut T,
        key: &ActivationKey,
        block_id: BlockId,
        env: &mut Env,
        predicates: &mut PredicateFacts,
        visited: &mut HashSet<BlockId>,
    ) -> Info {
        let module = self.module;
        let f = key.fn_id;
        if !visited.insert(block_id) {
            return Info::Pending;
        }
        let block = module.fn_by_id(f).block(block_id);
        for (stmt_index, Stmt::Let(v, prim)) in block.stmts.iter().enumerate() {
            let info = self.type_prim(t, prim, env);
            let proved_none = self.record_value_required_none(t, f, block_id, stmt_index, prim, &info, env);
            env.insert(*v, info);
            if let Prim::Extern(ident, _, args) = prim {
                let callsite = CallsiteId::new(key.fn_id, ident, EmitSlot::CallableBoundary);
                for arg in args {
                    self.seed_callable_boundary(t, key, callsite.clone(), arg.var, env);
                }
            }
            if let Some(fact) = predicate_fact(prim) {
                predicates.insert(*v, fact);
            }
            if let Some(info) = proved_none {
                return info;
            }
        }
        match &block.terminator {
            Term::Return(v) => env.get(v).cloned().unwrap_or(Info::Pending),
            // A halt path adds no value to the caller's return type, so it
            // contributes the control-flow join identity. That identity is
            // `NoReturn`, not `Unknown` and not `Known(none)`: `Unknown` is a
            // live-but-unproven value, and `Known(none)` would erase sibling
            // proof by flowing through the value-lattice widen.
            //
            // We still reach halt paths when the current proof cannot prove
            // a matcher fail arm dead. Proved-impossible branches are skipped
            // by predicate narrowing; unresolved fail arms stay neutral until
            // the fixpoint can classify them.
            Term::Halt(_) => Info::NoReturn,
            Term::Goto(target, args) => {
                let arg_infos = arg_infos_of(args, env);
                let target_params = module.fn_by_id(f).block(*target).params.clone();
                for (param, info) in target_params.iter().zip(arg_infos) {
                    env.insert(*param, info);
                }
                self.walk_block(t, key, *target, env, predicates, visited)
            }
            Term::If {
                cond, then_b, else_b, ..
            } => {
                let (then_b, else_b) = (*then_b, *else_b);
                let fact = predicates.get(cond).cloned();
                let truth = bool_truth(t, &info_of(*cond, env))
                    .or_else(|| fact.as_ref().and_then(|p| predicate_truth(t, module, p, env)));
                let (then_env, else_env) = if let Some(fact) = fact.as_ref() {
                    (
                        narrow_predicate(t, env, fact, true),
                        narrow_predicate(t, env, fact, false),
                    )
                } else {
                    (Some(env.clone()), Some(env.clone()))
                };
                if matches!(truth, Some(false)) || then_env.is_none() {
                    self.record_dead_arm(key, f, block_id, DeadBranch::Then);
                }
                if matches!(truth, Some(true)) || else_env.is_none() {
                    self.record_dead_arm(key, f, block_id, DeadBranch::Else);
                }
                match truth {
                    Some(true) => self.walk_branch(t, key, then_b, then_env, predicates, visited),
                    Some(false) => self.walk_branch(t, key, else_b, else_env, predicates, visited),
                    None => {
                        let a = self.walk_branch(t, key, then_b, then_env, predicates, visited);
                        let b = self.walk_branch(t, key, else_b, else_env, predicates, visited);
                        a.join(t, &b)
                    }
                }
            }
            Term::Call {
                callee,
                args,
                continuation,
                ..
            } => {
                let arg_infos = arg_infos_of(args, env);
                let ident = block.terminator.ident().expect("call terminator should carry ident");
                let direct_callsite = CallsiteId::new(key.fn_id, ident, EmitSlot::Direct);
                let r = self.call_target(t, key, direct_callsite, CallTarget::Direct(*callee), arg_infos);
                if matches!(r, Info::NoReturn) {
                    return Info::NoReturn;
                }
                let cont_inputs = cont_inputs_of(r, &continuation.captured, env);
                let cont_callsite = CallsiteId::new(key.fn_id, ident, EmitSlot::Cont);
                self.call_target(
                    t,
                    key,
                    cont_callsite,
                    CallTarget::Direct(continuation.fn_id),
                    cont_inputs,
                )
            }
            // A tail call forwards our own continuation, so its result is ours.
            Term::TailCall { callee, args, .. } => {
                let arg_infos = arg_infos_of(args, env);
                let ident = block
                    .terminator
                    .ident()
                    .expect("tail-call terminator should carry ident");
                let direct_callsite = CallsiteId::new(key.fn_id, ident, EmitSlot::Direct);
                self.call_target(t, key, direct_callsite, CallTarget::Direct(*callee), arg_infos)
            }
            Term::CallClosure {
                closure,
                args,
                continuation,
                ..
            } => {
                let arg_infos = arg_infos_of(args, env);
                let ident = block
                    .terminator
                    .ident()
                    .expect("closure-call terminator should carry ident");
                let closure_callsite = CallsiteId::new(key.fn_id, ident, EmitSlot::ClosureCall);
                let r = self.call_target(
                    t,
                    key,
                    closure_callsite,
                    CallTarget::Closure { value: *closure, env },
                    arg_infos,
                );
                if matches!(r, Info::NoReturn) {
                    return Info::NoReturn;
                }
                let cont_inputs = cont_inputs_of(r, &continuation.captured, env);
                let cont_callsite = CallsiteId::new(key.fn_id, ident, EmitSlot::Cont);
                self.call_target(
                    t,
                    key,
                    cont_callsite,
                    CallTarget::Direct(continuation.fn_id),
                    cont_inputs,
                )
            }
            Term::TailCallClosure { closure, args, .. } => {
                let arg_infos = arg_infos_of(args, env);
                let ident = block
                    .terminator
                    .ident()
                    .expect("tail-closure-call terminator should carry ident");
                let closure_callsite = CallsiteId::new(key.fn_id, ident, EmitSlot::ClosureCall);
                self.call_target(
                    t,
                    key,
                    closure_callsite,
                    CallTarget::Closure { value: *closure, env },
                    arg_infos,
                )
            }
            // Selective receive activates each reachable guard/body/after
            // outcome with opaque message bindings and joins their returns.
            Term::ReceiveMatched {
                clauses,
                after,
                captures,
                ..
            } => {
                let mut out: Option<Info> = None;
                for clause in clauses {
                    let mut bound_inputs = vec![Info::known(t.any()); clause.bound_names.len()];
                    let capture_inputs = arg_infos_of(captures, env);
                    bound_inputs.extend(capture_inputs.clone());
                    if let Some(guard) = clause.guard {
                        let guard_callsite = CallsiteId::new(key.fn_id, &clause.ident, EmitSlot::Cont);
                        let _ =
                            self.call_target(t, key, guard_callsite, CallTarget::Direct(guard), bound_inputs.clone());
                    }
                    let body_callsite = CallsiteId::new(key.fn_id, &clause.ident, EmitSlot::Cont);
                    let body_ret =
                        self.call_target(t, key, body_callsite, CallTarget::Direct(clause.body), bound_inputs);
                    out = Some(match out {
                        Some(prev) => prev.join(t, &body_ret),
                        None => body_ret,
                    });
                }
                if let Some(after) = after {
                    let after_callsite = CallsiteId::new(key.fn_id, &after.ident, EmitSlot::Cont);
                    let after_ret = self.call_target(
                        t,
                        key,
                        after_callsite,
                        CallTarget::Direct(after.body),
                        arg_infos_of(captures, env),
                    );
                    out = Some(match out {
                        Some(prev) => prev.join(t, &after_ret),
                        None => after_ret,
                    });
                }
                out.unwrap_or(Info::Unknown)
            }
        }
    }

    fn walk_branch<T: Types<Ty = Ty> + ClosureTypes>(
        &mut self,
        t: &mut T,
        key: &ActivationKey,
        block_id: BlockId,
        env: Option<Env>,
        predicates: &PredicateFacts,
        visited: &HashSet<BlockId>,
    ) -> Info {
        let Some(mut env) = env else {
            return Info::NoReturn;
        };
        let mut predicates = predicates.clone();
        let mut visited = visited.clone();
        self.walk_block(t, key, block_id, &mut env, &mut predicates, &mut visited)
    }

    fn record_dead_arm(&mut self, activation: &ActivationKey, fn_id: FnId, block_id: BlockId, branch: DeadBranch) {
        let fact = DeadArmFact {
            activation: activation.clone(),
            fn_id,
            block_id,
            branch,
        };
        if self.dead_arm_sites.insert(fact.clone()) {
            self.dead_arms.push(fact);
        }
    }

    fn record_value_required_none<T: Types<Ty = Ty>>(
        &mut self,
        t: &mut T,
        fn_id: FnId,
        block_id: BlockId,
        stmt_index: usize,
        prim: &Prim,
        info: &Info,
        env: &Env,
    ) -> Option<Info> {
        let Info::Known(value) = info else {
            return None;
        };
        if !t.is_empty(&value.ty) {
            return None;
        }
        let kind = invalid_operator_application(prim, env)?;
        if self.diagnostic_sites.insert((fn_id, block_id, stmt_index)) {
            self.diagnostics.push(TypeInferDiagnostic {
                fn_id,
                block_id,
                stmt_index,
                kind,
            });
        }
        Some(info.clone())
    }

    fn type_prim<T: Types<Ty = Ty> + ClosureTypes>(&mut self, t: &mut T, prim: &Prim, env: &Env) -> Info {
        let module = self.module;
        match prim {
            Prim::Const(c) => match c {
                Const::Int(n) => {
                    let ty = t.int();
                    let proof = ValueProof::Exact(t.int_lit(*n));
                    Info::known_with_proof(ty, proof)
                }
                Const::Float(x) => {
                    let ty = t.float();
                    let proof = ValueProof::Exact(t.float_lit(*x));
                    Info::known_with_proof(ty, proof)
                }
                Const::Nil => Info::known(t.nil()),
                Const::True => {
                    let ty = t.bool();
                    let proof = ValueProof::Exact(t.bool_lit(true));
                    Info::known_with_proof(ty, proof)
                }
                Const::False => {
                    let ty = t.bool();
                    let proof = ValueProof::Exact(t.bool_lit(false));
                    Info::known_with_proof(ty, proof)
                }
                Const::Atom(id) => {
                    let name = module.atom_names.get(*id as usize).map(String::as_str).unwrap_or("");
                    Info::known(t.atom_lit(name))
                }
            },
            Prim::BinOp(op, a, b) => {
                let lt = info_of(*a, env);
                let rt = info_of(*b, env);
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                        self.operator_spec_result(t, *op, &[lt, rt])
                    }
                    BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                        comparison_binop(t, *op, lt, rt)
                    }
                    BinOp::And | BinOp::Or => logical_binop(t, *op, lt, rt),
                }
            }
            Prim::UnOp(op, v) => match op {
                UnOp::Neg => negate_info(t, info_of(*v, env)),
                UnOp::Not => not_info(t, info_of(*v, env)),
            },
            Prim::IsEmptyList(_) | Prim::IsListCons(_) | Prim::TypeTest(_, _) | Prim::RuntimeTypeTest(_, _) => {
                Info::known(t.bool())
            }
            Prim::ListHead(v) => info_of(*v, env).map_known(|value| value.map_ty(|ty| t.list_element_type(&ty))),
            Prim::ListTail(v) => info_of(*v, env).map_known(|lt| {
                let elem = t.list_element_type(&lt.ty);
                ValueFact::new(t.list(elem))
            }),
            Prim::MakeList(elems, tail) => {
                let mut elem = t.none();
                for e in elems {
                    match info_of(*e, env) {
                        Info::Known(et) => elem = t.refine_widen(&elem, &et.ty),
                        Info::Pending => return Info::Pending,
                        Info::Unknown => return Info::Unknown,
                        Info::NoReturn => return Info::NoReturn,
                    }
                }
                let mut tail_ty = None;
                if let Some(tl) = tail {
                    match info_of(*tl, env) {
                        Info::Known(tt) => {
                            let te = t.list_element_type(&tt.ty);
                            elem = t.refine_widen(&elem, &te);
                            tail_ty = Some(tt.ty);
                        }
                        Info::Pending => return Info::Pending,
                        Info::Unknown => return Info::Unknown,
                        Info::NoReturn => return Info::NoReturn,
                    }
                }
                Info::known(if elems.is_empty() && tail.is_none() {
                    t.empty_list()
                } else if elems.is_empty() {
                    tail_ty.unwrap_or_else(|| t.empty_list())
                } else {
                    t.non_empty_list(elem)
                })
            }
            Prim::MakeTuple(vars) => {
                let mut tys = Vec::with_capacity(vars.len());
                let mut proof = Vec::with_capacity(vars.len());
                for v in vars {
                    match info_of(*v, env) {
                        Info::Known(value) => {
                            tys.push(value.ty);
                            proof.push(value.proof);
                        }
                        Info::Pending => return Info::Pending,
                        Info::Unknown => return Info::Unknown,
                        Info::NoReturn => return Info::NoReturn,
                    }
                }
                Info::known_with_proof(t.tuple(&tys), ValueProof::TupleFields(proof))
            }
            Prim::MakeStruct { module, fields } => type_make_struct(t, module, fields, env),
            Prim::TupleField(v, i) => info_of(*v, env).map_known(|value| value.tuple_field(t, *i as usize)),
            Prim::StructField(v, field) => type_struct_field(t, module, *v, field, env),
            Prim::MakeMap(entries) => type_make_map(t, entries, env),
            Prim::MapUpdate(base, entries) => type_map_update(t, *base, entries, env),
            Prim::MapGet(map, key) => type_map_get(t, *map, *key, env, false),
            Prim::MatcherMapGet(map, key) => type_map_get(t, *map, *key, env, true),
            Prim::IsMatcherMapMiss(v) => is_matcher_map_miss(t, info_of(*v, env)),
            Prim::MakeBitstring(_) | Prim::ConstBitstring(_, _) => Info::known(t.str_t()),
            Prim::MakeFnRef(_, target) => {
                let tfn = module.fn_by_id(*target);
                let n_args = tfn.block(tfn.entry).params.len();
                Info::known(t.fn_ref_lit(ClosureTarget::from(*target), n_args))
            }
            Prim::MakeClosure(_, target, caps) => {
                let mut cap_tys = Vec::with_capacity(caps.len());
                for c in caps {
                    match info_of(*c, env) {
                        Info::Known(value) => cap_tys.push(value.ty),
                        Info::Pending => return Info::Pending,
                        Info::Unknown => return Info::Unknown,
                        Info::NoReturn => return Info::NoReturn,
                    }
                }
                let tfn = module.fn_by_id(*target);
                let entry_params = tfn.block(tfn.entry).params.len();
                let n_args = entry_params.saturating_sub(cap_tys.len());
                Info::known(t.closure_lit(ClosureTarget::from(*target), cap_tys, n_args))
            }
            Prim::Extern(_, extern_id, args) => {
                let ret = extern_return_ty(t, module, *extern_id, args, env).unwrap_or_else(|| t.any());
                Info::known(ret)
            }
            // Prims not yet modeled are `Unknown` — undetermined, not `any`.
            // `any` is earned, never defaulted during inference; a final
            // boundary may erase a residual `Unknown` to `any`, but the solver
            // keeps the uncertainty visible.
            _ => Info::Unknown,
        }
    }
}

fn extern_return_ty<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    extern_id: ExternId,
    args: &[ExternArg],
    env: &Env,
) -> Option<Ty> {
    let decl = module.extern_idx.get(&extern_id).map(|&idx| &module.externs[idx])?;
    let mut witnesses = Vec::with_capacity(args.len());
    for arg in args {
        let value = match value_info(arg.var, env) {
            Ok(value) => value,
            Err(Info::Known(value)) => value,
            Err(Info::Pending) => return None,
            Err(Info::NoReturn) => return Some(t.none()),
            Err(Info::Unknown) => {
                witnesses.push(t.any());
                continue;
            }
        };
        witnesses.push(value.ty);
    }
    match instantiate_match(
        t,
        &decl.semantic_contract.params,
        &decl.semantic_contract.result,
        &decl.semantic_contract.constraints,
        &witnesses,
    ) {
        SchemeInstantiation::Known(matched) | SchemeInstantiation::Underconstrained(matched) => Some(matched.result),
        SchemeInstantiation::Invalid => Some(decl.ret_descr.clone()),
    }
}

fn predicate_fact(prim: &Prim) -> Option<PredicateFact> {
    match prim {
        Prim::BinOp(BinOp::Eq, a, b) => Some(PredicateFact::Eq(*a, *b)),
        Prim::BinOp(BinOp::Neq, a, b) => Some(PredicateFact::Neq(*a, *b)),
        Prim::IsEmptyList(v) => Some(PredicateFact::IsEmptyList(*v)),
        Prim::IsListCons(v) => Some(PredicateFact::IsListCons(*v)),
        Prim::IsMatcherMapMiss(v) => Some(PredicateFact::IsMatcherMapMiss(*v)),
        Prim::TypeTest(v, ty) => Some(PredicateFact::TypeTest(*v, (**ty).clone())),
        _ => None,
    }
}

fn bool_truth<T: Types<Ty = Ty>>(t: &mut T, info: &Info) -> Option<bool> {
    let Info::Known(value) = info else {
        return None;
    };
    if let Some(proof) = proof_ty(t, &value.proof)
        && let Some(b) = bool_from_ty(t, &proof)
    {
        return Some(b);
    }
    bool_from_ty(t, &value.ty)
}

fn bool_from_ty<T: Types<Ty = Ty>>(t: &T, ty: &Ty) -> Option<bool> {
    match t.as_atom_singleton(ty)?.as_str() {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

fn predicate_truth<T: Types<Ty = Ty>>(t: &mut T, module: &Module, pred: &PredicateFact, env: &Env) -> Option<bool> {
    match pred {
        PredicateFact::Eq(a, b) => eq_truth(t, module, *a, *b, env),
        PredicateFact::Neq(a, b) => eq_truth(t, module, *a, *b, env).map(|truth| !truth),
        PredicateFact::IsEmptyList(v) => {
            let current = known_ty(*v, env)?;
            let empty = t.empty_list();
            if t.is_subtype(&current, &empty) {
                return Some(true);
            }
            let meet = t.intersect(current, empty);
            if t.is_empty(&meet) { Some(false) } else { None }
        }
        PredicateFact::IsListCons(v) => {
            let current = known_ty(*v, env)?;
            let cons = {
                let any = t.any();
                t.non_empty_list(any)
            };
            if t.is_subtype(&current, &cons) {
                return Some(true);
            }
            let meet = t.intersect(current, cons);
            if t.is_empty(&meet) { Some(false) } else { None }
        }
        PredicateFact::IsMatcherMapMiss(v) => {
            let current = known_value(*v, env)?;
            matcher_map_miss_truth(&current)
        }
        PredicateFact::TypeTest(v, ty) => {
            let current = known_ty(*v, env)?;
            if t.is_subtype(&current, ty) {
                return Some(true);
            }
            let nominals = Nominals::new(&module.brand_inners, &module.opaque_inners);
            if t.is_value_disjoint(&current, ty, nominals) {
                Some(false)
            } else {
                None
            }
        }
    }
}

fn eq_truth<T: Types<Ty = Ty>>(t: &mut T, module: &Module, a: Var, b: Var, env: &Env) -> Option<bool> {
    if a == b {
        return Some(true);
    }
    let a_value = known_value(a, env)?;
    let b_value = known_value(b, env)?;
    let a_ty = proof_ty(t, &a_value.proof).unwrap_or_else(|| a_value.ty.clone());
    let b_ty = proof_ty(t, &b_value.proof).unwrap_or_else(|| b_value.ty.clone());
    if t.is_singleton_lit(&a_ty) && t.is_equivalent(&a_ty, &b_ty) {
        return Some(true);
    }
    let nominals = Nominals::new(&module.brand_inners, &module.opaque_inners);
    if t.is_value_disjoint(&a_ty, &b_ty, nominals) {
        Some(false)
    } else {
        None
    }
}

fn narrow_predicate<T: Types<Ty = Ty>>(t: &mut T, env: &Env, pred: &PredicateFact, truth: bool) -> Option<Env> {
    let mut out = env.clone();
    match pred {
        PredicateFact::Eq(a, b) => {
            if !narrow_eq(t, &mut out, *a, *b, truth) {
                return None;
            }
        }
        PredicateFact::Neq(a, b) => {
            if !narrow_eq(t, &mut out, *a, *b, !truth) {
                return None;
            }
        }
        PredicateFact::IsEmptyList(v) => {
            let empty = t.empty_list();
            if !refine_against(t, &mut out, *v, &empty, truth) {
                return None;
            }
        }
        PredicateFact::IsListCons(v) => {
            let cons = {
                let any = t.any();
                t.non_empty_list(any)
            };
            if !refine_against(t, &mut out, *v, &cons, truth) {
                return None;
            }
        }
        PredicateFact::IsMatcherMapMiss(_) => {}
        PredicateFact::TypeTest(v, ty) => {
            if !refine_against(t, &mut out, *v, ty, truth) {
                return None;
            }
        }
    }
    Some(out)
}

fn narrow_eq<T: Types<Ty = Ty>>(t: &mut T, env: &mut Env, a: Var, b: Var, truth: bool) -> bool {
    let a_ty = known_value(a, env).and_then(|value| proof_ty(t, &value.proof));
    let b_ty = known_value(b, env).and_then(|value| proof_ty(t, &value.proof));
    if let Some(a_ty) = a_ty.as_ref()
        && t.is_singleton_lit(a_ty)
        && !refine_against(t, env, b, a_ty, truth)
    {
        return false;
    }
    if let Some(b_ty) = b_ty.as_ref()
        && t.is_singleton_lit(b_ty)
        && !refine_against(t, env, a, b_ty, truth)
    {
        return false;
    }
    true
}

fn refine_against<T: Types<Ty = Ty>>(t: &mut T, env: &mut Env, subject: Var, domain: &Ty, truth: bool) -> bool {
    let Some(current) = known_value(subject, env) else {
        return true;
    };
    if truth {
        if !proof_fits(t, &current.proof, domain) {
            return false;
        }
    } else if let Some(proof) = proof_ty(t, &current.proof)
        && t.is_subtype(&proof, domain)
    {
        return false;
    }
    let next = if truth {
        t.intersect(current.ty.clone(), domain.clone())
    } else {
        t.difference(current.ty.clone(), domain.clone())
    };
    if t.is_empty(&next) {
        return false;
    }
    let proof = if proof_fits(t, &current.proof, &next) {
        current.proof
    } else {
        ValueProof::Unproven
    };
    env.insert(subject, Info::Known(ValueFact::with_proof(next, proof)));
    true
}

fn known_ty(v: Var, env: &Env) -> Option<Ty> {
    known_value(v, env).map(|value| value.ty)
}

fn known_value(v: Var, env: &Env) -> Option<ValueFact> {
    match env.get(&v)? {
        Info::Known(value) => Some(value.clone()),
        Info::Pending | Info::Unknown | Info::NoReturn => None,
    }
}

fn value_info(v: Var, env: &Env) -> Result<ValueFact, Info> {
    match env.get(&v).cloned().unwrap_or(Info::Pending) {
        Info::Known(value) => Ok(value),
        other => Err(other),
    }
}

fn proof_ty<T: Types<Ty = Ty>>(t: &mut T, proof: &ValueProof) -> Option<Ty> {
    match proof {
        ValueProof::Unproven => None,
        ValueProof::Exact(ty) => Some(ty.clone()),
        ValueProof::TupleFields(fields) => {
            let mut tys = Vec::with_capacity(fields.len());
            for field in fields {
                tys.push(proof_ty(t, field)?);
            }
            Some(t.tuple(&tys))
        }
        ValueProof::StructFields { module, .. } => {
            Some(struct_impl_target_type(t, module.rsplit('.').next().unwrap_or(module)))
        }
        ValueProof::MapFields { .. } | ValueProof::MatcherMapMiss => None,
        ValueProof::MatcherMapHit(value) => proof_ty(t, value),
    }
}

fn proof_fits<T: Types<Ty = Ty>>(t: &mut T, proof: &ValueProof, ty: &Ty) -> bool {
    if let ValueProof::TupleFields(fields) = proof {
        for (index, field) in fields.iter().enumerate() {
            if matches!(field, ValueProof::Unproven) {
                continue;
            }
            let field_ty = t.tuple_field_type(ty, index);
            if !proof_fits(t, field, &field_ty) {
                return false;
            }
        }
        return true;
    }
    if let ValueProof::MapFields { fields, .. } = proof {
        let map_top = t.map_top();
        let meet = t.intersect(ty.clone(), map_top);
        if t.is_empty(&meet) {
            return false;
        }
        for (key, field) in fields {
            if matches!(field, ValueProof::Unproven) {
                continue;
            }
            let Some(field_ty) = t.map_field_lookup(ty, key) else {
                return false;
            };
            if !proof_fits(t, field, &field_ty) {
                return false;
            }
        }
        return true;
    }
    if let ValueProof::MatcherMapHit(value) = proof {
        return proof_fits(t, value, ty);
    }
    let Some(proof) = proof_ty(t, proof) else {
        return true;
    };
    t.is_subtype(&proof, ty)
}

fn type_make_struct<T: Types<Ty = Ty>>(t: &mut T, module: &str, fields: &[(String, Var)], env: &Env) -> Info {
    let mut proof_fields = BTreeMap::new();
    for (field, value) in fields {
        let value = match value_info(*value, env) {
            Ok(value) => value,
            Err(info) => return info,
        };
        proof_fields.insert(field.clone(), value.proof);
    }
    let ty = struct_impl_target_type(t, module.rsplit('.').next().unwrap_or(module));
    Info::known_with_proof(
        ty,
        ValueProof::StructFields {
            module: module.to_string(),
            fields: proof_fields,
        },
    )
}

fn type_struct_field<T: Types<Ty = Ty>>(t: &mut T, module: &Module, subject: Var, field: &str, env: &Env) -> Info {
    let subject = match value_info(subject, env) {
        Ok(subject) => subject,
        Err(info) => return info,
    };
    let Some(ty) = struct_field_ty(t, module, &subject.ty, field) else {
        return Info::Unknown;
    };
    let proof = subject.proof.struct_field(field);
    let proof = if proof_fits(t, &proof, &ty) {
        proof
    } else {
        ValueProof::Unproven
    };
    Info::known_with_proof(ty, proof)
}

fn struct_field_ty<T: Types<Ty = Ty>>(t: &mut T, module: &Module, subject: &Ty, field: &str) -> Option<Ty> {
    let tag = t.opaque_singleton(subject)?;
    let order = struct_schema_for_impl_target(module, &tag)?;
    let index = order.iter().position(|name| name == field)?;
    let inner = module.opaque_inners.get(&tag).cloned()?;
    let comps = t.tuple_projections(&inner, order.len());
    comps.into_iter().nth(index)
}

fn struct_schema_for_impl_target<'a>(module: &'a Module, tag: &str) -> Option<&'a Vec<String>> {
    let target = tag.strip_prefix("impl-target::")?;
    let mut matches = module
        .struct_schemas
        .iter()
        .filter(|(name, _fields)| name.rsplit('.').next().unwrap_or(name.as_str()) == target)
        .map(|(_name, fields)| fields);
    let fields = matches.next()?;
    matches.next().is_none().then_some(fields)
}

fn map_key_of<T: Types<Ty = Ty>>(t: &mut T, value: &ValueFact) -> Option<MapKey> {
    if let Some(proof) = proof_ty(t, &value.proof)
        && let Some(key) = t.as_map_key(&proof)
    {
        return Some(key);
    }
    t.as_map_key(&value.ty)
}

fn type_make_map<T: Types<Ty = Ty>>(t: &mut T, entries: &[(Var, Var)], env: &Env) -> Info {
    let mut fields = Vec::with_capacity(entries.len());
    let mut proof_fields = BTreeMap::new();
    for (key, value) in entries {
        let key = match value_info(*key, env) {
            Ok(key) => key,
            Err(info) => return info,
        };
        let value = match value_info(*value, env) {
            Ok(value) => value,
            Err(info) => return info,
        };
        let Some(map_key) = map_key_of(t, &key) else {
            return Info::known(t.map_top());
        };
        fields.push((map_key.clone(), value.ty));
        proof_fields.insert(map_key, value.proof);
    }
    Info::known_with_proof(
        t.map(&fields),
        ValueProof::MapFields {
            fields: proof_fields,
            complete: true,
        },
    )
}

fn type_map_update<T: Types<Ty = Ty>>(t: &mut T, base: Var, entries: &[(Var, Var)], env: &Env) -> Info {
    let mut current = match value_info(base, env) {
        Ok(current) => current,
        Err(info) => return info,
    };
    let mut proof_fields = match replace(&mut current.proof, ValueProof::Unproven) {
        ValueProof::MapFields { fields, .. } => fields,
        _ => BTreeMap::new(),
    };
    for (key, value) in entries {
        let key = match value_info(*key, env) {
            Ok(key) => key,
            Err(info) => return info,
        };
        let value = match value_info(*value, env) {
            Ok(value) => value,
            Err(info) => return info,
        };
        if let Some(map_key) = map_key_of(t, &key) {
            current.ty = t.refine_map_field(&current.ty, &map_key, &value.ty);
            proof_fields.insert(map_key, value.proof);
        } else {
            current.ty = t.map_top();
            current.proof = ValueProof::Unproven;
            return Info::Known(current);
        }
    }
    current.proof = ValueProof::MapFields {
        fields: proof_fields,
        complete: false,
    };
    Info::Known(current)
}

fn type_map_get<T: Types<Ty = Ty>>(t: &mut T, map: Var, key: Var, env: &Env, matcher: bool) -> Info {
    let map = match value_info(map, env) {
        Ok(map) => map,
        Err(info) => return info,
    };
    let key = match value_info(key, env) {
        Ok(key) => key,
        Err(info) => return info,
    };
    let Some(map_key) = map_key_of(t, &key) else {
        return Info::Unknown;
    };
    match (matcher, map.proof.map_field(&map_key)) {
        (true, MapFieldProof::Miss) => {
            return Info::known_with_proof(t.none(), ValueProof::MatcherMapMiss);
        }
        (true, MapFieldProof::Hit(proof)) => {
            let ty = map_field_ty(t, &map.ty, &map_key).unwrap_or_else(|| t.none());
            let proof = if proof_fits(t, &proof, &ty) {
                proof
            } else {
                ValueProof::Unproven
            };
            return Info::known_with_proof(ty, ValueProof::MatcherMapHit(Box::new(proof)));
        }
        _ => {}
    }
    let ty = map_field_ty(t, &map.ty, &map_key).unwrap_or_else(|| t.none());
    let proof = match map.proof.map_field(&map_key) {
        MapFieldProof::Hit(proof) if proof_fits(t, &proof, &ty) => {
            if matcher {
                ValueProof::MatcherMapHit(Box::new(proof))
            } else {
                proof
            }
        }
        _ if matcher && t.map_known_keys(&map.ty).contains(&map_key) => {
            ValueProof::MatcherMapHit(Box::new(ValueProof::Unproven))
        }
        _ => ValueProof::Unproven,
    };
    Info::known_with_proof(ty, proof)
}

fn map_field_ty<T: Types<Ty = Ty>>(t: &mut T, map: &Ty, key: &MapKey) -> Option<Ty> {
    t.map_field_lookup(map, key)
}

fn is_matcher_map_miss<T: Types<Ty = Ty>>(t: &mut T, info: Info) -> Info {
    let value = match info {
        Info::Known(value) => value,
        other => return non_known(other),
    };
    if let Some(miss) = matcher_map_miss_truth(&value) {
        let ty = t.bool();
        let proof = ValueProof::Exact(t.bool_lit(miss));
        Info::known_with_proof(ty, proof)
    } else {
        Info::known(t.bool())
    }
}

fn matcher_map_miss_truth(value: &ValueFact) -> Option<bool> {
    match &value.proof {
        ValueProof::MatcherMapMiss => Some(true),
        ValueProof::MatcherMapHit(_) => Some(false),
        _ => None,
    }
}

fn comparison_binop<T: Types<Ty = Ty>>(t: &mut T, op: BinOp, left: Info, right: Info) -> Info {
    let (a, b) = match (left, right) {
        (Info::Known(a), Info::Known(b)) => (a, b),
        (a, b) => return non_known_pair(a, b),
    };
    if let Some(result) = fold_comparison(t, op, &a, &b) {
        let ty = t.bool();
        let proof = ValueProof::Exact(t.bool_lit(result));
        return Info::known_with_proof(ty, proof);
    }
    Info::known(t.bool())
}

fn logical_binop<T: Types<Ty = Ty>>(t: &mut T, op: BinOp, left: Info, right: Info) -> Info {
    let (a, b) = match (left, right) {
        (Info::Known(a), Info::Known(b)) => (a, b),
        (a, b) => return non_known_pair(a, b),
    };
    let a_bool = bool_fact(t, &a);
    let b_bool = bool_fact(t, &b);
    let proof = match (op, a_bool, b_bool) {
        (BinOp::And, Some(x), Some(y)) => ValueProof::Exact(t.bool_lit(x && y)),
        (BinOp::Or, Some(x), Some(y)) => ValueProof::Exact(t.bool_lit(x || y)),
        _ => ValueProof::Unproven,
    };
    Info::known_with_proof(t.bool(), proof)
}

fn negate_info<T: Types<Ty = Ty>>(t: &mut T, info: Info) -> Info {
    let value = match info {
        Info::Known(value) => value,
        other => return non_known(other),
    };
    let proof = if let Some(n) = exact_int(t, &value) {
        n.checked_neg()
            .map(|n| ValueProof::Exact(t.int_lit(n)))
            .unwrap_or(ValueProof::Unproven)
    } else if let Some(f) = exact_float(t, &value) {
        ValueProof::Exact(t.float_lit(-f))
    } else {
        ValueProof::Unproven
    };
    Info::Known(ValueFact::with_proof(value.ty, proof))
}

fn not_info<T: Types<Ty = Ty>>(t: &mut T, info: Info) -> Info {
    let value = match info {
        Info::Known(value) => value,
        other => return non_known(other),
    };
    let proof = bool_fact(t, &value)
        .map(|b| ValueProof::Exact(t.bool_lit(!b)))
        .unwrap_or(ValueProof::Unproven);
    Info::Known(ValueFact::with_proof(t.bool(), proof))
}

fn fold_comparison<T: Types<Ty = Ty>>(t: &mut T, op: BinOp, a: &ValueFact, b: &ValueFact) -> Option<bool> {
    use BinOp::*;
    if let (Some(ai), Some(bi)) = (
        exact_int(t, a).or_else(|| t.as_int_singleton(&a.ty)),
        exact_int(t, b).or_else(|| t.as_int_singleton(&b.ty)),
    ) {
        return match op {
            Eq => Some(ai == bi),
            Neq => Some(ai != bi),
            Lt => Some(ai < bi),
            Le => Some(ai <= bi),
            Gt => Some(ai > bi),
            Ge => Some(ai >= bi),
            _ => None,
        };
    }
    if let (Some(af), Some(bf)) = (
        exact_float(t, a).or_else(|| t.as_float_singleton(&a.ty)),
        exact_float(t, b).or_else(|| t.as_float_singleton(&b.ty)),
    ) {
        return match op {
            Eq => Some(af == bf),
            Neq => Some(af != bf),
            Lt => Some(af < bf),
            Le => Some(af <= bf),
            Gt => Some(af > bf),
            Ge => Some(af >= bf),
            _ => None,
        };
    }
    if matches!(op, Eq | Neq) && t.is_singleton_lit(&a.ty) && t.is_singleton_lit(&b.ty) {
        let same = t.is_equivalent(&a.ty, &b.ty);
        return Some(matches!(op, Eq) == same);
    }
    None
}

fn bool_fact<T: Types<Ty = Ty>>(t: &mut T, value: &ValueFact) -> Option<bool> {
    if let Some(proof) = proof_ty(t, &value.proof)
        && let Some(b) = bool_from_ty(t, &proof)
    {
        return Some(b);
    }
    bool_from_ty(t, &value.ty)
}

fn exact_int<T: Types<Ty = Ty>>(t: &T, value: &ValueFact) -> Option<i64> {
    match &value.proof {
        ValueProof::Exact(ty) => t.as_int_singleton(ty),
        _ => None,
    }
}

fn exact_float<T: Types<Ty = Ty>>(t: &T, value: &ValueFact) -> Option<f64> {
    match &value.proof {
        ValueProof::Exact(ty) => t.as_float_singleton(ty),
        _ => None,
    }
}

fn invalid_operator_application(prim: &Prim, env: &Env) -> Option<TypeInferDiagnosticKind> {
    let Prim::BinOp(op @ (BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod), left, right) = prim else {
        return None;
    };
    let left = known_ty(*left, env)?;
    let right = known_ty(*right, env)?;
    Some(TypeInferDiagnosticKind::InvalidOperator { op: *op, left, right })
}

/// Look up a var's cell, defaulting to `Pending` for the not-yet-bound.
fn info_of(v: Var, env: &HashMap<Var, Info>) -> Info {
    env.get(&v).cloned().unwrap_or(Info::Pending)
}

fn arg_infos_of(args: &[Var], env: &HashMap<Var, Info>) -> Vec<Info> {
    args.iter().map(|a| info_of(*a, env)).collect()
}

/// A continuation receives the returned value first, then the captured locals.
fn cont_inputs_of(r: Info, captured: &[Var], env: &HashMap<Var, Info>) -> Vec<Info> {
    let mut inputs = vec![r];
    inputs.extend(captured.iter().map(|c| info_of(*c, env)));
    inputs
}

/// Infer the reachable activation graph from an entry point. The outcome
/// carries structured activation data and a coarse status; detailed activation
/// facts, diagnostics, and dead matcher arms are emitted through telemetry.
pub(crate) fn infer_from_entry<T: Types<Ty = Ty> + ClosureTypes + RenderTypes>(
    t: &mut T,
    module: &Module,
    fn_id: FnId,
    input_tys: &[Ty],
    tel: &dyn Telemetry,
) -> TypeInferOutcome {
    let (solver, _) = solve_from_entry(t, module, fn_id, input_tys);
    let outcome = solver.outcome();
    solver.emit_telemetry(t, tel);
    outcome
}

fn solve_from_entry<'m, T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &'m Module,
    fn_id: FnId,
    input_tys: &[Ty],
) -> (Solver<'m>, ActivationKey) {
    let inputs = input_tys.iter().cloned().map(Info::known).collect();
    let mut solver = Solver::new(module);
    let key = solver.seed(t, fn_id, inputs);
    solver.run(t);
    (solver, key)
}

#[cfg(test)]
mod type_infer_test;
