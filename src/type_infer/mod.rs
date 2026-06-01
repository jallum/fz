//! Type specialization — the inference engine
//! (`.agent/docs/type-specialization.md`).
//!
//! Built off to the side; the planner is transplanted onto it in fz-g58.65.6.
//! A closure is modeled as a function whose first parameters are its captures,
//! bound at creation to known-typed values — so applying a closure is just a
//! call to its body function with the captures prepended as leading arguments.
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
//! flows through the spec table, never through the walk. The recursion fixpoint
//! lives entirely in the worklist.
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
//! The engine is wired into the planner at fz-g58.65.6; until then only its own
//! tests exercise it, so the module is dead in non-test builds.
#![allow(dead_code)]

use crate::fz_ir::{BinOp, BlockId, Const, FnId, Module, Prim, Stmt, Term, UnOp, Var};
use crate::types::{ClosureTarget, ClosureTypes, MapKey, Nominals, Ty, Types};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

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
        if self == other {
            self.clone()
        } else {
            Self::Unproven
        }
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
            Self::StructFields { fields, .. } => {
                fields.get(field).cloned().unwrap_or(Self::Unproven)
            }
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

    /// Activation-cell update: `Pending` is the not-yet-initialized return
    /// estimate, `NoReturn` contributes no value, `Unknown` is live uncertainty,
    /// and two `Known`s join through the refinement-lattice widen.
    fn widen<T: Types<Ty = Ty>>(&self, t: &mut T, other: &Info) -> Info {
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

fn branch_join<T: Types<Ty = Ty>>(t: &mut T, a: Info, b: Info) -> Info {
    match (a, b) {
        (Info::Pending, x) | (x, Info::Pending) => x,
        (Info::Unknown, _) | (_, Info::Unknown) => Info::Unknown,
        (Info::NoReturn, x) | (x, Info::NoReturn) => x,
        (Info::Known(a), Info::Known(b)) => Info::Known(a.widen(t, &b)),
    }
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

/// The call contract for applying a closure value to `arg_tys`: its body
/// function plus the full input vector `captures ++ args`.
///
/// Captures lead because lowering splices a closure's captured slots ahead of
/// its call arguments. The captures come straight from the closure value's
/// type, so a captured closure is carried at its own concrete type — a nested
/// closure is a concrete capture, not a placeholder. `None` when `closure_ty`
/// is not a single known closure (a union of targets is resolved later).
pub(crate) fn closure_apply_contract<T: Types<Ty = Ty> + ClosureTypes>(
    t: &T,
    closure_ty: &Ty,
    arg_tys: &[Ty],
) -> Option<(FnId, Vec<Ty>)> {
    let info = t.closure_lit_parts(closure_ty)?;
    let mut inputs = info.captures;
    inputs.extend_from_slice(arg_tys);
    Some((info.target.into(), inputs))
}

/// One monomorphic activation of a function body under a concrete input tuple.
///
/// `FnId` remains the callable/body identity. The activation key is the
/// inference instance: the same `FnId` can be activated at `int` and `:ok`
/// without joining those callers' returns together.
#[derive(Clone, PartialEq, Eq, Hash)]
struct ActivationKey {
    fn_id: FnId,
    inputs: Vec<ValueKey>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct ValueKey {
    ty: Ty,
    proof: ValueProof,
}

impl ValueKey {
    fn into_info(self) -> Info {
        Info::Known(ValueFact::with_proof(self.ty, self.proof))
    }
}

/// One function activation's current return estimate.
struct Spec {
    inputs: Vec<Info>,
    ret: Info,
}

/// The monotone worklist solver. Drives every reachable `(fn, inputs)` to a
/// joint fixpoint of input- and return-type estimates.
struct Solver<'m> {
    module: &'m Module,
    specs: HashMap<ActivationKey, Spec>,
    /// `callee activation -> caller activations whose return estimate read
    /// callee's ret`. When a callee's ret ascends, its callers are re-enqueued.
    deps: HashMap<ActivationKey, HashSet<ActivationKey>>,
    queue: VecDeque<ActivationKey>,
    queued: HashSet<ActivationKey>,
}

impl<'m> Solver<'m> {
    fn new(module: &'m Module) -> Self {
        Self {
            module,
            specs: HashMap::new(),
            deps: HashMap::new(),
            queue: VecDeque::new(),
            queued: HashSet::new(),
        }
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
    fn seed(&mut self, fn_id: FnId, inputs: Vec<Info>) {
        let key = ActivationKey {
            fn_id,
            inputs: inputs
                .iter()
                .filter_map(|input| match input {
                    Info::Known(value) => Some(ValueKey {
                        ty: value.ty.clone(),
                        proof: value.proof.clone(),
                    }),
                    Info::Pending | Info::Unknown | Info::NoReturn => None,
                })
                .collect(),
        };
        assert_eq!(
            key.inputs.len(),
            inputs.len(),
            "entry activations must be seeded with known inputs"
        );
        self.specs.insert(
            key.clone(),
            Spec {
                inputs,
                ret: Info::Pending,
            },
        );
        self.enqueue(key);
    }

    /// `caller` applies `callee` to `args`. A protocol-dispatch stub is
    /// devirtualized on its receiver (first arg) type before the call; an
    /// ordinary callee passes straight through.
    fn call<T: Types<Ty = Ty>>(
        &mut self,
        t: &mut T,
        caller: &ActivationKey,
        callee: FnId,
        args: Vec<Info>,
    ) -> Info {
        if self.module.protocol_call_targets.contains_key(&callee) {
            // A protocol call resolves to a concrete impl chosen by the
            // receiver type. A pending receiver waits for a later fixpoint
            // iteration; a live unknown receiver remains unknown.
            match args.first() {
                Some(Info::Pending) => return Info::Pending,
                Some(Info::Unknown) => return Info::Unknown,
                Some(Info::NoReturn) | None => return Info::NoReturn,
                Some(Info::Known(_)) => {}
            }
            return match self.resolve_protocol(t, callee, &args) {
                Some(impl_fn) => self.call_direct(t, caller, impl_fn, args),
                None => Info::Unknown,
            };
        }
        self.call_direct(t, caller, callee, args)
    }

    /// Resolve a protocol-dispatch stub to the concrete implementation fn for
    /// its receiver type, mirroring `ir_planner::walk::protocol_dispatch_key`:
    /// the single impl whose target type the receiver is a subtype of. `None`
    /// when the receiver is not yet `Known` or no impl matches.
    fn resolve_protocol<T: Types<Ty = Ty>>(
        &self,
        t: &mut T,
        callee: FnId,
        args: &[Info],
    ) -> Option<FnId> {
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
                let target_ty = crate::frontend::protocols::impl_target_type(t, &fact.target);
                t.is_subtype(&receiver_ty, &target_ty)
            })
            .filter_map(|fact| {
                fact.callbacks
                    .get(&(target.callback.clone(), target.arity))
                    .cloned()
            })
            .collect();
        matches.sort();
        matches.dedup();
        let export = matches.into_iter().next()?;
        let fn_name = format!("{}.{}", export.module, export.name);
        self.module.fn_by_name(&fn_name).map(|f| f.id)
    }

    /// Record the dependency, widen the callee's inputs (scheduling it if they
    /// grew), and hand back the callee's current return estimate (`Pending` for
    /// a callee not yet processed).
    fn call_direct<T: Types<Ty = Ty>>(
        &mut self,
        t: &mut T,
        caller: &ActivationKey,
        callee: FnId,
        args: Vec<Info>,
    ) -> Info {
        let Some(key) = activation_key(t, callee, &args) else {
            return unresolved_inputs(&args);
        };
        self.deps
            .entry(key.clone())
            .or_default()
            .insert(caller.clone());
        if !self.specs.contains_key(&key) {
            self.specs.insert(
                key.clone(),
                Spec {
                    inputs: key
                        .inputs
                        .iter()
                        .cloned()
                        .map(ValueKey::into_info)
                        .collect(),
                    ret: Info::Pending,
                },
            );
            self.enqueue(key.clone());
        }
        self.specs
            .get(&key)
            .map(|s| s.ret.clone())
            .unwrap_or(Info::Pending)
    }

    /// Run to fixpoint: repeatedly re-derive each scheduled function's return
    /// type; when it ascends, re-schedule the callers that read it.
    /// The return type a declared `@spec` assigns `f` for its current input
    /// types: instantiate every arrow against the inputs and union the matching
    /// results. `None` when `f` has no declared spec, its inputs aren't all
    /// `Known`, or the spec matcher cannot prove a matching arrow yet. "No
    /// match" is not `none` here: this API cannot distinguish contradiction
    /// from underconstrained polymorphism, so the solver must keep the cell
    /// `Unknown` until body proof or a stricter diagnostic pass proves
    /// impossibility.
    fn declared_spec_ret<T: Types<Ty = Ty> + ClosureTypes>(
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
                Info::Pending | Info::Unknown | Info::NoReturn => return None,
            }
        }
        let matches = spec_set.matching_arrows(t, &arg_tys);
        if matches.is_empty() {
            return None;
        }
        let mut ret = t.none();
        for m in matches {
            ret = t.union(ret, m.result);
        }
        Some(Info::known(ret))
    }

    fn run<T: Types<Ty = Ty> + ClosureTypes>(&mut self, t: &mut T) {
        while let Some(key) = self.pop() {
            let inputs = self.specs[&key].inputs.clone();
            let body_ret = self.walk_fn(t, &key, &inputs);
            // A declared `@spec` is a backstop for a body the engine cannot
            // infer (e.g. an extern-forwarding builtin like `dbg`/`Kernel.+`):
            // only when body inference is `Unknown` do we fall back to the spec
            // instantiated against the inputs. An inferable body keeps its
            // inferred (usually tighter) type, so the spec never blunts a
            // function the engine can read for itself — and a spec the
            // instantiator can't match (e.g. a protocol-typed param) can't
            // turn a precise body into `none`.
            let ret = match body_ret {
                Info::Unknown => self
                    .declared_spec_ret(t, key.fn_id, &inputs)
                    .unwrap_or(Info::Unknown),
                known => known,
            };
            let old = self.specs[&key].ret.clone();
            let new = old.widen(t, &ret);
            if !new.equiv(t, &old) {
                self.specs.get_mut(&key).unwrap().ret = new;
                if let Some(callers) = self.deps.get(&key).cloned() {
                    for c in callers {
                        self.enqueue(c);
                    }
                }
            }
        }
    }

    /// The return estimate `f` hands to its continuation, given its inputs.
    fn walk_fn<T: Types<Ty = Ty> + ClosureTypes>(
        &mut self,
        t: &mut T,
        key: &ActivationKey,
        inputs: &[Info],
    ) -> Info {
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
        for Stmt::Let(v, prim) in &block.stmts {
            let info = self.type_prim(t, prim, env);
            env.insert(*v, info);
            if let Some(fact) = predicate_fact(prim) {
                predicates.insert(*v, fact);
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
                cond,
                then_b,
                else_b,
                ..
            } => {
                let (then_b, else_b) = (*then_b, *else_b);
                let fact = predicates.get(cond).cloned();
                let truth = bool_truth(t, &info_of(*cond, env)).or_else(|| {
                    fact.as_ref()
                        .and_then(|p| predicate_truth(t, module, p, env))
                });
                let (then_env, else_env) = if let Some(fact) = fact.as_ref() {
                    (
                        narrow_predicate(t, env, fact, true),
                        narrow_predicate(t, env, fact, false),
                    )
                } else {
                    (Some(env.clone()), Some(env.clone()))
                };
                match truth {
                    Some(true) => self.walk_branch(t, key, then_b, then_env, predicates, visited),
                    Some(false) => self.walk_branch(t, key, else_b, else_env, predicates, visited),
                    None => {
                        let a = self.walk_branch(t, key, then_b, then_env, predicates, visited);
                        let b = self.walk_branch(t, key, else_b, else_env, predicates, visited);
                        branch_join(t, a, b)
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
                let r = self.call(t, key, *callee, arg_infos);
                if matches!(r, Info::NoReturn) {
                    return Info::NoReturn;
                }
                let cont_inputs = cont_inputs_of(r, &continuation.captured, env);
                self.call(t, key, continuation.fn_id, cont_inputs)
            }
            // A tail call forwards our own continuation, so its result is ours.
            Term::TailCall { callee, args, .. } => {
                let arg_infos = arg_infos_of(args, env);
                self.call(t, key, *callee, arg_infos)
            }
            Term::CallClosure {
                closure,
                args,
                continuation,
                ..
            } => {
                let arg_infos = arg_infos_of(args, env);
                let r = self.apply_closure(t, key, *closure, arg_infos, env);
                if matches!(r, Info::NoReturn) {
                    return Info::NoReturn;
                }
                let cont_inputs = cont_inputs_of(r, &continuation.captured, env);
                self.call(t, key, continuation.fn_id, cont_inputs)
            }
            Term::TailCallClosure { closure, args, .. } => {
                let arg_infos = arg_infos_of(args, env);
                self.apply_closure(t, key, *closure, arg_infos, env)
            }
            // Receive shapes are out of corpus scope (fz-g58.65.5).
            _ => Info::Unknown,
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

    /// Resolve a closure application to a call on its body fn (captures ++
    /// args). `Pending` waits; `Unknown` stays `Unknown`; a known value that
    /// cannot be resolved to one closure target is still not proven callable, so
    /// it also stays `Unknown` until a final boundary decides how to erase it.
    fn apply_closure<T: Types<Ty = Ty> + ClosureTypes>(
        &mut self,
        t: &mut T,
        caller: &ActivationKey,
        closure: Var,
        arg_infos: Vec<Info>,
        env: &Env,
    ) -> Info {
        let clo = env.get(&closure).cloned().unwrap_or(Info::Pending);
        let clo_ty = match clo {
            Info::Pending => return Info::Pending,
            Info::Unknown => return Info::Unknown,
            Info::NoReturn => return Info::NoReturn,
            Info::Known(value) => value.ty,
        };
        match t.closure_lit_parts(&clo_ty) {
            Some(parts) => {
                let target: FnId = parts.target.into();
                let mut inputs: Vec<Info> = parts.captures.into_iter().map(Info::known).collect();
                inputs.extend(arg_infos);
                self.call(t, caller, target, inputs)
            }
            // Couldn't resolve a single closure target ⇒ undetermined, not
            // `any` (which would assert "dynamic" as a fact). `any` is earned.
            None => Info::Unknown,
        }
    }

    fn type_prim<T: Types<Ty = Ty> + ClosureTypes>(
        &mut self,
        t: &mut T,
        prim: &Prim,
        env: &Env,
    ) -> Info {
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
                    let name = module
                        .atom_names
                        .get(*id as usize)
                        .map(String::as_str)
                        .unwrap_or("");
                    Info::known(t.atom_lit(name))
                }
            },
            Prim::BinOp(op, a, b) => {
                let lt = info_of(*a, env);
                let rt = info_of(*b, env);
                match op {
                    // `+`/`-`/`*` apply the four-clause numeric signature
                    // strictly (see `numeric_binop`): in-domain operands yield
                    // int/float per clause, an operand outside `int|float`
                    // yields `none` (the diagnostic seam), and `Unknown` stays
                    // `Unknown`.
                    BinOp::Add | BinOp::Sub | BinOp::Mul => numeric_binop(t, lt, rt),
                    // TODO(operator specs): `/` is float-only and `div`/`rem`
                    // are integer-only — give them their own clause sets. Until
                    // then they ride the operands' refinement join.
                    BinOp::Div | BinOp::Mod => match (lt, rt) {
                        (Info::Known(a), Info::Known(b)) => {
                            Info::known(t.refine_widen(&a.ty, &b.ty))
                        }
                        (Info::Unknown, _) | (_, Info::Unknown) => Info::Unknown,
                        (Info::NoReturn, _) | (_, Info::NoReturn) => Info::NoReturn,
                        (Info::Pending, _) | (_, Info::Pending) => Info::Pending,
                    },
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
            Prim::IsEmptyList(_) | Prim::IsListCons(_) | Prim::TypeTest(_, _) => {
                Info::known(t.bool())
            }
            Prim::ListHead(v) => {
                info_of(*v, env).map_known(|value| value.map_ty(|ty| t.list_element_type(&ty)))
            }
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
            Prim::TupleField(v, i) => {
                info_of(*v, env).map_known(|value| value.tuple_field(t, *i as usize))
            }
            Prim::StructField(v, field) => type_struct_field(t, module, *v, field, env),
            Prim::MakeMap(entries) => type_make_map(t, entries, env),
            Prim::MapUpdate(base, entries) => type_map_update(t, *base, entries, env),
            Prim::MapGet(map, key) => type_map_get(t, *map, *key, env, false),
            Prim::MatcherMapGet(map, key) => type_map_get(t, *map, *key, env, true),
            Prim::IsMatcherMapMiss(v) => is_matcher_map_miss(t, info_of(*v, env)),
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
            // Prims not yet modeled (bitstrings, externs) are
            // `Unknown` — undetermined, not `any`. `any` is earned, never
            // defaulted during inference; a final boundary may erase a residual
            // `Unknown` to `any`, but the solver keeps the uncertainty visible.
            _ => Info::Unknown,
        }
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

fn predicate_truth<T: Types<Ty = Ty>>(
    t: &mut T,
    module: &Module,
    pred: &PredicateFact,
    env: &Env,
) -> Option<bool> {
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

fn eq_truth<T: Types<Ty = Ty>>(
    t: &mut T,
    module: &Module,
    a: Var,
    b: Var,
    env: &Env,
) -> Option<bool> {
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

fn narrow_predicate<T: Types<Ty = Ty>>(
    t: &mut T,
    env: &Env,
    pred: &PredicateFact,
    truth: bool,
) -> Option<Env> {
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

fn refine_against<T: Types<Ty = Ty>>(
    t: &mut T,
    env: &mut Env,
    subject: Var,
    domain: &Ty,
    truth: bool,
) -> bool {
    let Some(current) = known_value(subject, env) else {
        return true;
    };
    if truth {
        if !proof_fits(t, &current.proof, domain) {
            return false;
        }
    } else if let Some(proof) = proof_ty(t, &current.proof) {
        if t.is_subtype(&proof, domain) {
            return false;
        }
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
            Some(crate::frontend::protocols::struct_impl_target_type(
                t,
                module.rsplit('.').next().unwrap_or(module),
            ))
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

fn type_make_struct<T: Types<Ty = Ty>>(
    t: &mut T,
    module: &str,
    fields: &[(String, Var)],
    env: &Env,
) -> Info {
    let mut proof_fields = BTreeMap::new();
    for (field, value) in fields {
        let value = match value_info(*value, env) {
            Ok(value) => value,
            Err(info) => return info,
        };
        proof_fields.insert(field.clone(), value.proof);
    }
    let ty = crate::frontend::protocols::struct_impl_target_type(
        t,
        module.rsplit('.').next().unwrap_or(module),
    );
    Info::known_with_proof(
        ty,
        ValueProof::StructFields {
            module: module.to_string(),
            fields: proof_fields,
        },
    )
}

fn type_struct_field<T: Types<Ty = Ty>>(
    t: &mut T,
    module: &Module,
    subject: Var,
    field: &str,
    env: &Env,
) -> Info {
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

fn struct_field_ty<T: Types<Ty = Ty>>(
    t: &mut T,
    module: &Module,
    subject: &Ty,
    field: &str,
) -> Option<Ty> {
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

fn type_map_update<T: Types<Ty = Ty>>(
    t: &mut T,
    base: Var,
    entries: &[(Var, Var)],
    env: &Env,
) -> Info {
    let mut current = match value_info(base, env) {
        Ok(current) => current,
        Err(info) => return info,
    };
    let mut proof_fields = match std::mem::replace(&mut current.proof, ValueProof::Unproven) {
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

fn type_map_get<T: Types<Ty = Ty>>(
    t: &mut T,
    map: Var,
    key: Var,
    env: &Env,
    matcher: bool,
) -> Info {
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

fn fold_comparison<T: Types<Ty = Ty>>(
    t: &mut T,
    op: BinOp,
    a: &ValueFact,
    b: &ValueFact,
) -> Option<bool> {
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

/// Whether `x`'s value set intersects `dom` (i.e. `x ⊓ dom` is inhabited).
fn ty_inhabits<T: Types<Ty = Ty>>(t: &mut T, x: &Ty, dom: &Ty) -> bool {
    let none = t.none();
    let meet = t.intersect(x.clone(), dom.clone());
    !t.is_equivalent(&meet, &none)
}

/// Apply the four-clause numeric signature of `+`/`-`/`*` to operand infos:
///
/// ```text
/// (int, int) -> int | (int, float) -> float | (float, int) -> float | (float, float) -> float
/// ```
///
/// `Unknown` operand ⇒ `Unknown` (undecided). Both operands in-domain
/// (consistent-subtype of `int|float`, so a dynamic `any` is permitted) ⇒ the
/// union of the returns of the clauses the operands hit: `int` only when both
/// can be `int`, `float` as soon as either can be. An operand outside the
/// domain (e.g. a tuple) matches no clause ⇒ `none` — the seam a diagnostic
/// hangs off, never laundered into a partial result.
fn numeric_binop<T: Types<Ty = Ty>>(t: &mut T, lt: Info, rt: Info) -> Info {
    let (a, b) = match (lt, rt) {
        (Info::Known(a), Info::Known(b)) => (a, b),
        (a, b) => return non_known_pair(a, b),
    };
    let int = t.int();
    let float = t.float();
    let any = t.any();
    let num = t.union(int.clone(), float.clone());

    let a_dynamic = t.is_equivalent(&a.ty, &any);
    let b_dynamic = t.is_equivalent(&b.ty, &any);
    let a_ok = a_dynamic || t.is_subtype(&a.ty, &num);
    let b_ok = b_dynamic || t.is_subtype(&b.ty, &num);
    if !a_ok || !b_ok {
        return Info::known(t.none());
    }

    let a_int = a_dynamic || ty_inhabits(t, &a.ty, &int);
    let a_float = a_dynamic || ty_inhabits(t, &a.ty, &float);
    let b_int = b_dynamic || ty_inhabits(t, &b.ty, &int);
    let b_float = b_dynamic || ty_inhabits(t, &b.ty, &float);

    let mut result = t.none();
    if a_int && b_int {
        result = t.union(result, int);
    }
    if a_float || b_float {
        result = t.union(result, float);
    }
    Info::known(result)
}

fn activation_key<T: Types<Ty = Ty>>(
    t: &mut T,
    fn_id: FnId,
    inputs: &[Info],
) -> Option<ActivationKey> {
    let mut key_inputs = Vec::with_capacity(inputs.len());
    for input in inputs {
        match input {
            Info::Known(value) => key_inputs.push(ValueKey {
                ty: t.widen_for_recursive_spec_key(&value.ty),
                proof: value.proof.clone(),
            }),
            Info::Pending | Info::Unknown | Info::NoReturn => return None,
        }
    }
    Some(ActivationKey {
        fn_id,
        inputs: key_inputs,
    })
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

/// Infer a function's return type from its body, given its input types,
/// running the worklist to a fixpoint. This helper is a type-returning boundary:
/// if the engine still has no return proof, expose `any` rather than inventing
/// `none`. `none` is only returned when inference proved the value uninhabited.
pub(crate) fn infer_return<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    fn_id: FnId,
    input_tys: &[Ty],
) -> Ty {
    let inputs = input_tys.iter().cloned().map(Info::known).collect();
    let mut solver = Solver::new(module);
    solver.seed(fn_id, inputs);
    solver.run(t);
    let key = ActivationKey {
        fn_id,
        inputs: input_tys
            .iter()
            .cloned()
            .map(|ty| ValueKey {
                ty,
                proof: ValueProof::Unproven,
            })
            .collect(),
    };
    match solver.specs.get(&key).map(|s| s.ret.clone()) {
        Some(Info::Known(value)) => value.ty,
        _ => t.any(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{FnBuilder, ModuleBuilder};
    use crate::telemetry::{ConfiguredTelemetry, Handler};
    use crate::types::{ClosureTarget, ConcreteTypes};
    use std::cell::RefCell;
    use std::panic::AssertUnwindSafe;
    use std::rc::Rc;

    /// Captures the `Module` from the `fz.frontend.lowered` telemetry event —
    /// the exact IR the planner consumes, emitted by the production frontend
    /// just before planning.
    struct LoweredCapture(Rc<RefCell<Option<Module>>>);

    impl Handler for LoweredCapture {
        fn handle(&self, ev: &crate::telemetry::Event<'_, '_, '_>) {
            if let ["fz", "frontend", "lowered"] = ev.name {
                if let Some(module) = ev
                    .metadata
                    .get("module")
                    .and_then(|v| v.downcast_ref::<Module>())
                {
                    *self.0.borrow_mut() = Some(module.clone());
                }
            }
        }
    }

    /// Lower a source program to its IR `Module` via the production frontend,
    /// snapshotting the module from telemetry at the lowering stage. The corpus
    /// runs the *whole* normal flow — including the old planner, which diverges
    /// (4096 cap) on the nested-closure programs. The lowered event fires before
    /// planning, so the snapshot lands first; the later panic is caught and
    /// discarded. We process the captured IR with our own engine.
    fn lower(src: &str) -> Module {
        let captured = Rc::new(RefCell::new(None));
        let tel = ConfiguredTelemetry::new();
        tel.attach(&["fz"], Box::new(LoweredCapture(captured.clone())));

        let prev_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let _ = std::panic::catch_unwind(AssertUnwindSafe(|| {
            let mut t = ConcreteTypes;
            let providers = crate::modules::pipeline::ProviderInputs::new(
                crate::modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string(),
                Vec::new(),
            );
            let _ = crate::modules::pipeline::compile_source_with_providers(
                &mut t,
                src.to_string(),
                "spike.fz".to_string(),
                &providers,
                &tel,
            );
        }));
        std::panic::set_hook(prev_hook);

        captured
            .borrow_mut()
            .take()
            .expect("frontend emitted no lowered module")
    }

    /// Drive the solver from `main` (no args) and read back the return type the
    /// engine settled for `fn_name`. Seeding `main` lets the engine discover
    /// every call's real argument types — including the closures `main`
    /// constructs — exactly as the planner will.
    fn infer_fn_via_main(module: &Module, fn_name: &str) -> Ty {
        let mut t = ConcreteTypes;
        // The entry point is `main` for a bare script, or `<Module>.main` when
        // the program wraps it in a `defmodule` (e.g. the named-fn-ref spike).
        let main_id = module
            .fns
            .iter()
            .find(|f| f.name == "main" || f.name.ends_with(".main"))
            .expect("main fn")
            .id;
        let mut solver = Solver::new(module);
        solver.seed(main_id, Vec::new());
        solver.run(&mut t);
        // A library fn name can carry several arities (e.g. `Enum.reduce/2` and
        // `Enum.reduce/3`); only the variant the program actually called is
        // reached and specialized. Read back that reached variant's settled
        // return — not the first same-named fn, which may be an unreached arity.
        module
            .fns
            .iter()
            .filter(|f| f.name == fn_name)
            .flat_map(|f| {
                solver.specs.iter().filter_map(move |(key, spec)| {
                    if key.fn_id == f.id {
                        Some(spec.ret.clone())
                    } else {
                        None
                    }
                })
            })
            .fold(None, |acc, ret| match (acc, ret) {
                (None, Info::Known(value)) => Some(value.ty),
                (Some(prev), Info::Known(value)) => Some(t.union(prev, value.ty)),
                (acc, Info::Pending | Info::Unknown | Info::NoReturn) => acc,
            })
            .unwrap_or_else(|| t.none())
    }

    /// `Pending` and `Unknown` are inference scaffolding, not answers. At the
    /// fixpoint of a supported program every *reached* function has either a
    /// `Known` return or `NoReturn`; a surviving pending/unknown return means a
    /// dependency never settled or a live construct is still unmodeled.
    #[test]
    fn fixpoint_leaves_no_reached_fn_unknown() {
        for (name, src) in [
            ("add", include_str!("../../spike/add.fz")),
            ("fold_tail", include_str!("../../spike/fold_tail.fz")),
            ("fold_nontail", include_str!("../../spike/fold_nontail.fz")),
            (
                "fold_capture_int",
                include_str!("../../spike/fold_capture_int.fz"),
            ),
            (
                "fold_capture_closure",
                include_str!("../../spike/fold_capture_closure.fz"),
            ),
            (
                "fold_state_machine",
                include_str!("../../spike/fold_state_machine.fz"),
            ),
        ] {
            let module = lower(src);
            let mut t = ConcreteTypes;
            let main_id = module.fn_by_name("main").unwrap().id;
            let mut solver = Solver::new(&module);
            solver.seed(main_id, Vec::new());
            solver.run(&mut t);
            let unsettled: Vec<&str> = solver
                .specs
                .iter()
                .filter(|(_, s)| matches!(s.ret, Info::Pending | Info::Unknown))
                .map(|(key, _)| module.fn_by_id(key.fn_id).name.as_str())
                .collect();
            assert!(
                unsettled.is_empty(),
                "{name}: reached fns left Pending/Unknown at fixpoint: {unsettled:?}"
            );
        }
    }

    /// Compile a program to its **LTO-linked** IR `Module` via the production
    /// pipeline — the runtime graph where `Enum.reduce`, `List.reduce`,
    /// `Enumerable.List.reduce`, and the `__protocol__.*` dispatch stubs are all
    /// local fns. Mirrors `ir_codegen::tests::runtime_graph_module`: the runtime
    /// library is embedded, so an empty provider list still links it.
    fn linked(src: &str) -> Module {
        use crate::modules::pipeline::{
            CompileMode, ProviderInputs, checked_module_for_mode, compile_source_with_providers,
            prepare_execution_graph,
        };
        let mut t = ConcreteTypes;
        let tel = crate::telemetry::NullTelemetry;
        let providers = ProviderInputs::new(
            crate::modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string(),
            Vec::new(),
        );
        let frontend = compile_source_with_providers(
            &mut t,
            src.to_string(),
            "spike.fz".to_string(),
            &providers,
            &tel,
        )
        .unwrap_or_else(|e| panic!("frontend: {e}"));
        let checked = checked_module_for_mode(&mut t, frontend, &tel, CompileMode::Normal)
            .unwrap_or_else(|e| panic!("checked: {e}"));
        let graph = prepare_execution_graph(&mut t, checked, &providers, &tel, CompileMode::Normal)
            .unwrap_or_else(|e| panic!("execution graph: {e}"));
        graph.module
    }

    /// The real runtime graph: `Enum.reduce` dispatches through the
    /// `Enumerable` protocol stub, which the engine devirtualizes on the
    /// receiver type (`list(int)` -> the `List` impl). The protocol-resolved
    /// `Enumerable.List.reduce` settles to its concrete `{:done,_}|{:halted,_}`
    /// shape, and `Enum.reduce` unwraps it to `int` — no `none`. This is the
    /// fold_state_machine shape plus one protocol hop, end to end.
    /// Protocol dispatch generalizes across callbacks and impls on the runtime
    /// graph. The user-facing `Enum.*` result settles to a concrete `int` (no
    /// `none`) for: a `List` reduce with an inline lambda; a `List` reduce with
    /// a well-typed named-fn reference (`&Main.reducer/2`); and `Enum.count`
    /// (the `count` callback, not `reduce`).
    ///
    #[test]
    fn runtime_graph_enum_ops_settle_to_int() {
        let cases = [
            (
                "list lambda",
                "Enum.reduce",
                include_str!("../../spike/enum_reduce.fz"),
            ),
            (
                "named-fn ref",
                "Enum.reduce",
                include_str!("../../spike/enum_reduce_named_ref_ok.fz"),
            ),
            (
                "count",
                "Enum.count",
                include_str!("../../spike/enum_count.fz"),
            ),
            (
                "range reduce",
                "Enum.reduce",
                include_str!("../../spike/enum_reduce_range.fz"),
            ),
        ];
        let mut t = ConcreteTypes;
        let int = t.int();
        for (label, entry, src) in cases {
            let module = linked(src);
            let ret = infer_fn_via_main(&module, entry);
            assert!(
                t.is_equivalent(&ret, &int),
                "{label}: {entry} should settle to int, got {ret:?}"
            );
        }
    }

    #[test]
    fn enum_reduce_runtime_graph_settles() {
        let module = linked(include_str!("../../spike/enum_reduce.fz"));
        let mut t = ConcreteTypes;
        let int = t.int();

        let reduce_ret = infer_fn_via_main(&module, "Enum.reduce");
        assert!(
            t.is_equivalent(&reduce_ret, &int),
            "Enum.reduce([1,2,3],0,+) should settle to int, got {reduce_ret:?}"
        );

        // The reducer returns an `int`, so the loop control is proved `:cont`
        // all the way through; `:halted` and `:suspended` are dead for this
        // callsite, not part of the settled callback result.
        let done = {
            let a = t.atom_lit("done");
            let i = t.int();
            t.tuple(&[a, i])
        };
        let list_reduce_ret = infer_fn_via_main(&module, "Enumerable.List.reduce");
        assert!(
            t.is_equivalent(&list_reduce_ret, &done),
            "Enumerable.List.reduce should settle to {{:done,int}} for an int-returning reducer, got {list_reduce_ret:?}"
        );
    }

    #[test]
    fn add_infers_int_via_harness() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/add.fz"));
        let add_id = module.fn_by_name("add").expect("add fn").id;
        let int = t.int();
        let ret = infer_return(&mut t, &module, add_id, &[int.clone(), int.clone()]);
        assert!(
            t.is_equivalent(&ret, &int),
            "add(int, int) should infer int"
        );
    }

    #[test]
    fn infer_return_erases_residual_unknown_to_any_at_boundary() {
        let mut b = FnBuilder::new(FnId(0), "unknown_expr");
        let entry = b.block(vec![]);
        let value = b.let_(entry, Prim::MakeBitstring(vec![]));
        b.set_terminator(entry, Term::Return(value));

        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let module = mb.build();

        let mut t = ConcreteTypes;
        let ret = infer_return(&mut t, &module, FnId(0), &[]);
        let any = t.any();
        assert!(
            t.is_equivalent(&ret, &any),
            "a live value the spike cannot prove should erase to any at the Ty boundary, got {ret:?}"
        );
    }

    #[test]
    fn live_unknown_branch_survives_control_join_to_boundary() {
        let mut b = FnBuilder::new(FnId(0), "branch_unknown");
        let cond = b.fresh_var();
        let entry = b.block(vec![cond]);
        let unknown_b = b.block(vec![]);
        let known_b = b.block(vec![]);
        let unknown = b.let_(unknown_b, Prim::MakeBitstring(vec![]));
        b.set_terminator(unknown_b, Term::Return(unknown));
        let one = b.let_(known_b, Prim::Const(Const::Int(1)));
        b.set_terminator(known_b, Term::Return(one));
        b.set_terminator(entry, Term::if_user(cond, unknown_b, known_b));

        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let module = mb.build();

        let mut t = ConcreteTypes;
        let bool_ty = t.bool();
        let ret = infer_return(&mut t, &module, FnId(0), &[bool_ty]);
        let any = t.any();
        assert!(
            t.is_equivalent(&ret, &any),
            "a live unknown arm must not be displaced by a known sibling arm, got {ret:?}"
        );
    }

    #[test]
    fn halt_branch_contributes_no_return_value_to_control_join() {
        let mut b = FnBuilder::new(FnId(0), "branch_halt");
        let cond = b.fresh_var();
        let entry = b.block(vec![cond]);
        let halt_b = b.block(vec![]);
        let return_b = b.block(vec![]);
        let halted = b.let_(halt_b, Prim::Const(Const::Int(1)));
        b.set_terminator(halt_b, Term::Halt(halted));
        let returned = b.let_(return_b, Prim::Const(Const::Int(2)));
        b.set_terminator(return_b, Term::Return(returned));
        b.set_terminator(entry, Term::if_user(cond, halt_b, return_b));

        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let module = mb.build();

        let mut t = ConcreteTypes;
        let bool_ty = t.bool();
        let ret = infer_return(&mut t, &module, FnId(0), &[bool_ty]);
        let int = t.int();
        assert!(
            t.is_equivalent(&ret, &int),
            "a halt arm contributes no function return value; sibling return should remain int, got {ret:?}"
        );
    }

    #[test]
    fn direct_calls_instantiate_polymorphic_identity_per_callsite() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/poly_id.fz"));
        let ret = infer_fn_via_main(&module, "main");
        let expected = {
            let int = t.int();
            let ok = t.atom_lit("ok");
            t.tuple(&[int, ok])
        };
        assert!(
            t.is_equivalent(&ret, &expected),
            "main should keep id(1) and id(:ok) as separate instantiations, got {ret:?}"
        );
    }

    #[test]
    fn named_refs_instantiate_polymorphic_identity_per_callsite() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/poly_named_ref.fz"));
        let ret = infer_fn_via_main(&module, "main");
        let expected = {
            let int = t.int();
            let ok = t.atom_lit("ok");
            t.tuple(&[int, ok])
        };
        assert!(
            t.is_equivalent(&ret, &expected),
            "&id/1 should create separate activation reads for int and :ok calls, got {ret:?}"
        );
    }

    #[test]
    fn named_refs_drive_pattern_dispatch_per_activation() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/poly_named_ref_pattern.fz"));
        let ret = infer_fn_via_main(&module, "main");
        let expected = {
            let one = t.atom_lit("one");
            let two = t.atom_lit("two");
            t.tuple(&[one, two])
        };
        assert!(
            t.is_equivalent(&ret, &expected),
            "&pick/1 should feed each call argument into matcher proof and keep the catch-all dead, got {ret:?}"
        );
    }

    #[test]
    fn captured_closure_refs_instantiate_by_capture_and_arg_facts() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/poly_capture_ref.fz"));
        let ret = infer_fn_via_main(&module, "main");
        let expected = {
            let ok = t.atom_lit("ok");
            let int = t.int();
            let right = t.atom_lit("right");
            let int_pair = t.tuple(&[ok.clone(), int]);
            let atom_pair = t.tuple(&[ok, right]);
            t.tuple(&[int_pair, atom_pair])
        };
        assert!(
            t.is_equivalent(&ret, &expected),
            "captured closure should prepend capture facts inside inference while keeping call arity explicit, got {ret:?}"
        );
    }

    #[test]
    fn direct_calls_specialize_atom_pattern_dispatch_by_input() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/match_atom_partition.fz"));
        let ret = infer_fn_via_main(&module, "main");
        let expected = {
            let one = t.atom_lit("one");
            let two = t.atom_lit("two");
            t.tuple(&[one, two])
        };
        assert!(
            t.is_equivalent(&ret, &expected),
            "main should select distinct matcher leaves for :left and :right activations, got {ret:?}"
        );
    }

    #[test]
    fn direct_calls_specialize_list_pattern_dispatch_by_shape() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/match_list_partition.fz"));
        let ret = infer_fn_via_main(&module, "main");
        let expected = {
            let empty = t.atom_lit("empty");
            let cons = t.atom_lit("cons");
            t.tuple(&[empty, cons])
        };
        assert!(
            t.is_equivalent(&ret, &expected),
            "main should select empty-list and cons matcher leaves per activation, got {ret:?}"
        );
    }

    #[test]
    fn list_pattern_binding_flows_into_selected_leaf() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/match_list_binding.fz"));
        let ret = infer_fn_via_main(&module, "main");
        let expected = {
            let empty = t.atom_lit("empty");
            let int = t.int();
            t.tuple(&[empty, int])
        };
        assert!(
            t.is_equivalent(&ret, &expected),
            "cons leaf should return the matched head type, got {ret:?}"
        );
    }

    #[test]
    fn tuple_pattern_binding_flows_into_selected_leaf() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/match_tuple_binding.fz"));
        let ret = infer_fn_via_main(&module, "main");
        let expected = {
            let int = t.int();
            let error = t.atom_lit("error");
            t.tuple(&[int, error])
        };
        assert!(
            t.is_equivalent(&ret, &expected),
            "tuple leaf should return the matched payload type, got {ret:?}"
        );
    }

    #[test]
    fn nested_pattern_binding_flows_into_selected_leaf() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/match_nested_binding.fz"));
        let ret = infer_fn_via_main(&module, "main");
        let expected = {
            let int = t.int();
            let error = t.atom_lit("error");
            t.tuple(&[int, error])
        };
        assert!(
            t.is_equivalent(&ret, &expected),
            "nested tuple/list leaf should return the matched head type, got {ret:?}"
        );
    }

    #[test]
    fn nested_pattern_partition_selects_sibling_leaves() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/match_nested_partition.fz"));
        let ret = infer_fn_via_main(&module, "main");
        let expected = {
            let empty = t.atom_lit("empty");
            let int = t.int();
            let error = t.atom_lit("error");
            t.tuple(&[empty, int, error])
        };
        assert!(
            t.is_equivalent(&ret, &expected),
            "nested tuple/list partition should select empty, cons, and error leaves, got {ret:?}"
        );
    }

    #[test]
    fn tuple_tag_partition_selects_matching_payloads() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/match_tuple_tag_partition.fz"));
        let ret = infer_fn_via_main(&module, "main");
        let expected = {
            let int = t.int();
            let bad = t.atom_lit("bad");
            t.tuple(&[int, bad])
        };
        assert!(
            t.is_equivalent(&ret, &expected),
            "same-arity tuple partition should select payloads by tag, got {ret:?}"
        );
    }

    #[test]
    fn tuple_arity_partition_selects_matching_shape() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/match_tuple_arity_partition.fz"));
        let ret = infer_fn_via_main(&module, "main");
        let expected = {
            let int = t.int();
            let pair = t.tuple(&[int.clone(), int.clone()]);
            let other = t.atom_lit("other");
            t.tuple(&[int, pair, other])
        };
        assert!(
            t.is_equivalent(&ret, &expected),
            "tuple arity partition should select each matching shape, got {ret:?}"
        );
    }

    #[test]
    fn guard_partition_selects_refined_clause() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/match_guard_partition.fz"));
        let ret = infer_fn_via_main(&module, "main");
        let expected = {
            let int = t.int();
            let fallback = t.atom_lit("fallback");
            t.tuple(&[int, fallback])
        };
        assert!(
            t.is_equivalent(&ret, &expected),
            "guarded tuple clause should select by guard proof, got {ret:?}"
        );
    }

    #[test]
    fn map_pattern_binding_flows_into_selected_leaf() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/match_map_binding.fz"));
        let ret = infer_fn_via_main(&module, "main");
        let expected = {
            let int = t.int();
            let none = t.atom_lit("none");
            t.tuple(&[int, none])
        };
        assert!(
            t.is_equivalent(&ret, &expected),
            "map leaf should bind the matched key value without reaching the catch-all, got {ret:?}"
        );
    }

    /// Every corpus fold settles `myreduce` to `int` — including the two the
    /// old planner ran to the 4096 visit cap (`fold_capture_closure`,
    /// `fold_state_machine`). `int` is `number` in the simplified spike lattice
    /// (`1 -> integer -> any`).
    #[test]
    fn corpus_folds_settle_myreduce_to_int() {
        let corpus = [
            ("fold_tail", include_str!("../../spike/fold_tail.fz")),
            ("fold_nontail", include_str!("../../spike/fold_nontail.fz")),
            (
                "fold_capture_int",
                include_str!("../../spike/fold_capture_int.fz"),
            ),
            (
                "fold_capture_closure",
                include_str!("../../spike/fold_capture_closure.fz"),
            ),
            (
                "fold_state_machine",
                include_str!("../../spike/fold_state_machine.fz"),
            ),
        ];
        let mut t = ConcreteTypes;
        let int = t.int();
        for (name, src) in corpus {
            let module = lower(src);
            let ret = infer_fn_via_main(&module, "myreduce");
            assert!(
                t.is_equivalent(&ret, &int),
                "{name}: myreduce should settle to int, got {ret:?}"
            );
        }
    }

    #[test]
    fn closure_apply_prepends_captures_as_leading_params() {
        // A closure over fn7 capturing one int, applied to (int, int), is a call
        // to fn7 with inputs [int] ++ [int, int].
        let mut t = ConcreteTypes;
        let cap = t.int();
        let clo = t.closure_lit(ClosureTarget(7), vec![cap], 2);
        let a = t.int();
        let b = t.int();
        let (target, inputs) =
            closure_apply_contract(&t, &clo, &[a, b]).expect("singleton closure");
        assert_eq!(target, FnId(7));
        assert_eq!(inputs.len(), 3, "captures ++ args");
    }

    #[test]
    fn captured_closure_is_carried_concretely() {
        // W captures U. Applying W must surface U as a concrete leading input —
        // the nested-closure case the old planner could not settle.
        let mut t = ConcreteTypes;
        let inner = t.closure_lit(ClosureTarget(9), vec![], 2);
        let outer = t.closure_lit(ClosureTarget(8), vec![inner], 2);
        let a = t.int();
        let b = t.int();
        let (target, inputs) =
            closure_apply_contract(&t, &outer, &[a, b]).expect("singleton closure");
        assert_eq!(target, FnId(8));
        let captured = t
            .closure_lit_parts(&inputs[0])
            .expect("leading input is the captured closure, concrete");
        assert_eq!(FnId::from(captured.target), FnId(9));
    }

    #[test]
    fn non_closure_has_no_apply_contract() {
        let mut t = ConcreteTypes;
        let int = t.int();
        assert!(closure_apply_contract(&t, &int, &[]).is_none());
    }

    /// `Pending` (dependency not ready), `Unknown` (live value not proven), and
    /// `Known(none)` (the uninhabited type) are different states and must not be
    /// conflated. Only `Pending` is the activation-cell initialization identity;
    /// `Unknown` is sticky so live uncertainty survives to the final boundary.
    /// `Known(none)` carries information and is projected normally.
    #[test]
    fn unknown_is_not_none() {
        let mut t = ConcreteTypes;
        let int = t.int();
        let none = t.none();

        // Distinct cells.
        assert!(!Info::Pending.equiv(&t, &Info::known(none.clone())));
        assert!(!Info::Unknown.equiv(&t, &Info::known(none.clone())));

        // Activation-cell update: `Pending` yields to the first fact, but a live
        // `Unknown` remains unknown.
        assert!(
            Info::Pending
                .widen(&mut t, &Info::known(int.clone()))
                .equiv(&t, &Info::known(int.clone()))
        );
        assert!(
            Info::Unknown
                .widen(&mut t, &Info::known(int.clone()))
                .equiv(&t, &Info::Unknown)
        );
        assert!(
            Info::known(none.clone())
                .widen(&mut t, &Info::known(int.clone()))
                .equiv(&t, &Info::known(int.clone()))
        );

        // Projection: `Unknown` short-circuits — the mapping closure never runs.
        let mut ran = false;
        let projected = Info::Unknown.map_known(|value| {
            ran = true;
            value
        });
        assert!(!ran, "projecting Unknown must not evaluate the projection");
        assert!(matches!(projected, Info::Unknown));

        // A `Known` value (even the empty type) *is* projected.
        let mut ran = false;
        let _ = Info::known(none).map_known(|value| {
            ran = true;
            value
        });
        assert!(ran, "projecting a Known value evaluates the projection");
    }
}
