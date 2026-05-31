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
//! `Module`. Each reachable function gets one [`Spec`] — the running join of
//! every input tuple it has been called with, plus its current return type.
//! Both ascend a finite-height refinement lattice (via `refine_widen`), so the
//! fixpoint terminates.
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
//! The fixpoint distinguishes two bottoms (see [`Info`]). The *type* `none` is
//! ⊥ of the value lattice — the empty, uninhabited set ("returns nothing,
//! ever"); it is a fact. [`Info::Unknown`] is ⊥ of the *information* lattice —
//! the absence of a fact ("not yet determined"), which only ascends as the
//! worklist learns. They share the join identity (`widen(⊥, x) = x`) but differ
//! under projection: projecting `Unknown` is `Unknown` (we still know nothing),
//! whereas projecting `Known(none)` is `Known(none)` (a field of an uninhabited
//! value is itself uninhabited). Conflating them lets a not-yet-computed
//! continuation argument project to `any` and poison the fixpoint forever.
//!
//! The engine is wired into the planner at fz-g58.65.6; until then only its own
//! tests exercise it, so the module is dead in non-test builds.
#![allow(dead_code)]

use crate::fz_ir::{BinOp, BlockId, Const, FnId, Module, Prim, Stmt, Term, UnOp, Var};
use crate::types::{ClosureTarget, ClosureTypes, Ty, Types};
use std::collections::{HashMap, HashSet, VecDeque};

/// A cell in the inference fixpoint.
///
/// `Unknown` is ⊥ of the *information* lattice — "not yet determined", the
/// identity for [`Info::widen`]. It is distinct from the *type* `none` (the
/// empty, uninhabited set): a function that provably never returns settles to
/// `Known(none)`, which is information, not its absence. Projecting `Unknown`
/// yields `Unknown`; projecting `Known(t)` yields `Known(proj t)`.
#[derive(Clone)]
enum Info {
    Unknown,
    Known(Ty),
}

impl Info {
    /// Least upper bound in the information lattice: `Unknown` is the identity,
    /// two `Known`s join through the refinement-lattice widen.
    fn widen<T: Types<Ty = Ty>>(&self, t: &mut T, other: &Info) -> Info {
        match (self, other) {
            (Info::Unknown, x) | (x, Info::Unknown) => x.clone(),
            (Info::Known(a), Info::Known(b)) => Info::Known(t.refine_widen(a, b)),
        }
    }

    fn equiv<T: Types<Ty = Ty>>(&self, t: &T, other: &Info) -> bool {
        match (self, other) {
            (Info::Unknown, Info::Unknown) => true,
            (Info::Known(a), Info::Known(b)) => t.is_equivalent(a, b),
            _ => false,
        }
    }

    /// Map a known type through `f`; `Unknown` is preserved. The shape of
    /// projection: we cannot project what we do not yet know.
    fn map_known(self, f: impl FnOnce(Ty) -> Ty) -> Info {
        match self {
            Info::Unknown => Info::Unknown,
            Info::Known(ty) => Info::Known(f(ty)),
        }
    }
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

/// One function's specialization: the running join of every input tuple it has
/// been called with, and its current return estimate. Both only ever ascend.
struct Spec {
    inputs: Vec<Info>,
    ret: Info,
}

/// The monotone worklist solver. Drives every reachable `(fn, inputs)` to a
/// joint fixpoint of input- and return-type estimates.
struct Solver<'m> {
    module: &'m Module,
    specs: HashMap<FnId, Spec>,
    /// `callee -> callers whose return estimate read callee's ret`. When a
    /// callee's ret ascends, its callers are re-enqueued.
    deps: HashMap<FnId, HashSet<FnId>>,
    queue: VecDeque<FnId>,
    queued: HashSet<FnId>,
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

    fn enqueue(&mut self, f: FnId) {
        if self.queued.insert(f) {
            self.queue.push_back(f);
        }
    }

    fn pop(&mut self) -> Option<FnId> {
        let f = self.queue.pop_front()?;
        self.queued.remove(&f);
        Some(f)
    }

    /// Seed an entry point with its known input types and schedule it.
    fn seed(&mut self, fn_id: FnId, inputs: Vec<Info>) {
        self.specs.insert(
            fn_id,
            Spec {
                inputs,
                ret: Info::Unknown,
            },
        );
        self.enqueue(fn_id);
    }

    /// Widen `callee`'s recorded input tuple by `args`. Returns whether the
    /// stored inputs changed (a fresh callee always counts as changed).
    fn widen_inputs<T: Types<Ty = Ty>>(&mut self, t: &mut T, callee: FnId, args: Vec<Info>) -> bool {
        match self.specs.get(&callee) {
            None => {
                self.specs.insert(
                    callee,
                    Spec {
                        inputs: args,
                        ret: Info::Unknown,
                    },
                );
                true
            }
            Some(spec) => {
                let old = spec.inputs.clone();
                if old.len() != args.len() {
                    self.specs.get_mut(&callee).unwrap().inputs = args;
                    return true;
                }
                let mut widened = Vec::with_capacity(old.len());
                let mut changed = false;
                for (o, a) in old.iter().zip(args.iter()) {
                    let w = o.widen(t, a);
                    if !w.equiv(t, o) {
                        changed = true;
                    }
                    widened.push(w);
                }
                if changed {
                    self.specs.get_mut(&callee).unwrap().inputs = widened;
                }
                changed
            }
        }
    }

    /// `caller` applies `callee` to `args`: record the dependency, widen the
    /// callee's inputs (scheduling it if they grew), and hand back the callee's
    /// current return estimate (`Unknown` for a callee not yet processed).
    fn call<T: Types<Ty = Ty>>(
        &mut self,
        t: &mut T,
        caller: FnId,
        callee: FnId,
        args: Vec<Info>,
    ) -> Info {
        self.deps.entry(callee).or_default().insert(caller);
        if self.widen_inputs(t, callee, args) {
            self.enqueue(callee);
        }
        self.specs
            .get(&callee)
            .map(|s| s.ret.clone())
            .unwrap_or(Info::Unknown)
    }

    /// Run to fixpoint: repeatedly re-derive each scheduled function's return
    /// type; when it ascends, re-schedule the callers that read it.
    fn run<T: Types<Ty = Ty> + ClosureTypes>(&mut self, t: &mut T) {
        while let Some(f) = self.pop() {
            let inputs = self.specs[&f].inputs.clone();
            let ret = self.walk_fn(t, f, &inputs);
            let old = self.specs[&f].ret.clone();
            let new = old.widen(t, &ret);
            if !new.equiv(t, &old) {
                self.specs.get_mut(&f).unwrap().ret = new;
                if let Some(callers) = self.deps.get(&f).cloned() {
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
        f: FnId,
        inputs: &[Info],
    ) -> Info {
        let fnir = self.module.fn_by_id(f);
        let mut env: HashMap<Var, Info> = HashMap::new();
        for (param, info) in fnir.block(fnir.entry).params.iter().zip(inputs) {
            env.insert(*param, info.clone());
        }
        let mut visited = HashSet::new();
        self.walk_block(t, f, fnir.entry, &mut env, &mut visited)
    }

    /// Walk one block of `f`. Intra-fn control (`Goto`/`If`) recurses here;
    /// inter-fn edges route through [`Solver::call`]. Returns the value `f`
    /// hands to its continuation along this path (`Unknown` for non-returning
    /// `Halt` paths — they contribute no information to the join).
    fn walk_block<T: Types<Ty = Ty> + ClosureTypes>(
        &mut self,
        t: &mut T,
        f: FnId,
        block_id: BlockId,
        env: &mut HashMap<Var, Info>,
        visited: &mut HashSet<BlockId>,
    ) -> Info {
        let module = self.module;
        if !visited.insert(block_id) {
            return Info::Unknown;
        }
        let block = module.fn_by_id(f).block(block_id);
        for Stmt::Let(v, prim) in &block.stmts {
            let info = self.type_prim(t, prim, env);
            env.insert(*v, info);
        }
        match &block.terminator {
            Term::Return(v) => env.get(v).cloned().unwrap_or(Info::Unknown),
            // A halt path adds no information to the caller's return type, so it
            // contributes the join identity. That identity is `Unknown`, *not*
            // `Known(none)`: our join is the lossy refinement-widen, and
            // `refine_widen(none, X)` widens `X` (via `widen_for_recursive_spec_key`)
            // rather than returning it untouched — so a `none` halt-path would
            // spuriously degrade a sibling branch's precise type. `Unknown` is
            // the true identity (`widen` returns the other operand verbatim).
            //
            // We reach a halt path only because the walk is branch-blind: it
            // traverses both arms of every `If`, including the synthesized
            // "no clause matched → halt" arm that is statically dead. Pruning
            // those arms by type is fz-g58.65.5; until then the identity keeps
            // the dead arm from perturbing the result.
            Term::Halt(_) => Info::Unknown,
            Term::Goto(target, args) => {
                let arg_infos = arg_infos_of(args, env);
                let target_params = module.fn_by_id(f).block(*target).params.clone();
                for (param, info) in target_params.iter().zip(arg_infos) {
                    env.insert(*param, info);
                }
                self.walk_block(t, f, *target, env, visited)
            }
            Term::If {
                then_b, else_b, ..
            } => {
                let (then_b, else_b) = (*then_b, *else_b);
                let mut env_t = env.clone();
                let mut vis_t = visited.clone();
                let a = self.walk_block(t, f, then_b, &mut env_t, &mut vis_t);
                let mut env_e = env.clone();
                let mut vis_e = visited.clone();
                let b = self.walk_block(t, f, else_b, &mut env_e, &mut vis_e);
                a.widen(t, &b)
            }
            Term::Call {
                callee,
                args,
                continuation,
                ..
            } => {
                let arg_infos = arg_infos_of(args, env);
                let r = self.call(t, f, *callee, arg_infos);
                let cont_inputs = cont_inputs_of(r, &continuation.captured, env);
                self.call(t, f, continuation.fn_id, cont_inputs)
            }
            // A tail call forwards our own continuation, so its result is ours.
            Term::TailCall { callee, args, .. } => {
                let arg_infos = arg_infos_of(args, env);
                self.call(t, f, *callee, arg_infos)
            }
            Term::CallClosure {
                closure,
                args,
                continuation,
                ..
            } => {
                let arg_infos = arg_infos_of(args, env);
                let r = self.apply_closure(t, f, *closure, arg_infos, env);
                let cont_inputs = cont_inputs_of(r, &continuation.captured, env);
                self.call(t, f, continuation.fn_id, cont_inputs)
            }
            Term::TailCallClosure { closure, args, .. } => {
                let arg_infos = arg_infos_of(args, env);
                self.apply_closure(t, f, *closure, arg_infos, env)
            }
            // Receive shapes are out of corpus scope (fz-g58.65.5).
            _ => Info::Unknown,
        }
    }

    /// Resolve a closure application to a call on its body fn (captures ++
    /// args). `Unknown` operand stays `Unknown`; a known non-closure type
    /// (e.g. `any`) yields `any`.
    fn apply_closure<T: Types<Ty = Ty> + ClosureTypes>(
        &mut self,
        t: &mut T,
        f: FnId,
        closure: Var,
        arg_infos: Vec<Info>,
        env: &HashMap<Var, Info>,
    ) -> Info {
        let clo = env.get(&closure).cloned().unwrap_or(Info::Unknown);
        let clo_ty = match clo {
            Info::Unknown => return Info::Unknown,
            Info::Known(ty) => ty,
        };
        match t.closure_lit_parts(&clo_ty) {
            Some(parts) => {
                let target: FnId = parts.target.into();
                let mut inputs: Vec<Info> = parts.captures.into_iter().map(Info::Known).collect();
                inputs.extend(arg_infos);
                self.call(t, f, target, inputs)
            }
            None => Info::Known(t.any()),
        }
    }

    fn type_prim<T: Types<Ty = Ty> + ClosureTypes>(
        &mut self,
        t: &mut T,
        prim: &Prim,
        env: &HashMap<Var, Info>,
    ) -> Info {
        let module = self.module;
        match prim {
            Prim::Const(c) => Info::Known(match c {
                Const::Int(n) => t.int_lit(*n),
                Const::Float(x) => t.float_lit(*x),
                Const::Nil => t.nil(),
                Const::True => t.bool_lit(true),
                Const::False => t.bool_lit(false),
                Const::Atom(id) => {
                    let name = module
                        .atom_names
                        .get(*id as usize)
                        .map(String::as_str)
                        .unwrap_or("");
                    t.atom_lit(name)
                }
            }),
            Prim::BinOp(op, a, b) => {
                let lt = info_of(*a, env);
                let rt = info_of(*b, env);
                match op {
                    // Arithmetic rides the operands' refinement join
                    // (int ⊔ int = int) — and only once both are known.
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                        match (lt, rt) {
                            (Info::Known(a), Info::Known(b)) => Info::Known(t.refine_widen(&a, &b)),
                            _ => Info::Unknown,
                        }
                    }
                    // A comparison is `bool` whatever the operands turn out to be.
                    _ => Info::Known(t.bool()),
                }
            }
            Prim::UnOp(op, v) => match op {
                UnOp::Neg => info_of(*v, env),
                UnOp::Not => Info::Known(t.bool()),
            },
            Prim::IsEmptyList(_) | Prim::IsListCons(_) | Prim::TypeTest(_, _) => {
                Info::Known(t.bool())
            }
            Prim::ListHead(v) => info_of(*v, env).map_known(|lt| t.list_element_type(&lt)),
            Prim::ListTail(v) => info_of(*v, env).map_known(|lt| {
                let elem = t.list_element_type(&lt);
                t.list(elem)
            }),
            Prim::MakeList(elems, tail) => {
                let mut elem = t.none();
                for e in elems {
                    match info_of(*e, env) {
                        Info::Known(et) => elem = t.refine_widen(&elem, &et),
                        Info::Unknown => return Info::Unknown,
                    }
                }
                if let Some(tl) = tail {
                    match info_of(*tl, env) {
                        Info::Known(tt) => {
                            let te = t.list_element_type(&tt);
                            elem = t.refine_widen(&elem, &te);
                        }
                        Info::Unknown => return Info::Unknown,
                    }
                }
                Info::Known(if elems.is_empty() && tail.is_none() {
                    t.empty_list()
                } else {
                    t.list(elem)
                })
            }
            Prim::MakeTuple(vars) => {
                let mut tys = Vec::with_capacity(vars.len());
                for v in vars {
                    match info_of(*v, env) {
                        Info::Known(ty) => tys.push(ty),
                        Info::Unknown => return Info::Unknown,
                    }
                }
                Info::Known(t.tuple(&tys))
            }
            Prim::TupleField(v, i) => info_of(*v, env).map_known(|tv| {
                let arity = t.max_tuple_arity(&tv);
                let projs = t.tuple_projections(&tv, arity);
                projs.get(*i as usize).cloned().unwrap_or_else(|| t.any())
            }),
            Prim::MakeClosure(_, target, caps) => {
                let mut cap_tys = Vec::with_capacity(caps.len());
                for c in caps {
                    match info_of(*c, env) {
                        Info::Known(ty) => cap_tys.push(ty),
                        Info::Unknown => return Info::Unknown,
                    }
                }
                let tfn = module.fn_by_id(*target);
                let entry_params = tfn.block(tfn.entry).params.len();
                let n_args = entry_params.saturating_sub(cap_tys.len());
                Info::Known(t.closure_lit(ClosureTarget::from(*target), cap_tys, n_args))
            }
            // Remaining prims (maps, bitstrings, externs, structs): fz-g58.65.5.
            _ => Info::Known(t.any()),
        }
    }
}

/// Look up a var's cell, defaulting to `Unknown` for the not-yet-bound.
fn info_of(v: Var, env: &HashMap<Var, Info>) -> Info {
    env.get(&v).cloned().unwrap_or(Info::Unknown)
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
/// running the worklist to a fixpoint. Returns `none` if the function is never
/// determined to return (e.g. unreachable) — `Unknown` is an internal cell, not
/// a result.
pub(crate) fn infer_return<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    fn_id: FnId,
    input_tys: &[Ty],
) -> Ty {
    let inputs = input_tys.iter().cloned().map(Info::Known).collect();
    let mut solver = Solver::new(module);
    solver.seed(fn_id, inputs);
    solver.run(t);
    match solver.specs.get(&fn_id).map(|s| s.ret.clone()) {
        Some(Info::Known(ty)) => ty,
        _ => t.none(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
        let main_id = module.fn_by_name("main").expect("main fn").id;
        let target = module.fn_by_name(fn_name).expect("named fn").id;
        let mut solver = Solver::new(module);
        solver.seed(main_id, Vec::new());
        solver.run(&mut t);
        match solver.specs.get(&target).map(|s| s.ret.clone()) {
            Some(Info::Known(ty)) => ty,
            _ => t.none(),
        }
    }

    /// `Unknown` is iteration scaffolding, not an answer. At the fixpoint of a
    /// well-formed program every *reached* function has been walked and its
    /// callees resolved, so each settles to a `Known` type — even a path that
    /// only halts settles to `Known(none)`. A surviving `Unknown` would mean a
    /// function we reached but never propagated a return into: an analysis gap.
    /// So when we're done, there are no unknowns.
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
            let unknowns: Vec<&str> = solver
                .specs
                .iter()
                .filter(|(_, s)| matches!(s.ret, Info::Unknown))
                .map(|(id, _)| module.fn_by_id(*id).name.as_str())
                .collect();
            assert!(
                unknowns.is_empty(),
                "{name}: reached fns left Unknown at fixpoint: {unknowns:?}"
            );
        }
    }

    #[test]
    fn add_infers_int_via_harness() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/add.fz"));
        let add_id = module.fn_by_name("add").expect("add fn").id;
        let int = t.int();
        let ret = infer_return(&mut t, &module, add_id, &[int.clone(), int.clone()]);
        assert!(t.is_equivalent(&ret, &int), "add(int, int) should infer int");
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

    /// `Unknown` (no information yet) and `Known(none)` (the uninhabited type)
    /// are different bottoms and must not be conflated. They share the join
    /// identity but diverge under projection: projecting `Unknown` must *not*
    /// evaluate the projection (it stays `Unknown`), which is what stops a
    /// not-yet-computed value from projecting to `any` and poisoning the
    /// fixpoint. `Known(none)` carries information and is projected normally.
    #[test]
    fn unknown_is_not_none() {
        let mut t = ConcreteTypes;
        let int = t.int();
        let none = t.none();

        // Distinct cells.
        assert!(!Info::Unknown.equiv(&t, &Info::Known(none.clone())));

        // Join: both bottoms are the identity, so each yields `int`.
        assert!(Info::Unknown.widen(&mut t, &Info::Known(int.clone())).equiv(&t, &Info::Known(int.clone())));
        assert!(
            Info::Known(none.clone())
                .widen(&mut t, &Info::Known(int.clone()))
                .equiv(&t, &Info::Known(int.clone()))
        );

        // Projection: `Unknown` short-circuits — the mapping closure never runs.
        let mut ran = false;
        let projected = Info::Unknown.map_known(|ty| {
            ran = true;
            ty
        });
        assert!(!ran, "projecting Unknown must not evaluate the projection");
        assert!(matches!(projected, Info::Unknown));

        // A `Known` value (even the empty type) *is* projected.
        let mut ran = false;
        let _ = Info::Known(none).map_known(|ty| {
            ran = true;
            ty
        });
        assert!(ran, "projecting a Known value evaluates the projection");
    }
}
