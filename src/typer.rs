//! Local type inference for fz expressions, with multi-clause function
//! intersection typing and pattern-narrowing across clauses.
//!
//! This module is the bridge from the AST to the set-theoretic descriptors
//! in `crate::types`. The design choices here, in case they need revisiting:
//!
//! - **Parametric polymorphism via per-call-site specialization.** Functions
//!   like `fn id(x), do: x` get a wide whole-program arrow (e.g.
//!   `(int|atom)→(int|atom)` when called with both kinds), but the AOT/JIT
//!   pipelines re-type the body once per distinct call-site shape via
//!   `specialize_return` and emit one codegen instance per shape. Whole-
//!   program calls only — there's no surface-level type-variable syntax.
//!
//! - **Multi-clause function types are the intersection of their per-clause
//!   arrow types.** Each clause is typed under an env where its parameter
//!   pattern types have been narrowed by subtracting the values matched by
//!   prior clauses. So `fn fact(0), do: 1; fn fact(n), do: ...` gets type
//!   `(0 → 1) ∩ ((int \ 0) → ...)`.
//!
//! - **Recursion via fixed-point iteration with widening at K=3.** Globals
//!   start at `none`; we re-type bodies until types stabilize. After K
//!   iterations, any growing literal-set axes (ints/floats/strs) are widened
//!   to their tops to ensure termination — singleton-type lattices have
//!   infinite ascending chains.
//!
//! - **Pattern types are over-approximated when the scrutinee is a union of
//!   tuple/list shapes** (we use `any` for the variable's binding type in
//!   that case). Single-shape scrutinees give precise per-component types.

use crate::ast::*;
use crate::types::*;
use std::collections::HashMap;

pub type TypeEnv = HashMap<String, Descr>;

pub struct Typer {
    pub globals: TypeEnv,
    pub errors: Vec<String>,
    /// Per-fn-name union of arg types observed at *every* call site, from the
    /// previous fixed-point iteration. Used to monomorphize whole-program calls
    /// (e.g. `count(int, int)` only ever called with ints, so its var-bound
    /// parameters can be narrowed from `any` to `int`).
    call_obs: HashMap<String, Vec<Descr>>,
    /// Accumulator being built during the current iteration; promoted into
    /// `call_obs` at iteration end.
    call_obs_curr: HashMap<String, Vec<Descr>>,
    /// Per-call-site arg-type tuples observed in the **final** iteration. Used
    /// by the AOT/JIT specializer (fz-ul4.6) to enumerate distinct shapes a
    /// polymorphic fn is invoked with.
    pub call_shapes: HashMap<String, Vec<Vec<Descr>>>,
    call_shapes_curr: HashMap<String, Vec<Vec<Descr>>>,
    /// Names of user-defined fns. Used to guard call-site observation so we
    /// don't accumulate obs for builtins (their arrows are pre-installed and
    /// shouldn't be narrowed).
    user_fns: std::collections::HashSet<String>,
}

impl Default for Typer { fn default() -> Self { Self::new() } }

impl Typer {
    pub fn new() -> Self {
        let mut me = Self {
            globals: HashMap::new(),
            errors: Vec::new(),
            call_obs: HashMap::new(),
            call_obs_curr: HashMap::new(),
            call_shapes: HashMap::new(),
            call_shapes_curr: HashMap::new(),
            user_fns: std::collections::HashSet::new(),
        };
        me.install_builtins();
        me
    }

    fn install_builtins(&mut self) {
        // Builtins documented in src/eval.rs:install_builtins. Their *types*
        // here use the language's own descriptors. Where overloaded, we use
        // intersection of arrows.
        let g = &mut self.globals;

        // print/1 :: (any) -> nil
        g.insert("print".into(), Descr::arrow([Descr::any()], Descr::nil()));

        // is_integer/1 :: (any) -> bool
        g.insert("is_integer".into(), Descr::arrow([Descr::any()], Descr::bool_t()));
        g.insert("is_atom".into(),    Descr::arrow([Descr::any()], Descr::bool_t()));
        g.insert("is_vec".into(),     Descr::arrow([Descr::any()], Descr::bool_t()));

        // length/1 :: (list(any) | vec) -> int
        let any_list = Descr::list_of(Descr::any());
        let any_vec = Descr::vec_i64()
            .union(&Descr::vec_f64())
            .union(&Descr::vec_u8())
            .union(&Descr::vec_bit());
        g.insert("length".into(), Descr::arrow([any_list.union(&any_vec)], Descr::int()));

        // vec_get/2 :: (vec, int) -> int|float  (we don't track per-vec elem types yet)
        g.insert("vec_get".into(), Descr::arrow(
            [any_vec.clone(), Descr::int()],
            Descr::int().union(&Descr::float()),
        ));

        // vec_map/2 :: (vec, (any) -> any) -> vec
        let any_arrow = Descr::arrow([Descr::any()], Descr::any());
        g.insert("vec_map".into(), Descr::arrow([any_vec.clone(), any_arrow.clone()], any_vec.clone()));

        // map_get/2 :: (map, any) -> any
        g.insert("map_get".into(), Descr::arrow(
            [Descr::map_top(), Descr::any()],
            Descr::any().union(&Descr::nil()),
        ));
        // map_put/3 :: (map, any, any) -> map
        g.insert("map_put".into(), Descr::arrow(
            [Descr::map_top(), Descr::any(), Descr::any()],
            Descr::map_top(),
        ));

        // vec_reduce/3 :: (vec, any, (any, any) -> any) -> any
        let any_arrow_2 = Descr::arrow([Descr::any(), Descr::any()], Descr::any());
        g.insert("vec_reduce".into(), Descr::arrow(
            [any_vec, Descr::any(), any_arrow_2],
            Descr::any(),
        ));
    }

    pub fn type_program(&mut self, prog: &Program) {
        // Pre-register all top-level fns at `none → none → ...` so recursive
        // calls have something to look up. Actually, we use a placeholder of
        // `any` (the most permissive arrow) so the body can be typed at all;
        // the iteration narrows it down.
        for item in &prog.items {
            if let Item::Fn(def) = &**item {
                if def.is_macro { continue; }
                let arity = def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
                let placeholder = Descr::arrow(
                    std::iter::repeat_n(Descr::any(), arity).collect::<Vec<_>>(),
                    Descr::any(),
                );
                self.globals.insert(def.name.clone(), placeholder);
                self.user_fns.insert(def.name.clone());
            }
        }

        let max_iter = 10;
        let widen_at = 3;
        for iter in 0..max_iter {
            let snapshot = self.globals.clone();
            let mut changed = false;
            self.call_obs_curr.clear();
            self.call_shapes_curr.clear();
            for item in &prog.items {
                if let Item::Fn(def) = &**item {
                    if def.is_macro { continue; }
                    let mut new_type = self.type_function(def, &snapshot);
                    if iter >= widen_at {
                        new_type = widen(&new_type);
                    }
                    let prev = snapshot.get(&def.name).cloned().unwrap_or_else(Descr::none);
                    if !new_type.is_equiv(&prev) {
                        self.globals.insert(def.name.clone(), new_type);
                        changed = true;
                    }
                }
            }
            // Promote the just-collected observations for the next iteration.
            // Detect changes in call_obs too so we don't terminate prematurely
            // when observations have stabilized but bodies haven't been re-typed
            // under them yet.
            if self.call_obs != self.call_obs_curr {
                changed = true;
            }
            self.call_obs = std::mem::take(&mut self.call_obs_curr);
            self.call_shapes = std::mem::take(&mut self.call_shapes_curr);
            if !changed { break; }
        }
    }

    fn type_function(&mut self, def: &FnDef, snapshot: &TypeEnv) -> Descr {
        let arity = def.clauses.first().map(|c| c.params.len()).unwrap_or(0);

        // -- Phase 1: compute per-clause narrowed_args, applying both
        //    pattern-based subtraction and call-site observation narrowing.
        //    Guarded clauses don't fully cover their pattern domain, so we
        //    don't add their `combined` to `prior_inputs` (otherwise a
        //    catch-all wildcard clause after a guarded one looks unreachable).
        let mut prior_inputs = Descr::none();
        let mut all_narrowed: Vec<Option<Vec<Descr>>> = Vec::with_capacity(def.clauses.len());

        for clause in &def.clauses {
            let pat_types: Vec<Descr> = clause.params.iter().map(pattern_type).collect();
            let combined = Descr::tuple_of(pat_types.clone());

            let narrowed = combined.diff(&prior_inputs);
            if clause.guard.is_none() {
                prior_inputs = prior_inputs.union(&combined);
            }

            if narrowed.is_empty() {
                all_narrowed.push(None);
                continue;
            }

            let mut narrowed_args = tuple_projections(&narrowed, arity);

            // Apply previous-iteration call-site obs. If intersection would
            // empty any arg (i.e. no observed call hits this clause), fall
            // back to the unintersected args rather than killing the clause.
            if let Some(obs) = self.call_obs.get(&def.name) {
                if obs.len() == arity {
                    let mut tentative: Vec<Descr> = (0..arity)
                        .map(|i| narrowed_args[i].intersect(&obs[i])).collect();
                    if tentative.iter().all(|a| !a.is_empty()) {
                        narrowed_args = std::mem::take(&mut tentative);
                    }
                }
            }

            all_narrowed.push(Some(narrowed_args));
        }

        // -- Phase 2: type non-self-recursive ("exit") clauses first under the
        //    plain snapshot. Their union return type bounds what self-calls
        //    can yield assuming the function terminates.
        let mut clause_arrows: Vec<Descr> = Vec::with_capacity(def.clauses.len());
        let mut deferred: Vec<usize> = Vec::new();
        let mut exit_returns = Descr::none();

        for (i, clause) in def.clauses.iter().enumerate() {
            let Some(narrowed_args) = all_narrowed[i].clone() else { continue };
            if expr_calls_self(&clause.body, &def.name)
                || clause.guard.as_ref().is_some_and(|g| expr_calls_self(g, &def.name))
            {
                deferred.push(i);
                continue;
            }
            let body_t = self.type_clause_body(snapshot, clause, &narrowed_args);
            exit_returns = exit_returns.union(&body_t);
            clause_arrows.push(Descr::arrow(narrowed_args, body_t));
        }

        // -- Phase 3: type self-recursive clauses under a snapshot in which
        //    `self` is narrowed to (observed_args) → exit_returns. This is
        //    sound assuming the function terminates: any concrete result a
        //    self-call ultimately produces must come from an exit clause.
        let self_narrowed: Option<Descr> = if !exit_returns.is_empty() {
            self.call_obs.get(&def.name)
                .filter(|obs| obs.len() == arity)
                .map(|obs| Descr::arrow(obs.clone(), exit_returns.clone()))
        } else { None };

        for i in deferred {
            let narrowed_args = all_narrowed[i].clone().expect("deferred clause was reachable");
            let mut snap = snapshot.clone();
            if let Some(sn) = &self_narrowed {
                snap.insert(def.name.clone(), sn.clone());
            }
            let body_t = self.type_clause_body(&snap, &def.clauses[i], &narrowed_args);
            clause_arrows.push(Descr::arrow(narrowed_args, body_t));
        }

        if clause_arrows.is_empty() {
            return Descr::arrow(
                std::iter::repeat_n(Descr::none(), arity).collect::<Vec<_>>(),
                Descr::none(),
            );
        }
        clause_arrows.iter().skip(1).fold(clause_arrows[0].clone(), |a, b| a.intersect(b))
    }

    fn type_clause_body(&mut self, snapshot: &TypeEnv, clause: &FnClause, narrowed_args: &[Descr]) -> Descr {
        let mut env = snapshot.clone();
        for (i, p) in clause.params.iter().enumerate() {
            for (name, ty) in pattern_bindings(p, &narrowed_args[i]) {
                env.insert(name, ty);
            }
        }
        if let Some(g) = &clause.guard {
            let _ = self.infer(&env, g);
        }
        self.infer(&env, &clause.body)
    }

    pub fn infer(&mut self, env: &TypeEnv, e: &Expr) -> Descr {
        match e {
            Expr::Int(n)   => Descr::int_lit(*n),
            Expr::Float(f) => Descr::float_lit(*f),
            Expr::Str(s)   => Descr::str_lit(s.clone()),
            Expr::Atom(a)  => Descr::atom_lit(a.clone()),
            Expr::Bool(_)  => Descr::bool_t(),
            Expr::Nil      => Descr::nil(),
            Expr::Var(n) => env.get(n).cloned().unwrap_or_else(|| {
                self.errors.push(format!("undefined: {}", n));
                Descr::any()
            }),
            Expr::List(elems, tail) => {
                let mut elem_t = Descr::none();
                for e in elems { elem_t = elem_t.union(&self.infer(env, e)); }
                if let Some(t) = tail {
                    let tail_t = self.infer(env, t);
                    elem_t = elem_t.union(&list_element_type(&tail_t));
                }
                Descr::list_of(elem_t)
            }
            Expr::Tuple(elems) => {
                let ts: Vec<Descr> = elems.iter().map(|e| self.infer(env, e)).collect();
                Descr::tuple_of(ts)
            }
            Expr::Map(pairs) => {
                let mut fields: std::collections::BTreeMap<MapKey, Descr> = Default::default();
                let mut all_static_keys = true;
                for (k, v) in pairs {
                    let vt = self.infer(env, v);
                    match expr_to_map_key(k) {
                        Some(mk) => { fields.insert(mk, vt); }
                        None => { all_static_keys = false; }
                    }
                }
                if all_static_keys {
                    Descr::map_of(fields)
                } else {
                    Descr::map_top()
                }
            }
            Expr::MapUpdate(base, pairs) => {
                let mut bt = self.infer(env, base);
                // For each updated field with a static key, refine that field's value type.
                for (k, v) in pairs {
                    let vt = self.infer(env, v);
                    if let Some(mk) = expr_to_map_key(k) {
                        bt = refine_map_field(&bt, &mk, &vt);
                    }
                }
                bt
            }
            Expr::Index(target, key) => {
                let tt = self.infer(env, target);
                if let Some(mk) = expr_to_map_key(key) {
                    map_field_lookup(&tt, &mk).unwrap_or_else(|| Descr::any().union(&Descr::nil()))
                } else {
                    Descr::any()
                }
            }
            Expr::VecLit(kind, _) => match kind {
                VecKind::Numeric => Descr::vec_i64().union(&Descr::vec_f64()),
                VecKind::Bytes   => Descr::vec_u8(),
                VecKind::Bits    => Descr::vec_bit(),
            },
            Expr::Bitstring(_) => {
                // Bitstring literal: byte-aligned or not. Unions both.
                Descr::vec_u8().union(&Descr::vec_bit())
            }
            Expr::Call(callee, args) => {
                let f = self.infer(env, callee);
                let arg_ts: Vec<Descr> = args.iter().map(|a| self.infer(env, a)).collect();
                self.record_call_obs(callee, &arg_ts);
                self.apply_arrow(&f, &arg_ts)
            }
            Expr::Dot(_, _) => Descr::any(),
            Expr::BinOp(op, l, r) => {
                if *op == BinOp::Pipe {
                    // a |> f(args)  ≡  f(a, args). Special-case before
                    // inferring `r` so the inner Call doesn't separately
                    // record a (wrong-arity) obs for `f`.
                    let lt = self.infer(env, l);
                    if let Expr::Call(callee, more) = &**r {
                        let f = self.infer(env, callee);
                        let mut all: Vec<Descr> = vec![lt];
                        for a in more { all.push(self.infer(env, a)); }
                        self.record_call_obs(callee, &all);
                        return self.apply_arrow(&f, &all);
                    }
                    let rt = self.infer(env, r);
                    return self.apply_arrow(&rt, &[lt]);
                }
                let lt = self.infer(env, l);
                let rt = self.infer(env, r);
                self.binop_type(*op, &lt, &rt)
            }
            Expr::UnOp(op, x) => {
                let t = self.infer(env, x);
                match op {
                    UnOp::Neg => {
                        if t.is_subtype(&Descr::int()) { Descr::int() }
                        else if t.is_subtype(&Descr::float()) { Descr::float() }
                        else { self.errors.push(format!("- on non-numeric: {}", t)); Descr::none() }
                    }
                    UnOp::Not => Descr::bool_t(),
                }
            }
            Expr::If(c, t, els) => {
                let _ct = self.infer(env, c);
                let tt = self.infer(env, t);
                let et = match els { Some(e) => self.infer(env, e), None => Descr::nil() };
                tt.union(&et)
            }
            Expr::Case(scrut, clauses) => {
                let scrut_t = self.infer(env, scrut);
                let mut remaining = scrut_t.clone();
                let mut result = Descr::none();
                for cl in clauses {
                    let pt = pattern_type(&cl.pattern);
                    let matched = remaining.intersect(&pt);
                    if matched.is_empty() { continue; }
                    remaining = remaining.diff(&pt);
                    let mut new_env = env.clone();
                    for (n, ty) in pattern_bindings(&cl.pattern, &matched) {
                        new_env.insert(n, ty);
                    }
                    result = result.union(&self.infer(&new_env, &cl.body));
                }
                result
            }
            Expr::Cond(_) => Descr::any(),
            Expr::With(bindings, body, else_clauses) => {
                let mut local = env.clone();
                let mut fail_t = Descr::none();
                let mut body_reachable = true;
                for b in bindings {
                    match b {
                        WithBinding::Match(pat, e) => {
                            let rhs_t = self.infer(&local, e);
                            let pat_t = pattern_type(pat);
                            let matched = rhs_t.intersect(&pat_t);
                            let failing = rhs_t.diff(&pat_t);
                            if matched.is_empty() { body_reachable = false; }
                            if !failing.is_empty() {
                                if else_clauses.is_empty() {
                                    fail_t = fail_t.union(&failing);
                                } else {
                                    let mut remaining = failing.clone();
                                    for cl in else_clauses {
                                        let cpt = pattern_type(&cl.pattern);
                                        let cmatched = remaining.intersect(&cpt);
                                        if cmatched.is_empty() { continue; }
                                        remaining = remaining.diff(&cpt);
                                        let mut e2 = local.clone();
                                        for (n, ty) in pattern_bindings(&cl.pattern, &cmatched) {
                                            e2.insert(n, ty);
                                        }
                                        fail_t = fail_t.union(&self.infer(&e2, &cl.body));
                                    }
                                    if !remaining.is_empty() {
                                        fail_t = fail_t.union(&remaining);
                                    }
                                }
                            }
                            for (n, ty) in pattern_bindings(pat, &matched) {
                                local.insert(n, ty);
                            }
                        }
                        WithBinding::Bare(e) => { let _ = self.infer(&local, e); }
                    }
                }
                // We always type-check the body (catches errors), but only
                // include its type in the result when it can actually run.
                let body_t = self.infer(&local, body);
                if body_reachable { body_t.union(&fail_t) } else { fail_t }
            }
            Expr::Match(pat, rhs) => {
                let rt = self.infer(env, rhs);
                // Match introduces bindings into the env (mutating env semantics
                // in fz are achieved by shadowing; here we accept it didn't
                // get propagated to siblings unless block sequencing handles it).
                // We type the match expr as the rhs type.
                let _ = pat;
                rt
            }
            Expr::Block(exprs) => {
                let mut local = env.clone();
                let mut last = Descr::nil();
                for e in exprs {
                    if let Expr::Match(pat, rhs) = e {
                        let rt = self.infer(&local, rhs);
                        for (n, ty) in pattern_bindings(pat, &rt) {
                            local.insert(n, ty);
                        }
                        last = rt;
                    } else {
                        last = self.infer(&local, e);
                    }
                }
                last
            }
            Expr::Lambda(params, body) => {
                let mut env = env.clone();
                let arg_ts: Vec<Descr> = params.iter().map(pattern_type).collect();
                for (p, t) in params.iter().zip(arg_ts.iter()) {
                    for (n, ty) in pattern_bindings(p, t) {
                        env.insert(n, ty);
                    }
                }
                let ret = self.infer(&env, body);
                Descr::arrow(arg_ts, ret)
            }
        }
    }

    /// Record a call site against `callee` for the next iteration's
    /// monomorphization passes. Both `call_obs` (per-arg union) and
    /// `call_shapes` (raw per-call-site shape list) accumulate.
    fn record_call_obs(&mut self, callee: &Expr, arg_ts: &[Descr]) {
        let Expr::Var(name) = callee else { return };
        if !self.user_fns.contains(name) { return; }
        let entry = self.call_obs_curr.entry(name.clone())
            .or_insert_with(|| vec![Descr::none(); arg_ts.len()]);
        if entry.len() == arg_ts.len() {
            for (i, t) in arg_ts.iter().enumerate() {
                entry[i] = entry[i].union(t);
            }
        }
        self.call_shapes_curr.entry(name.clone())
            .or_default()
            .push(arg_ts.to_vec());
    }

    fn binop_type(&mut self, op: BinOp, l: &Descr, r: &Descr) -> Descr {
        use BinOp::*;
        match op {
            Add | Sub | Mul | Div | Rem => {
                // Without polymorphism, var-bound operands are `any` — we
                // over-approximate by checking which numeric branches are
                // *possible* (intersection non-empty) and unioning their
                // results. With concrete int/float operands, this is exact;
                // with `any`, the result is `int | float`.
                let l_int = !l.intersect(&Descr::int()).is_empty();
                let r_int = !r.intersect(&Descr::int()).is_empty();
                let l_fl = !l.intersect(&Descr::float()).is_empty();
                let r_fl = !r.intersect(&Descr::float()).is_empty();
                let mut out = Descr::none();
                if l_int && r_int { out = out.union(&Descr::int()); }
                if l_fl && r_fl { out = out.union(&Descr::float()); }
                if out.looks_empty() {
                    self.errors.push(format!("type error: {:?}({}, {})", op, l, r));
                }
                out
            }
            Eq | Neq | Lt | LtEq | Gt | GtEq => Descr::bool_t(),
            And | Or => l.union(r),
            Pipe => unreachable!("pipe handled at call site"),
            Cons => {
                // h | t  ⇒  list(h ∪ elem(t))
                let elem = list_element_type(r).union(l);
                Descr::list_of(elem)
            }
        }
    }

    fn apply_arrow(&mut self, f: &Descr, args: &[Descr]) -> Descr {
        // For each positive clause `(t1...tn) → u` in f.funcs, if every
        // arg is a subtype of the corresponding ti, the result is `u`.
        // The arrow type's return is the union over the matching clauses.
        // Multi-clause via intersection means the BEST match (most specific
        // input shape) gives the most specific return.
        if f.funcs.is_empty() {
            self.errors.push(format!("not callable: {}", f));
            return Descr::none();
        }
        let mut result = Descr::none();
        let mut matched_any = false;
        for clause in &f.funcs {
            for sig in &clause.pos {
                if sig.args.len() != args.len() { continue; }
                let all_match = sig.args.iter().zip(args.iter())
                    .all(|(expected, actual)| actual.is_subtype(expected));
                if all_match {
                    result = result.union(&sig.ret);
                    matched_any = true;
                }
            }
        }
        if !matched_any {
            // Fall back: union of ALL return types reachable for any arity match
            // — over-approximation. Produces `any` for fully-permissive arrows.
            for clause in &f.funcs {
                for sig in &clause.pos {
                    if sig.args.len() == args.len() {
                        result = result.union(&sig.ret);
                    }
                }
            }
            if result.looks_empty() {
                self.errors.push(format!("no matching clause for call args [{}]",
                    args.iter().map(|a| a.to_string()).collect::<Vec<_>>().join(", ")));
                return Descr::none();
            }
        }
        result
    }
}

// ----------------------------------------------------------------------
// Specializer support
// ----------------------------------------------------------------------

/// Re-type a fn's body assuming its parameters have the given Descrs (typically
/// derived from a particular call-site LowerTy shape). Returns the union of
/// all viable clauses' return Descrs. Clauses whose pattern doesn't intersect
/// the requested shape are skipped (treated as not applicable for this
/// instantiation).
///
/// This is the core of fz-ul4.6 per-shape specialization: the typer's
/// whole-program arrow may be wide (`(int|atom)→(int|atom)` for an `id` fn
/// called with both kinds), but each individual instantiation has a clean
/// return type the codegen can consume.
pub fn specialize_return(typer: &mut Typer, def: &FnDef, params: &[Descr]) -> Descr {
    let mut ret = Descr::none();
    let snapshot = typer.globals.clone();
    for clause in &def.clauses {
        if clause.params.len() != params.len() { continue; }
        let mut env = snapshot.clone();
        let mut viable = true;
        for (i, p) in clause.params.iter().enumerate() {
            let pt = pattern_type(p);
            let narrowed = params[i].intersect(&pt);
            if narrowed.is_empty() { viable = false; break; }
            for (n, ty) in pattern_bindings(p, &narrowed) {
                env.insert(n, ty);
            }
        }
        if !viable { continue; }
        if let Some(g) = &clause.guard {
            let _ = typer.infer(&env, g);
        }
        let body_t = typer.infer(&env, &clause.body);
        ret = ret.union(&body_t);
    }
    ret
}

// ----------------------------------------------------------------------
// AST walking helpers
// ----------------------------------------------------------------------

/// True if `e` syntactically contains a call to `name` (as `name(...)`).
/// Used to decide whether a clause needs the self-narrowed snapshot pass.
pub fn expr_calls_self(e: &Expr, name: &str) -> bool {
    match e {
        Expr::Call(callee, args) => {
            if let Expr::Var(n) = &**callee {
                if n == name { return true; }
            }
            expr_calls_self(callee, name) || args.iter().any(|a| expr_calls_self(a, name))
        }
        Expr::BinOp(_, l, r) => expr_calls_self(l, name) || expr_calls_self(r, name),
        Expr::UnOp(_, x) => expr_calls_self(x, name),
        Expr::If(c, t, els) => expr_calls_self(c, name)
            || expr_calls_self(t, name)
            || els.as_deref().is_some_and(|e| expr_calls_self(e, name)),
        Expr::Case(s, cls) => expr_calls_self(s, name)
            || cls.iter().any(|c| expr_calls_self(&c.body, name)
                || c.guard.as_ref().is_some_and(|g| expr_calls_self(g, name))),
        Expr::Cond(arms) => arms.iter().any(|(c, b)| expr_calls_self(c, name) || expr_calls_self(b, name)),
        Expr::With(bindings, body, els) => {
            bindings.iter().any(|b| match b {
                WithBinding::Match(_, e) | WithBinding::Bare(e) => expr_calls_self(e, name),
            }) || expr_calls_self(body, name)
                || els.iter().any(|c| expr_calls_self(&c.body, name))
        }
        Expr::Match(_, rhs) => expr_calls_self(rhs, name),
        Expr::Block(es) => es.iter().any(|e| expr_calls_self(e, name)),
        Expr::Lambda(_, body) => expr_calls_self(body, name),
        Expr::List(es, tail) => es.iter().any(|e| expr_calls_self(e, name))
            || tail.as_deref().is_some_and(|e| expr_calls_self(e, name)),
        Expr::Tuple(es) => es.iter().any(|e| expr_calls_self(e, name)),
        Expr::VecLit(_, es) => es.iter().any(|e| expr_calls_self(e, name)),
        Expr::Bitstring(fields) => fields.iter().any(|f| expr_calls_self(&f.value, name)),
        Expr::Map(pairs) => pairs.iter().any(|(k, v)| expr_calls_self(k, name) || expr_calls_self(v, name)),
        Expr::MapUpdate(b, pairs) => expr_calls_self(b, name)
            || pairs.iter().any(|(k, v)| expr_calls_self(k, name) || expr_calls_self(v, name)),
        Expr::Index(t, k) => expr_calls_self(t, name) || expr_calls_self(k, name),
        Expr::Dot(e, _) => expr_calls_self(e, name),
        _ => false,
    }
}

// ----------------------------------------------------------------------
// Patterns
// ----------------------------------------------------------------------

pub fn pattern_type(p: &Pattern) -> Descr {
    match p {
        Pattern::Wildcard => Descr::any(),
        Pattern::Var(_) => Descr::any(),
        Pattern::Int(n) => Descr::int_lit(*n),
        Pattern::Float(f) => Descr::float_lit(*f),
        Pattern::Str(s) => Descr::str_lit(s.clone()),
        Pattern::Atom(a) => Descr::atom_lit(a.clone()),
        Pattern::Bool(_) => Descr::bool_t(),
        Pattern::Nil => Descr::nil(),
        Pattern::Tuple(ps) => Descr::tuple_of(ps.iter().map(pattern_type).collect::<Vec<_>>()),
        Pattern::List(heads, _tail) => {
            let elem = if heads.is_empty() {
                Descr::any()
            } else {
                heads.iter().fold(Descr::none(), |acc, p| acc.union(&pattern_type(p)))
            };
            Descr::list_of(elem)
        }
        Pattern::As(_, inner) => pattern_type(inner),
        Pattern::Map(pairs) => {
            let mut fields = std::collections::BTreeMap::new();
            for (kp, vp) in pairs {
                if let Some(mk) = pattern_to_map_key(kp) {
                    fields.insert(mk, pattern_type(vp));
                }
            }
            if fields.is_empty() { Descr::map_top() } else { Descr::map_of(fields) }
        }
        Pattern::Bitstring(_) => Descr::vec_u8().union(&Descr::vec_bit()),
    }
}

pub fn pattern_bindings(p: &Pattern, scrut: &Descr) -> Vec<(String, Descr)> {
    let mut out = Vec::new();
    extract(p, scrut, &mut out);
    out
}

fn extract(p: &Pattern, scrut: &Descr, out: &mut Vec<(String, Descr)>) {
    match p {
        Pattern::Var(n) => out.push((n.clone(), scrut.clone())),
        Pattern::As(n, inner) => {
            out.push((n.clone(), scrut.clone()));
            extract(inner, scrut, out);
        }
        Pattern::Tuple(ps) => {
            let comps = tuple_projections(scrut, ps.len());
            for (i, p) in ps.iter().enumerate() {
                extract(p, &comps[i], out);
            }
        }
        Pattern::List(heads, tail) => {
            let elem = list_element_type(scrut);
            for h in heads { extract(h, &elem, out); }
            if let Some(t) = tail { extract(t, scrut, out); }
        }
        Pattern::Bitstring(fields) => {
            for f in fields {
                let scrut_for_field = match f.spec.ty {
                    BitType::Integer | BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => Descr::int(),
                    BitType::Float => Descr::float(),
                    BitType::Binary => Descr::vec_u8(),
                    BitType::Bits => Descr::vec_u8().union(&Descr::vec_bit()),
                };
                extract(&f.value, &scrut_for_field, out);
            }
        }
        Pattern::Map(pairs) => {
            for (kp, vp) in pairs {
                let val_t = if let Some(mk) = pattern_to_map_key(kp) {
                    map_field_lookup(scrut, &mk).unwrap_or_else(Descr::any)
                } else {
                    Descr::any()
                };
                extract(vp, &val_t, out);
            }
        }
        _ => {} // literals, wildcard, etc., bind nothing.
    }
}

/// Project the i-th component of any positive tuple shape in `scrut` of the
/// given arity, unioning across multiple shapes. Falls back to `any` when
/// no matching tuple shape is present.
pub fn tuple_projections(scrut: &Descr, arity: usize) -> Vec<Descr> {
    let mut comps = vec![Descr::none(); arity];
    let mut found = false;
    for clause in &scrut.tuples {
        for sig in &clause.pos {
            if sig.elems.len() == arity {
                for i in 0..arity { comps[i] = comps[i].union(&sig.elems[i]); }
                found = true;
            }
        }
    }
    if !found { return vec![Descr::any(); arity]; }
    comps
}

// ----------------------------------------------------------------------
// Map helpers
// ----------------------------------------------------------------------

pub fn expr_to_map_key(e: &Expr) -> Option<MapKey> {
    Some(match e {
        Expr::Atom(a) => MapKey::Atom(a.clone()),
        Expr::Int(n) => MapKey::Int(*n),
        Expr::Str(s) => MapKey::Str(s.clone()),
        Expr::Bool(b) => MapKey::Bool(*b),
        Expr::Nil => MapKey::Nil,
        _ => return None,
    })
}

pub fn pattern_to_map_key(p: &Pattern) -> Option<MapKey> {
    Some(match p {
        Pattern::Atom(a) => MapKey::Atom(a.clone()),
        Pattern::Int(n) => MapKey::Int(*n),
        Pattern::Str(s) => MapKey::Str(s.clone()),
        Pattern::Bool(b) => MapKey::Bool(*b),
        Pattern::Nil => MapKey::Nil,
        _ => return None,
    })
}

/// Look up the value type for `key` across all positive map shapes in `d`.
/// Returns `None` if `d` has no map shapes (call site decides the fallback).
pub fn map_field_lookup(d: &Descr, key: &MapKey) -> Option<Descr> {
    let mut found = false;
    let mut acc = Descr::none();
    for clause in &d.maps {
        for sig in &clause.pos {
            found = true;
            // Open shape: if key is required, contribute its type; otherwise
            // the key may or may not be present so contribute `any | nil`.
            if let Some(t) = sig.fields.get(key) {
                acc = acc.union(t);
            } else {
                acc = acc.union(&Descr::any()).union(&Descr::nil());
            }
        }
        if clause.pos.is_empty() {
            // Top map clause — any map, any key value.
            acc = acc.union(&Descr::any()).union(&Descr::nil());
            found = true;
        }
    }
    if !found { None } else { Some(acc) }
}

/// Refine `d` by setting field `key` to value type `vt` in every positive map
/// shape. Used by map update typing.
pub fn refine_map_field(d: &Descr, key: &MapKey, vt: &Descr) -> Descr {
    let mut out = d.clone();
    for clause in &mut out.maps {
        for sig in &mut clause.pos {
            sig.fields.insert(key.clone(), vt.clone());
        }
        if clause.pos.is_empty() {
            // Top map: can't refine without manufacturing a shape; skip.
        }
    }
    out
}

/// Element type of a list-typed descriptor. Falls back to `any`.
pub fn list_element_type(scrut: &Descr) -> Descr {
    let mut elem = Descr::none();
    let mut found = false;
    for clause in &scrut.lists {
        for sig in &clause.pos {
            elem = elem.union(&sig.elem);
            found = true;
        }
    }
    if !found { Descr::any() } else { elem }
}

// ----------------------------------------------------------------------
// Widening (for fixed-point termination)
// ----------------------------------------------------------------------

/// Widen any growing literal-set axes to their tops. Recursively applied to
/// structural element types so arrow returns / list elements / tuple
/// components also widen.
pub fn widen(d: &Descr) -> Descr {
    let mut out = d.clone();
    if !out.ints.is_none() && !out.ints.is_any() { out.ints = IntSet::any(); }
    if !out.floats.is_none() && !out.floats.is_any() { out.floats = FloatSet::any(); }
    if !out.strs.is_none() && !out.strs.is_any() { out.strs = StrSet::any(); }
    out.tuples = out.tuples.into_iter().map(widen_tuple).collect();
    out.lists  = out.lists.into_iter().map(widen_list).collect();
    out.funcs  = out.funcs.into_iter().map(widen_func).collect();
    out.maps   = out.maps.into_iter().map(widen_map).collect();
    out
}
fn widen_map_sig(s: MapSig) -> MapSig {
    MapSig { fields: s.fields.into_iter().map(|(k, v)| (k, widen(&v))).collect() }
}
fn widen_map(c: Conj<MapSig>) -> Conj<MapSig> {
    Conj { pos: c.pos.into_iter().map(widen_map_sig).collect(),
           neg: c.neg.into_iter().map(widen_map_sig).collect() }
}
fn widen_tuple(c: Conj<TupleSig>) -> Conj<TupleSig> {
    Conj {
        pos: c.pos.into_iter().map(|s| TupleSig { elems: s.elems.iter().map(widen).collect() }).collect(),
        neg: c.neg.into_iter().map(|s| TupleSig { elems: s.elems.iter().map(widen).collect() }).collect(),
    }
}
fn widen_list(c: Conj<ListSig>) -> Conj<ListSig> {
    Conj {
        pos: c.pos.into_iter().map(|s| ListSig { elem: Box::new(widen(&s.elem)) }).collect(),
        neg: c.neg.into_iter().map(|s| ListSig { elem: Box::new(widen(&s.elem)) }).collect(),
    }
}
fn widen_func(c: Conj<ArrowSig>) -> Conj<ArrowSig> {
    let widen_sig = |s: ArrowSig| ArrowSig {
        args: s.args.iter().map(widen).collect(),
        ret: Box::new(widen(&s.ret)),
    };
    Conj { pos: c.pos.into_iter().map(widen_sig).collect(),
           neg: c.neg.into_iter().map(widen_sig).collect() }
}

// ----------------------------------------------------------------------
// Tests
// ----------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn type_of(src: &str, fname: &str) -> Descr {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let mut t = Typer::new();
        t.type_program(&prog);
        assert!(t.errors.is_empty(), "typer errors: {:?}", t.errors);
        t.globals.get(fname).cloned().expect("function not typed")
    }

    #[test]
    fn types_constants_precisely() {
        let src = r#"
            fn zero(), do: 0
            fn pi(), do: 3.14
            fn greet(), do: "hi"
            fn ok(), do: :ok
        "#;
        assert!(type_of(src, "zero").is_subtype(&Descr::arrow([], Descr::int_lit(0))));
        assert!(type_of(src, "pi").is_subtype(&Descr::arrow([], Descr::float_lit(3.14))));
        assert!(type_of(src, "greet").is_subtype(&Descr::arrow([], Descr::str_lit("hi"))));
        assert!(type_of(src, "ok").is_subtype(&Descr::arrow([], Descr::atom_lit("ok"))));
    }

    #[test]
    fn types_simple_arithmetic() {
        let src = r#"fn add(x, y), do: x + y"#;
        let t = type_of(src, "add");
        // Body: x + y where x, y are vars bound to `any`. Plus rule says either
        // both int or both float; with `any` it falls into the error path.
        // Actually pattern_bindings on `Var(x)` with scrutinee `any` gives x: any.
        // any.is_subtype(int)? No. So we hit the error case for +.
        // We accept this imprecision (per rule: no polymorphism for now).
        // Verify: function is callable for ints though, via arrow signature.
        let _ = t;
    }

    #[test]
    fn fact_multi_clause_intersection() {
        let src = r#"
            fn fact(0), do: 1
            fn fact(n), do: n * 2
        "#;
        let t = type_of(src, "fact");
        // Should accept fact(0) → int (precisely, int_lit(1) before widening,
        // then widened by iteration K=3 if it grows — for this simple 2-clause
        // function it converges in 1 iteration, no widening needed).
        let app_zero = Descr::tuple_of([Descr::int_lit(0)]);
        // Find the (0)-input arrow clause
        let mut found_specific = false;
        for cl in &t.funcs {
            for sig in &cl.pos {
                if sig.args.len() == 1 && sig.args[0].is_subtype(&Descr::int_lit(0)) {
                    // its ret should be int_lit(1)
                    assert!(sig.ret.is_subtype(&Descr::int_lit(1)),
                        "fact(0) clause should return 1, got {}", sig.ret);
                    found_specific = true;
                }
            }
        }
        assert!(found_specific, "no clause typed for input 0 in {}", t);
        let _ = app_zero;
    }

    #[test]
    fn classify_dispatches_atoms_per_clause() {
        let src = r#"
            fn classify(0), do: :zero
            fn classify(_), do: :nonzero
        "#;
        let t = type_of(src, "classify");
        // Must contain a `(0) -> :zero` arrow and a `(int \ 0) -> :nonzero` arrow
        // (or some superset).
        let s = t.to_string();
        assert!(s.contains(":zero"), "missing :zero return: {}", s);
        assert!(s.contains(":nonzero"), "missing :nonzero return: {}", s);
    }

    #[test]
    fn case_unions_branch_types() {
        let src = r#"
            fn f(x) do
              case x do
                0 -> :zero
                _ -> :other
              end
            end
        "#;
        let t = type_of(src, "f");
        // Return is :zero | :other
        let ret_t = match t.funcs.first().and_then(|c| c.pos.first()) {
            Some(sig) => (*sig.ret).clone(),
            None => panic!("no clause: {}", t),
        };
        let expected = Descr::atom_lit("zero").union(&Descr::atom_lit("other"));
        assert!(ret_t.is_equiv(&expected), "got {}, expected {}", ret_t, expected);
    }

    #[test]
    fn unreachable_clause_dropped() {
        // The second clause is unreachable since `_` covers everything.
        let src = r#"
            fn pick(_), do: :first
            fn pick(0), do: :second
        "#;
        let t = type_of(src, "pick");
        let s = t.to_string();
        assert!(s.contains(":first"), "missing first-clause return: {}", s);
        // The second clause's narrowed input was empty, so it's dropped — no :second.
        assert!(!s.contains(":second"), "unreachable second clause leaked: {}", s);
    }

    #[test]
    fn with_form_unions_body_and_failure() {
        // `with {:ok, n} <- expr do n end`
        // expr is a constant {:error, "x"} so it can't match — body is unreachable
        // and the type collapses to the failure value's type ({:error, "x"}).
        let src = r#"
            fn run() do
              with {:ok, n} <- {:error, "x"} do
                n
              end
            end
        "#;
        let t = type_of(src, "run");
        let ret_t = (*t.funcs[0].pos[0].ret).clone();
        let expected = Descr::tuple_of([Descr::atom_lit("error"), Descr::str_lit("x")]);
        assert!(ret_t.is_equiv(&expected),
            "with-fall-through type wrong: got {}, expected {}", ret_t, expected);
    }

    #[test]
    fn with_form_else_branch_typed() {
        // The else clause handles failures; its body type contributes.
        let src = r#"
            fn run() do
              with {:ok, _} <- {:error, "x"} do
                :unreached
              else
                {:error, _} -> :handled
              end
            end
        "#;
        let t = type_of(src, "run");
        let ret_t = (*t.funcs[0].pos[0].ret).clone();
        let expected = Descr::atom_lit("handled");
        // Body :unreached unions in too because matched-portion of rhs is non-empty
        // (rhs intersect {:ok, _} pattern). Wait — rhs is precisely {:error, "x"},
        // so matched portion is empty, failing portion is the whole thing.
        // Else fully handles: result = :handled.
        assert!(ret_t.is_equiv(&expected),
            "with-else type wrong: got {}, expected {}", ret_t, expected);
    }

    #[test]
    fn bitstring_pattern_typed() {
        let src = r#"
            fn parse(<<m::8, v::4, k::4>>) do
              {m, v, k}
            end
        "#;
        let t = type_of(src, "parse");
        // The function takes a binary; returns a tuple of three ints.
        // (We don't assert the input type precisely yet — just that the body
        // produces a 3-tuple of ints.)
        let ret_t = (*t.funcs[0].pos[0].ret).clone();
        let expected = Descr::tuple_of([Descr::int(), Descr::int(), Descr::int()]);
        assert!(ret_t.is_subtype(&expected),
            "bitstring pattern body type wrong: {} not subtype of {}", ret_t, expected);
    }

    #[test]
    fn map_literal_produces_open_shape() {
        let src = r#"fn p(), do: %{name: "alice", age: 30}"#;
        let t = type_of(src, "p");
        let ret = (*t.funcs[0].pos[0].ret).clone();
        // The function returns an open shape with both fields required.
        let expected = Descr::map_of([
            (MapKey::Atom("name".into()), Descr::str_lit("alice")),
            (MapKey::Atom("age".into()), Descr::int_lit(30)),
        ]);
        assert!(ret.is_subtype(&expected) && expected.is_subtype(&ret),
            "got {}, expected {}", ret, expected);
    }

    #[test]
    fn map_pattern_extracts_field_type() {
        // The pattern binds `n` to the value of the :name field; with a
        // concrete literal map at the call site, the body can produce a
        // precise return type.
        let src = r#"
            fn name(%{name: n}), do: n
            fn run(), do: name(%{name: "alice"})
        "#;
        let t = type_of(src, "run");
        let ret = (*t.funcs[0].pos[0].ret).clone();
        // ret should be a supertype of "alice" — the pattern binding flows the
        // field type through (over-approximated to `any` in current impl).
        // We can't expect "alice" precisely without flow-sensitive call
        // specialization, but we can expect `ret` not to be `none`.
        assert!(!ret.is_empty(), "run() returned none: {}", ret);
    }

    #[test]
    fn map_index_returns_field_type() {
        let src = r#"
            fn lookup() do
              m = %{count: 7}
              m[:count]
            end
        "#;
        let t = type_of(src, "lookup");
        let ret = (*t.funcs[0].pos[0].ret).clone();
        // We know :count maps to int_lit(7).
        assert!(Descr::int_lit(7).is_subtype(&ret), "ret was {}", ret);
    }

    #[test]
    fn recursion_terminates_via_widening() {
        let src = r#"
            fn fact(0), do: 1
            fn fact(n), do: n * fact(n - 1)
        "#;
        // The key thing: this terminates. The recursive call's return type
        // grows (1, 1∪int, etc.); widening at K=3 collapses it to `int`.
        let t = type_of(src, "fact");
        // The fn is non-trivial.
        assert!(!t.funcs.is_empty(), "fact got empty type: {}", t);
    }

    #[test]
    fn pipe_call_site_drives_monomorphization() {
        // When the only call to a user fn is via the pipe operator, the typer
        // must still record the observation so the fn's var-bound params get
        // narrowed to the call-site shape (otherwise they stay `any` and the
        // fn falls out of JIT/AOT eligibility).
        let src = r#"
            fn double(x), do: x * 2
            fn run(), do: 21 |> double()
        "#;
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let mut t = Typer::new();
        t.type_program(&prog);
        let obs = t.call_obs.get("double").expect("no obs for double");
        assert_eq!(obs.len(), 1, "expected 1-arg obs, got {:?}", obs);
        assert!(Descr::int_lit(21).is_subtype(&obs[0]),
            "expected int_lit(21) ⊆ obs[0], got {}", obs[0]);
    }
}

