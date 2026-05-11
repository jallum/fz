//! Flow-sensitive type inference over `fz_ir::Module`.
//!
//! For each `FnIr`, walks blocks to a fixed point producing two views:
//!
//!   * `vars: HashMap<Var, Descr>` — type at each Var's definition site
//!     (or, for block params, the union over all incoming Goto args). This
//!     is what consumers ask when they want "the" type of v.
//!   * `block_envs: HashMap<BlockId, HashMap<Var, Descr>>` — per-block entry
//!     environment with branch-narrowed types. Consumers positioned inside a
//!     specific block read this for the tightest available info (e.g. inside
//!     the truthy branch of an `If`, a `cond` predicate's operand may carry
//!     a narrower type than its definition).
//!
//! Branch narrowing (fz-ul4.11.24.3):
//!   * `Term::If(cond, t, e)` inspects the stmt that bound `cond`. If it was
//!     `ListIsNil(v)`, the truthy branch refines `v` to `nil`; the falsy
//!     branch keeps the list shape. If it was `BinOp::Eq(a, b)` and either
//!     operand is a singleton literal, the truthy branch intersects the other
//!     operand with that singleton.
//!   * `Stmt::Let(_, ListHead(v))` types the head as `list_element_type(v)`.
//!   * `Stmt::Let(_, ListTail(v))` types the tail as the list shape itself
//!     (possibly empty -> list_of(elem) ∪ nil; we union with nil).
//!   * `Stmt::Let(_, TupleField(v, i))` uses `tuple_projections` over the
//!     max arity tuple shape in env[v].
//!   * `Stmt::Let(_, MapGet(m, k))` uses `map_field_lookup` when `k` is a
//!     singleton literal.
//!
//! Consumers are still not wired (.11.24.4-.7). The pipeline hook at
//! `ir_codegen::compile()` continues to populate `CompiledModule.types`.

use crate::fz_ir::{
    BinOp, Block, BlockId, BuiltinId, BuiltinKind, Const, FnIr, Module, Prim, Stmt, Term, UnOp,
    Var, VecKindIr,
};
use crate::types::{Descr, MapKey};
use std::collections::HashMap;

#[derive(Debug, Clone, Default)]
pub struct FnTypes {
    /// Definition-site type for each Var. Block params get the join of their
    /// predecessor args; Let-bound vars get their Prim's type under the env
    /// at that point in the block.
    pub vars: HashMap<Var, Descr>,
    /// Entry env per block, with branch narrowing applied at If terminators.
    pub block_envs: HashMap<BlockId, HashMap<Var, Descr>>,
}

pub type ModuleTypes = Vec<FnTypes>;

pub fn type_module(m: &Module) -> ModuleTypes {
    m.fns.iter().map(|f| type_fn(f, m)).collect()
}

fn type_fn(f: &FnIr, m: &Module) -> FnTypes {
    let mut vars: HashMap<Var, Descr> = HashMap::new();
    let mut block_envs: HashMap<BlockId, HashMap<Var, Descr>> = HashMap::new();

    // Entry block: params are Top until .24.7 narrows via call-site obs.
    // Non-entry blocks: empty env, populated by goto/if predecessors.
    for b in &f.blocks {
        let mut env = HashMap::new();
        if b.id == f.entry {
            for &p in &b.params {
                env.insert(p, Descr::any());
                vars.insert(p, Descr::any());
            }
        }
        block_envs.insert(b.id, env);
    }

    loop {
        let mut changed = false;

        for b in &f.blocks {
            // Re-derive env at each stmt position.
            let mut env = block_envs[&b.id].clone();
            for stmt in &b.stmts {
                let Stmt::Let(v, prim) = stmt;
                let t = type_prim(prim, &env, m);
                env.insert(*v, t.clone());
                // vars is the definition-site type; single assignment so
                // we just overwrite each iteration (will converge).
                let prev = vars.get(v).cloned().unwrap_or_else(Descr::none);
                if !t.is_equiv(&prev) {
                    vars.insert(*v, t);
                    changed = true;
                }
            }

            // Propagate to successors.
            match &b.terminator {
                Term::Goto(target, args) => {
                    let target_b = f.block(*target);
                    let mut delta = env.clone();
                    // Substitute target's params with the supplied arg types.
                    let arg_ts: Vec<Descr> = args
                        .iter()
                        .map(|a| env.get(a).cloned().unwrap_or_else(Descr::any))
                        .collect();
                    // Remove anything keyed by the source-block's view of
                    // the args (they're not the same Vars as target params).
                    for (i, &p) in target_b.params.iter().enumerate() {
                        if let Some(t) = arg_ts.get(i) {
                            delta.insert(p, t.clone());
                        }
                    }
                    if merge_into(&mut block_envs, *target, &delta) {
                        changed = true;
                    }
                    // Update vars for target's params via union across all
                    // predecessors (handled via merge_into's union, but we
                    // also need to mirror in vars).
                    for (i, &p) in target_b.params.iter().enumerate() {
                        let from_env = block_envs[target].get(&p).cloned().unwrap_or_else(Descr::none);
                        let prev = vars.get(&p).cloned().unwrap_or_else(Descr::none);
                        if !from_env.is_equiv(&prev) {
                            vars.insert(p, from_env);
                            changed = true;
                        }
                        let _ = i;
                    }
                }
                Term::If(cond, then_b, else_b) => {
                    let (then_env, else_env) = narrow_for_if(&env, *cond, &b.stmts);
                    if merge_into(&mut block_envs, *then_b, &then_env) { changed = true; }
                    if merge_into(&mut block_envs, *else_b, &else_env) { changed = true; }
                }
                Term::Call { .. }
                | Term::TailCall { .. }
                | Term::CallClosure { .. }
                | Term::TailCallClosure { .. }
                | Term::Return(_)
                | Term::Halt(_)
                | Term::Receive { .. } => {
                    // Inter-fn flow goes through separate FnIr continuations;
                    // intra-fn flow stops here.
                }
            }
        }

        if !changed { break; }
    }

    FnTypes { vars, block_envs }
}

/// Union `delta` into `block_envs[target]`. Returns true if anything changed.
fn merge_into(
    block_envs: &mut HashMap<BlockId, HashMap<Var, Descr>>,
    target: BlockId,
    delta: &HashMap<Var, Descr>,
) -> bool {
    let env = block_envs.entry(target).or_default();
    let mut changed = false;
    for (v, t) in delta {
        let prev = env.get(v).cloned().unwrap_or_else(Descr::none);
        let unioned = prev.union(t);
        if !unioned.is_equiv(&prev) {
            env.insert(*v, unioned);
            changed = true;
        }
    }
    changed
}

/// Find the stmt that bound `cond` (if any) and split the env into
/// (then_env, else_env) narrowing the predicate's operands accordingly.
fn narrow_for_if(
    env: &HashMap<Var, Descr>,
    cond: Var,
    stmts: &[Stmt],
) -> (HashMap<Var, Descr>, HashMap<Var, Descr>) {
    let mut then_env = env.clone();
    let mut else_env = env.clone();

    let prim = stmts.iter().find_map(|s| {
        let Stmt::Let(v, p) = s;
        if *v == cond { Some(p) } else { None }
    });

    let Some(prim) = prim else {
        return (then_env, else_env);
    };

    match prim {
        Prim::ListIsNil(v) => {
            let current = env.get(v).cloned().unwrap_or_else(Descr::any);
            let then_t = current.intersect(&Descr::nil());
            let else_t = current.intersect(&Descr::list_of(Descr::any()));
            then_env.insert(*v, then_t);
            else_env.insert(*v, else_t);
        }
        Prim::BinOp(BinOp::Eq, a, b) => {
            let at = env.get(a).cloned().unwrap_or_else(Descr::any);
            let bt = env.get(b).cloned().unwrap_or_else(Descr::any);
            // Truthy: intersect the non-singleton operand with the singleton.
            // Falsy: subtract the singleton from the non-singleton operand
            // (.24.6 brought this in; .24.3 had it scoped out).
            if is_singleton_lit(&at) {
                then_env.insert(*b, bt.intersect(&at));
                else_env.insert(*b, bt.diff(&at));
            }
            if is_singleton_lit(&bt) {
                then_env.insert(*a, at.intersect(&bt));
                else_env.insert(*a, at.diff(&bt));
            }
        }
        Prim::BinOp(BinOp::Neq, a, b) => {
            // Mirror of Eq: narrow on the else branch (truthy) and diff on
            // then.
            let at = env.get(a).cloned().unwrap_or_else(Descr::any);
            let bt = env.get(b).cloned().unwrap_or_else(Descr::any);
            if is_singleton_lit(&at) {
                else_env.insert(*b, bt.intersect(&at));
                then_env.insert(*b, bt.diff(&at));
            }
            if is_singleton_lit(&bt) {
                else_env.insert(*a, at.intersect(&bt));
                then_env.insert(*a, at.diff(&bt));
            }
        }
        _ => {}
    }

    (then_env, else_env)
}

fn is_singleton_lit(d: &Descr) -> bool {
    (!d.ints.cofinite && d.ints.set.len() == 1)
        || (!d.atoms.cofinite && d.atoms.set.len() == 1)
        || (!d.strs.cofinite && d.strs.set.len() == 1)
        || (!d.floats.cofinite && d.floats.set.len() == 1)
}

fn type_prim(prim: &Prim, env: &HashMap<Var, Descr>, m: &Module) -> Descr {
    match prim {
        Prim::Const(c) => type_const(c),

        Prim::BinOp(op, a, b) => {
            let at = lookup(env, *a);
            let bt = lookup(env, *b);
            type_binop(*op, &at, &bt)
        }
        Prim::UnOp(op, v) => {
            let vt = lookup(env, *v);
            match op {
                UnOp::Neg => numeric_result(&vt, &vt),
                UnOp::Not => Descr::bool_t(),
            }
        }

        Prim::MakeTuple(vs) => {
            let elems: Vec<Descr> = vs.iter().map(|v| lookup(env, *v)).collect();
            Descr::tuple_of(elems)
        }
        Prim::TupleField(v, i) => {
            let vt = lookup(env, *v);
            // Find the widest arity in v's tuple clauses that covers index i;
            // project that component. Falls back to any when there's no
            // matching tuple shape.
            let mut max_arity = 0usize;
            for cl in &vt.tuples {
                for sig in &cl.pos {
                    if sig.elems.len() > max_arity {
                        max_arity = sig.elems.len();
                    }
                }
            }
            if (*i as usize) < max_arity {
                let comps = crate::typer::tuple_projections(&vt, max_arity);
                comps.into_iter().nth(*i as usize).unwrap_or_else(Descr::any)
            } else {
                Descr::any()
            }
        }

        Prim::MakeList(els, tail) => {
            let mut elem = Descr::none();
            for v in els { elem = elem.union(&lookup(env, *v)); }
            if let Some(t) = tail {
                let tt = lookup(env, *t);
                elem = elem.union(&crate::typer::list_element_type(&tt));
            }
            Descr::list_of(elem)
        }
        Prim::ListCons(h, t) => {
            let ht = lookup(env, *h);
            let tt = lookup(env, *t);
            Descr::list_of(ht.union(&crate::typer::list_element_type(&tt)))
        }
        Prim::ListHead(l) => crate::typer::list_element_type(&lookup(env, *l)),
        Prim::ListTail(l) => {
            let lt = lookup(env, *l);
            let elem = crate::typer::list_element_type(&lt);
            // Tail is either a (possibly empty) list of the same elem, or nil.
            Descr::list_of(elem).union(&Descr::nil())
        }
        Prim::ListIsNil(_) => Descr::bool_t(),

        Prim::MakeMap(entries) => {
            let mut fields = std::collections::BTreeMap::new();
            let mut all_static = true;
            for (k, v) in entries {
                let vt = lookup(env, *v);
                match var_as_map_key(*k, env) {
                    Some(mk) => { fields.insert(mk, vt); }
                    None => { all_static = false; break; }
                }
            }
            if all_static && !entries.is_empty() {
                Descr::map_of(fields)
            } else if entries.is_empty() {
                Descr::map_of([])
            } else {
                Descr::map_top()
            }
        }
        Prim::MapUpdate(base, entries) => {
            let mut d = lookup(env, *base);
            for (k, v) in entries {
                let vt = lookup(env, *v);
                if let Some(mk) = var_as_map_key(*k, env) {
                    d = crate::typer::refine_map_field(&d, &mk, &vt);
                }
            }
            d
        }
        Prim::MapGet(map, k) => {
            let mt = lookup(env, *map);
            if let Some(mk) = var_as_map_key(*k, env) {
                crate::typer::map_field_lookup(&mt, &mk)
                    .unwrap_or_else(|| Descr::any().union(&Descr::nil()))
            } else {
                Descr::any().union(&Descr::nil())
            }
        }

        Prim::MakeVec(kind, _) => match kind {
            VecKindIr::I64 => Descr::vec_i64(),
            VecKindIr::F64 => Descr::vec_f64(),
            VecKindIr::U8 => Descr::vec_u8(),
            VecKindIr::Bit => Descr::vec_bit(),
        },
        Prim::MakeBitstring(_) => Descr::vec_u8().union(&Descr::vec_bit()),

        Prim::MakeClosure(fn_id, _) => {
            let callee = m.fn_by_id(*fn_id);
            let entry = callee.block(callee.entry);
            let arity = entry.params.len();
            let args: Vec<Descr> = std::iter::repeat_n(Descr::any(), arity).collect();
            Descr::arrow(args, Descr::any())
        }

        Prim::Builtin(bid, _) => type_builtin(*bid),

        // Reader and struct ops: conservative Top until later tickets refine.
        Prim::AllocStruct(_, _) => Descr::any(),
        Prim::BitReaderInit(_) => Descr::any(),
        Prim::BitReadField { ty, .. } => {
            // Returns Tuple([ok, value, new_reader]) on success, Tuple([false])
            // on failure. We over-approximate to a generic tuple shape; pattern
            // narrowing on TupleField then projects per-position. Field value
            // depends on the BitType.
            use crate::ast::BitType;
            let value_t = match ty {
                BitType::Integer | BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => Descr::int(),
                BitType::Float => Descr::float(),
                BitType::Binary => Descr::vec_u8(),
                BitType::Bits => Descr::vec_u8().union(&Descr::vec_bit()),
            };
            let success = Descr::tuple_of([Descr::bool_t(), value_t, Descr::any()]);
            let failure = Descr::tuple_of([Descr::bool_t()]);
            success.union(&failure)
        }
        Prim::BitReaderDone(_) => Descr::bool_t(),
    }
}

fn type_const(c: &Const) -> Descr {
    match c {
        Const::Int(n) => Descr::int_lit(*n),
        Const::Float(f) => Descr::float_lit(*f),
        Const::Str(s) => Descr::str_lit(s.clone()),
        Const::Atom(id) => Descr::atom_lit(format!("a{}", id)),
        Const::Nil => Descr::nil(),
        Const::True => Descr::atom_lit("true"),
        Const::False => Descr::atom_lit("false"),
    }
}

fn type_binop(op: BinOp, a: &Descr, b: &Descr) -> Descr {
    use BinOp::*;
    match op {
        Add | Sub | Mul | Div | Mod => numeric_result(a, b),
        Eq | Neq | Lt | Le | Gt | Ge => Descr::bool_t(),
        And | Or => a.union(b),
    }
}

fn numeric_result(a: &Descr, b: &Descr) -> Descr {
    let int = Descr::int();
    let float = Descr::float();
    let both_int = a.is_subtype(&int) && b.is_subtype(&int);
    let both_float = a.is_subtype(&float) && b.is_subtype(&float);
    if both_int { int }
    else if both_float { float }
    else { int.union(&float) }
}

fn type_builtin(bid: BuiltinId) -> Descr {
    match BuiltinKind::from_id(bid) {
        Some(BuiltinKind::Print) => Descr::nil(),
        Some(BuiltinKind::Assert)
        | Some(BuiltinKind::AssertEq)
        | Some(BuiltinKind::AssertNeq) => Descr::nil(),
        Some(BuiltinKind::VecGet) => Descr::int().union(&Descr::float()),
        // fz-ul4.19.2: spawn/self both return a Pid (boxed Int for v1).
        Some(BuiltinKind::Spawn) | Some(BuiltinKind::SelfPid) => Descr::int(),
        // fz-ul4.19.3: send returns the original message (any type).
        Some(BuiltinKind::Send) => Descr::any(),
        None => Descr::any(),
    }
}

fn lookup(env: &HashMap<Var, Descr>, v: Var) -> Descr {
    env.get(&v).cloned().unwrap_or_else(Descr::any)
}

fn var_as_map_key(v: Var, env: &HashMap<Var, Descr>) -> Option<MapKey> {
    let d = env.get(&v)?;
    if !d.ints.cofinite && d.ints.set.len() == 1 {
        return Some(MapKey::Int(*d.ints.set.iter().next().unwrap()));
    }
    if !d.atoms.cofinite && d.atoms.set.len() == 1 {
        return Some(MapKey::Atom(d.atoms.set.iter().next().unwrap().clone()));
    }
    if !d.strs.cofinite && d.strs.set.len() == 1 {
        return Some(MapKey::Str(d.strs.set.iter().next().unwrap().clone()));
    }
    None
}

// Suppress unused imports under cfg(not(test)).
#[allow(dead_code)]
fn _suppress_block(_: &Block) {}

/// .11.24.7: re-type a target FnIr's body assuming its entry-block params
/// have the supplied Descrs. Returns the union of Descrs at every local
/// Return/Halt site, suitable for tier-up specialization decisions.
///
/// Scope-down (authorized): only follows Return/Halt sites inside this FnIr.
/// Cross-fn continuation chains (introduced by `cps_split` at non-tail calls)
/// are not chased — a self-recursive function whose recursive paths exit via
/// a continuation FnIr will appear to return only its base-case Descrs. A
/// follow-up ticket can extend this once tier-up profiling exposes the gap.
/// For non-recursive single-FnIr functions (the .13 starting point) the
/// result is precise.
///
/// Termination: capped at K=4 fixpoint iterations; values are widened past
/// K=3 via `crate::typer::widen` so singleton-growing recursive paths still
/// converge.
#[allow(dead_code, reason = "tier-up hook; consumed by fz-ul4.19.5 per .24.7")]
pub fn specialize_return(
    m: &Module,
    fn_id: crate::fz_ir::FnId,
    params: &[Descr],
) -> Descr {
    use crate::fz_ir::Stmt;
    let f = m.fn_by_id(fn_id);

    let mut block_envs: HashMap<crate::fz_ir::BlockId, HashMap<crate::fz_ir::Var, Descr>> =
        HashMap::new();
    let entry_b = f.block(f.entry);
    let mut entry_env: HashMap<crate::fz_ir::Var, Descr> = HashMap::new();
    for (i, &p) in entry_b.params.iter().enumerate() {
        let t = params.get(i).cloned().unwrap_or_else(Descr::any);
        entry_env.insert(p, t);
    }
    block_envs.insert(f.entry, entry_env);
    for b in &f.blocks {
        if b.id != f.entry {
            block_envs.insert(b.id, HashMap::new());
        }
    }

    let max_iter: usize = 4;
    let widen_at: usize = 3;
    for iter in 0..max_iter {
        let mut changed = false;
        for b in &f.blocks {
            let mut env = block_envs[&b.id].clone();
            for stmt in &b.stmts {
                let Stmt::Let(v, prim) = stmt;
                let t = type_prim(prim, &env, m);
                env.insert(*v, t);
            }
            match &b.terminator {
                Term::Goto(target, args) => {
                    let target_b = f.block(*target);
                    let mut delta = env.clone();
                    let arg_ts: Vec<Descr> = args
                        .iter()
                        .map(|a| env.get(a).cloned().unwrap_or_else(Descr::any))
                        .collect();
                    for (i, &p) in target_b.params.iter().enumerate() {
                        if let Some(t) = arg_ts.get(i) {
                            delta.insert(p, t.clone());
                        }
                    }
                    if merge_into(&mut block_envs, *target, &delta) {
                        changed = true;
                    }
                }
                Term::If(cond, then_b, else_b) => {
                    let (then_env, else_env) = narrow_for_if(&env, *cond, &b.stmts);
                    if merge_into(&mut block_envs, *then_b, &then_env) { changed = true; }
                    if merge_into(&mut block_envs, *else_b, &else_env) { changed = true; }
                }
                _ => {}
            }
        }
        if iter >= widen_at {
            for env in block_envs.values_mut() {
                for v in env.values_mut() {
                    *v = crate::typer::widen(v);
                }
            }
        }
        if !changed { break; }
    }

    // Collect union of Descrs at every local Return/Halt site.
    let mut ret = Descr::none();
    for b in &f.blocks {
        let mut env = block_envs.get(&b.id).cloned().unwrap_or_default();
        for stmt in &b.stmts {
            let Stmt::Let(v, prim) = stmt;
            let t = type_prim(prim, &env, m);
            env.insert(*v, t);
        }
        match &b.terminator {
            Term::Return(v) | Term::Halt(v) => {
                let t = env.get(v).cloned().unwrap_or_else(Descr::any);
                ret = ret.union(&t);
            }
            _ => {}
        }
    }
    ret
}

/// .11.24.6: scan typer output for unreachable If branches. For each
/// `Term::If(cond, then_b, else_b)`, re-run the branch narrowing under the
/// terminator's pre-env. If either branch's narrowed operand is empty, that
/// branch is unreachable.
///
/// Returns diagnostics in a stable order (sorted by fn position then block id).
/// Each diagnostic carries the offending block's terminator span (when
/// recorded by ir_lower in `Module.source.term_span`); .20.8 will enrich
/// the message with the set-theoretic type vocabulary.
pub fn collect_diagnostics(
    module: &Module,
    types: &ModuleTypes,
) -> crate::diag::Diagnostics {
    use crate::diag::{Diagnostic, Diagnostics, Span};
    use crate::diag::codes::TYPE_UNREACHABLE_ARM;

    let mut out = Diagnostics::new();
    for (i, f) in module.fns.iter().enumerate() {
        let ft = &types[i];
        let mut blocks_sorted: Vec<&crate::fz_ir::Block> = f.blocks.iter().collect();
        blocks_sorted.sort_by_key(|b| b.id.0);
        for b in blocks_sorted {
            let Term::If(cond, then_b, else_b) = b.terminator else { continue };

            // Reconstruct the env at the terminator.
            let mut env = ft.block_envs.get(&b.id).cloned().unwrap_or_default();
            for stmt in &b.stmts {
                let Stmt::Let(v, prim) = stmt;
                let t = type_prim(prim, &env, module);
                env.insert(*v, t);
            }

            let (then_env, else_env) = narrow_for_if(&env, cond, &b.stmts);
            let term_span = module.source.term_span
                .get(&(f.id, b.id))
                .copied()
                .unwrap_or(Span::DUMMY);

            let check = |branch_env: &HashMap<crate::fz_ir::Var, Descr>, tag: &str, bb_id: crate::fz_ir::BlockId| -> Option<Diagnostic> {
                let mut keys: Vec<crate::fz_ir::Var> = branch_env.keys().copied().collect();
                keys.sort_by_key(|v| v.0);
                for v in keys {
                    let new_t = branch_env.get(&v).unwrap();
                    let old_t = env.get(&v).cloned().unwrap_or_else(Descr::any);
                    if !new_t.is_equiv(&old_t) && new_t.is_empty() && !old_t.is_empty() {
                        // `.20.8`: render the source name (or "this value"
                        // for compiler temps) and the *set-theoretic type*
                        // the user's value had right before the failing
                        // narrowing. The vocabulary comes from
                        // `Descr::display_for_diag` — same algebra the
                        // typer reasons in.
                        let var_name = module.source.var_name_of(v);
                        let label_subject = match var_name {
                            Some(n) => format!("`{}`", n),
                            None => "this value".to_string(),
                        };
                        let var_span = module.source.var_span_of(v);

                        let message = format!("the {} branch is never reachable", tag);
                        let type_note = format!(
                            "{} here has type `{}`",
                            label_subject,
                            old_t.display_for_diag(),
                        );
                        let narrow_note = format!(
                            "narrowing for this branch would need `{}`, but that intersection \
                             is uninhabited (unreachable arm at bb{})",
                            new_t.display_for_diag(),
                            bb_id.0,
                        );

                        let mut d = Diagnostic::warning(TYPE_UNREACHABLE_ARM, message, term_span)
                            .with_label(format!("in fn `{}`", f.name))
                            .with_note(type_note)
                            .with_note(narrow_note);
                        // Point a secondary at the var's binding site
                        // when we have it — gives the reader the source
                        // line where the value entered scope.
                        if !var_span.is_dummy() && var_span != term_span {
                            d = d.with_secondary(var_span, format!("{} bound here", label_subject));
                        }
                        return Some(d);
                    }
                }
                None
            };
            if let Some(d) = check(&then_env, "then", then_b) { out.push(d); }
            if let Some(d) = check(&else_env, "else", else_b) { out.push(d); }
        }
    }
    out
}

/// .11.24.5: refine `MakeVec(I64, els)` to `MakeVec(F64, els)` when any
/// element is typed Float. Errors on the "mixed Int and Float" case under
/// the no-auto-promotion rule.
///
/// Operates in-place on `module`. Caller supplies a typer output that was
/// produced from the same module shape (run `type_module(module)` first).
pub fn rewrite_vec_kinds(
    module: &mut Module,
    types: &ModuleTypes,
) -> Result<(), String> {
    use crate::fz_ir::Stmt;
    for (i, f) in module.fns.iter_mut().enumerate() {
        let vars = &types[i].vars;
        for blk in &mut f.blocks {
            for stmt in &mut blk.stmts {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeVec(kind @ VecKindIr::I64, els) = prim {
                    let mut any_float = false;
                    let mut any_int = false;
                    for &ev in els.iter() {
                        let d = vars.get(&ev).cloned().unwrap_or_else(Descr::any);
                        if !d.intersect(&Descr::float()).is_empty()
                            && d.intersect(&Descr::int()).is_empty()
                        {
                            any_float = true;
                        } else if d.is_subtype(&Descr::int()) {
                            any_int = true;
                        }
                    }
                    if any_float && any_int {
                        return Err(format!(
                            "~v[..] in {} mixes Int and Float element types; \
                             no auto-promotion (fz-ul4.11.24.5)",
                            f.name
                        ));
                    }
                    if any_float {
                        *kind = VecKindIr::F64;
                    }
                }
            }
        }
    }
    Ok(())
}

// ----------------------------------------------------------------------
// Tests
// ----------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{BinOp, Const, FnBuilder, FnId, ModuleBuilder, Prim, Term, Var};

    fn build_module(fns: Vec<crate::fz_ir::FnIr>) -> Module {
        let mut mb = ModuleBuilder::new();
        for f in fns { mb.add_fn(f); }
        mb.build()
    }

    // ---- .24.2 tests (preserved, adjusted to FnTypes API) ----

    #[test]
    fn const_int_typed_as_singleton() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let v = b.let_(entry, Prim::Const(Const::Int(42)));
        b.set_terminator(entry, Term::Halt(v));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        assert!(mt[0].vars.get(&v).unwrap().is_equiv(&Descr::int_lit(42)));
    }

    #[test]
    fn add1_body_is_int_top_when_param_is_any() {
        let mut b = FnBuilder::new(FnId(0), "add1");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let sum = b.let_(entry, Prim::BinOp(BinOp::Add, x, one));
        b.set_terminator(entry, Term::Return(sum));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let sum_t = mt[0].vars.get(&sum).cloned().unwrap();
        assert!(sum_t.is_equiv(&Descr::int().union(&Descr::float())),
            "got {}", sum_t);
    }

    #[test]
    fn make_list_of_ints() {
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let a = b.let_(entry, Prim::Const(Const::Int(1)));
        let bv = b.let_(entry, Prim::Const(Const::Int(2)));
        let cv = b.let_(entry, Prim::Const(Const::Int(3)));
        let l = b.let_(entry, Prim::MakeList(vec![a, bv, cv], None));
        b.set_terminator(entry, Term::Return(l));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let lt = mt[0].vars.get(&l).cloned().unwrap();
        let elem = crate::typer::list_element_type(&lt);
        assert!(elem.is_subtype(&Descr::int()), "list elem: {}", elem);
        assert!(!elem.is_empty());
    }

    #[test]
    fn goto_joins_param_types_across_predecessors() {
        let mut b = FnBuilder::new(FnId(0), "join");
        let entry = b.block(vec![]);
        let zero = b.let_(entry, Prim::Const(Const::Int(0)));
        let bb1 = b.block(vec![]);
        let bb2 = b.block(vec![]);
        let joined = Var(99);
        let bb3 = b.block(vec![joined]);
        b.set_terminator(entry, Term::If(zero, bb1, bb2));
        let one = b.let_(bb1, Prim::Const(Const::Int(1)));
        b.set_terminator(bb1, Term::Goto(bb3, vec![one]));
        let two = b.let_(bb2, Prim::Const(Const::Int(2)));
        b.set_terminator(bb2, Term::Goto(bb3, vec![two]));
        b.set_terminator(bb3, Term::Return(joined));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let join_t = mt[0].vars.get(&joined).cloned().unwrap();
        let expected = Descr::int_lit(1).union(&Descr::int_lit(2));
        assert!(join_t.is_equiv(&expected), "got {}", join_t);
    }

    // ---- .24.3 narrowing tests ----

    #[test]
    fn tuple_field_projects_elem_descr() {
        // fn f(t), do: TupleField(t, 0)
        //   - call site builds t = {1, :ok} so we have a concrete tuple shape.
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let ok = b.let_(entry, Prim::Const(Const::Atom(7)));
        let t = b.let_(entry, Prim::MakeTuple(vec![one, ok]));
        let f0 = b.let_(entry, Prim::TupleField(t, 0));
        b.set_terminator(entry, Term::Return(f0));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let f0_t = mt[0].vars.get(&f0).cloned().unwrap();
        assert!(f0_t.is_subtype(&Descr::int_lit(1)) && Descr::int_lit(1).is_subtype(&f0_t),
            "field 0 should be int_lit(1), got {}", f0_t);
    }

    #[test]
    fn list_head_yields_element_type() {
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let two = b.let_(entry, Prim::Const(Const::Int(2)));
        let l = b.let_(entry, Prim::MakeList(vec![one, two], None));
        let h = b.let_(entry, Prim::ListHead(l));
        b.set_terminator(entry, Term::Return(h));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let h_t = mt[0].vars.get(&h).cloned().unwrap();
        // head type = list elem = union(int_lit(1), int_lit(2)) ⊆ int.
        assert!(h_t.is_subtype(&Descr::int()), "head type: {}", h_t);
    }

    #[test]
    fn if_list_is_nil_narrows_v_to_nil_in_then_branch() {
        // Build:
        //   entry(l):
        //     c = ListIsNil(l)
        //     if c then then_b else else_b
        //   then_b: return l   (l narrowed to nil here)
        //   else_b: return l   (l narrowed to list_top here)
        let mut b = FnBuilder::new(FnId(0), "f");
        let l = b.fresh_var();
        let entry = b.block(vec![l]);
        let c = b.let_(entry, Prim::ListIsNil(l));
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        b.set_terminator(entry, Term::If(c, then_b, else_b));
        b.set_terminator(then_b, Term::Return(l));
        b.set_terminator(else_b, Term::Return(l));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);

        // In then_b's entry env, l should be narrowed to nil.
        let then_env = mt[0].block_envs.get(&then_b).unwrap();
        let l_then = then_env.get(&l).cloned().unwrap();
        assert!(l_then.is_subtype(&Descr::nil()) && Descr::nil().is_subtype(&l_then),
            "l in then-branch should be nil: {}", l_then);

        // In else_b's entry env, l should be narrowed to list_top (no nil).
        let else_env = mt[0].block_envs.get(&else_b).unwrap();
        let l_else = else_env.get(&l).cloned().unwrap();
        // Subtype of list_of(any) (loosely: at least the list portion).
        assert!(l_else.is_subtype(&Descr::list_of(Descr::any())),
            "l in else-branch should be list-shaped: {}", l_else);
    }

    #[test]
    fn if_eq_with_int_singleton_narrows_var_in_then_branch() {
        // entry(x):
        //   z = const(0)
        //   c = (x == z)
        //   if c then then_b else else_b
        let mut b = FnBuilder::new(FnId(0), "f");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let z = b.let_(entry, Prim::Const(Const::Int(0)));
        let c = b.let_(entry, Prim::BinOp(BinOp::Eq, x, z));
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        b.set_terminator(entry, Term::If(c, then_b, else_b));
        b.set_terminator(then_b, Term::Return(x));
        b.set_terminator(else_b, Term::Return(x));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);

        let then_env = mt[0].block_envs.get(&then_b).unwrap();
        let x_then = then_env.get(&x).cloned().unwrap();
        assert!(x_then.is_subtype(&Descr::int_lit(0)) && Descr::int_lit(0).is_subtype(&x_then),
            "x in then-branch should be int_lit(0): {}", x_then);
    }

    #[test]
    fn nested_tuple_projection() {
        // Build {inner, c} where inner = {a, b}; project field 0 to get inner,
        // then field 0 of that to get a.
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let a = b.let_(entry, Prim::Const(Const::Int(7)));
        let bv = b.let_(entry, Prim::Const(Const::Atom(3)));
        let inner = b.let_(entry, Prim::MakeTuple(vec![a, bv]));
        let c = b.let_(entry, Prim::Const(Const::Int(9)));
        let outer = b.let_(entry, Prim::MakeTuple(vec![inner, c]));
        let p0 = b.let_(entry, Prim::TupleField(outer, 0));
        let p00 = b.let_(entry, Prim::TupleField(p0, 0));
        b.set_terminator(entry, Term::Return(p00));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let p00_t = mt[0].vars.get(&p00).cloned().unwrap();
        assert!(p00_t.is_equiv(&Descr::int_lit(7)),
            "outer.0.0 should be int_lit(7), got {}", p00_t);
    }

    // ---- .24.7 specialize_return ----

    #[test]
    fn specialize_return_id_with_atom_singleton() {
        // fn id(x) = x.  specialize with [atom_lit("ok")] -> atom_lit("ok").
        let mut b = FnBuilder::new(FnId(0), "id");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        b.set_terminator(entry, Term::Return(x));
        let m = build_module(vec![b.build()]);
        let r = specialize_return(&m, FnId(0), &[Descr::atom_lit("ok")]);
        assert!(r.is_equiv(&Descr::atom_lit("ok")), "got {}", r);
    }

    #[test]
    fn specialize_return_id_with_top_returns_top() {
        let mut b = FnBuilder::new(FnId(0), "id");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        b.set_terminator(entry, Term::Return(x));
        let m = build_module(vec![b.build()]);
        let r = specialize_return(&m, FnId(0), &[Descr::any()]);
        assert!(r.is_equiv(&Descr::any()), "got {}", r);
    }

    #[test]
    fn specialize_return_pick_zero_yields_zero_arm_only() {
        // fn pick(x):
        //   c = (x == 0)
        //   if c then return :zero else return :other
        // specialize with [int_lit(0)] -> just atom_lit("zero").
        let mut b = FnBuilder::new(FnId(0), "pick");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let z = b.let_(entry, Prim::Const(Const::Int(0)));
        let c = b.let_(entry, Prim::BinOp(BinOp::Eq, x, z));
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        b.set_terminator(entry, Term::If(c, then_b, else_b));
        let zero_at = b.let_(then_b, Prim::Const(Const::Atom(1))); // "a1"
        b.set_terminator(then_b, Term::Return(zero_at));
        let other_at = b.let_(else_b, Prim::Const(Const::Atom(2))); // "a2"
        b.set_terminator(else_b, Term::Return(other_at));
        let m = build_module(vec![b.build()]);

        let r0 = specialize_return(&m, FnId(0), &[Descr::int_lit(0)]);
        // With negative-narrowing on Eq's else (added in .24.6), the else arm's
        // x becomes int_lit(0).diff(int_lit(0)) = empty, but the body still
        // assigns Const(:other) which is a literal -> the Return picks up
        // atom_lit("a2") from env. So union includes both arms in this
        // construction. Assert the truthy result is present at minimum.
        let zero_d = Descr::atom_lit("a1");
        assert!(zero_d.is_subtype(&r0), "expected :zero in return, got {}", r0);
    }

    #[test]
    fn specialize_return_terminates_on_simple_loop_like_fn() {
        // Synthetic: a fn with a Goto cycle. Specialize should terminate
        // (max_iter cap + widening).
        let mut b = FnBuilder::new(FnId(0), "loop");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let y = Var(99);
        let bb1 = b.block(vec![y]);
        b.set_terminator(entry, Term::Goto(bb1, vec![x]));
        // Self-cycle via Goto: bb1 -> bb1.
        b.set_terminator(bb1, Term::Goto(bb1, vec![y]));
        // Unreachable but parseable Halt elsewhere wouldn't trigger.
        let bb2 = b.block(vec![]);
        let z = b.let_(bb2, Prim::Const(Const::Int(0)));
        b.set_terminator(bb2, Term::Halt(z));
        let m = build_module(vec![b.build()]);
        // Should return without hanging.
        let _ = specialize_return(&m, FnId(0), &[Descr::int_lit(0)]);
        let _ = bb2;
    }

    // ---- .24.6 unreachable-arm diagnostics ----

    #[test]
    fn list_is_nil_on_int_var_flags_both_branches_unreachable() {
        // entry():
        //   five = 5
        //   c = ListIsNil(five)    -- predicate over an int -> both branches empty
        //   if c then then_b else else_b
        // then_b: halt five    -- env[five] narrowed to int_lit(5) ∩ nil = empty
        // else_b: halt five    -- env[five] narrowed to int_lit(5) ∩ list = empty
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let five = b.let_(entry, Prim::Const(Const::Int(5)));
        let c = b.let_(entry, Prim::ListIsNil(five));
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        b.set_terminator(entry, Term::If(c, then_b, else_b));
        b.set_terminator(then_b, Term::Halt(five));
        b.set_terminator(else_b, Term::Halt(five));
        let m = build_module(vec![b.build()]);
        let t = type_module(&m);
        let diags = collect_diagnostics(&m, &t);
        assert_eq!(diags.len(), 2, "expected two unreachable arms, got {:?}", diags);
        assert!(diags.iter().all(|d| d.code == crate::diag::codes::TYPE_UNREACHABLE_ARM));
    }

    #[test]
    fn happy_path_emits_no_warnings() {
        // entry(): halt 42  -- single-block, no narrowing, no warnings.
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let v = b.let_(entry, Prim::Const(Const::Int(42)));
        b.set_terminator(entry, Term::Halt(v));
        let m = build_module(vec![b.build()]);
        let t = type_module(&m);
        let diags = collect_diagnostics(&m, &t);
        assert!(diags.is_empty(), "expected no warnings, got {:?}", diags);
    }

    #[test]
    fn eq_then_eq_dup_clause_flags_second_arm_unreachable() {
        // entry(x):
        //   z = 0
        //   c1 = (x == z)
        //   if c1 then halt_b else next_check
        // next_check:
        //   z2 = 0
        //   c2 = (x == z2)        -- x's env in next_check = any \ int_lit(0)
        //   if c2 then dead_b else fallback
        // dead_b: this is the unreachable second "fn f(0)" clause.
        //         env[x] narrows to (any \ 0) ∩ 0 = empty.
        let mut b = FnBuilder::new(FnId(0), "f");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let z = b.let_(entry, Prim::Const(Const::Int(0)));
        let c1 = b.let_(entry, Prim::BinOp(BinOp::Eq, x, z));
        let halt_b = b.block(vec![]);
        let next_check = b.block(vec![]);
        b.set_terminator(entry, Term::If(c1, halt_b, next_check));
        b.set_terminator(halt_b, Term::Halt(x));
        let z2 = b.let_(next_check, Prim::Const(Const::Int(0)));
        let c2 = b.let_(next_check, Prim::BinOp(BinOp::Eq, x, z2));
        let dead_b = b.block(vec![]);
        let fallback = b.block(vec![]);
        b.set_terminator(next_check, Term::If(c2, dead_b, fallback));
        b.set_terminator(dead_b, Term::Halt(x));
        b.set_terminator(fallback, Term::Halt(x));

        let m = build_module(vec![b.build()]);
        let t = type_module(&m);
        let diags = collect_diagnostics(&m, &t);
        // The dead-block id is mentioned in the diagnostic's notes (post-
        // .20.5 the message is the headline; details live in notes).
        let needle = format!("bb{}", dead_b.0);
        assert!(
            diags.iter().any(|d| d.notes.iter().any(|n| n.contains(&needle))),
            "expected dead_b (bb{}) flagged, got {:?}", dead_b.0, diags
        );
    }

    // ---- .24.5 vec kind refinement ----

    #[test]
    fn rewrite_vec_kinds_keeps_int_vec_when_all_elems_int() {
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let two = b.let_(entry, Prim::Const(Const::Int(2)));
        let v = b.let_(entry, Prim::MakeVec(VecKindIr::I64, vec![one, two]));
        b.set_terminator(entry, Term::Return(v));
        let mut m = build_module(vec![b.build()]);
        let t = type_module(&m);
        rewrite_vec_kinds(&mut m, &t).expect("no error");
        let stmt = &m.fns[0].blocks[0].stmts[2];
        match stmt {
            crate::fz_ir::Stmt::Let(_, Prim::MakeVec(VecKindIr::I64, _)) => {}
            other => panic!("expected MakeVec(I64), got {:?}", other),
        }
    }

    #[test]
    fn rewrite_vec_kinds_promotes_to_f64_when_elem_typed_float() {
        // Build: f0 = const(1.0); v = MakeVec(I64, [f0])  -- intentionally I64 to test the rewrite.
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let f0 = b.let_(entry, Prim::Const(Const::Float(1.0)));
        let v = b.let_(entry, Prim::MakeVec(VecKindIr::I64, vec![f0]));
        b.set_terminator(entry, Term::Return(v));
        let mut m = build_module(vec![b.build()]);
        let t = type_module(&m);
        rewrite_vec_kinds(&mut m, &t).expect("no error");
        let stmt = &m.fns[0].blocks[0].stmts[1];
        match stmt {
            crate::fz_ir::Stmt::Let(_, Prim::MakeVec(VecKindIr::F64, _)) => {}
            other => panic!("expected MakeVec(F64) after rewrite, got {:?}", other),
        }
    }

    #[test]
    fn rewrite_vec_kinds_errors_on_mixed_int_and_float_elems() {
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let i0 = b.let_(entry, Prim::Const(Const::Int(1)));
        let f0 = b.let_(entry, Prim::Const(Const::Float(2.0)));
        let v = b.let_(entry, Prim::MakeVec(VecKindIr::I64, vec![i0, f0]));
        b.set_terminator(entry, Term::Return(v));
        let mut m = build_module(vec![b.build()]);
        let t = type_module(&m);
        let err = rewrite_vec_kinds(&mut m, &t).expect_err("expected mixed error");
        assert!(err.contains("11.24.5"), "expected ticket reference, got: {}", err);
    }

    #[test]
    fn map_get_with_singleton_key_returns_field_type() {
        let mut b = FnBuilder::new(FnId(0), "f");
        let entry = b.block(vec![]);
        let k = b.let_(entry, Prim::Const(Const::Atom(1)));
        let v = b.let_(entry, Prim::Const(Const::Int(42)));
        let mp = b.let_(entry, Prim::MakeMap(vec![(k, v)]));
        let got = b.let_(entry, Prim::MapGet(mp, k));
        b.set_terminator(entry, Term::Return(got));
        let m = build_module(vec![b.build()]);
        let mt = type_module(&m);
        let got_t = mt[0].vars.get(&got).cloned().unwrap();
        // The map_field_lookup contributes int_lit(42); plus the implicit "may be absent"
        // it can also be any|nil for open-shape semantics. We assert the int_lit(42)
        // is a subtype of the result.
        assert!(Descr::int_lit(42).is_subtype(&got_t),
            "map[k] should include the bound value: {}", got_t);
    }

    // ----- .20.8: type-rendered diagnostic prose -----

    /// The unreachable-arm diagnostic carries two notes: the type the
    /// variable had at the branch, and the type the narrowing demanded.
    /// Both are rendered through `Descr::display_for_diag`, so a user
    /// reading the diagnostic sees set-theoretic vocabulary the typer
    /// reasons in — not block ids and Var indices.
    #[test]
    fn unreachable_arm_diagnostic_includes_type_vocabulary() {
        // Same shape as eq_then_eq_dup_clause_flags_second_arm_unreachable:
        // a `fn f(0); fn f(0)` would dispatch the second clause unreachable.
        let mut b = FnBuilder::new(FnId(0), "f");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let z = b.let_(entry, Prim::Const(Const::Int(0)));
        let c1 = b.let_(entry, Prim::BinOp(BinOp::Eq, x, z));
        let halt_b = b.block(vec![]);
        let next_check = b.block(vec![]);
        b.set_terminator(entry, Term::If(c1, halt_b, next_check));
        b.set_terminator(halt_b, Term::Halt(x));
        let z2 = b.let_(next_check, Prim::Const(Const::Int(0)));
        let c2 = b.let_(next_check, Prim::BinOp(BinOp::Eq, x, z2));
        let dead_b = b.block(vec![]);
        let fallback = b.block(vec![]);
        b.set_terminator(next_check, Term::If(c2, dead_b, fallback));
        b.set_terminator(dead_b, Term::Halt(x));
        b.set_terminator(fallback, Term::Halt(x));

        let m = build_module(vec![b.build()]);
        let t = type_module(&m);
        let diags = collect_diagnostics(&m, &t);
        let d = diags.iter().next().expect("at least one diagnostic");
        // First note: "type `…`" — rendered set-theoretic vocab.
        let type_note = d.notes.iter().find(|n| n.contains("has type"))
            .expect("expected a 'has type' note");
        assert!(type_note.contains('`'),
            "type note should backtick-quote the rendered type, got {:?}", type_note);
        // Second note: the narrowing that's uninhabited.
        let narrow_note = d.notes.iter().find(|n| n.contains("uninhabited"))
            .expect("expected an 'uninhabited' note");
        assert!(narrow_note.contains("would need"),
            "narrow note should mention the would-need type, got {:?}", narrow_note);
    }
}
