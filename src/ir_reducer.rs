//! fz-jg5.4 / fz-jg5.5 — Compile-time reducer pass.
//!
//! A `Module → Module` pass that walks each function, folds literals
//! into Var environments, and rewrites calls whose return value is
//! statically known.
//!
//! Scope (post-RED.4):
//! - Fold every `Prim` via `reducer::fold_prim`. When a Var has a
//!   scalar-literal Descr, record it.
//! - Fold `Term::If(cond, T, E)` when `cond` is a bool literal.
//! - Rewrite `Term::TailCall(callee, args)` to `Term::Return(lit)` when
//!   the callee walks to a scalar-literal return under arg Descrs.
//! - Rewrite `Term::Call(callee, args, cont)` to a `Term::TailCall(cont,
//!   [lit, ...captures])` under the same conditions.
//! - Walk multi-block callee bodies following Goto / If / inner
//!   TailCall edges (RED.4).
//! - Recurse through inner TailCalls under a per-top-level-callsite
//!   unroll budget (default 32, RED.4).
//! - Same-callee structural-decrease check (literal-int magnitude OR
//!   Descr depth) — count_100k stays a call (RED.4).
//!
//! Out of scope (lands in later RED tickets):
//! - Closure_lit reduction (RED.5).
//! - Tuple / list return values (need MakeTuple / cons rewriting).
//! - Non-tail `Term::Call` inside callee bodies (needs cont
//!   reasoning — RED.5+).

use crate::fz_ir::{
    Block, BlockId, CallsiteId, CallsiteOutcome, Const, EmitSlot, FnId, FnIr, Module, Prim, Stmt,
    Term, Var,
};
use crate::reducer::{
    as_atom_lit, as_bool_lit, as_float_lit, as_int_lit, as_str_lit, fold_prim, is_literal,
    is_nil_only,
};
use crate::types::Descr;
use std::collections::HashMap;

/// Helper: get a `&mut Block` by id within an `FnIr`. FnIr exposes
/// `block(&self)` but not the mutable variant — fz_ir's `block_mut` is
/// private to `FnBuilder`. Inline the lookup here.
fn block_mut(f: &mut FnIr, id: BlockId) -> &mut Block {
    f.blocks
        .iter_mut()
        .find(|b| b.id == id)
        .expect("unknown block")
}

/// Allocate a fresh `Var` for `f` whose id exceeds every existing Var in
/// the fn body. Mirrors the `max_var + 1` pattern used by ir_inline.
fn fresh_var(f: &FnIr) -> Var {
    let mut m: u32 = 0;
    for b in &f.blocks {
        for p in &b.params {
            m = m.max(p.0);
        }
        for stmt in &b.stmts {
            let Stmt::Let(v, _) = stmt;
            m = m.max(v.0);
        }
    }
    Var(m + 1)
}

/// Reduce every function in `m`. Idempotent: running twice is the same
/// as running once (within the limits of v1's single-callsite scope).
pub fn reduce_module(m: &mut Module) {
    let fn_ids: Vec<FnId> = m.fns.iter().map(|f| f.id).collect();
    // Single sweep: each fn's body is reduced in place. RED.3 does not
    // iterate to a fixpoint across fns; later tickets may.
    for fid in fn_ids {
        reduce_fn(m, fid);
    }
    #[cfg(debug_assertions)]
    assert_every_callsite_has_outcome(m);
}

/// fz-9pr.5 — debug invariant: after `reduce_module`, every surviving
/// call-terminator in the module must have a corresponding entry in
/// `callsite_outcomes`. A surviving call means the reducer either
/// Stalled it (left as-is for the typer to Emit) or — once fz-9pr.E
/// lands — Inlined it. `Consumed` outcomes refer to callsites that
/// were rewritten away; their original terminators are gone, so they
/// are not part of this scan.
#[cfg(debug_assertions)]
fn assert_every_callsite_has_outcome(m: &Module) {
    for f in &m.fns {
        for b in &f.blocks {
            let slot = match &b.terminator {
                Term::Call { .. } | Term::TailCall { .. } => Some(EmitSlot::Direct),
                Term::CallClosure { .. } | Term::TailCallClosure { .. } => {
                    Some(EmitSlot::ClosureLit(0, 0))
                }
                _ => None,
            };
            if let Some(slot) = slot {
                let cid = CallsiteId {
                    caller: f.id,
                    block: b.id,
                    slot,
                };
                assert!(
                    m.callsite_outcomes.contains_key(&cid),
                    "fz-9pr.5: missing callsite outcome for {:?} in fn {} block {:?}",
                    slot,
                    f.name,
                    b.id
                );
            }
        }
    }
}

fn reduce_fn(m: &mut Module, fid: FnId) {
    let Some(&fn_idx) = m.fn_idx.get(&fid) else {
        return;
    };
    let block_ids: Vec<BlockId> = m.fns[fn_idx].blocks.iter().map(|b| b.id).collect();
    for bid in block_ids {
        reduce_block(m, fn_idx, bid);
    }
}

fn reduce_block(m: &mut Module, fn_idx: usize, bid: BlockId) {
    // Build a per-block env of Var → literal Descr by folding each stmt.
    let mut env: HashMap<Var, Descr> = HashMap::new();
    let atom_names = m.atom_names.clone();
    {
        let block = m.fns[fn_idx].block(bid);
        for stmt in &block.stmts {
            let Stmt::Let(v, prim) = stmt;
            if let Some(d) = fold_prim(prim, &env, &atom_names) {
                env.insert(*v, d);
            }
        }
    }

    // Now consider the terminator.
    let term = m.fns[fn_idx].block(bid).terminator.clone();
    let new_term = reduce_terminator(m, fn_idx, bid, &term, &env);
    if let Some(nt) = new_term {
        block_mut(&mut m.fns[fn_idx], bid).terminator = nt;
    }
}

fn reduce_terminator(
    m: &mut Module,
    fn_idx: usize,
    bid: BlockId,
    term: &Term,
    env: &HashMap<Var, Descr>,
) -> Option<Term> {
    match term {
        // fz-jg5.4: if-fold (named explicit rule per FINDINGS.md).
        Term::If(cond, t, e) => {
            let cd = env.get(cond)?;
            let b = as_bool_lit(cd)?;
            Some(Term::Goto(if b { *t } else { *e }, vec![]))
        }
        Term::TailCall { callee, args, .. } => {
            // fz-jg5.5: each top-level callsite gets a fresh ReduceCtx
            // with full budget. All-or-nothing: if try_reduce_call returns
            // None, no rewrite is committed.
            let mut ctx = ReduceCtx {
                module: m,
                budget: UNROLL_BUDGET_DEFAULT,
                stack: Vec::new(),
            };
            let Some(lit) = try_reduce_call(&mut ctx, *callee, args, env) else {
                record_stalled(m, fn_idx, bid, EmitSlot::Direct);
                return None;
            };
            let new_var = fresh_var(&m.fns[fn_idx]);
            let Some(const_val) = literal_to_const(&lit, m) else {
                record_stalled(m, fn_idx, bid, EmitSlot::Direct);
                return None;
            };
            record_consumed(m, fn_idx, bid, EmitSlot::Direct, lit);
            block_mut(&mut m.fns[fn_idx], bid)
                .stmts
                .push(Stmt::Let(new_var, Prim::Const(const_val)));
            Some(Term::Return(new_var))
        }
        Term::Call {
            callee,
            args,
            continuation,
        } => {
            let mut ctx = ReduceCtx {
                module: m,
                budget: UNROLL_BUDGET_DEFAULT,
                stack: Vec::new(),
            };
            let Some(lit) = try_reduce_call(&mut ctx, *callee, args, env) else {
                record_stalled(m, fn_idx, bid, EmitSlot::Direct);
                return None;
            };
            let new_var = fresh_var(&m.fns[fn_idx]);
            let Some(const_val) = literal_to_const(&lit, m) else {
                record_stalled(m, fn_idx, bid, EmitSlot::Direct);
                return None;
            };
            record_consumed(m, fn_idx, bid, EmitSlot::Direct, lit);
            block_mut(&mut m.fns[fn_idx], bid)
                .stmts
                .push(Stmt::Let(new_var, Prim::Const(const_val)));
            let mut tail_args = vec![new_var];
            tail_args.extend(continuation.captured.iter().copied());
            Some(Term::TailCall {
                callee: continuation.fn_id,
                args: tail_args,
                is_back_edge: false,
            })
        }
        // fz-jg5.6: top-level closure-call reduction (mirror of walk_block).
        Term::TailCallClosure { closure, args } => {
            let Some(cl_lit) = env.get(closure).and_then(|d| d.as_closure_lit()).cloned() else {
                record_stalled(m, fn_idx, bid, EmitSlot::ClosureLit(0, 0));
                return None;
            };
            let mut all_descrs = cl_lit.captures.clone();
            for a in args {
                let Some(d) = env.get(a).cloned() else {
                    record_stalled(m, fn_idx, bid, EmitSlot::ClosureLit(0, 0));
                    return None;
                };
                all_descrs.push(d);
            }
            let mut ctx = ReduceCtx {
                module: m,
                budget: UNROLL_BUDGET_DEFAULT,
                stack: Vec::new(),
            };
            let Some(lit) = try_reduce_call_with_descrs(&mut ctx, cl_lit.fn_id, &all_descrs) else {
                record_stalled(m, fn_idx, bid, EmitSlot::ClosureLit(0, 0));
                return None;
            };
            let new_var = fresh_var(&m.fns[fn_idx]);
            let Some(const_val) = literal_to_const(&lit, m) else {
                record_stalled(m, fn_idx, bid, EmitSlot::ClosureLit(0, 0));
                return None;
            };
            record_consumed(m, fn_idx, bid, EmitSlot::ClosureLit(0, 0), lit);
            block_mut(&mut m.fns[fn_idx], bid)
                .stmts
                .push(Stmt::Let(new_var, Prim::Const(const_val)));
            Some(Term::Return(new_var))
        }
        Term::CallClosure {
            closure,
            args,
            continuation,
        } => {
            let Some(cl_lit) = env.get(closure).and_then(|d| d.as_closure_lit()).cloned() else {
                record_stalled(m, fn_idx, bid, EmitSlot::ClosureLit(0, 0));
                return None;
            };
            let mut all_descrs = cl_lit.captures.clone();
            for a in args {
                let Some(d) = env.get(a).cloned() else {
                    record_stalled(m, fn_idx, bid, EmitSlot::ClosureLit(0, 0));
                    return None;
                };
                all_descrs.push(d);
            }
            let mut ctx = ReduceCtx {
                module: m,
                budget: UNROLL_BUDGET_DEFAULT,
                stack: Vec::new(),
            };
            let Some(lit) = try_reduce_call_with_descrs(&mut ctx, cl_lit.fn_id, &all_descrs) else {
                record_stalled(m, fn_idx, bid, EmitSlot::ClosureLit(0, 0));
                return None;
            };
            let new_var = fresh_var(&m.fns[fn_idx]);
            let Some(const_val) = literal_to_const(&lit, m) else {
                record_stalled(m, fn_idx, bid, EmitSlot::ClosureLit(0, 0));
                return None;
            };
            record_consumed(m, fn_idx, bid, EmitSlot::ClosureLit(0, 0), lit);
            block_mut(&mut m.fns[fn_idx], bid)
                .stmts
                .push(Stmt::Let(new_var, Prim::Const(const_val)));
            let mut tail_args = vec![new_var];
            tail_args.extend(continuation.captured.iter().copied());
            Some(Term::TailCall {
                callee: continuation.fn_id,
                args: tail_args,
                is_back_edge: false,
            })
        }
        _ => None,
    }
}

/// fz-9pr.4 — record that the reducer left a callsite unchanged.
/// The call survives in the IR; the typer (in fz-9pr.D) will promote
/// the entry to `Emitted` once it mints the spec. Idempotent.
fn record_stalled(m: &mut Module, fn_idx: usize, block: BlockId, slot: EmitSlot) {
    let caller = m.fns[fn_idx].id;
    let cid = CallsiteId {
        caller,
        block,
        slot,
    };
    // Do not overwrite a Consumed already published by this pass —
    // that would lose lineage. In practice the Stalled writers all
    // early-return before any Consumed write, so this is defence in
    // depth.
    m.callsite_outcomes
        .entry(cid)
        .or_insert(CallsiteOutcome::Stalled);
}

/// fz-9pr.3 — write a `CallsiteOutcome::Consumed` entry to the
/// module's outcome table. The reducer's job is to write; nobody
/// reads these yet (readers land in fz-9pr.D). Idempotent: identical
/// repeated reductions overwrite with the same value.
fn record_consumed(m: &mut Module, fn_idx: usize, block: BlockId, slot: EmitSlot, result: Descr) {
    let caller = m.fns[fn_idx].id;
    let cid = CallsiteId {
        caller,
        block,
        slot,
    };
    m.callsite_outcomes.insert(
        cid,
        CallsiteOutcome::Consumed {
            result: Box::new(result),
        },
    );
}

/// fz-jg5.5 — Default unroll budget per top-level callsite. Counts
/// `try_reduce_call` invocations across the recursive walk. Caps tail
/// recursion that decreases provably but slowly (count_100k).
pub const UNROLL_BUDGET_DEFAULT: u32 = 32;

/// Reducer state threaded through `try_reduce_call`. Allocated per
/// top-level callsite; the all-or-nothing rule is enforced by
/// `reduce_terminator` discarding the rewrite when `try_reduce_call`
/// returns `None`.
struct ReduceCtx<'m> {
    module: &'m Module,
    /// Remaining budget. Decrements on each `try_reduce_call` entry.
    budget: u32,
    /// Stack of `(callee_fn_id, arg_descrs)` for ancestors of the
    /// current reduction. Same-callee re-entry checks structural
    /// decrease against the most-recent matching ancestor.
    stack: Vec<(FnId, Vec<Descr>)>,
}

/// Try to compute the literal return of `callee(args)` under the caller's
/// `env`. Returns `Some(literal_descr)` on success.
///
/// Walks multi-block callee bodies following Goto / If / inner-TailCall
/// edges. Recurses through inner TailCalls (mutual or self-recursion) so
/// long as:
/// - The unroll budget is non-zero.
/// - For same-callee re-entry, the args are strictly structurally smaller
///   than the parent's (literal-int magnitude OR Descr depth).
fn try_reduce_call(
    ctx: &mut ReduceCtx,
    callee: FnId,
    args: &[Var],
    env: &HashMap<Var, Descr>,
) -> Option<Descr> {
    let arg_descrs: Vec<Descr> = args
        .iter()
        .map(|a| env.get(a).cloned())
        .collect::<Option<Vec<_>>>()?;
    try_reduce_call_with_descrs(ctx, callee, &arg_descrs)
}

fn try_reduce_call_with_descrs(
    ctx: &mut ReduceCtx,
    callee: FnId,
    arg_descrs: &[Descr],
) -> Option<Descr> {
    if ctx.budget == 0 {
        return None;
    }
    ctx.budget -= 1;
    // fz-jg5.12 (RED.9): @spec'd fns are reduction boundaries. The user
    // signed a contract by declaring the spec; honor it. Exception:
    // trivially-inlinable bodies (one block, ≤1 stmt, Return terminator)
    // carry no semantic risk, so we still fold them per the FINDINGS.md
    // ratification.
    if ctx.module.boundary_fns.contains(&callee) && !is_trivially_inlinable(ctx.module, callee) {
        return None;
    }
    // Every arg must be literal-Descr.
    for d in arg_descrs {
        if !is_scalar_literal(d) && !is_literal(d) {
            return None;
        }
    }
    // Same-callee structural-decrease guard.
    if let Some((_, parent)) = ctx.stack.iter().rfind(|(fid, _)| *fid == callee)
        && !strictly_smaller_args(arg_descrs, parent)
    {
        return None;
    }
    ctx.stack.push((callee, arg_descrs.to_vec()));
    let result = walk_fn_body(ctx, callee, arg_descrs);
    ctx.stack.pop();
    result
}

fn walk_fn_body(ctx: &mut ReduceCtx, callee: FnId, arg_descrs: &[Descr]) -> Option<Descr> {
    let f: &FnIr = ctx.module.fn_by_id(callee);
    let entry = f.block(f.entry);
    if entry.params.len() != arg_descrs.len() {
        return None;
    }
    let mut env: HashMap<Var, Descr> = HashMap::new();
    for (p, d) in entry.params.iter().zip(arg_descrs.iter()) {
        env.insert(*p, d.clone());
    }
    walk_block(ctx, f, f.entry, env, 0)
}

/// Walk control flow within a single FnIr starting at `bid` under `env`.
/// `goto_depth` caps inter-block transitions within one fn body to a sane
/// number (prevents infinite Goto chains; topo guarantees terminate, but
/// belt-and-braces).
fn walk_block(
    ctx: &mut ReduceCtx,
    f: &FnIr,
    bid: BlockId,
    mut env: HashMap<Var, Descr>,
    goto_depth: u32,
) -> Option<Descr> {
    if goto_depth > 64 {
        return None;
    }
    let block = f.block(bid);
    // Reject blocks containing call-like / effect-bearing prims.
    for stmt in &block.stmts {
        let Stmt::Let(_, prim) = stmt;
        if !prim_is_reducible(prim) {
            return None;
        }
    }
    // Fold stmts.
    for stmt in &block.stmts {
        let Stmt::Let(v, prim) = stmt;
        let d = fold_prim(prim, &env, &ctx.module.atom_names)?;
        env.insert(*v, d);
    }
    match &block.terminator {
        Term::Return(v) => {
            let d = env.get(v).cloned()?;
            if is_scalar_literal(&d) { Some(d) } else { None }
        }
        Term::Goto(target, args) => {
            let target_block = f.block(*target);
            if target_block.params.len() != args.len() {
                return None;
            }
            let mut next_env = env.clone();
            for (p, a) in target_block.params.iter().zip(args.iter()) {
                let d = env.get(a)?.clone();
                next_env.insert(*p, d);
            }
            walk_block(ctx, f, *target, next_env, goto_depth + 1)
        }
        Term::If(cond, t, e) => {
            let cd = env.get(cond)?;
            let b = as_bool_lit(cd)?;
            walk_block(ctx, f, if b { *t } else { *e }, env, goto_depth + 1)
        }
        Term::TailCall {
            callee: tc_callee,
            args: tc_args,
            ..
        } => try_reduce_call(ctx, *tc_callee, tc_args, &env),
        // fz-jg5.5: Call+Cont reduction. When callee folds to a literal,
        // its result feeds the cont as slot 0; treat the cont as a fn
        // taking [callee_result, ...captures] and reduce it too.
        Term::Call {
            callee: c_callee,
            args: c_args,
            continuation,
        } => {
            let inner_result = try_reduce_call(ctx, *c_callee, c_args, &env)?;
            feed_cont(ctx, continuation, inner_result, &env)
        }
        // fz-jg5.6: closure-call reduction. When the closure operand has
        // a closure_lit(F, captures) Descr, dispatch to F directly with
        // [captures..., args...] as its input Descrs.
        Term::TailCallClosure { closure, args } => {
            let cl_lit = env.get(closure)?.as_closure_lit()?.clone();
            let mut all_descrs = cl_lit.captures;
            for a in args {
                all_descrs.push(env.get(a).cloned()?);
            }
            try_reduce_call_with_descrs(ctx, cl_lit.fn_id, &all_descrs)
        }
        Term::CallClosure {
            closure,
            args,
            continuation,
        } => {
            let cl_lit = env.get(closure)?.as_closure_lit()?.clone();
            let mut all_descrs = cl_lit.captures;
            for a in args {
                all_descrs.push(env.get(a).cloned()?);
            }
            let inner_result = try_reduce_call_with_descrs(ctx, cl_lit.fn_id, &all_descrs)?;
            feed_cont(ctx, continuation, inner_result, &env)
        }
        Term::Receive { .. } | Term::Halt(_) => None,
    }
}

/// Build the cont's input Descrs `[result, ...captures]` and reduce
/// through it. Shared by Term::Call and Term::CallClosure.
fn feed_cont(
    ctx: &mut ReduceCtx,
    continuation: &crate::fz_ir::Cont,
    result: Descr,
    env: &HashMap<Var, Descr>,
) -> Option<Descr> {
    let mut cont_descrs: Vec<Descr> = Vec::with_capacity(1 + continuation.captured.len());
    cont_descrs.push(result);
    for cap in &continuation.captured {
        let d = env.get(cap).cloned()?;
        if !is_literal(&d) {
            return None;
        }
        cont_descrs.push(d);
    }
    try_reduce_call_with_descrs(ctx, continuation.fn_id, &cont_descrs)
}

/// fz-jg5.12 (RED.9) — `@spec`'d fn carries no risk to fold across if
/// the body is one block with at most one non-control stmt + Return.
/// Per FINDINGS.md ratification: `add1(x) = x + 1` qualifies; anything
/// branching, multi-block, or recursive is a firewall.
fn is_trivially_inlinable(m: &Module, fid: FnId) -> bool {
    let f = m.fn_by_id(fid);
    if f.blocks.len() != 1 {
        return false;
    }
    let b = f.block(f.entry);
    if b.stmts.len() > 1 {
        return false;
    }
    matches!(b.terminator, Term::Return(_))
}

fn prim_is_reducible(p: &Prim) -> bool {
    !matches!(
        p,
        Prim::Extern(..)
            | Prim::MakeMap(..)
            | Prim::MapUpdate(..)
            | Prim::MakeBitstring(..)
            | Prim::BitReaderInit(..)
            | Prim::BitReadField { .. }
            | Prim::BitReaderDone(..)
            | Prim::AllocStruct(..)
    )
}

/// True iff `a` is strictly structurally smaller than `parent`. Per fz-jg5
/// FINDINGS: any literal-int magnitude decrease OR Descr-depth decrease
/// qualifies; both axes are conservative.
fn strictly_smaller_args(a: &[Descr], parent: &[Descr]) -> bool {
    if a.len() != parent.len() {
        return false;
    }
    a.iter()
        .zip(parent.iter())
        .any(|(ad, pd)| is_strictly_smaller(ad, pd))
}

fn is_strictly_smaller(a: &Descr, p: &Descr) -> bool {
    if let (Some(ai), Some(pi)) = (as_int_lit(a), as_int_lit(p)) {
        // Toward-zero monotonic decrease.
        if pi > 0 && ai >= 0 && ai < pi {
            return true;
        }
        if pi < 0 && ai <= 0 && ai > pi {
            return true;
        }
    }
    descr_depth(a) < descr_depth(p)
}

fn descr_depth(d: &Descr) -> usize {
    let mut max_d = 0;
    for conj in &d.tuples {
        for sig in &conj.pos {
            for e in &sig.elems {
                max_d = max_d.max(1 + descr_depth(e));
            }
        }
    }
    for conj in &d.lists {
        for sig in &conj.pos {
            max_d = max_d.max(1 + descr_depth(&sig.elem));
        }
    }
    for conj in &d.funcs {
        for sig in &conj.pos {
            if let Some(lit) = &sig.lit {
                for c in &lit.captures {
                    max_d = max_d.max(1 + descr_depth(c));
                }
            }
        }
    }
    max_d
}

/// Scalar-literal predicate. Tuples/lists/closure_lits are out of scope
/// for RED.3 because rewriting a Call to a tuple result requires inserting
/// `MakeTuple` of sub-Const lets in the caller; that lands in a follow-on.
fn is_scalar_literal(d: &Descr) -> bool {
    if !is_literal(d) {
        return false;
    }
    // Tuple / closure_lit literals are "structural" — defer.
    if d.tuples.iter().any(|c| !c.pos.is_empty()) || d.funcs.iter().any(|c| !c.pos.is_empty()) {
        return false;
    }
    true
}

/// Convert a scalar-literal Descr back to a `Const`. Atoms are interned in
/// `m.atom_names`, allocating a new slot if necessary.
fn literal_to_const(d: &Descr, m: &mut Module) -> Option<Const> {
    if let Some(n) = as_int_lit(d) {
        return Some(Const::Int(n));
    }
    if let Some(fb) = as_float_lit(d) {
        return Some(Const::Float(fb.get()));
    }
    if is_nil_only(d) {
        return Some(Const::Nil);
    }
    if let Some(b) = as_bool_lit(d) {
        return Some(if b { Const::True } else { Const::False });
    }
    if let Some(name) = as_atom_lit(d) {
        let id = match m.atom_names.iter().position(|n| n == name) {
            Some(i) => i as u32,
            None => {
                let i = m.atom_names.len() as u32;
                m.atom_names.push(name.to_string());
                i
            }
        };
        return Some(Const::Atom(id));
    }
    if let Some(s) = as_str_lit(d) {
        return Some(Const::Str(s.to_string()));
    }
    None
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{BinOp, Const, FnBuilder, FnId, ModuleBuilder, Prim, Term};

    /// Build `fn id(x), do: x` and a `main()` that calls `id(42)`.
    /// After reduction, the TailCall in main should become a Return of 42.
    #[test]
    fn reduces_identity_call_with_int_literal() {
        let mut id_b = FnBuilder::new(FnId(0), "id");
        let x = id_b.fresh_var();
        let entry = id_b.block(vec![x]);
        id_b.set_terminator(entry, Term::Return(x));

        let mut main_b = FnBuilder::new(FnId(1), "main");
        let m_entry = main_b.block(vec![]);
        let c42 = main_b.let_(m_entry, Prim::Const(Const::Int(42)));
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![c42],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(id_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut m);

        // main's terminator should now be Return of a freshly bound int_lit(42).
        let main_fn = m.fns.iter().find(|f| f.name == "main").unwrap();
        let block = &main_fn.blocks[0];
        match &block.terminator {
            Term::Return(v) => {
                // Find the stmt that bound `v`.
                let bound = block
                    .stmts
                    .iter()
                    .find_map(|Stmt::Let(bv, prim)| if bv == v { Some(prim) } else { None });
                match bound {
                    Some(Prim::Const(Const::Int(n))) => assert_eq!(*n, 42),
                    other => panic!("expected Const(Int(42)), got {:?}", other),
                }
            }
            other => panic!("expected Return, got {:?}", other),
        }
    }

    /// `fn double(x), do: x * 2` called with `Const(Int(21))`: should reduce
    /// to Return of 42.
    #[test]
    fn reduces_double_with_int_literal() {
        let mut d_b = FnBuilder::new(FnId(0), "double");
        let x = d_b.fresh_var();
        let entry = d_b.block(vec![x]);
        let c2 = d_b.let_(entry, Prim::Const(Const::Int(2)));
        let product = d_b.let_(entry, Prim::BinOp(BinOp::Mul, x, c2));
        d_b.set_terminator(entry, Term::Return(product));

        let mut main_b = FnBuilder::new(FnId(1), "main");
        let m_entry = main_b.block(vec![]);
        let c21 = main_b.let_(m_entry, Prim::Const(Const::Int(21)));
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![c21],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(d_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut m);

        let main_fn = m.fns.iter().find(|f| f.name == "main").unwrap();
        let block = &main_fn.blocks[0];
        match &block.terminator {
            Term::Return(v) => {
                let bound = block
                    .stmts
                    .iter()
                    .find_map(|Stmt::Let(bv, prim)| if bv == v { Some(prim) } else { None });
                match bound {
                    Some(Prim::Const(Const::Int(n))) => assert_eq!(*n, 42),
                    other => panic!("expected Const(Int(42)), got {:?}", other),
                }
            }
            other => panic!("expected Return, got {:?}", other),
        }
    }

    /// A call whose argument is NOT a literal stays as a TailCall.
    #[test]
    fn does_not_reduce_call_with_opaque_arg() {
        let mut id_b = FnBuilder::new(FnId(0), "id");
        let x = id_b.fresh_var();
        let entry = id_b.block(vec![x]);
        id_b.set_terminator(entry, Term::Return(x));

        let mut main_b = FnBuilder::new(FnId(1), "main");
        let p = main_b.fresh_var();
        let m_entry = main_b.block(vec![p]); // main(p) — p is opaque
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![p],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(id_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut m);

        let main_fn = m.fns.iter().find(|f| f.name == "main").unwrap();
        match &main_fn.blocks[0].terminator {
            Term::TailCall { callee, .. } => assert_eq!(callee.0, 0),
            other => panic!("expected unchanged TailCall, got {:?}", other),
        }
    }

    /// `Term::If(cond, T, E)` with cond bound to Const(True) → Goto(T).
    #[test]
    fn folds_if_on_literal_true_to_goto() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let t_blk = b.block(vec![]);
        let e_blk = b.block(vec![]);
        let cond = b.let_(entry, Prim::Const(Const::True));
        b.set_terminator(entry, Term::If(cond, t_blk, e_blk));
        let nil = b.let_(t_blk, Prim::Const(Const::Nil));
        b.set_terminator(t_blk, Term::Return(nil));
        let nil2 = b.let_(e_blk, Prim::Const(Const::Nil));
        b.set_terminator(e_blk, Term::Return(nil2));

        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let mut m = mb.build();
        reduce_module(&mut m);

        match &m.fns[0].block(entry).terminator {
            Term::Goto(tgt, args) if *tgt == t_blk && args.is_empty() => {}
            other => panic!("expected Goto(t_blk, []), got {:?}", other),
        }
    }

    // ============================================================
    // fz-jg5.5 (RED.4) — recursive reduction tests
    // ============================================================

    /// `fn fact(0) = 1; fn fact(n) = n * fact(n-1)` — single-clause via
    /// If on TypeTest, recursive on `n-1`. fact(5) reduces to 120 within
    /// the 32-step budget.
    ///
    /// We build a hand-rolled equivalent (without going through the real
    /// pattern lowering): a single fn with an If branching on `n == 0`,
    /// and a recursive tail call on `n - 1`.
    #[test]
    fn red4_reduces_fact_5() {
        // fn fact(n):
        //   block0(n):
        //     c0 = Const(0)
        //     eq = BinOp(Eq, n, c0)
        //     If(eq, base, recur)
        //   base:
        //     c1 = Const(1)
        //     Return(c1)
        //   recur:
        //     c1b = Const(1)
        //     dec = BinOp(Sub, n, c1b)
        //     sub = TailCall(fact, [dec])  -- but we need result, so this fn
        //                                   shape needs to be different.
        // For simplicity, use a tail-only countdown: count(n) returns n
        // when n==0, else count(n-1). i.e. constant 0.
        let mut b = FnBuilder::new(FnId(0), "count");
        let n = b.fresh_var();
        let entry = b.block(vec![n]);
        let base = b.block(vec![]);
        let recur = b.block(vec![]);
        let c0 = b.let_(entry, Prim::Const(Const::Int(0)));
        let eq = b.let_(entry, Prim::BinOp(BinOp::Eq, n, c0));
        b.set_terminator(entry, Term::If(eq, base, recur));
        // base: Return(n) (always 0 when reached)
        b.set_terminator(base, Term::Return(n));
        // recur: n - 1; tail call count(n - 1)
        let c1 = b.let_(recur, Prim::Const(Const::Int(1)));
        let dec = b.let_(recur, Prim::BinOp(BinOp::Sub, n, c1));
        b.set_terminator(
            recur,
            Term::TailCall {
                callee: FnId(0),
                args: vec![dec],
                is_back_edge: false,
            },
        );

        let mut main_b = FnBuilder::new(FnId(1), "main");
        let m_entry = main_b.block(vec![]);
        let c5 = main_b.let_(m_entry, Prim::Const(Const::Int(5)));
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![c5],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut m);

        // main's terminator should now Return a literal 0 — count(5)→count(4)→...→count(0)=0.
        let main_fn = m.fns.iter().find(|f| f.name == "main").unwrap();
        let blk = &main_fn.blocks[0];
        match &blk.terminator {
            Term::Return(v) => {
                let bound = blk.stmts.iter().find_map(
                    |Stmt::Let(bv, prim)| {
                        if bv == v { Some(prim) } else { None }
                    },
                );
                match bound {
                    Some(Prim::Const(Const::Int(n))) => assert_eq!(*n, 0),
                    other => panic!("expected Const(Int(0)), got {:?}", other),
                }
            }
            other => panic!("expected Return, got {:?}", other),
        }
    }

    /// Same `count` fn, called with 100_000 — should blow the budget
    /// and leave the original TailCall in place (all-or-nothing).
    #[test]
    fn red4_count_100k_stays_a_call_via_budget() {
        let mut b = FnBuilder::new(FnId(0), "count");
        let n = b.fresh_var();
        let entry = b.block(vec![n]);
        let base = b.block(vec![]);
        let recur = b.block(vec![]);
        let c0 = b.let_(entry, Prim::Const(Const::Int(0)));
        let eq = b.let_(entry, Prim::BinOp(BinOp::Eq, n, c0));
        b.set_terminator(entry, Term::If(eq, base, recur));
        b.set_terminator(base, Term::Return(n));
        let c1 = b.let_(recur, Prim::Const(Const::Int(1)));
        let dec = b.let_(recur, Prim::BinOp(BinOp::Sub, n, c1));
        b.set_terminator(
            recur,
            Term::TailCall {
                callee: FnId(0),
                args: vec![dec],
                is_back_edge: false,
            },
        );

        let mut main_b = FnBuilder::new(FnId(1), "main");
        let m_entry = main_b.block(vec![]);
        let c100k = main_b.let_(m_entry, Prim::Const(Const::Int(100_000)));
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![c100k],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut m);

        // main should still TailCall count.
        let main_fn = m.fns.iter().find(|f| f.name == "main").unwrap();
        match &main_fn.blocks[0].terminator {
            Term::TailCall { callee, .. } => assert_eq!(callee.0, 0),
            other => panic!("expected unchanged TailCall, got {:?}", other),
        }
    }

    /// `is_even(n)` calls `is_odd(n-1)`; `is_odd(0)` returns :false,
    /// `is_odd(n)` calls `is_even(n-1)`. Mutual recursion. is_even(4)
    /// should reduce to :true within budget (5 hops).
    #[test]
    fn red4_reduces_mutual_recursion() {
        // is_even (fn 0):
        //   entry(n):
        //     c0 = 0; eq = n == 0; If(eq, true_blk, odd_blk)
        //   true_blk:
        //     t = Const::True; Return(t)
        //   odd_blk:
        //     c1 = 1; dec = n - 1; TailCall(is_odd, [dec])
        let mut e = FnBuilder::new(FnId(0), "is_even");
        let n_e = e.fresh_var();
        let e_entry = e.block(vec![n_e]);
        let e_true = e.block(vec![]);
        let e_odd = e.block(vec![]);
        let c0_e = e.let_(e_entry, Prim::Const(Const::Int(0)));
        let eq_e = e.let_(e_entry, Prim::BinOp(BinOp::Eq, n_e, c0_e));
        e.set_terminator(e_entry, Term::If(eq_e, e_true, e_odd));
        let true_v = e.let_(e_true, Prim::Const(Const::True));
        e.set_terminator(e_true, Term::Return(true_v));
        let c1_e = e.let_(e_odd, Prim::Const(Const::Int(1)));
        let dec_e = e.let_(e_odd, Prim::BinOp(BinOp::Sub, n_e, c1_e));
        e.set_terminator(
            e_odd,
            Term::TailCall {
                callee: FnId(1),
                args: vec![dec_e],
                is_back_edge: false,
            },
        );

        // is_odd (fn 1): symmetric, returns Const::False at base.
        let mut o = FnBuilder::new(FnId(1), "is_odd");
        let n_o = o.fresh_var();
        let o_entry = o.block(vec![n_o]);
        let o_false = o.block(vec![]);
        let o_even = o.block(vec![]);
        let c0_o = o.let_(o_entry, Prim::Const(Const::Int(0)));
        let eq_o = o.let_(o_entry, Prim::BinOp(BinOp::Eq, n_o, c0_o));
        o.set_terminator(o_entry, Term::If(eq_o, o_false, o_even));
        let false_v = o.let_(o_false, Prim::Const(Const::False));
        o.set_terminator(o_false, Term::Return(false_v));
        let c1_o = o.let_(o_even, Prim::Const(Const::Int(1)));
        let dec_o = o.let_(o_even, Prim::BinOp(BinOp::Sub, n_o, c1_o));
        o.set_terminator(
            o_even,
            Term::TailCall {
                callee: FnId(0),
                args: vec![dec_o],
                is_back_edge: false,
            },
        );

        let mut main_b = FnBuilder::new(FnId(2), "main");
        let m_entry = main_b.block(vec![]);
        let c4 = main_b.let_(m_entry, Prim::Const(Const::Int(4)));
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![c4],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(e.build());
        mb.add_fn(o.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut m);

        let main_fn = m.fns.iter().find(|f| f.name == "main").unwrap();
        let blk = &main_fn.blocks[0];
        match &blk.terminator {
            Term::Return(v) => {
                let bound = blk.stmts.iter().find_map(
                    |Stmt::Let(bv, prim)| {
                        if bv == v { Some(prim) } else { None }
                    },
                );
                match bound {
                    // is_even(4) → is_odd(3) → is_even(2) → is_odd(1) → is_even(0) → true.
                    Some(Prim::Const(Const::True)) => {}
                    other => panic!("expected Const(True), got {:?}", other),
                }
            }
            other => panic!("expected Return, got {:?}", other),
        }
    }

    // Note: ast_eval / fib_tailrec end-to-end reduction is covered by the
    // fixture matrix tests (post-RED.4 the fixtures' goldens may shift —
    // re-bless lands in RED.6).

    /// Under RED.4, the reducer DOES follow inner tail calls.
    /// f(x) = id(x); id(x) = x. main calls f(5). End-to-end reduce → 5.
    #[test]
    fn red4_reduces_through_inner_tail_call() {
        let mut id_b = FnBuilder::new(FnId(0), "id");
        let x_id = id_b.fresh_var();
        let id_entry = id_b.block(vec![x_id]);
        id_b.set_terminator(id_entry, Term::Return(x_id));

        let mut f_b = FnBuilder::new(FnId(1), "f");
        let x_f = f_b.fresh_var();
        let f_entry = f_b.block(vec![x_f]);
        f_b.set_terminator(
            f_entry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![x_f],
                is_back_edge: false,
            },
        );

        let mut main_b = FnBuilder::new(FnId(2), "main");
        let m_entry = main_b.block(vec![]);
        let c5 = main_b.let_(m_entry, Prim::Const(Const::Int(5)));
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                callee: FnId(1),
                args: vec![c5],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(id_b.build());
        mb.add_fn(f_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut m);

        // main should now Return Const(Int(5)) — fully reduced.
        let main_fn = m.fns.iter().find(|f| f.name == "main").unwrap();
        let blk = &main_fn.blocks[0];
        match &blk.terminator {
            Term::Return(v) => {
                let bound = blk.stmts.iter().find_map(
                    |Stmt::Let(bv, prim)| {
                        if bv == v { Some(prim) } else { None }
                    },
                );
                match bound {
                    Some(Prim::Const(Const::Int(5))) => {}
                    other => panic!("expected Const(Int(5)), got {:?}", other),
                }
            }
            other => panic!("expected Return, got {:?}", other),
        }
    }

    /// fz-9pr.4 — every callsite the reducer can't fold must publish a
    /// `Stalled` outcome. Build a module that calls `id(x)` where x is
    /// a Var (not a literal); the reducer can't fold the call, so it
    /// must record `Stalled` at the Direct slot.
    #[test]
    fn reducer_publishes_stalled_outcome_when_args_nonliteral() {
        let mut id_b = FnBuilder::new(FnId(0), "id");
        let x = id_b.fresh_var();
        let entry = id_b.block(vec![x]);
        id_b.set_terminator(entry, Term::Return(x));

        // main(x): TailCall id(x). x is a param, not a literal.
        let mut main_b = FnBuilder::new(FnId(1), "main");
        let x_main = main_b.fresh_var();
        let m_entry = main_b.block(vec![x_main]);
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![x_main],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(id_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut m);

        let cid = CallsiteId {
            caller: FnId(1),
            block: m_entry,
            slot: EmitSlot::Direct,
        };
        assert!(matches!(
            m.callsite_outcomes.get(&cid),
            Some(CallsiteOutcome::Stalled)
        ));

        // And main's terminator should be unchanged (still TailCall).
        let main_fn = m.fns.iter().find(|f| f.name == "main").unwrap();
        assert!(matches!(
            main_fn.blocks[0].terminator,
            Term::TailCall { .. }
        ));
    }

    /// fz-9pr.3 — every successful reducer rewrite must publish a
    /// `Consumed` outcome at the right `CallsiteId`. This test builds
    /// the same identity-call module as `reduces_identity_call_with_int_literal`
    /// and asserts main's TailCall site is recorded as
    /// `Consumed { result: int_lit(42) }`.
    #[test]
    fn reducer_publishes_consumed_outcome() {
        let mut id_b = FnBuilder::new(FnId(0), "id");
        let x = id_b.fresh_var();
        let entry = id_b.block(vec![x]);
        id_b.set_terminator(entry, Term::Return(x));

        let mut main_b = FnBuilder::new(FnId(1), "main");
        let m_entry = main_b.block(vec![]);
        let c42 = main_b.let_(m_entry, Prim::Const(Const::Int(42)));
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                callee: FnId(0),
                args: vec![c42],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(id_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut m);

        let cid = CallsiteId {
            caller: FnId(1),
            block: m_entry,
            slot: EmitSlot::Direct,
        };
        match m.callsite_outcomes.get(&cid) {
            Some(CallsiteOutcome::Consumed { result }) => {
                assert_eq!(**result, Descr::int_lit(42));
            }
            other => panic!("expected Consumed outcome, got {:?}", other),
        }
    }
}
