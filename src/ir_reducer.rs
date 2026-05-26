//! fz-jg5.4 / fz-jg5.5 — Compile-time reducer pass.
//!
//! A `Module → Module` pass that walks each function, folds literals
//! into Var environments, and rewrites calls whose return value is
//! statically known.
//!
//! Scope (post-RED.4):
//! - Fold every `Prim` via `reducer::fold_prim`. When a Var has a
//!   scalar-literal type, record it.
//! - Fold `Term::if_user(cond, T, E)` when `cond` is a bool literal.
//! - Rewrite `Term::TailCall(callee, args)` to `Term::Return(lit)` when
//!   the callee walks to a scalar-literal return under literal arg types.
//! - Rewrite `Term::Call(callee, args, cont)` to a `Term::TailCall(cont,
//!   [lit, ...captures])` under the same conditions.
//! - Walk multi-block callee bodies following Goto / If / inner
//!   TailCall edges (RED.4).
//! - Recurse through inner TailCalls under a per-top-level-callsite
//!   unroll budget (default 32, RED.4).
//! - Same-callee structural-decrease check (literal-int magnitude OR
//!   type depth) — count_100k stays a call (RED.4).
//!
//! Out of scope (lands in later RED tickets):
//! - Closure_lit reduction (RED.5).
//! - Tuple / list return values (need MakeTuple / cons rewriting).
//! - Non-tail `Term::Call` inside callee bodies (needs cont
//!   reasoning — RED.5+).
//!
//! ## fz-9pr.6 — partial fold for Term::Call when cont doesn't fold
//!
//! Investigation: `reduce_terminator`'s `Term::Call` branch already
//! handles "callee folds, cont doesn't" by rewriting to
//! `TailCall(cont.fn_id, [literal_var, ...captures])`. And `walk_block`
//! at the recursive layer already calls `feed_cont` when an inner Call's
//! callee folds. So a "partial fold" at the Term::Call level wouldn't
//! help: the existing two paths already cover everything the current
//! reducer can fold.
//!
//! The reason `closure_typed_captures`'s `apply1(add_to(10, 20), 12)`
//! survives is *deeper*: `add_to(10, 20)` returns a `closure_lit(fn14,
//! [10, 20])` — a STRUCTURAL literal. `walk_block`'s Return arm gates
//! on `is_scalar_literal`, so the walk returns None and the entire
//! chain stalls at main's outermost `Call add_to`. Fixing this requires
//! teaching the reducer to rewrite a `Call` whose result is a
//! `closure_lit` type — i.e., emit a `Prim::MakeClosure(fn14, [c10, c20])`
//! and feed THAT Var into the cont. That's a much bigger feature
//! (per-shape Const reconstruction; see `literal_to_const`'s
//! current scalar-only scope), and is out of fz-9pr's epic.
//!
//! Resolution: fz-9pr.6 is doc-only. apply1's callsite remains
//! `Stalled`; the planner (fz-9pr.D) will Emit it. The follow-up that
//! could lift this is a fz-jg5 successor — "closure-typed return"
//! reduction.
//!
//! ## fz-9pr.7 — partial fold for Term::CallClosure when cont doesn't fold
//!
//! `Term::CallClosure` mirrors `Term::Call` exactly here: the
//! top-level branch (`reduce_terminator`) handles "closure_lit operand,
//! inner call folds, but cont doesn't" by rewriting to TailCall(cont,
//! [literal_var, ...captures]); the recursive layer (`walk_block`)
//! handles inner CallClosure via the same `feed_cont` helper as Call.
//! Same blocker: `walk_block`'s Return arm gates on
//! `is_scalar_literal`, so a callee that returns a closure_lit (e.g.
//! `curried_add`'s `add3(10)` ⇒ `closure_lit(fn_outer, [10])`) fails
//! the walk. The fix is the same Const-reconstruction for closure_lit
//! results, and is out of fz-9pr's scope.
//!
//! Resolution: fz-9pr.7 is doc-only. `curried_add`'s `apply(...)`
//! callsites remain `Stalled`; the planner Emits them. Runtime
//! behaviour and spec set unchanged.

use crate::callsite_walk::slot_for_term;
use crate::fz_ir::{
    Block, BlockId, CallsiteId, Const, EmitSlot, FnId, FnIr, Module, Prim, StalledReason, Stmt,
    Term, Var,
};
use crate::reducer::fold_prim;
use std::collections::HashMap;

/// fz-uwq.9 — per-pass diagnostic record of what the reducer did at
/// each callsite. Returned from [`reduce_module`] alongside the
/// rewritten `Module`. These facts are **diagnostic** — `fz dump
/// --emit outcomes` reads them — and not load-bearing for codegen.
///
/// - `consumed[cid] = result` — the reducer rewrote this callsite
///   away. The original call-shaped terminator is gone, replaced
///   by a Return / TailCall that delivers `result`.
/// - `stalled[cid] = reason` — the reducer left the callsite alone
///   and recorded why. The dump pipeline renders the reason as a
///   `via <reason>` annotation on the planner's Emitted line at the
///   same `CallsiteId`, so coverage gaps stay legible.
///
/// Codegen dispatches via `SpecPlan.dispatches`; dumps read both this
/// log and the planner's per-spec dispatch tables.
#[derive(Debug, Default, Clone)]
pub struct ReducerLog {
    pub consumed: HashMap<CallsiteId, crate::types::Ty>,
    pub stalled: HashMap<CallsiteId, StalledReason>,
}

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
///
/// fz-uwq.9 — returns a [`ReducerLog`] of every Consumed / Stalled
/// fact. Callers that want the diagnostic pass the log to the dump
/// pipeline; codegen drops it.
pub fn reduce_module<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::LiteralTypes>(
    t: &mut T,
    m: &mut Module,
) -> ReducerLog {
    reduce_module_with_telemetry(t, m, &crate::telemetry::NullTelemetry)
}

pub fn reduce_module_with_telemetry<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::LiteralTypes,
>(
    t: &mut T,
    m: &mut Module,
    tel: &dyn crate::telemetry::Telemetry,
) -> ReducerLog {
    let mut log = ReducerLog::default();
    let fn_ids: Vec<FnId> = m.fns.iter().map(|f| f.id).collect();
    // Single sweep: each fn's body is reduced in place. RED.3 does not
    // iterate to a fixpoint across fns; later tickets may.
    for fid in fn_ids {
        reduce_fn(t, m, fid, &mut log, tel);
    }
    #[cfg(debug_assertions)]
    assert_every_surviving_call_in_log(m, &log);
    log
}

/// fz-9pr.5 — debug invariant: after `reduce_module`, every surviving
/// call-terminator in the module must have a corresponding entry in
/// the reducer log. A surviving call means the reducer Stalled it
/// (left as-is for the planner to Emit). `Consumed` entries refer to
/// callsites that were rewritten away; their original terminators
/// are gone, so they are not part of this scan.
#[cfg(debug_assertions)]
fn assert_every_surviving_call_in_log(m: &Module, log: &ReducerLog) {
    for f in &m.fns {
        for b in &f.blocks {
            if let Some(slot) = slot_for_term(&b.terminator) {
                let term_ident = b
                    .terminator
                    .ident()
                    .expect("slot_for_term gave Some → terminator has ident")
                    .clone();
                let cid = CallsiteId {
                    caller: f.id,
                    ident: term_ident,
                    slot,
                };
                // Stalled (reducer left this terminator alone) OR
                // Consumed (reducer rewrote a Call into a TailCall at
                // the same slot — the new terminator is still a
                // callsite even though the old one was consumed).
                assert!(
                    log.stalled.contains_key(&cid) || log.consumed.contains_key(&cid),
                    "fz-9pr.5: surviving callsite {:?} in fn {} block {:?} has no Stalled or \
                     Consumed entry in ReducerLog",
                    slot,
                    f.name,
                    b.id
                );
            }
        }
    }
}

fn reduce_fn<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::LiteralTypes>(
    t: &mut T,
    m: &mut Module,
    fid: FnId,
    log: &mut ReducerLog,
    tel: &dyn crate::telemetry::Telemetry,
) {
    let Some(&fn_idx) = m.fn_idx.get(&fid) else {
        return;
    };
    let block_ids: Vec<BlockId> = m.fns[fn_idx].blocks.iter().map(|b| b.id).collect();
    for bid in block_ids {
        reduce_block(t, m, fn_idx, bid, log, tel);
    }
}

fn reduce_block<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::LiteralTypes>(
    t: &mut T,
    m: &mut Module,
    fn_idx: usize,
    bid: BlockId,
    log: &mut ReducerLog,
    tel: &dyn crate::telemetry::Telemetry,
) {
    // Build a per-block env of Var → literal type by folding each stmt.
    let mut env: HashMap<Var, T::Ty> = HashMap::new();
    let atom_names = m.atom_names.clone();
    {
        let block = m.fns[fn_idx].block(bid);
        for stmt in &block.stmts {
            let Stmt::Let(v, prim) = stmt;
            if let Some(d) = fold_prim(t, prim, &env, &atom_names) {
                env.insert(*v, d);
            }
        }
    }

    // Now consider the terminator.
    let term = m.fns[fn_idx].block(bid).terminator.clone();
    let new_term = reduce_terminator(t, m, fn_idx, bid, &term, &env, log, tel);
    if let Some(nt) = new_term {
        block_mut(&mut m.fns[fn_idx], bid).terminator = nt;
    }
}

fn reduce_terminator<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::LiteralTypes>(
    t: &mut T,
    m: &mut Module,
    fn_idx: usize,
    bid: BlockId,
    term: &Term,
    env: &HashMap<Var, T::Ty>,
    log: &mut ReducerLog,
    tel: &dyn crate::telemetry::Telemetry,
) -> Option<Term> {
    // fz-9pr.17 — slot vocabulary lives in callsite_walk::slot_for_term;
    // every record_* call below routes through this single source of
    // truth, replacing the four duplicated EmitSlot literals that used
    // to live in each match arm.
    let slot = slot_for_term(term);
    match term {
        // fz-jg5.4: if-fold (named explicit rule per FINDINGS.md).
        Term::If {
            cond,
            then_b,
            else_b,
            ..
        } => {
            let cd = env.get(cond)?;
            let b = t.as_bool_lit(cd)?;
            Some(Term::Goto(if b { *then_b } else { *else_b }, vec![]))
        }
        Term::TailCall {
            ident,
            callee,
            args,
            ..
        } => {
            // fz-jg5.5: each top-level callsite gets a fresh ReduceCtx
            // with full budget. All-or-nothing: if try_reduce_call returns
            // None, no rewrite is committed.
            let slot = slot.unwrap();
            let mut ctx = fresh_ctx(m, t);
            let Some(lit) = try_reduce_call(&mut ctx, *callee, args, env) else {
                let reason = ctx.last_reason.unwrap_or(StalledReason::Other);
                record_stalled(m, fn_idx, ident, slot, reason, log, tel);
                return None;
            };
            let Some(new_var) = ty_to_materialize(t, &lit, m, fn_idx, bid, ident.span()) else {
                record_stalled(
                    m,
                    fn_idx,
                    ident,
                    slot,
                    StalledReason::CalleeBodyShape,
                    log,
                    tel,
                );
                return None;
            };
            record_consumed(t, m, fn_idx, ident, slot, &lit, log, tel);
            Some(Term::Return(new_var))
        }
        Term::Call {
            ident,
            callee,
            args,
            continuation,
        } => {
            let slot = slot.unwrap();
            let mut ctx = fresh_ctx(m, t);
            let Some(lit) = try_reduce_call(&mut ctx, *callee, args, env) else {
                let reason = ctx.last_reason.unwrap_or(StalledReason::Other);
                record_stalled(m, fn_idx, ident, slot, reason, log, tel);
                return None;
            };
            let Some(new_var) = ty_to_materialize(t, &lit, m, fn_idx, bid, ident.span()) else {
                record_stalled(
                    m,
                    fn_idx,
                    ident,
                    slot,
                    StalledReason::CalleeBodyShape,
                    log,
                    tel,
                );
                return None;
            };
            record_consumed(t, m, fn_idx, ident, slot, &lit, log, tel);
            let mut tail_args = vec![new_var];
            tail_args.extend(continuation.captured.iter().copied());
            // fz-kgk — INHERIT the Call's ident on the new TailCall;
            // same callsite, transformed terminator shape.
            Some(Term::TailCall {
                ident: ident.clone(),
                callee: continuation.fn_id,
                args: tail_args,
                is_back_edge: false,
            })
        }
        // fz-jg5.6: top-level closure-call reduction (mirror of walk_block).
        Term::TailCallClosure {
            ident,
            closure,
            args,
        } => {
            let slot = slot.unwrap();
            let Some(crate::types::ClosureLitInfo {
                target: closure_target,
                captures: closure_captures,
            }) = env.get(closure).and_then(|ty| t.closure_lit_parts(ty))
            else {
                record_stalled(
                    m,
                    fn_idx,
                    ident,
                    slot,
                    StalledReason::NoClosureLitTarget,
                    log,
                    tel,
                );
                return None;
            };
            let mut all_tys = closure_captures;
            for a in args {
                let Some(ty) = env.get(a).cloned() else {
                    record_stalled(m, fn_idx, ident, slot, StalledReason::OpaqueArg, log, tel);
                    return None;
                };
                all_tys.push(ty);
            }
            let mut ctx = fresh_ctx(m, t);
            let Some(lit) = try_reduce_call_with_tys(&mut ctx, closure_target.into(), &all_tys)
            else {
                let reason = ctx.last_reason.unwrap_or(StalledReason::Other);
                record_stalled(m, fn_idx, ident, slot, reason, log, tel);
                return None;
            };
            let Some(new_var) = ty_to_materialize(t, &lit, m, fn_idx, bid, ident.span()) else {
                record_stalled(
                    m,
                    fn_idx,
                    ident,
                    slot,
                    StalledReason::CalleeBodyShape,
                    log,
                    tel,
                );
                return None;
            };
            record_consumed(t, m, fn_idx, ident, slot, &lit, log, tel);
            Some(Term::Return(new_var))
        }
        Term::CallClosure {
            ident,
            closure,
            args,
            continuation,
        } => {
            let slot = slot.unwrap();
            let Some(crate::types::ClosureLitInfo {
                target: closure_target,
                captures: closure_captures,
            }) = env.get(closure).and_then(|ty| t.closure_lit_parts(ty))
            else {
                record_stalled(
                    m,
                    fn_idx,
                    ident,
                    slot,
                    StalledReason::NoClosureLitTarget,
                    log,
                    tel,
                );
                return None;
            };
            let mut all_tys = closure_captures;
            for a in args {
                let Some(ty) = env.get(a).cloned() else {
                    record_stalled(m, fn_idx, ident, slot, StalledReason::OpaqueArg, log, tel);
                    return None;
                };
                all_tys.push(ty);
            }
            let mut ctx = fresh_ctx(m, t);
            let Some(lit) = try_reduce_call_with_tys(&mut ctx, closure_target.into(), &all_tys)
            else {
                let reason = ctx.last_reason.unwrap_or(StalledReason::Other);
                record_stalled(m, fn_idx, ident, slot, reason, log, tel);
                return None;
            };
            let Some(new_var) = ty_to_materialize(t, &lit, m, fn_idx, bid, ident.span()) else {
                record_stalled(
                    m,
                    fn_idx,
                    ident,
                    slot,
                    StalledReason::CalleeBodyShape,
                    log,
                    tel,
                );
                return None;
            };
            record_consumed(t, m, fn_idx, ident, slot, &lit, log, tel);
            let mut tail_args = vec![new_var];
            tail_args.extend(continuation.captured.iter().copied());
            // fz-kgk — INHERIT the CallClosure's ident on the new
            // TailCall; same callsite, transformed terminator shape.
            Some(Term::TailCall {
                ident: ident.clone(),
                callee: continuation.fn_id,
                args: tail_args,
                is_back_edge: false,
            })
        }
        _ => None,
    }
}

/// fz-9pr.4 / fz-9pr.16 — record that the reducer left a callsite
/// unchanged, with a reason. The call survives in the IR; the planner
/// (in fz-9pr.D) will promote the entry to `Emitted` once it mints
/// the spec. Idempotent: re-recording uses the first reason written.
fn record_stalled(
    m: &Module,
    fn_idx: usize,
    ident: &crate::fz_ir::CallsiteIdent,
    slot: EmitSlot,
    reason: StalledReason,
    log: &mut ReducerLog,
    tel: &dyn crate::telemetry::Telemetry,
) {
    let caller = m.fns[fn_idx].id;
    let cid = CallsiteId {
        caller,
        ident: ident.clone(),
        slot,
    };
    // Do not overwrite if a Consumed/Stalled entry is already there —
    // that would lose lineage. In practice the Stalled writers all
    // early-return before any Consumed write within the same pass,
    // so this is defence in depth.
    if let std::collections::hash_map::Entry::Vacant(entry) = log.stalled.entry(cid) {
        let cid = entry.key();
        tel.event(
            &["fz", "reducer", "stalled"],
            crate::metadata! {
                caller_fn_id: cid.caller.0 as u64,
                slot: slot_name(cid.slot),
                reason: reason.to_string(),
                stalled_reason: crate::telemetry::value::opaque(&reason),
            },
        );
        entry.insert(reason);
    }
}

/// fz-9pr.3 — record a Consumed (reducer rewrote this callsite away)
/// in the [`ReducerLog`]. Diagnostic-only; codegen no longer reads
/// these (it reads `SpecPlan.dispatches` for `Emitted` decisions and
/// computes its own arg / cont keys at call sites).
fn record_consumed<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::LiteralTypes>(
    _t: &T,
    m: &Module,
    fn_idx: usize,
    ident: &crate::fz_ir::CallsiteIdent,
    slot: EmitSlot,
    result: &T::Ty,
    log: &mut ReducerLog,
    tel: &dyn crate::telemetry::Telemetry,
) {
    let caller = m.fns[fn_idx].id;
    let cid = CallsiteId {
        caller,
        ident: ident.clone(),
        slot,
    };
    tel.event(
        &["fz", "reducer", "consumed"],
        crate::metadata! {
            caller_fn_id: caller.0 as u64,
            slot: slot_name(slot),
            result: crate::telemetry::value::opaque(result),
        },
    );
    log.consumed.insert(cid, result.clone());
}

fn slot_name(slot: EmitSlot) -> &'static str {
    match slot {
        EmitSlot::Direct => "direct",
        EmitSlot::Cont => "cont",
        EmitSlot::ClosureCall => "closure_call",
        EmitSlot::MakeClosure => "make_closure",
    }
}

/// fz-jg5.5 — Default unroll budget per top-level callsite. Counts
/// `try_reduce_call` invocations across the recursive walk. Caps tail
/// recursion that decreases provably but slowly (count_100k).
pub const UNROLL_BUDGET_DEFAULT: u32 = 32;

/// Reducer state threaded through `try_reduce_call`. Allocated per
/// top-level callsite; the all-or-nothing rule is enforced by
/// `reduce_terminator` discarding the rewrite when `try_reduce_call`
/// returns `None`.
struct ReduceCtx<'m, T: crate::types::Types> {
    module: &'m Module,
    /// Remaining budget. Decrements on each `try_reduce_call` entry.
    budget: u32,
    /// Stack of `(callee_fn_id, arg_tys)` for ancestors of the
    /// current reduction. Same-callee re-entry checks structural
    /// decrease against the most-recent matching ancestor.
    stack: Vec<(FnId, Vec<T::Ty>)>,
    /// fz-9pr.16 — first stall reason hit on the current top-level
    /// reduction attempt. Innermost-set-wins: a deep `OpaqueArg`
    /// leaf survives all the way back to `reduce_terminator` where
    /// it is published into `ReducerLog.stalled`.
    last_reason: Option<StalledReason>,
    /// fz-mm2.58 — Types seam threaded through the reducer's recursive
    /// walk so that `fold_prim` can be called with `t`.
    t: &'m mut T,
}

impl<'m, T: crate::types::Types> ReduceCtx<'m, T> {
    fn note(&mut self, r: StalledReason) {
        if self.last_reason.is_none() {
            self.last_reason = Some(r);
        }
    }
}

/// Build a fresh `ReduceCtx` at top-level callsite entry. Centralises
/// the boilerplate that used to live in each `reduce_terminator` arm.
fn fresh_ctx<'m, T: crate::types::Types>(m: &'m Module, t: &'m mut T) -> ReduceCtx<'m, T> {
    ReduceCtx {
        module: m,
        budget: UNROLL_BUDGET_DEFAULT,
        stack: Vec::new(),
        last_reason: None,
        t,
    }
}

/// Try to compute the literal return of `callee(args)` under the caller's
/// `env`. Returns `Some(literal_descr)` on success.
///
/// Walks multi-block callee bodies following Goto / If / inner-TailCall
/// edges. Recurses through inner TailCalls (mutual or self-recursion) so
/// long as:
/// - The unroll budget is non-zero.
/// - For same-callee re-entry, the args are strictly structurally smaller
///   than the parent's (literal-int magnitude OR type depth).
fn try_reduce_call<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::LiteralTypes>(
    ctx: &mut ReduceCtx<'_, T>,
    callee: FnId,
    args: &[Var],
    env: &HashMap<Var, T::Ty>,
) -> Option<T::Ty> {
    let mut arg_tys: Vec<T::Ty> = Vec::with_capacity(args.len());
    for a in args {
        let Some(ty) = env.get(a).cloned() else {
            ctx.note(StalledReason::OpaqueArg);
            return None;
        };
        arg_tys.push(ty);
    }
    try_reduce_call_with_tys(ctx, callee, &arg_tys)
}

fn stall_reason_for_non_literal_ty<T: crate::types::Types>(t: &T, d: &T::Ty) -> StalledReason {
    if t.has_vars(d) {
        StalledReason::UnresolvedTypeVar
    } else {
        StalledReason::OpaqueArg
    }
}

fn try_reduce_call_with_tys<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::LiteralTypes,
>(
    ctx: &mut ReduceCtx<'_, T>,
    callee: FnId,
    arg_tys: &[T::Ty],
) -> Option<T::Ty> {
    if ctx.budget == 0 {
        ctx.note(StalledReason::BudgetExhausted);
        return None;
    }
    ctx.budget -= 1;
    // fz-jg5.12 (RED.9): @spec'd fns are reduction boundaries. The user
    // signed a contract by declaring the spec; honor it. Exception:
    // trivially-inlinable bodies (one block, ≤1 stmt, Return terminator)
    // carry no semantic risk, so we still fold them per the FINDINGS.md
    // ratification.
    if ctx.module.boundary_fns.contains(&callee) && !is_trivially_inlinable(ctx.module, callee) {
        ctx.note(StalledReason::BoundaryFn);
        return None;
    }
    // Every arg must be literal.
    for ty in arg_tys {
        if !ctx.t.is_literal(ty) {
            ctx.note(stall_reason_for_non_literal_ty(ctx.t, ty));
            return None;
        }
    }
    // Same-callee structural-decrease guard.
    if let Some((_, parent)) = ctx.stack.iter().rfind(|(fid, _)| *fid == callee)
        && !strictly_smaller_args(ctx.t, arg_tys, parent)
    {
        ctx.note(StalledReason::StructuralDecrease);
        return None;
    }
    ctx.stack.push((callee, arg_tys.to_vec()));
    let result = walk_fn_body(ctx, callee, arg_tys);
    ctx.stack.pop();
    result
}

fn walk_fn_body<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::LiteralTypes>(
    ctx: &mut ReduceCtx<'_, T>,
    callee: FnId,
    arg_tys: &[T::Ty],
) -> Option<T::Ty> {
    let f: &FnIr = ctx.module.fn_by_id(callee);
    let entry = f.block(f.entry);
    if entry.params.len() != arg_tys.len() {
        ctx.note(StalledReason::CalleeBodyShape);
        return None;
    }
    let mut env: HashMap<Var, T::Ty> = HashMap::new();
    for (p, ty) in entry.params.iter().zip(arg_tys.iter()) {
        env.insert(*p, ty.clone());
    }
    walk_block(ctx, f, f.entry, env, 0)
}

/// Walk control flow within a single FnIr starting at `bid` under `env`.
/// `goto_depth` caps inter-block transitions within one fn body to a sane
/// number (prevents infinite Goto chains; topo guarantees terminate, but
/// belt-and-braces).
fn walk_block<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::LiteralTypes>(
    ctx: &mut ReduceCtx<'_, T>,
    f: &FnIr,
    bid: BlockId,
    mut env: HashMap<Var, T::Ty>,
    goto_depth: u32,
) -> Option<T::Ty> {
    if goto_depth > 64 {
        ctx.note(StalledReason::CalleeBodyShape);
        return None;
    }
    let block = f.block(bid);
    // Reject blocks containing call-like / effect-bearing prims.
    for stmt in &block.stmts {
        let Stmt::Let(_, prim) = stmt;
        if !prim_is_reducible(prim) {
            ctx.note(StalledReason::NonReduciblePrim);
            return None;
        }
    }
    // Fold stmts.
    for stmt in &block.stmts {
        let Stmt::Let(v, prim) = stmt;
        let Some(d) = fold_prim(ctx.t, prim, &env, &ctx.module.atom_names) else {
            ctx.note(StalledReason::OpaqueArg);
            return None;
        };
        env.insert(*v, d);
    }
    match &block.terminator {
        Term::Return(v) => {
            let Some(ty) = env.get(v).cloned() else {
                ctx.note(StalledReason::OpaqueArg);
                return None;
            };
            if ctx.t.is_materializable(&ty) {
                Some(ty)
            } else {
                ctx.note(StalledReason::CalleeBodyShape);
                None
            }
        }
        Term::Goto(target, args) => {
            let target_block = f.block(*target);
            if target_block.params.len() != args.len() {
                ctx.note(StalledReason::CalleeBodyShape);
                return None;
            }
            let mut next_env = env.clone();
            for (p, a) in target_block.params.iter().zip(args.iter()) {
                let Some(d) = env.get(a).cloned() else {
                    ctx.note(StalledReason::OpaqueArg);
                    return None;
                };
                next_env.insert(*p, d);
            }
            walk_block(ctx, f, *target, next_env, goto_depth + 1)
        }
        Term::If {
            cond,
            then_b,
            else_b,
            ..
        } => {
            let Some(cd) = env.get(cond) else {
                ctx.note(StalledReason::OpaqueArg);
                return None;
            };
            let Some(b) = ctx.t.as_bool_lit(cd) else {
                ctx.note(stall_reason_for_non_literal_ty(ctx.t, cd));
                return None;
            };
            walk_block(
                ctx,
                f,
                if b { *then_b } else { *else_b },
                env,
                goto_depth + 1,
            )
        }
        Term::TailCall {
            ident: _,
            callee: tc_callee,
            args: tc_args,
            ..
        } => try_reduce_call(ctx, *tc_callee, tc_args, &env),
        // fz-jg5.5: Call+Cont reduction. When callee folds to a literal,
        // its result feeds the cont as slot 0; treat the cont as a fn
        // taking [callee_result, ...captures] and reduce it too.
        Term::Call {
            ident: _,
            callee: c_callee,
            args: c_args,
            continuation,
        } => {
            let inner_result = try_reduce_call(ctx, *c_callee, c_args, &env)?;
            feed_cont(ctx, continuation, inner_result, &env)
        }
        // fz-jg5.6: closure-call reduction. When the closure operand has
        // a closure_lit(F, captures) type, dispatch to F directly with
        // [captures..., args...] as its input types.
        Term::TailCallClosure {
            closure,
            args,
            ident: _,
        } => {
            let Some(crate::types::ClosureLitInfo {
                target: closure_target,
                captures: closure_captures,
            }) = env.get(closure).and_then(|ty| ctx.t.closure_lit_parts(ty))
            else {
                ctx.note(StalledReason::NoClosureLitTarget);
                return None;
            };
            let mut all_tys = closure_captures;
            for a in args {
                let Some(ty) = env.get(a).cloned() else {
                    ctx.note(StalledReason::OpaqueArg);
                    return None;
                };
                all_tys.push(ty);
            }
            try_reduce_call_with_tys(ctx, closure_target.into(), &all_tys)
        }
        Term::CallClosure {
            ident: _,
            closure,
            args,
            continuation,
        } => {
            let Some(crate::types::ClosureLitInfo {
                target: closure_target,
                captures: closure_captures,
            }) = env.get(closure).and_then(|ty| ctx.t.closure_lit_parts(ty))
            else {
                ctx.note(StalledReason::NoClosureLitTarget);
                return None;
            };
            let mut all_tys = closure_captures;
            for a in args {
                let Some(ty) = env.get(a).cloned() else {
                    ctx.note(StalledReason::OpaqueArg);
                    return None;
                };
                all_tys.push(ty);
            }
            let inner_result = try_reduce_call_with_tys(ctx, closure_target.into(), &all_tys)?;
            feed_cont(ctx, continuation, inner_result, &env)
        }
        Term::Receive { .. } | Term::ReceiveMatched { .. } | Term::Halt(_) => {
            ctx.note(StalledReason::CalleeBodyShape);
            None
        }
    }
}

/// Build the cont's input types `[result, ...captures]` and reduce
/// through it. Shared by Term::Call and Term::CallClosure.
fn feed_cont<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::LiteralTypes>(
    ctx: &mut ReduceCtx<'_, T>,
    continuation: &crate::fz_ir::Cont,
    result: T::Ty,
    env: &HashMap<Var, T::Ty>,
) -> Option<T::Ty> {
    let mut cont_tys: Vec<T::Ty> = Vec::with_capacity(1 + continuation.captured.len());
    cont_tys.push(result);
    for cap in &continuation.captured {
        let Some(ty) = env.get(cap).cloned() else {
            ctx.note(StalledReason::OpaqueArg);
            return None;
        };
        if !ctx.t.is_literal(&ty) {
            ctx.note(stall_reason_for_non_literal_ty(ctx.t, &ty));
            return None;
        }
        cont_tys.push(ty);
    }
    try_reduce_call_with_tys(ctx, continuation.fn_id, &cont_tys)
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
            | Prim::DestTupleBegin { .. }
            | Prim::DestTupleSet { .. }
            | Prim::DestFreeze { .. }
            | Prim::DestListBegin { .. }
            | Prim::DestListCons { .. }
            | Prim::DestListFreeze { .. }
            | Prim::MakeMap(..)
            | Prim::MapUpdate(..)
            | Prim::DestMapBegin { .. }
            | Prim::DestMapPut { .. }
            | Prim::DestMapFreeze { .. }
            | Prim::MakeBitstring(..)
            | Prim::BitReaderInit(..)
            | Prim::BitReadField { .. }
            | Prim::BitReaderDone(..)
    )
}

/// True iff `a` is strictly structurally smaller than `parent`. Per fz-jg5
/// FINDINGS: any literal-int magnitude decrease OR type-depth decrease
/// qualifies; both axes are conservative.
fn strictly_smaller_args<T: crate::types::Types>(t: &T, a: &[T::Ty], parent: &[T::Ty]) -> bool {
    if a.len() != parent.len() {
        return false;
    }
    a.iter()
        .zip(parent.iter())
        .any(|(ad, pd)| t.is_strictly_smaller(ad, pd))
}

/// fz-f88.1 — Single materializer for type → block stmts.
///
/// Owns the type→stmts vocabulary. Returns a fresh Var bound to the
/// materialized literal, after pushing the necessary stmts into the
/// target block. None if `d` is not materializable.
///
/// Arms:
/// - scalar (f88.1): delegates to seam-owned `scalar_literal`.
/// - closure_lit (f88.2): materializes captures recursively, then
///   pushes `Prim::MakeClosure(fn_id, cap_vars)`.
/// - tuple_lit (f88.3): materializes elements recursively, then
///   pushes `Prim::MakeTuple(elem_vars)`.
/// - empty list (f88.3): pushes `Prim::MakeList(vec![], None)`.
///
/// Non-empty list literal folding stays out of scope (L1 follow-up
/// fz-4lo): the `list_of(elem)` lattice loses length info.
fn ty_to_materialize<T: crate::types::Types + crate::types::LiteralTypes>(
    t: &T,
    d: &T::Ty,
    m: &mut Module,
    fn_idx: usize,
    bid: BlockId,
    at_span: crate::diag::Span,
) -> Option<Var> {
    if let Some(scalar_lit) = t.scalar_literal(d) {
        let const_val = scalar_literal_to_const(scalar_lit, m);
        let v = fresh_var(&m.fns[fn_idx]);
        block_mut(&mut m.fns[fn_idx], bid)
            .stmts
            .push(Stmt::Let(v, Prim::Const(const_val)));
        return Some(v);
    }
    if let Some(crate::types::ClosureLitInfo {
        target: closure_target,
        captures: closure_captures,
    }) = t.closure_lit_parts(d)
    {
        let mut cap_vars = Vec::with_capacity(closure_captures.len());
        for c in &closure_captures {
            cap_vars.push(ty_to_materialize(t, c, m, fn_idx, bid, at_span)?);
        }
        let closure_fn_id = closure_target.into();
        let v = fresh_var(&m.fns[fn_idx]);
        // fz-rrh — synthesized MakeClosure: the closure_lit type was
        // folded by the reducer. Tag the ident with the triggering
        // callsite's span so the dump points at where the reduction
        // fired.
        block_mut(&mut m.fns[fn_idx], bid).stmts.push(Stmt::Let(
            v,
            Prim::make_closure(at_span, closure_fn_id, cap_vars),
        ));
        return Some(v);
    }
    if let Some(elems) = t.tuple_lit_elems(d) {
        let mut elem_vars = Vec::with_capacity(elems.len());
        for e in &elems {
            elem_vars.push(ty_to_materialize(t, e, m, fn_idx, bid, at_span)?);
        }
        let v = fresh_var(&m.fns[fn_idx]);
        block_mut(&mut m.fns[fn_idx], bid)
            .stmts
            .push(Stmt::Let(v, Prim::MakeTuple(elem_vars)));
        return Some(v);
    }
    if t.is_empty_list_lit(d) {
        let v = fresh_var(&m.fns[fn_idx]);
        block_mut(&mut m.fns[fn_idx], bid)
            .stmts
            .push(Stmt::Let(v, Prim::MakeList(vec![], None)));
        return Some(v);
    }
    None
}

/// Convert a seam-owned scalar literal back to a `Const`. Atoms are
/// interned in `m.atom_names`, allocating a new slot if necessary.
fn scalar_literal_to_const(lit: crate::types::ScalarLiteral, m: &mut Module) -> Const {
    match lit {
        crate::types::ScalarLiteral::Int(n) => Const::Int(n),
        crate::types::ScalarLiteral::Float(f) => Const::Float(f),
        crate::types::ScalarLiteral::Nil => Const::Nil,
        crate::types::ScalarLiteral::Bool(b) => {
            if b {
                Const::True
            } else {
                Const::False
            }
        }
        crate::types::ScalarLiteral::Atom(name) => {
            let id = match m.atom_names.iter().position(|n| *n == name) {
                Some(i) => i as u32,
                None => {
                    let i = m.atom_names.len() as u32;
                    m.atom_names.push(name);
                    i
                }
            };
            Const::Atom(id)
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{BinOp, Const, FnBuilder, FnId, ModuleBuilder, Prim, Term};
    use crate::types::Types;

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
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(0),
                args: vec![c42],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(id_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut crate::types::ConcreteTypes, &mut m);

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
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(0),
                args: vec![c21],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(d_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut crate::types::ConcreteTypes, &mut m);

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
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(0),
                args: vec![p],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(id_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut crate::types::ConcreteTypes, &mut m);

        let main_fn = m.fns.iter().find(|f| f.name == "main").unwrap();
        match &main_fn.blocks[0].terminator {
            Term::TailCall { callee, .. } => assert_eq!(callee.0, 0),
            other => panic!("expected unchanged TailCall, got {:?}", other),
        }
    }

    /// `Term::if_user(cond, T, E)` with cond bound to Const(True) → Goto(T).
    #[test]
    fn folds_if_on_literal_true_to_goto() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let t_blk = b.block(vec![]);
        let e_blk = b.block(vec![]);
        let cond = b.let_(entry, Prim::Const(Const::True));
        b.set_terminator(entry, Term::if_user(cond, t_blk, e_blk));
        let nil = b.let_(t_blk, Prim::Const(Const::Nil));
        b.set_terminator(t_blk, Term::Return(nil));
        let nil2 = b.let_(e_blk, Prim::Const(Const::Nil));
        b.set_terminator(e_blk, Term::Return(nil2));

        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let mut m = mb.build();
        reduce_module(&mut crate::types::ConcreteTypes, &mut m);

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
        b.set_terminator(entry, Term::if_user(eq, base, recur));
        // base: Return(n) (always 0 when reached)
        b.set_terminator(base, Term::Return(n));
        // recur: n - 1; tail call count(n - 1)
        let c1 = b.let_(recur, Prim::Const(Const::Int(1)));
        let dec = b.let_(recur, Prim::BinOp(BinOp::Sub, n, c1));
        b.set_terminator(
            recur,
            Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
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
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(0),
                args: vec![c5],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut crate::types::ConcreteTypes, &mut m);

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
        b.set_terminator(entry, Term::if_user(eq, base, recur));
        b.set_terminator(base, Term::Return(n));
        let c1 = b.let_(recur, Prim::Const(Const::Int(1)));
        let dec = b.let_(recur, Prim::BinOp(BinOp::Sub, n, c1));
        b.set_terminator(
            recur,
            Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
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
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(0),
                args: vec![c100k],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut crate::types::ConcreteTypes, &mut m);

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
        e.set_terminator(e_entry, Term::if_user(eq_e, e_true, e_odd));
        let true_v = e.let_(e_true, Prim::Const(Const::True));
        e.set_terminator(e_true, Term::Return(true_v));
        let c1_e = e.let_(e_odd, Prim::Const(Const::Int(1)));
        let dec_e = e.let_(e_odd, Prim::BinOp(BinOp::Sub, n_e, c1_e));
        e.set_terminator(
            e_odd,
            Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
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
        o.set_terminator(o_entry, Term::if_user(eq_o, o_false, o_even));
        let false_v = o.let_(o_false, Prim::Const(Const::False));
        o.set_terminator(o_false, Term::Return(false_v));
        let c1_o = o.let_(o_even, Prim::Const(Const::Int(1)));
        let dec_o = o.let_(o_even, Prim::BinOp(BinOp::Sub, n_o, c1_o));
        o.set_terminator(
            o_even,
            Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
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
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
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
        reduce_module(&mut crate::types::ConcreteTypes, &mut m);

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
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
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
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
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
        reduce_module(&mut crate::types::ConcreteTypes, &mut m);

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
        let stall_ident = crate::fz_ir::CallsiteIdent::synthetic();
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                ident: stall_ident.clone(),
                callee: FnId(0),
                args: vec![x_main],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(id_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        let tel = crate::telemetry::ConfiguredTelemetry::new();
        let cap = crate::telemetry::Capture::new();
        tel.attach(&["fz", "reducer"], cap.handler());
        let log = reduce_module_with_telemetry(&mut crate::types::ConcreteTypes, &mut m, &tel);

        let cid = CallsiteId {
            caller: FnId(1),
            ident: stall_ident,
            slot: EmitSlot::Direct,
        };
        assert!(log.stalled.contains_key(&cid));
        assert_eq!(cap.count(&["fz", "reducer", "stalled"]), 1);
        let ev = cap.last(&["fz", "reducer", "stalled"]).unwrap();
        assert!(matches!(
            ev.metadata.get("reason"),
            Some(crate::telemetry::Value::Str(_))
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
        let consumed_ident = crate::fz_ir::CallsiteIdent::synthetic();
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                ident: consumed_ident.clone(),
                callee: FnId(0),
                args: vec![c42],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(id_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        let tel = crate::telemetry::ConfiguredTelemetry::new();
        let cap = crate::telemetry::Capture::new();
        tel.attach(&["fz", "reducer"], cap.handler());
        let log = reduce_module_with_telemetry(&mut crate::types::ConcreteTypes, &mut m, &tel);

        let cid = CallsiteId {
            caller: FnId(1),
            ident: consumed_ident,
            slot: EmitSlot::Direct,
        };
        let mut t = crate::types::ConcreteTypes;
        match log.consumed.get(&cid) {
            Some(result) => {
                assert_eq!(*result, t.int_lit(42));
            }
            None => panic!("expected Consumed log entry, got {:?}", log.consumed),
        }
        assert_eq!(cap.count(&["fz", "reducer", "consumed"]), 1);
    }

    /// fz-f88.3 — `fn pair(x, y), do: {x, y}` then `main(): pair(1, 2)`.
    /// After reduction, main returns a fresh MakeTuple whose elements
    /// resolve to Const(Int(1)) and Const(Int(2)).
    #[test]
    fn reduces_call_returning_tuple_lit() {
        let mut pair_b = FnBuilder::new(FnId(0), "pair");
        let x = pair_b.fresh_var();
        let y = pair_b.fresh_var();
        let entry = pair_b.block(vec![x, y]);
        let t = pair_b.let_(entry, Prim::MakeTuple(vec![x, y]));
        pair_b.set_terminator(entry, Term::Return(t));

        let mut main_b = FnBuilder::new(FnId(1), "main");
        let m_entry = main_b.block(vec![]);
        let c1 = main_b.let_(m_entry, Prim::Const(Const::Int(1)));
        let c2 = main_b.let_(m_entry, Prim::Const(Const::Int(2)));
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(0),
                args: vec![c1, c2],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(pair_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut crate::types::ConcreteTypes, &mut m);

        let main_fn = m.fns.iter().find(|f| f.name == "main").unwrap();
        let blk = &main_fn.blocks[0];
        let returned = match &blk.terminator {
            Term::Return(v) => *v,
            other => panic!("expected Return, got {:?}", other),
        };
        let bound = blk
            .stmts
            .iter()
            .find_map(|Stmt::Let(bv, prim)| if *bv == returned { Some(prim) } else { None })
            .expect("returned var should be bound in main");
        match bound {
            Prim::MakeTuple(elems) => {
                assert_eq!(elems.len(), 2);
                let lookup = |v: Var| -> Option<&Prim> {
                    blk.stmts.iter().find_map(
                        |Stmt::Let(bv, prim)| {
                            if *bv == v { Some(prim) } else { None }
                        },
                    )
                };
                assert!(matches!(lookup(elems[0]), Some(Prim::Const(Const::Int(1)))));
                assert!(matches!(lookup(elems[1]), Some(Prim::Const(Const::Int(2)))));
            }
            other => panic!("expected MakeTuple, got {:?}", other),
        }
    }

    /// fz-f88.3 — `fn empty(), do: []` then `main(): empty()`. After
    /// reduction, main's Return points at a fresh `MakeList(vec![], None)`.
    #[test]
    fn reduces_call_returning_empty_list() {
        let mut e_b = FnBuilder::new(FnId(0), "empty");
        let entry = e_b.block(vec![]);
        let nil_list = e_b.let_(entry, Prim::MakeList(vec![], None));
        e_b.set_terminator(entry, Term::Return(nil_list));

        let mut main_b = FnBuilder::new(FnId(1), "main");
        let m_entry = main_b.block(vec![]);
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(0),
                args: vec![],
                is_back_edge: false,
            },
        );

        let mut mb = ModuleBuilder::new();
        mb.add_fn(e_b.build());
        mb.add_fn(main_b.build());
        let mut m = mb.build();
        reduce_module(&mut crate::types::ConcreteTypes, &mut m);

        let main_fn = m.fns.iter().find(|f| f.name == "main").unwrap();
        let blk = &main_fn.blocks[0];
        let returned = match &blk.terminator {
            Term::Return(v) => *v,
            other => panic!("expected Return, got {:?}", other),
        };
        let bound = blk
            .stmts
            .iter()
            .find_map(|Stmt::Let(bv, prim)| if *bv == returned { Some(prim) } else { None })
            .expect("returned var should be bound in main");
        match bound {
            Prim::MakeList(elems, tail) => {
                assert!(elems.is_empty());
                assert!(tail.is_none());
            }
            other => panic!("expected MakeList([], None), got {:?}", other),
        }
    }

    // ------------------------------------------------------------------
    // fz-try.10 — explicit Var vs Any stall reasons
    // ------------------------------------------------------------------

    #[test]
    fn stall_reason_for_var_ty_is_unresolved_type_var() {
        // A pure-var Ty surfaces as UnresolvedTypeVar — a parametric
        // claim, not a widening one.
        let mut t = crate::types::ConcreteTypes;
        let v = t.type_var(crate::types::TypeVarId(7));
        let r = stall_reason_for_non_literal_ty(&t, &v);
        assert_eq!(r, StalledReason::UnresolvedTypeVar);
    }

    #[test]
    fn stall_reason_for_mixed_ty_is_unresolved_type_var() {
        // A type with both concrete and var content is still an
        // unresolved type variable case — the var blocks the fold; the
        // concrete part alone would have folded.
        let mut t = crate::types::ConcreteTypes;
        let int = t.int();
        let var = t.type_var(crate::types::TypeVarId(7));
        let mixed = t.union(int, var);
        let r = stall_reason_for_non_literal_ty(&t, &mixed);
        assert_eq!(r, StalledReason::UnresolvedTypeVar);
    }

    #[test]
    fn stall_reason_for_any_ty_is_opaque_arg() {
        // Genuine `any` (no info, widening fixpoint) surfaces as OpaqueArg.
        let mut t = crate::types::ConcreteTypes;
        let any = t.any();
        let r = stall_reason_for_non_literal_ty(&t, &any);
        assert_eq!(r, StalledReason::OpaqueArg);
    }

    #[test]
    fn stall_reason_for_non_literal_concrete_ty_is_opaque_arg() {
        // A concrete-but-non-singleton type (e.g., `int` as a top
        // type, not an int_lit) is OpaqueArg — we lack precision, not
        // parametricity.
        let mut t = crate::types::ConcreteTypes;
        let int = t.int();
        let r = stall_reason_for_non_literal_ty(&t, &int);
        assert_eq!(r, StalledReason::OpaqueArg);
    }

    #[test]
    fn unresolved_type_var_renders_distinctly() {
        // Display impl exists and renders distinctly from OpaqueArg so
        // outcome rows can tell them apart.
        assert_eq!(
            format!("{}", StalledReason::UnresolvedTypeVar),
            "UnresolvedTypeVar"
        );
        assert_eq!(format!("{}", StalledReason::OpaqueArg), "OpaqueArg");
        assert_ne!(
            format!("{}", StalledReason::UnresolvedTypeVar),
            format!("{}", StalledReason::OpaqueArg),
        );
    }
}
