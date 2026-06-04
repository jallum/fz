//! Per-fn return-shape capabilities — cached structural facts the return-demand
//! grant reads in O(1) instead of re-walking bodies per call site.
//!
//! The retired return-context machinery recomputed "does this fn return a tuple
//! of arity N?" and "does this fn return a freshly-built list?" recursively, per
//! call edge. Those are properties of a fn's body and call graph, not of any
//! caller, so we compute them once here and store them on `ModulePlan`.
//!
//! Both callee-side facts are conjunctive over the static call graph (every
//! return path must agree), so each is a **greatest fixpoint**: start every fn
//! at its most optimistic value and retract until stable. A pure call cycle with
//! no concrete returning path therefore stays "capable" only if nothing on the
//! cycle forces otherwise — matching the old DFS, which treated a cycle edge as
//! optimistically satisfied.

use super::fn_types::{FnEffects, ReturnCapabilities, ReturnCapability};
use crate::fz_ir::{Block, FnIr, Module, Prim, Stmt, Term, Var};
use std::collections::{HashMap, HashSet};

/// Compute the per-fn `ReturnCapability` map for `m`. `fn_effects` supplies the
/// already-cached motion-safety barrier per fn.
pub(crate) fn compute_return_capabilities(m: &Module, fn_effects: &FnEffects) -> ReturnCapabilities {
    let tuple_arity = compute_tuple_arity(m);
    m.fns
        .iter()
        .map(|f| {
            let blocks_motion = fn_effects
                .get(&f.id)
                .copied()
                .unwrap_or_default()
                .blocks_return_context_motion();
            (
                f.id,
                ReturnCapability {
                    returns_tuple_of_arity: tuple_arity.get(&f.id).copied().flatten(),
                    blocks_motion,
                    destructures_slot0_into_arity: destructures_slot0_into_arity(f),
                },
            )
        })
        .collect()
}

/// Lattice for the tuple-arity greatest fixpoint: `Top` is the optimistic start
/// (no constraint yet), `Arity(n)` is "every return path so far is an n-tuple",
/// and `Bottom` is "disqualified" (a non-tuple return, conflicting arities, or a
/// terminator that does not deliver a tuple).
#[derive(Clone, Copy, PartialEq, Eq)]
enum ArityState {
    Top,
    Arity(usize),
    Bottom,
}

fn meet(a: ArityState, b: ArityState) -> ArityState {
    match (a, b) {
        (ArityState::Bottom, _) | (_, ArityState::Bottom) => ArityState::Bottom,
        (ArityState::Top, x) | (x, ArityState::Top) => x,
        (ArityState::Arity(n), ArityState::Arity(m)) => {
            if n == m {
                ArityState::Arity(n)
            } else {
                ArityState::Bottom
            }
        }
    }
}

fn compute_tuple_arity(m: &Module) -> HashMap<crate::fz_ir::FnId, Option<usize>> {
    let mut state: HashMap<_, _> = m.fns.iter().map(|f| (f.id, ArityState::Top)).collect();
    loop {
        let mut changed = false;
        for f in &m.fns {
            let next = tuple_arity_step(f, &state);
            if state[&f.id] != next {
                state.insert(f.id, next);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    state
        .into_iter()
        .map(|(id, s)| {
            (
                id,
                match s {
                    ArityState::Arity(n) => Some(n),
                    ArityState::Top | ArityState::Bottom => None,
                },
            )
        })
        .collect()
}

fn tuple_arity_step(f: &FnIr, state: &HashMap<crate::fz_ir::FnId, ArityState>) -> ArityState {
    let mut acc = ArityState::Top;
    let mut saw_exit = false;
    for b in &f.blocks {
        match &b.terminator {
            Term::Return(v) => {
                saw_exit = true;
                acc = meet(
                    acc,
                    match return_var_tuple_arity(b, *v) {
                        Some(n) => ArityState::Arity(n),
                        None => ArityState::Bottom,
                    },
                );
            }
            Term::TailCall { callee, .. } => {
                saw_exit = true;
                acc = meet(acc, state.get(callee).copied().unwrap_or(ArityState::Bottom));
            }
            // Internal edges and halts deliver no return value of their own.
            Term::Goto(_, _) | Term::If { .. } | Term::Halt(_) => {}
            // A `Call` returns through a separate continuation fn, and opaque
            // calls / receive have no statically known tuple shape.
            _ => acc = meet(acc, ArityState::Bottom),
        }
        if acc == ArityState::Bottom {
            break;
        }
    }
    if saw_exit { acc } else { ArityState::Bottom }
}

/// `Some(n)` if `ret` is defined in `b` by a tuple construction of arity `n`
/// (a direct `MakeTuple` or a frozen destination tuple), else `None`.
fn return_var_tuple_arity(b: &Block, ret: Var) -> Option<usize> {
    for Stmt::Let(dst, prim) in b.stmts.iter().rev() {
        if *dst != ret {
            continue;
        }
        return match prim {
            Prim::MakeTuple(elems) => Some(elems.len()),
            Prim::DestFreeze { dest, .. } => b.stmts.iter().find_map(|Stmt::Let(v, p)| match p {
                Prim::DestTupleBegin { arity, .. } if *v == *dest => Some(*arity),
                _ => None,
            }),
            _ => None,
        };
    }
    None
}

/// The continuation-side dual of `returns_tuple_of_arity`: `Some(n)` when `f`'s
/// slot-0 input (the result hole) is consumed purely as an `n`-tuple — every
/// use is a `TupleField(slot0, i)` projection covering `0..n`, with only
/// `TypeTest(slot0, _)` tolerated, and the tuple is never used whole. Any other
/// use of slot0 (in a prim, a terminator operand, or a continuation capture)
/// means the value is needed materially, so the producer cannot deliver fields.
fn destructures_slot0_into_arity(f: &FnIr) -> Option<usize> {
    let slot0 = *f.block(f.entry).params.first()?;
    let mut seen: HashSet<u32> = HashSet::new();
    let mut max_idx: Option<u32> = None;
    for b in &f.blocks {
        for Stmt::Let(_, prim) in &b.stmts {
            match prim {
                Prim::TupleField(v, idx) if *v == slot0 => {
                    seen.insert(*idx);
                    max_idx = Some(max_idx.map_or(*idx, |m| m.max(*idx)));
                }
                Prim::TypeTest(v, _) if *v == slot0 => {}
                other => {
                    let mut used = HashSet::new();
                    other.collect_used_vars(&mut used);
                    if used.contains(&slot0) {
                        return None;
                    }
                }
            }
        }
        if term_uses_var(&b.terminator, slot0) {
            return None;
        }
    }
    let arity = max_idx? as usize + 1;
    (arity > 0 && seen.len() == arity).then_some(arity)
}

/// Whether `term` reads `v` as a value operand — including threading it into a
/// continuation's captures. `ReceiveMatched` is treated conservatively as a use
/// (a clean tuple destructure never ends in a receive).
fn term_uses_var(term: &Term, v: Var) -> bool {
    match term {
        Term::Goto(_, args) => args.contains(&v),
        Term::If { cond, .. } => *cond == v,
        Term::Call { args, continuation, .. } => args.contains(&v) || continuation.captured.contains(&v),
        Term::TailCall { args, .. } => args.contains(&v),
        Term::CallClosure {
            closure,
            args,
            continuation,
            ..
        } => *closure == v || args.contains(&v) || continuation.captured.contains(&v),
        Term::TailCallClosure { closure, args, .. } => *closure == v || args.contains(&v),
        Term::Return(r) | Term::Halt(r) => *r == v,
        Term::ReceiveMatched { .. } => true,
    }
}

#[cfg(test)]
#[path = "capabilities_test.rs"]
mod capabilities_test;
