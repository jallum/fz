//! fz-9pr.17 (fz-CO.D.0) — block-callsite enumerator for the planner's
//! discovery walk.
//!
//! `walk_spec_for_discovery` in ir_planner needs the mapping from a block's
//! terminator to "which callsite slots does it contribute, and what does each
//! one target." This module hosts that mapping once.
//!
//! ## What it yields
//!
//! Given a block and a per-Var type env (caller-side: the planner uses
//! `block_envs`), `block_callsites` produces
//! the *structural* list of callsite slots the block's terminator
//! contributes. Each entry carries the `EmitSlot` plus the data the
//! consumer needs to (a) look up / rewrite the actual term and
//! (b) compute its target spec key:
//!
//!   - `Direct` — direct target, arg `Var`s.
//!   - `CallClosureKnown` — resolved target `FnId` (via callable capability),
//!     the closure `Var`, and arg `Var`s.
//!   - `ClosureLit(c, s)` — target `FnId` from the lit, captures,
//!     arg `Var`s.
//!   - `Cont` — continuation `FnId` + captured `Var`s, plus a tag
//!     that names the slot-0 source (callee return / closure return).
//!
//! ## What it does NOT yield
//!
//! - `MakeClosure(stmt_idx)` — stmt-level, handled separately because
//!   it's a closure-value construction event, not a body-spec dispatch
//!   site. No per-callsite slot fires for it.
//! - Per-spec type keys — consumers build those from the structural
//!   payload + their own env.

use crate::fz_ir::{Cont, DirectCallTarget, EmitSlot, FnId, Term, Var};
use crate::types::{ClosureLitInfo, ClosureTypes, Ty, Types};
use std::collections::HashMap;

/// fz-9pr.17 — one structural callsite produced by a block's terminator.
///
/// `slot` is the canonical `EmitSlot` (Direct / CallClosureKnown /
/// ClosureLit(c, s) / Cont). `kind` carries the data both the planner's
/// key computation and the reducer's fold attempt need.
#[derive(Clone)]
pub struct BlockCallsite<'a> {
    pub slot: EmitSlot,
    pub kind: CallsiteKind<'a>,
}

/// fz-9pr.17 — per-slot structural payload.
#[derive(Clone)]
pub enum CallsiteKind<'a> {
    /// `Term::Call` / `Term::TailCall`. `callee` is the static target.
    Direct {
        callee: &'a DirectCallTarget,
        args: &'a [Var],
    },
    /// `Term::CallClosure` / `Term::TailCallClosure` whose `closure`
    /// Var resolved through callable capabilities to a static FnId. Carries
    /// the closure Var too so downstream consumers can recover capture-state
    /// facts from the caller spec's capability map instead of re-reading a
    /// public key that may have erased closure identity.
    CallClosureKnown {
        closure: Var,
        target: FnId,
        args: &'a [Var],
    },
    /// `Term::CallClosure` / `Term::TailCallClosure` whose `closure`
    /// Var has a closure-lit callable clause. Captures are spliced
    /// ahead of `args` when building the target key.
    ClosureLit {
        fn_id: FnId,
        captures: Vec<Ty>,
        args: &'a [Var],
    },
    /// Continuation of `Term::Call` / `Term::CallClosure`. Slot 0 of the
    /// cont's key is the value flowing in (callee return or closure return);
    /// `cont.captured[i]` lands at param slot `i + 1`.
    Cont { cont: &'a Cont, source: ContSource<'a> },
}

/// fz-9pr.17 — names the source of slot 0 for a `Cont` callsite so the
/// planner's key-builder can fetch the right effective_return / use the
/// right `any` semantics.
#[derive(Clone)]
pub enum ContSource<'a> {
    /// `Term::Call`: slot 0 = local effective return or provider-boundary any.
    Call {
        callee: &'a DirectCallTarget,
        args: &'a [Var],
    },
    /// `Term::CallClosure`: slot 0 = effective_return of the closure
    /// target (known capability path) OR resolved via closure-lit lattice.
    /// Both paths use `closure`/`args`.
    CallClosure { closure: Var, args: &'a [Var] },
}

/// fz-9pr.17 — enumerate the terminator-derived callsites of `block`.
///
/// `env` is the caller-side per-Var type env at the *end* of the
/// block's stmt sequence; used to extract a `closure` Var's
/// closure-literal callable clauses when the terminator is `CallClosure` /
/// `TailCallClosure`. `known_closure_targets` is the caller spec's resolved
/// Var → target-FnId capability map (planner-side); the reducer passes an
/// empty map and gets no `CallClosureKnown` entries — its closure-literal
/// path comes from the seam query alone.
///
/// Block-stmt callsites (`Prim::MakeClosure`) and per-stmt
/// opaque-arity bookkeeping are *not* yielded — they're planner-specific
/// and live on the planner's own per-stmt loop.
pub fn block_callsites<'a, T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    term: &'a Term,
    env: &'a HashMap<Var, Ty>,
    known_closure_targets: &HashMap<Var, FnId>,
) -> Vec<BlockCallsite<'a>> {
    let mut out: Vec<BlockCallsite<'a>> = Vec::new();
    match term {
        Term::Call {
            ident: _,
            callee,
            args,
            continuation,
        } => {
            out.push(BlockCallsite {
                slot: EmitSlot::Direct,
                kind: CallsiteKind::Direct { callee, args },
            });
            out.push(BlockCallsite {
                slot: EmitSlot::Cont,
                kind: CallsiteKind::Cont {
                    cont: continuation,
                    source: ContSource::Call { callee, args },
                },
            });
        }
        Term::TailCall { callee, args, .. } => {
            out.push(BlockCallsite {
                slot: EmitSlot::Direct,
                kind: CallsiteKind::Direct { callee, args },
            });
        }
        Term::CallClosure {
            ident: _,
            closure,
            args,
            continuation,
        } => {
            push_closure_call(t, &mut out, *closure, args, env, known_closure_targets);
            out.push(BlockCallsite {
                slot: EmitSlot::Cont,
                kind: CallsiteKind::Cont {
                    cont: continuation,
                    source: ContSource::CallClosure {
                        closure: *closure,
                        args,
                    },
                },
            });
        }
        Term::TailCallClosure {
            closure,
            args,
            ident: _,
        } => {
            push_closure_call(t, &mut out, *closure, args, env, known_closure_targets);
        }
        // fz-yxs — ReceiveMatched's clause/after bodies are FnId fields, not
        // call-shaped continuations; they're reached via callgraph_edges.
        // The bodies internally TailCall the join cont, so the join cont's
        // slot-0 type is learned through those tail calls (already enumerated
        // when each body fn is visited). Nothing to yield here.
        Term::ReceiveMatched { .. } => {}
        Term::If { .. } | Term::Goto(..) | Term::Return(..) | Term::Halt(..) => {}
    }
    out
}

fn push_closure_call<'a, T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    out: &mut Vec<BlockCallsite<'a>>,
    closure: Var,
    args: &'a [Var],
    env: &'a HashMap<Var, Ty>,
    known_closure_targets: &HashMap<Var, FnId>,
) {
    // fz-try.11 — both known-capability and closure_lit paths share the same
    // structural slot `EmitSlot::ClosureCall`. Variation between
    // statically-resolvable (known capability) and runtime-resolved (lit)
    // dispatch lives on the Dispatch enum at row time, not on the slot.
    if let Some(&target) = known_closure_targets.get(&closure) {
        out.push(BlockCallsite {
            slot: EmitSlot::ClosureCall,
            kind: CallsiteKind::CallClosureKnown { closure, target, args },
        });
    }
    if let Some(cv_ty) = env.get(&closure)
        && let Some(clauses) = t.callable_clauses(cv_ty)
    {
        for clause in clauses {
            if let Some(ClosureLitInfo { target, captures, .. }) = clause.closure {
                out.push(BlockCallsite {
                    slot: EmitSlot::ClosureCall,
                    kind: CallsiteKind::ClosureLit {
                        fn_id: FnId(target.0),
                        captures,
                        args,
                    },
                });
            }
        }
    }
}

#[cfg(test)]
mod callsite_walk_test;
