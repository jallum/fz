//! fz-9pr.17 (fz-CO.D.0) — block-callsite enumerator shared by the
//! reducer and the planner's discovery walk.
//!
//! Three passes (reducer, `walk_spec_for_discovery` in ir_planner, and
//! historically ir_inline) each duplicated the mapping from a block's
//! terminator to "which callsite slots does it contribute, and what
//! does each one target." This module hosts that mapping once.
//!
//! ## What it yields
//!
//! Given a block and a per-Var type env (caller-side: planner uses
//! `block_envs`, reducer uses its fold env), `block_callsites` produces
//! the *structural* list of callsite slots the block's terminator
//! contributes. Each entry carries the `EmitSlot` plus the data the
//! consumer needs to (a) look up / rewrite the actual term and
//! (b) compute its target spec key:
//!
//!   - `Direct` — callee `FnId`, arg `Var`s.
//!   - `CallClosureKnown` — resolved target `FnId` (via callable capability),
//!     the closure `Var`, and arg `Var`s.
//!   - `ClosureLit(c, s)` — target `FnId` from the lit, captures,
//!     arg `Var`s.
//!   - `Cont` — continuation `FnId` + captured `Var`s, plus a tag
//!     that names the slot-0 source (callee return / closure return
//!     / receive).
//!
//! ## What it does NOT yield
//!
//! - `MakeClosure(stmt_idx)` — stmt-level, handled separately because
//!   it's a closure-value construction event, not a body-spec dispatch
//!   site. No per-callsite slot fires for it.
//! - Per-spec type keys — consumers build those from the structural
//!   payload + their own env.
//!
//! ## Why the reducer also calls it
//!
//! The reducer rewrites the terminator (which is per-Term, not
//! per-callsite), so its `reduce_terminator` keeps the `match` on
//! `Term`. But the "what slot would I record stalled/consumed against"
//! decision is exactly `block_callsites`'s `slot` field — so the
//! reducer asks the enumerator (via `slot_for_term`) for that one
//! piece of vocabulary, killing the four duplicated `EmitSlot::Direct`
//! / `EmitSlot::ClosureCall` literals scattered across the four
//! arms of `reduce_terminator`.

use crate::fz_ir::{Cont, EmitSlot, FnId, Term, Var};
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
    /// `Term::Call` / `Term::TailCall`. `callee` is the static FnId.
    Direct { callee: FnId, args: &'a [Var] },
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
    /// Continuation of `Term::Call` / `Term::CallClosure` /
    /// `Term::Receive`. Slot 0 of the cont's key is the value flowing
    /// in (callee return, closure return, or the received message);
    /// `cont.captured[i]` lands at param slot `i + 1`.
    Cont { cont: &'a Cont, source: ContSource<'a> },
}

/// fz-9pr.17 — names the source of slot 0 for a `Cont` callsite so the
/// planner's key-builder can fetch the right effective_return / use the
/// right `any` semantics.
#[derive(Clone)]
pub enum ContSource<'a> {
    /// `Term::Call`: slot 0 = `effective_returns[(callee, arg_tys)]`.
    Call { callee: FnId, args: &'a [Var] },
    /// `Term::CallClosure`: slot 0 = effective_return of the closure
    /// target (known capability path) OR resolved via closure-lit lattice.
    /// Both paths use `closure`/`args`.
    CallClosure { closure: Var, args: &'a [Var] },
    /// `Term::Receive`: slot 0 is opaque (`any`).
    Receive,
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
                kind: CallsiteKind::Direct { callee: *callee, args },
            });
            out.push(BlockCallsite {
                slot: EmitSlot::Cont,
                kind: CallsiteKind::Cont {
                    cont: continuation,
                    source: ContSource::Call { callee: *callee, args },
                },
            });
        }
        Term::TailCall { callee, args, .. } => {
            out.push(BlockCallsite {
                slot: EmitSlot::Direct,
                kind: CallsiteKind::Direct { callee: *callee, args },
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
        Term::Receive { continuation, ident: _ } => {
            out.push(BlockCallsite {
                slot: EmitSlot::Cont,
                kind: CallsiteKind::Cont {
                    cont: continuation,
                    source: ContSource::Receive,
                },
            });
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
            if let Some(ClosureLitInfo { target, captures }) = clause.closure {
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

/// fz-9pr.17 — the canonical `EmitSlot` the reducer should record
/// against when its fold attempt at a block's terminator succeeds or
/// stalls. Returns `None` for non-call terminators.
///
/// Post-fz-try.11: closure-call terminators map to the uniform
/// `EmitSlot::ClosureCall`; clause-fanout variation moves to the
/// Dispatch enum at row time.
pub fn slot_for_term(term: &Term) -> Option<EmitSlot> {
    match term {
        Term::Call { .. } | Term::TailCall { .. } => Some(EmitSlot::Direct),
        Term::CallClosure { .. } | Term::TailCallClosure { .. } => Some(EmitSlot::ClosureCall),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{BlockId, CallsiteIdent, Cont, FnId, Term, Var};
    use crate::types::{ClosureTypes, ConcreteTypes, Types};

    fn empty_env() -> HashMap<Var, Ty> {
        HashMap::new()
    }
    fn empty_fc() -> HashMap<Var, FnId> {
        HashMap::new()
    }

    #[test]
    fn empty_for_non_call_terms() {
        let mut t = ConcreteTypes;
        let env = empty_env();
        let fc = empty_fc();
        assert!(block_callsites(&mut t, &Term::Goto(BlockId(0), vec![]), &env, &fc).is_empty());
        assert!(block_callsites(&mut t, &Term::if_user(Var(0), BlockId(0), BlockId(1)), &env, &fc).is_empty());
        assert!(block_callsites(&mut t, &Term::Return(Var(0)), &env, &fc).is_empty());
        assert!(block_callsites(&mut t, &Term::Halt(Var(0)), &env, &fc).is_empty());
    }

    #[test]
    fn tail_call_yields_direct_only() {
        let mut ct = ConcreteTypes;
        let t = Term::TailCall {
            ident: CallsiteIdent::synthetic(),
            callee: FnId(7),
            args: vec![Var(1), Var(2)],
            is_back_edge: false,
        };
        let env = empty_env();
        let fc = empty_fc();
        let cs = block_callsites(&mut ct, &t, &env, &fc);
        assert_eq!(cs.len(), 1);
        assert!(matches!(cs[0].slot, EmitSlot::Direct));
        match &cs[0].kind {
            CallsiteKind::Direct { callee, args } => {
                assert_eq!(callee.0, 7);
                assert_eq!(args.len(), 2);
            }
            _ => panic!("expected Direct"),
        }
    }

    #[test]
    fn call_yields_direct_then_cont() {
        let mut tct = ConcreteTypes;
        let t = Term::Call {
            ident: CallsiteIdent::synthetic(),
            callee: FnId(5),
            args: vec![Var(1)],
            continuation: Cont {
                fn_id: FnId(9),
                captured: vec![Var(2)],
            },
        };
        let env = empty_env();
        let fc = empty_fc();
        let cs = block_callsites(&mut tct, &t, &env, &fc);
        assert_eq!(cs.len(), 2);
        assert!(matches!(cs[0].slot, EmitSlot::Direct));
        assert!(matches!(cs[1].slot, EmitSlot::Cont));
        match &cs[1].kind {
            CallsiteKind::Cont {
                cont,
                source: ContSource::Call { callee, .. },
            } => {
                assert_eq!(cont.fn_id.0, 9);
                assert_eq!(callee.0, 5);
            }
            _ => panic!("expected Cont/Call source"),
        }
    }

    #[test]
    fn tail_call_closure_unresolved_yields_nothing() {
        let mut ct = ConcreteTypes;
        let term = Term::TailCallClosure {
            ident: CallsiteIdent::synthetic(),
            closure: Var(3),
            args: vec![Var(1)],
        };
        let env = empty_env();
        let fc = empty_fc();
        let cs = block_callsites(&mut ct, &term, &env, &fc);
        assert!(cs.is_empty());
    }

    #[test]
    fn tail_call_closure_known_fns_yields_known() {
        let mut ct = ConcreteTypes;
        let term = Term::TailCallClosure {
            ident: CallsiteIdent::synthetic(),
            closure: Var(3),
            args: vec![Var(1)],
        };
        let env = empty_env();
        let mut fc = empty_fc();
        fc.insert(Var(3), FnId(11));
        let cs = block_callsites(&mut ct, &term, &env, &fc);
        assert_eq!(cs.len(), 1);
        assert!(matches!(cs[0].slot, EmitSlot::ClosureCall));
    }

    #[test]
    fn tail_call_closure_closure_lit_yields_lit_callsite() {
        let mut ct = ConcreteTypes;
        let term = Term::TailCallClosure {
            ident: CallsiteIdent::synthetic(),
            closure: Var(3),
            args: vec![Var(1)],
        };
        let mut env = empty_env();
        let cap = ct.int_lit(7);
        env.insert(Var(3), ct.closure_lit(FnId(11).into(), vec![cap], 1));
        let fc = empty_fc();
        let cs = block_callsites(&mut ct, &term, &env, &fc);
        assert_eq!(cs.len(), 1);
        match &cs[0].kind {
            CallsiteKind::ClosureLit { fn_id, captures, args } => {
                assert_eq!(fn_id.0, 11);
                assert_eq!(captures.len(), 1);
                assert_eq!(args.len(), 1);
            }
            _ => panic!("expected ClosureLit"),
        }
    }

    #[test]
    fn call_closure_yields_cont_when_closure_unresolved() {
        let mut tct = ConcreteTypes;
        let t = Term::CallClosure {
            ident: CallsiteIdent::synthetic(),
            closure: Var(3),
            args: vec![Var(1)],
            continuation: Cont {
                fn_id: FnId(9),
                captured: vec![],
            },
        };
        let env = empty_env();
        let fc = empty_fc();
        let cs = block_callsites(&mut tct, &t, &env, &fc);
        assert_eq!(cs.len(), 1);
        assert!(matches!(cs[0].slot, EmitSlot::Cont));
    }

    #[test]
    fn receive_yields_cont_with_receive_source() {
        let mut ct = ConcreteTypes;
        let term = Term::Receive {
            ident: CallsiteIdent::synthetic(),
            continuation: Cont {
                fn_id: FnId(9),
                captured: vec![],
            },
        };
        let env = empty_env();
        let fc = empty_fc();
        let cs = block_callsites(&mut ct, &term, &env, &fc);
        assert_eq!(cs.len(), 1);
        match &cs[0].kind {
            CallsiteKind::Cont {
                source: ContSource::Receive,
                ..
            } => {}
            _ => panic!("expected Receive source"),
        }
    }

    #[test]
    fn slot_for_term_routes_each_kind() {
        assert!(matches!(
            slot_for_term(&Term::TailCall {
                ident: CallsiteIdent::synthetic(),
                callee: FnId(0),
                args: vec![],
                is_back_edge: false
            }),
            Some(EmitSlot::Direct)
        ));
        assert!(matches!(
            slot_for_term(&Term::TailCallClosure {
                ident: CallsiteIdent::synthetic(),
                closure: Var(0),
                args: vec![]
            }),
            Some(EmitSlot::ClosureCall)
        ));
        assert!(slot_for_term(&Term::Halt(Var(0))).is_none());
    }
}
